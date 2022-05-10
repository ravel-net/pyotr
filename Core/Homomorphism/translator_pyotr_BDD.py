import sys
import os
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

import re
import psycopg2 
import copy
from time import time
from tqdm import tqdm
import z3
from z3 import And, Not, Or, Implies
import databaseconfig as cfg
from psycopg2.extras import execute_values

# BDD manager Module
import BDD_managerModule as bddmm
import pyotr_translator_BDD.BDD_manager.encodeCUDD as encodeCUDD

OPEN_OUTPUT = True
conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# Set domain knowledge
DOMAIN = ['1', '2'] # daulft domain [1, 2]
VARIABLES = []
EMPTY_CONDITION_IDX = None

def set_domain(domain): # TODO: support vary domain for each variable
    global DOMAIN 
    DOMAIN = domain

def set_variables(variables):
    global VARIABLES
    VARIABLES = variables

def set_empty_condition_index(idx):
    global EMPTY_CONDITION_IDX
    EMPTY_CONDITION_IDX = idx

# def str_to_BDD(condition):
#     return 0

# def operate_BDDs(bdd1, bdd2, op):
#     return 0

def process_condition_on_ctable(tablename):
    """
    convert condition to BDD version
    """
    cursor = conn.cursor()
    sql = "select * from {}".format(tablename)
    cursor.execute(sql)

    count_num = cursor.rowcount
    
    '''
    locate condition
    '''
    cond_idx = -1
    for idx, col in enumerate(cursor.description):
        if 'condition' in col[0]:
            cond_idx = idx

    new_tuples = []
    for i in tqdm(range(count_num)):
        row = cursor.fetchone()
        list_row = list(row)

        if len(list_row[cond_idx]) == 0:
            # list_row[cond_idx] = None
            if EMPTY_CONDITION_IDX is None:
                condition = ""
                begin_process = time()
                encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, DOMAIN, VARIABLES)
                end_process_encode = time()
                empty_condition_idx = bddmm.str_to_BDD(encoded_c)
                end_process_strToBDD = time()
                if OPEN_OUTPUT:
                    print("Time to encode condition {}: {} s".format(empty_condition_idx, end_process_encode-begin_process))
                    print("Time to str_to_BDD in condition {}: {} s".format(empty_condition_idx, end_process_strToBDD-end_process_encode))
                set_empty_condition_index(empty_condition_idx)
            list_row[cond_idx] = EMPTY_CONDITION_IDX
        else:
            condition = ", ".join(list_row[cond_idx])
            print(condition)

            # bdd_idx = str_to_BDD(condition) # TODO: integrate C API (DONE)
            # Call BDD module 
            begin_process = time()
            encoded_c, variablesArray = encodeCUDD.convertToCUDD(condition, DOMAIN, VARIABLES)
            end_process_encode = time()
            bdd_idx = bddmm.str_to_BDD(encoded_c)
            end_process_strToBDD = time()
            if OPEN_OUTPUT:
                print("Time to encode condition {}: {} s".format(bdd_idx, end_process_encode-begin_process))
                print("Time to str_to_BDD in condition {}: {} s".format(bdd_idx, end_process_strToBDD-end_process_encode))
            list_row[cond_idx] = bdd_idx

        row = tuple(list_row)
        new_tuples.append(copy.deepcopy(row))

    out_tablename = tablename + '_bdd'
    
    sql = "drop table if exists {out_tablename}".format(out_tablename=out_tablename)
    cursor.execute(sql)

    sql = "create table {out_tablename} as select * from {tablename} with NO DATA".format(out_tablename=out_tablename, tablename=tablename)
    cursor.execute(sql)

    sql = "alter table if exists {out_tablename} drop column condition".format(out_tablename=out_tablename)
    cursor.execute(sql)

    # sql = "alter table if exists {out_tablename} alter condition type integer USING(condition::integer)".format(out_tablename=out_tablename)
    sql = "alter table if exists {out_tablename} add column condition integer".format(out_tablename=out_tablename)
    cursor.execute(sql)

    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    execute_values(cursor, sql, new_tuples)
    # cursor.executemany(new_tuples)
    conn.commit()

    return out_tablename

#create data content
def data(tree):
    if OPEN_OUTPUT:
        print("\n************************Step 1: create data content****************************")
    cursor = conn.cursor()
    table_num = len(tree['from'])

    """
    # if the number of table > 1
    # it operates join, no matter it is * or selected columns, extract all columns from all tables
    # if the number of table = 1
    # it may operates selection or projection
    """
    sql = ""

    columns = get_all_columns(tree['from'])
    extra_cols = get_extra_columns(tree['select'])

    new_tree = copy.deepcopy(tree)
    new_tree['select'] = extra_cols + columns  
    sql = "create table output as " + tree_to_str(new_tree)
    if OPEN_OUTPUT:
        print(sql)
    
    cursor.execute("DROP TABLE IF EXISTS output")
    begin = time()
    cursor.execute(sql)
    end = time()
    if OPEN_OUTPUT:
        print("\ndata executing time: ", end-begin)
    # logging.warning("data execution time: %s" % str(end-begin))
    
    conn.commit()
    return end-begin

def upd_condition(tree, datatype):
    count_time = 0
    if OPEN_OUTPUT:
        print("\n************************Step 2: update condition****************************")
    cursor = conn.cursor()

    '''
    process the corresponding columns of join/selection conditions
    '''
    where_clause = tree['where']
    keyword = list(where_clause.keys())[0]
    conditions = copy.deepcopy(where_clause[keyword])

    sql = ""
    cond_list = []
    where_list = [] # store left operand and right operand
    for cond in conditions:
        if cond[0][1] == '.': cond[0][1] = '_'
        if cond[2][1] == '.': cond[2][1] = '_'
        left_opd = "".join(cond[0])
        right_opd = "".join(cond[2])

        if cond[1] == '=':
            cond_list.append("{} || ' {} ' || {}".format(left_opd, '==', right_opd))
        else:
            cond_list.append("{} || ' {} ' || {}".format(left_opd, cond[1], right_opd))
        
        where_list.append([left_opd, right_opd])
    '''
    get condition columns from all tables
    '''
    from_clause = tree['from']
    cond_cols = []
    for t in from_clause:
        if t[2] == '': # no alias
            cond_cols.append("{}_condition".format(t[0]))
        else:
            cond_cols.append("{}_condition".format(t[2]))

    '''
    add id column which is primary key
    '''
    cursor.execute("select * from output limit 1")
    cols_name = [row[0] for row in cursor.description]
    if 'id' not in cols_name:
        cursor.execute("ALTER TABLE output ADD COLUMN id SERIAL PRIMARY KEY;")
    else:
        cols_name.remove('id')

    ''' 
    get the join/selection conditions(new condition) and two old condition indices
    '''
    upd_conditions = {}
    sql = "select {}, {}, id from output".format(", ".join(cond_list), ", ".join(cond_cols))

    len_cond_cols = len(cond_cols)
    bound = len_cond_cols + 1
    pos = -bound
    total_BDD_time = 0

    if OPEN_OUTPUT:
        print(sql)
    cursor.execute(sql)
    count_num = cursor.rowcount

    # print("current directory:", os.getcwd())
    # current_direcory = os.getcwd()
    # f = open(current_direcory+"/join_condition.txt", "a")
    # f.write("new_condition_idx sat condition\n")
    # f2 = open(current_direcory+"/old_condition.txt", "a")
    # f2.write("old_condition_idx sat indexes\n")
    # f3 = open(current_direcory+"/new_condition.txt", "a")
    # f3.write("new_condition_idx sat indexes\n")

    for i in tqdm(range(count_num)):
        row = cursor.fetchone()
        c_condition = ""

        if keyword == '' or keyword == 'and':
            c_condition = "And({})".format(", ".join(list(row[:pos])))
        else:
            c_condition = "Or({})".format(", ".join(list(row[:pos])))
        '''
        convert new join/selection conditions to BDD version
        '''
        begin_encode = time()
        encoded_c, variable_arr = encodeCUDD.convertToCUDD(c_condition, DOMAIN, VARIABLES)
        begin = time()
        bdd_c_idx = bddmm.str_to_BDD(encoded_c)
        end = time()
        if OPEN_OUTPUT:
            print("Time to encode condition {}: {} s".format(bdd_c_idx, begin-begin_encode))
            print("Time to str_to_BDD in condition {}: {} s".format(bdd_c_idx, end-begin))
        total_BDD_time += end - begin

        # sat = bddmm.evaluate(bdd_c_idx)
        # f.write("{} {} {}\n".format(bdd_c_idx, sat, c_condition)) # new_condition_idx
        '''
        logical operation on old BDDs
        '''
        bdds_idx = None
        
        for i in range(pos, -1): # -1 is the position of id, 
            if row[i] is None:
                continue
            
            bdd1 = bdds_idx
            if bdd1 is None:
                bdds_idx = row[i]
                continue
            
            bdd2 = row[i]
            begin = time()
            bdds_idx = bddmm.operate_BDDs(bdd1, bdd2, "&")
            end = time()
            if OPEN_OUTPUT:
                print("Time to operate BDD {} &: {} s".format(bdds_idx, end-begin))
            total_BDD_time += end - begin

        # sat_f2 = bddmm.evaluate(bdds_idx)
        # f2.write("{} {} {}\n".format(bdds_idx, sat_f2, row[pos:-1])) # old_condition_idx

        new_idx = None
        if bdds_idx is not None and bdd_c_idx is not None:
            begin = time()
            new_idx = bddmm.operate_BDDs(bdds_idx, bdd_c_idx, "&")
            end = time()
            if OPEN_OUTPUT:
                print("Time to operate BDD {} &: {} s".format(new_idx, end-begin))
            total_BDD_time += end - begin
        elif bdds_idx is None:
            new_idx = bdd_c_idx
        else:
            new_idx = bdds_idx
        
        # print("new_idx:", new_idx, "Sat:", sat)
        # sat_f3 = bddmm.evaluate(new_idx)
        # f3.write("{} {} {}\n".format(new_idx, sat_f3, [bdd_c_idx, bdds_idx]))

        upd_conditions[row[-1]] = new_idx # key is id
        # print("new_idx", new_idx)
        # print(upd_conditions)
        # print("---------------------------")
    # print(upd_conditions)
    # f.close()
    # f2.close()
    # f3.close()

    sql = "alter table if exists output add column condition integer"
    cursor.execute(sql)
    conn.commit()

    for key in upd_conditions.keys():
        sql = "update output set condition = {} where id = {}".format(upd_conditions[key], key)
        cursor.execute(sql)
    conn.commit()

    '''
    Check the selected columns
    if select *, drop duplicated columns,
    else only keep selected columns
    '''
    drop_cols = set()
    if '*' in tree['select']:
        # remove duplicated columns
        for cond in conditions:
            if cond[1] == '=':
                left_opd = "".join(cond[0])
                right_opd = "".join(cond[2])
                sql = "update output set {} = {} where not is_var({}::{})".format(left_opd, right_opd, right_opd, datatype)
                if right_opd in cols_name:
                    drop_cols.add(right_opd)
                if OPEN_OUTPUT:
                    print(sql)
                cursor.execute(sql)
    else:
        # only keep specified columns
        selected_cols = copy.deepcopy(tree['select'])
        select_col_dict = {}
        for col in selected_cols:
            if col[0][1] == '.': 
                col[0][1] = '_'
            
            if "'" in col[0][2]: # working when select constant value
                col[0][2] = col[0][2].replace("'", "")
                
            name = "".join(col[0])
            select_col_dict[name] = col[2]

        rename_col = []
        keys = select_col_dict.keys()
        for col in cols_name:
            if col in keys and select_col_dict[col] != '' and col != select_col_dict[col] :
                rename_col.append("{} to {}".format(col, select_col_dict[col]))
                continue
            if col == 'condition':
                continue
            if col not in keys:
                drop_cols.add(col)

        if len(rename_col) > 0: 
            for new_col in rename_col:
                sql = "ALTER TABLE output rename column " + new_col
                if OPEN_OUTPUT:
                    print(sql)
                cursor.execute(sql)
    
    # drop old condition column from table
    drop_cols = drop_cols.union(cond_cols)
    # print(drop_cols)
    if len(drop_cols) > 0:
        sql = "ALTER TABLE output drop column " + ", drop column ".join(drop_cols)
        if OPEN_OUTPUT:
            print(sql)
        cursor.execute(sql)
    conn.commit()
    if OPEN_OUTPUT:
        print("\ncondition execution time:", count_time)
    return total_BDD_time

def generate_tree(query):
    tree = {}
    # remove ;
    if ';' in query:
        query = query[:-1]
    query_lower = query.lower()
    
    select_pattern = re.compile(r'select(.*?)from', re.S)
    select_clause = re.findall(select_pattern, query_lower)
    tree["select"] = process_select_clause(select_clause[0].strip())
    
    from_clause = ""
    from_pattern_may_include_where = re.compile(r'from(.*)', re.S)
    from_clause_may_include_where = re.findall(from_pattern_may_include_where, query_lower)[0].strip()

    '''
    get substring from 'from' keyword to the end
    sql may contain 'where' clause or not
    '''
    if 'where' in from_clause_may_include_where:
        patern = re.compile(r'(.*?)where', re.S)
        from_clause = re.findall(patern, from_clause_may_include_where)[0].strip()
        # detect the location of where
        where_index = query_lower.find('where')
        where_clause = query[where_index+5:]
        tree["where"] = process_where_clause(where_clause.strip())
    else:
        from_clause = from_clause_may_include_where
    tree["from"] = process_from_clause(from_clause)

    if OPEN_OUTPUT:
        print(tree) 
    return tree

def tree_to_str(tree):
    tree_copy = copy.deepcopy(tree)
    sql_parts = []

    select_clause = tree_copy['select']
    select_part = ''
    if '*' in select_clause:
        select_part = '*'
    else:
        for idx, c in enumerate(select_clause):
            c[0] = "".join(c[0])
            if c[1] == 'as':
                select_clause[idx] = " ".join(c)
            else:
                select_clause[idx] = "".join(c)
        # select_clause = list(set(select_clause))
        '''
        remove duplicates in all columns and extra columns
        '''
        select_clause_no_dup = []
        for s in select_clause:
            if s not in select_clause_no_dup:
                select_clause_no_dup.append(s)

        select_part = ", ".join(select_clause_no_dup)
    sql_parts.append('select')
    sql_parts.append(select_part)

    from_clause = tree_copy['from']
    for idx, f in enumerate(from_clause):
        if f[1] == '' or f[1] == ' ':
            from_clause[idx] = "".join(f)
        else:
            from_clause[idx] = " ".join(f)
    from_part = ", ".join(from_clause)
    sql_parts.append('from')
    sql_parts.append(from_part)

    if 'where' in tree_copy.keys():
        sql_parts.append('where')
        where_clause = tree_copy['where']
        key = list(where_clause.keys())[0]
        conditions = where_clause[key]
        for idx, f in enumerate(conditions):
            f[0] = "".join(f[0])
            f[2] = "".join(f[2])
            where_clause[key][idx] = " ".join(f)
        where_part = " {} ".format(key).join(where_clause[key])
        sql_parts.append(where_part)

    sql = " ".join(sql_parts)
    # print(sql)
    return sql

def process_opr(cond):
    # if (not cond[0][2].isdigit()) and (not cond[2][2].isdigit()):
    #     usr_func = opr_to_func(cond[1])
    #     return [usr_func, '(', [cond[0], cond[2]], ')']
    usr_func = opr_to_func(cond[1])
    return [usr_func, '(', [cond[0], cond[2]], ')']
    # return cond

def opr_to_func(opr):
    if opr == '!=' or opr == '<>':
        return 'not_equal'
    elif opr == '<':
        return 'less'
    elif opr == '>':
        return 'greater'
    elif opr == '<=':
        return 'leq'
    elif opr == '>=':
        return 'geq'
    elif opr == '=':
        return 'equal'
    
def process_select_clause(clause):
    cols = []
    if '*' in clause:
        return "*"
    for col in clause.split(','):
        col = col.strip()

        tuple = [] #[tablename, '.'/'', colname, 'as'/'', renaming_name]
        # whether exits renaming col, keyword is AS or space(omit AS)
        newname_list = ['', '']
        if 'as' in col or ' ' in col:
            items = []
            if 'as' in col:
                items = col.split('as')
                newname_list[0] = 'as'
            else:
                items = col.split(' ')
                newname_list[0] = ' '
            newname_list[1] = items[1].strip()
            col = items[0].strip()
        
        # whether determine table name
        if '.' in col:
            items = col.split('.')
            tuple = [items[0].strip(), '.', items[1].strip()]
        else:
            tuple = ['', '', col]
        
        t = [tuple]
        t.extend(newname_list) # t --> [[tablename, flag, colname], flag, newcolname]
        cols.append(t)
    
    return cols

def process_from_clause(clause):
    cols = []
    for col in clause.split(','):
        col = col.strip()

        tuple = [''] #[tablename, 'as'/'', renaming_name]
        # whether exits renaming table, keyword is AS or space(omit AS)
        newname_list = ['', '']
        if 'as' in col or ' ' in col:
            items = []
            if 'as' in col:
                items = col.split('as')
                newname_list[0] = 'as'
            else:
                items = col.split(' ')
                newname_list[0] = ' '
            newname_list[1] = items[1].strip()
            col = items[0].strip()
        
        tuple[0] = col
     
        tuple += newname_list
        cols.append(tuple)
    # cols = [col.strip() for col in clause.split(',')]
    return cols

def process_where_clause(clause):
    cond_list = []
    conditions = re.split('and|or', clause, flags=re.IGNORECASE)
    for c in conditions:
        c = c.strip() 
        match = re.search('!=|<=|>=|<>|<|>|=', c)
        left_opd = c[:match.span()[0]].strip()
        opr = match.group()
        right_opd = c[match.span()[1]:].strip()
        
        # whether specify table's name
        left_opr_list = ['', '', ''] # [tablename, '.'/'', col]
        if '.' in left_opd:
            items = left_opd.split('.')
            left_opr_list[0] = items[0].strip()
            left_opr_list[1] = '.'
            left_opr_list[2] = items[1].strip()
        else:
            left_opr_list[2] = left_opd

        # whether specify table's name
        right_opr_list = ['', '', ''] # [tablename, '.'/'', col]
        if '.' in right_opd:
            items = right_opd.split('.')
            right_opr_list[0] = items[0].strip()
            right_opr_list[1] = '.'
            right_opr_list[2] = items[1].strip()
        else:
            right_opr_list[2] = right_opd
        
        # cond = process_opr([left_opr_list, opr, right_opr_list]) #(left_operand, operator, right_operand)
        cond = [left_opr_list, opr, right_opr_list]
        cond_list.append(cond)
    
    
    match = re.search('and|or', clause, flags=re.IGNORECASE)
    keyword = match.group().lower() if match is not None else ""

    return {keyword:cond_list}

def get_all_columns(tables):
    columns = []
    # col_conds = []
    cursor = conn.cursor()
    if len(tables) == 1:
        t = tables[0] # t format: [tablename, as/space, alias]
        cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
        for col in cursor.description:
            # if 'cond' in col[0]:
            #     if t[2] == '': # no alias, use tablename 
            #         col_conds.append("{}.{}".format(t[0], col[0]))
            #     else: # use alias
            #         col_conds.append("{}.{}".format(t[2], col[0]))
            #     continue
            if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                if 'condition' in col[0]:
                    columns.append([['', '', col[0]], 'as', '{}_{}'.format(t[0], col[0])])
                else:
                    columns.append([['', '', col[0]], '', ''])
            else:
                columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
    else:
        for t in tables:
            cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
            for col in cursor.description:
                # if 'cond' in col[0]:
                #     if t[2] == '':
                #         col_conds.append("{}.{}".format(t[0], col[0]))
                #     else:
                #         col_conds.append("{}.{}".format(t[2], col[0]))
                #     continue

                if col[0].isdigit() or type(col[0]) == int: # select constant column
                    columns.append([['', '', col[0]], 'as', '"{}"'.format(col[0])])
                    continue

                if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                    columns.append([[t[0], '.', col[0]], 'as', '{}_{}'.format(t[0], col[0])])
                else:
                    columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
        # print(col_conds)
    # columns.append([['', '', ' || '.join(col_conds)], 'as', 'condition'])
    # print(columns)
    return columns

def get_extra_columns(select):
    extra_cols = []
    if select == '*':
        return extra_cols
    for s in select: # s format: [['t0', '.', 'n1'], '', ''] or [['', '', "'1'"], '', ''] select 1 or  [['', '', "'w'"], '', ''] select 'w'
        col = s[0][2]
        if "'" in col: # select constant value, such as '1', 'w'
            p = re.compile(r"'(.*?)'", re.S)
            col = re.findall(p, col)[0]
            extra_cols.append([['', '', s[0][2]], 'as', '"{}"'.format(col)]) 
        
        elif col.isdigit(): # select inetger number such as 1
            extra_cols.append([['', '', s[0][2]], 'as', '"{}"'.format(col)])
    return extra_cols            

            
if __name__ == "__main__":
    # sql = "select policy1.path, policy2.dest from policy1, policy2 where policy1.path = policy2.path and policy1.dest != policy2.dest;"
    # sql = "select * from policy1, policy2 where policy1.path = policy2.path and policy1.dest != policy2.dest;"
    # sql = "select * from policy1 where path != '123'"
    # sql = "select 1, path from policy1 where path != '123'"
    # sql = "select t1.n1 as n1, t3.n2 as n2 from tv t1, tv t2, tv t3, tv t4, tv t5, tv t6 where t1.n1 = 1 aNd t2.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = 2 and t4.n1 = 1 and t4.n2 = 1 and t5.n1 = 'u' and t5.n2 = 'u' and t6.n1 = 'v' and t6.n2 = 'v';" 
    # sql = "select * from bgp_policy where dest = '1' aNd (path='1' or min_len<2);"
    # sql = "select * from policy1, policy2 where policy1.dest = policy2.dest"
    # sql = "select a, b from policy1"
    # sql = "select policy1.dest as dest, policy2.path as path from policy1, policy2 where policy1.dest = policy2.dest and policy1.path = policy2.path"
    # sql = "select * from f_table_rib1000 f1, f_table_rib1000 f2, f_table_rib1000 f3 where f1.fid = f2.fid or f2.fid = f3.fid or f1.nid2 = f2.nid1 or f2.nid2 = f3.nid1"
    # sql = "select * from f_table_rib1000 f1, f_table_rib1000 f2 where f1.fid = f2.fid and f1.nid2 = f2.nid1"
    # sql = "select * from policy1 where path != '[ABC]'"
    # sql = "select f1.n1, f3.n2 from fw f1, fw f2, fw f3 where f1.n2 = f2.n1 and f2.n2 = f3.n2"
    # sql = "select t1.n1, t2.n2 from tp t1, tp t2 where t1.n1 = '1' and t1.n2 = '1' and t2.n1 = '1' and t2.n2 = '2';"
    # sql = "select t2.n1, t2.n2 from tp t1, tp t2 where t1.n1 = '1' and t1.n2 = '1' and t2.n1 = '1' and t2.n2 = '2';"
    # sql = "select t1.n1, t3.n2 from tv t1, tv t2, tv t3, tv t4, tv t5, tv t6 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '2' and t4.n1 = '1' and t4.n2 = '1' and t5.n1 = t5.n2 and t6.n1 = t6.n2 and t1.n1 = t4.n1 and t2.n1 = t5.n1 and t3.n1 = t6.n1;"
    # sql = "select t1.n1, t3.n2 from tp t1, tp t2, tp t3, tp t4, tp t5, tp t6 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '2' and t4.n1 = '1' and t4.n2 = '1' and t5.n1 = t5.n2 and t6.n1 = t6.n2 and t1.n1 = t4.n1 and t2.n1 = t5.n1 and t3.n1 = t6.n1;"
    # sql = "select t0.n1 as n1, t1.n2 as n2 from f4755_intf t0, f4755_intf t1 where t0.n2 = t1.n1 and t0.n1 != t1.n2"
    # sql = "select t0.n1, t2.n2 from tp t0, tp t1, tp t2, tp t3, tp t4, tp t5 where t0.n1 = '1' and t0.n2 = t1.n1 and t2.n2 = '2' and t1.n2 = t2.n1 and t3.n1 = '1' and t3.n2 = '1' and t4.n1 = t4.n2 and t1.n1 = t4.n2 and t5.n1 = t5.n2 and t2.n1 = t5.n2"
    bddmm.initialize(3, 2)
    set_domain(['1', '2'])
    set_variables(['x', 'y', 'z'])

    process_condition_on_ctable('fwd') # convert string version condition to BDD version

    # sql = "select * from fwd_bdd where n2 != '2' and n1 = n2" # run successfuly
    # sql = "select * from fwd_bdd where n2 != '2'" # happens memory leakage on str_to_BDD()
    # sql = "select t1.n1, t2.n2 from fwd_bdd t1, fwd_bdd t2 where t1.n1 = '1' and t1.n2 = t2.n1"
    sql = "select 1, t2.n2 from fwd_bdd t1, fwd_bdd t2 where t1.n1 = '1' and t1.n2 = t2.n1"
    tree = generate_tree(sql)

    # begin = time.time()
    data(tree)
    upd_condition(tree)

    merge_tuples.merge_tuples("output", "merged",  ['1', '2'], ['x', 'y', 'z'])
