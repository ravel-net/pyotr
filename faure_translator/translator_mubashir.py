from os import rename
import re
import psycopg2 
import copy
import time
from tqdm import tqdm
import z3
import pprint
from z3 import And, Not, Or, Implies
import databaseconfig as cfg
from os.path import dirname, abspath, join
import sys
root = dirname(dirname(abspath(__file__)))
filename = join(root, 'util')
sys.path.append(filename)
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
import tableau as tableau
import closure_overhead
# import logging
# logging.basicConfig(filename='joins_data/joins_typed.log', level=logging.DEBUG)

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

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

    # print(tree)
    return tree

#create data content
def data(tree):
    # print("\n************************Step 1: create data content****************************")
    cursor = conn.cursor()
    table_num = len(tree['from'])

    """
    # if the number of table > 1
    # it operates join, no matter it is * or selected columns, extract all columns from all tables
    # if the number of table = 1
    # it may operates selection or projection
    """
    sql = ""
    # if table_num > 1: 
    #     columns = get_all_columns(tree['from'])
    #     new_tree = copy.deepcopy(tree)
    #     new_tree['select'] = columns
    #     sql = "create table output as " + tree_to_str(new_tree)
    #     print(sql)

    # else:
    #     print("selection or projection")
    #     print("Step 1: create data content")
    #     sql = "create table output as " + tree_to_str(tree)
    #     print(sql)

    columns = get_all_columns(tree['from'])
    new_tree = copy.deepcopy(tree)
    new_tree['select'] = columns
    sql = "create table output as " + tree_to_str(new_tree)
    # print(sql)
    
    cursor.execute("DROP TABLE IF EXISTS output")
    begin = time.time()
    cursor.execute(sql)
    end = time.time()
    # print("\ndata executing time: ", end-begin)
    # logging.warning("data execution time: %s" % str(end-begin))
    conn.commit()
    return end-begin

def upd_condition(tree):
    count_time = 0
    # print("\n************************Step 2: update condition****************************")
    cursor = conn.cursor()

    where_caluse = tree['where']
    keyword = list(where_caluse.keys())[0]
    conditions = copy.deepcopy(where_caluse[keyword])

    sql = ""
    cond_list = []
    where_list = []
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

    begin = time.time()
    if keyword == '' or keyword == 'and':
        
        # for c in cond_list:
        for idx, c in enumerate(cond_list):
            # sql = "update output set condition = array_append(condition, {})".format(c)
            sql = "update output set condition = array_append(condition, {}) where is_var({}) or is_var({})".format(c, where_list[idx][0], where_list[idx][1])
            # print(sql)
            cursor.execute(sql)
    else:
        # keyword == or
        sql = "update output set condition = array_append(condition, {})".format("'Or(' || " + " || ' , ' || ".join(cond_list) + " || ')'")
        # print(sql)
        cursor.execute(sql)
    count_time += (time.time() - begin)

    '''
    Check the selected columns
    if select *, drop duplicated columns,
    else only keep selected columns
    '''
    # table_num = len(tree['from'])
    drop_cols = []
    # if table_num > 1:
    if '*' in tree['select']:
        # remove duplicated columns
        # print('remove redundent')
        begin = time.time()
        for cond in conditions:
            if cond[1] == '=':
                left_opd = "".join(cond[0])
                right_opd = "".join(cond[2])
                sql = "update output set {} = {} where not is_var({})".format(left_opd, right_opd, right_opd)
                drop_cols.append(right_opd)
                # print(sql)
                cursor.execute(sql)
        count_time += time.time() - begin
    else:
        # only keep specified columns
        # print('keep specified columns')
        selected_cols = copy.deepcopy(tree['select'])

        select_col_dict = {}
        for col in selected_cols:
            if col[0][1] == '.': 
                col[0][1] = '_'
            name = "".join(col[0])
            select_col_dict[name] = col[2]

        rename_col = []
        keys = select_col_dict.keys()
        cursor.execute("select * from output limit 1")
        for col in cursor.description:
            col = col[0]
            if col in keys and select_col_dict[col] != '' and col != select_col_dict[col] :
                rename_col.append("{} to {}".format(col, select_col_dict[col]))
                continue
            if col == 'condition':
                continue
            if col not in keys:
                drop_cols.append(col)

        if len(rename_col) > 0: 
            begin = time.time()
            for new_col in rename_col:
                sql = "ALTER TABLE output rename column " + new_col
                # print(sql)
                cursor.execute(sql)
            count_time += time.time() - begin

    if len(drop_cols) > 0:
        begin = time.time()
        sql = "ALTER TABLE output drop column " + ", drop column ".join(drop_cols)
        # print(sql)
        cursor.execute(sql)
        count_time += time.time() - begin
    conn.commit()
    # print("\ncondition execution time:", count_time)
    # logging.warning("condition execution time: %s" % str(count_time))
    return count_time
            
def normalization():
    # print("\n************************Step 3: Normalization****************************")
    cursor = conn.cursor()
    # print('Step3: Normalization')
    begin = time.time()
    # sql = 'delete from output where is_contradiction(condition);'
    # print(sql)
    # cursor.execute(sql)
    
    # sql = "UPDATE output SET condition = '{}' WHERE is_tauto(condition);"
    # print(sql)
    # cursor.execute(sql)

    # sql = "UPDATE output SET condition = remove_redundant(condition) WHERE has_redundant(condition);"
    # print(sql)
    # cursor.execute(sql)
    # print("\nz3 execution time:", time.time()-begin)
    # print("red, tau", time.time()-begin)
    cursor.execute("select * from output limit 1")
    if 'id' not in [row[0] for row in cursor.description]:
        cursor.execute("ALTER TABLE output ADD COLUMN id SERIAL PRIMARY KEY;")
    '''
    delete contradiction
    '''
    # print("delete contradiction")
    contrd_begin = time.time()
    cursor.execute("select id, condition from output")
    contrad_count = cursor.rowcount
    # logging.info("size of input(delete contradiction): %s" % str(count))
    del_tuple = []
    solver = z3.Solver()
    for i in tqdm(range(contrad_count)):
        row = cursor.fetchone()
        is_contrad = iscontradiction(solver, row[1])

        if is_contrad:
            del_tuple.append(row[0])
        
    if len(del_tuple) == 0:
        pass
    elif len(del_tuple) == 1:
        cursor.execute("delete from output where id = {}".format(del_tuple[0]))
    else:
        cursor.execute("delete from output where id in {}".format(tuple(del_tuple)))
    contr_end = time.time()
    # logging.warning("delete contradiction execution time: %s" % str(contr_end-contrd_begin))

    '''
    set tautology and remove redundant
    '''
    # print("remove redundant")
    redun_begin = time.time()
    cursor.execute("select id, condition from output")
    redun_count = cursor.rowcount
    # logging.info("size of input(remove redundancy and tautology): %s" % str(count))
    upd_cur = conn.cursor()

    tauto_solver = z3.Solver()
    for i in tqdm(range(redun_count)):
        row = cursor.fetchone()
        has_redun, result = has_redundancy(solver, tauto_solver, row[1])
        if has_redun:
            if result != '{}':
                result = ['"{}"'.format(r) for r in result]
                upd_cur.execute("UPDATE output SET condition = '{}' WHERE id = {}".format("{" + ", ".join(result) + "}", row[0]))
            else:
                upd_cur.execute("UPDATE output SET condition = '{{}}' WHERE id = {}".format(row[0]))
    redun_end = time.time()
    # logging.warning("remove redundancy and tautology execution time: %s" % str(redun_end-redun_begin))
    
    # logging.warning("z3 execution time: %s" % str((contr_end-contrd_begin)+(redun_end-redun_begin)))
    conn.commit()
    return {"contradiction":[contrad_count, contr_end-contrd_begin], "redundancy":[redun_count, redun_end-redun_begin]}
   
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
        select_part = ", ".join(select_clause)
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
            # '''
            # len f = 3, use default operator [left_opd, operator, right_opd]
            # len f = 4, use user-defined function [usr_func, '(', [left_opd, right_opd], ')']
            # '''
            # if len(f) == 3:
            #     f[0] = "".join(f[0])
            #     f[2] = "".join(f[2])
            #     where_clause[key][idx] = " ".join(f)
            # else:
            #     f[2][0] = "".join(f[2][0])
            #     f[2][1] = "".join(f[2][1])
            #     f[2] = ", ".join(f[2])
            #     where_clause[key][idx] = "".join(f)

            # comparison = []
            # comparison.append("".join(f[0]))
            # comparison.append("".join(f[1]))
            # comparison.append("".join(f[2]).strip("\""))
            # where_clause[key][idx] = "".join(comparison)
            f = process_opr(f)
            f[2][0] = "".join(f[2][0])
            f[2][1] = "".join(f[2][1])
            f[2] = ", ".join(f[2])
            where_clause[key][idx] = "".join(f)
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

def test(clause, cond_list):
    last = 0 
    i = 0
    while i < len(clause):
        if clause[i] == '(': 
            if i > last:
                cond_list.append(clause[last:i].strip())
                temp_list = []
                j = test(clause[i+1:], temp_list)
                cond_list.append(temp_list)
                i = i + j + 1
                last = i
        elif clause[i] == ')':
            if i > last:
                cond_list.append(clause[last:i].strip())
            return i + 1
        else:
            i = i + 1

def get_all_columns(tables):
    columns = []
    col_conds = []
    cursor = conn.cursor()
    if len(tables) == 1:
        t = tables[0]
        cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
        for col in cursor.description:
            if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                columns.append([['', '', col[0]], '', ''])
            else:
                columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
    else:
        for t in tables:
            cursor.execute("select * from {} limit 1".format(t[0])) # t[0] is tablename
            for col in cursor.description:
                if 'cond' in col[0]:
                    if t[2] == '':
                        col_conds.append("{}.{}".format(t[0], col[0]))
                    else:
                        col_conds.append("{}.{}".format(t[2], col[0]))
                    continue
                if t[2] == '': # t[2] is renaming tablename, if t[2] not none, use renaming tablename in column name, else use original tablename in column name
                    columns.append([[t[0], '.', col[0]], 'as', '{}_{}'.format(t[0], col[0])])
                else:
                    columns.append([[t[2], '.', col[0]], 'as', '{}_{}'.format(t[2], col[0])])
        # print(col_conds)
        columns.append([['', '', ' || '.join(col_conds)], 'as', 'condition'])
    # print(columns)
    return columns
            
def iscontradiction(solver, conditions):
    solver.push()

    if len(conditions) == 0:
        return 

    vars = set() # save Int compared variables for shortest path policy
    for c in conditions:
        if '<=' in c:
            conds = c.split('<=')  # l(x3) <= x4
            
            var1 = conds[0].strip()
            var2 = conds[1].strip()
            
            if var1[0].isalpha():
                op1 = "z3.Int('{}')".format(var1)
                vars.add(var1)
            else:
                op1 = "z3.IntVal({})".format(int(var1))

            if var2[0].isalpha():
                op2 = "z3.Int('{}')".format(var2)
                vars.add(var2)
            else:
                op2 = "z3.IntVal({})".format(int(var2))

            expr = "{} <= {}".format(op1, op2)
            #print(expr)
            solver.add(eval(expr))
            continue

        # nopath means no path to dest
        if 'nopath' in c:
            solver.pop()
            return True
            
        if 'Or' not in c:
            #c_list = c.strip().split(' ')
            c = c.strip()

            first_space = c.find(' ')
            second_space = c.find(' ', first_space + 1)

            c_list = [c[:first_space].strip(), c[first_space + 1: second_space].strip(), c[second_space + 1:].strip()]

            if c_list[0] in vars: # if variable in vars that means this variable is Int variable and need to further set Int value for it
                solver.add(z3.Int(c_list[0]) == z3.IntVal(int(c_list[2])))
                continue
            elif c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                op1 = f"z3.String('{c_list[0]}')"
            else: 
                if c_list[0].startswith("i_"):
                    op1 = f"z3.StringVal('{c_list[0][2:]}')"
                else:
                    op1 = f"z3.StringVal('{c_list[0]}')"

            if c_list[2][0].isalpha() and not c_list[2].startswith("i_"):
                op2 = f"z3.String('{c_list[2]}')"
            else:
                if c_list[2].startswith("i_"):
                    op2 = f"z3.StringVal('{c_list[2][2:]}')"
                else:
                    op2 = f"z3.StringVal('{c_list[2]}')"
                
            #expr = f"{c_list[0]} {c_list[1]} z3.StringVal('{c_list[2]}')"
            expr = f"{op1} {c_list[1]} {op2}"
            # print(c, expr)
            #plpy.info(expr)
            solver.add(eval(expr))
        
        else:  #-- includes Or()
            c = c.strip().replace('Or','').replace('(','').replace(')','').strip()

            or_input = "Or("
            or_list =  c.split(',')
            for single_cond in or_list:
                c_list = single_cond.strip(). split(' ')
            
                if c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                    op1 = f"z3.String('{c_list[0]}')"
                else: 
                    # op1 = f"z3.StringVal('{c_list[0]}')"
                    if c_list[0].startswith("i_"):
                        op1 = f"z3.StringVal('{c_list[0][2:]}')"
                    else:
                        op1 = f"z3.StringVal('{c_list[0]}')"

                if c_list[2][0].isalpha() and not c_list[2].startswith("i_"):
                    op2 = f"z3.String('{c_list[2]}')"
                else:
                    # op2 = f"z3.StringVal('{c_list[2]}')"
                    if c_list[2].startswith("i_"):
                        op2 = f"z3.StringVal('{c_list[2][2:]}')"
                    else:
                        op2 = f"z3.StringVal('{c_list[2]}')"
                    
                #expr = f"{c_list[0]} {c_list[1]} z3.StringVal('{c_list[2]}')"
                expr = f"{op1} {c_list[1]} {op2}"
                or_input += expr + ','
    
            or_input = or_input[:-1] + ')'
            #plpy.info(or_input)
            solver.add(eval(or_input))

    result = solver.check()

    if result == z3.unsat:
        solver.pop()
        return True
    else:
        solver.pop()
        return False

def istauto(solver, conditions):
    if len(conditions) == 0:
        return True
    for c in conditions:
        condition = initial_z3_variable(c)
        solver.push()
        solver.add(eval(condition))
        re = solver.check()
        solver.pop()

        if str(re) == 'sat':
            pass
        else:
            return False
    return True

def initial_z3_variable(condition):
    expr = ""
    if 'Or' not in condition:

        c1_list = condition.split(' ')
        
        if c1_list[0][0].isalpha() and not c1_list[0].startswith("i_"):
            op11 = f"z3.String('{c1_list[0]}')"
        else: 
            # op11 = f"z3.StringVal('{c1_list[0]}')"
            if c1_list[0].startswith("i_"):
                op11 = f"z3.StringVal('{c1_list[0][2:]}')"
            else:
                op11 = f"z3.StringVal('{c1_list[0]}')"
    
        if c1_list[2][0].isalpha() and not c1_list[0].startswith("i_"):
            op12 = f"z3.String('{c1_list[2]}')"
        else:
            # op12 = f"z3.StringVal('{c1_list[2]}')"
            if c1_list[2].startswith("i_"):
                op12 = f"z3.StringVal('{c1_list[2][2:]}')"
            else:
                op12 = f"z3.StringVal('{c1_list[2]}')"
        
        operator1 = c1_list[1]

        expr = f"{op11} {operator1} {op12}"
    else: 
        cond_idx1 = condition.strip().replace('Or','')[1:-1]
        or_input = "Or("
        or_list =  cond_idx1.split(',')
        for single_cond in or_list:
            c_list = single_cond.strip(). split(' ')
        
            if c_list[0][0].isalpha() and not c_list[0].startswith("i_"):
                op11 = f"z3.String('{c_list[0]}')"
            else: 
                # op11 = f"z3.StringVal('{c_list[0]}')"
                if c_list[0].startswith("i_"):
                    op11 = f"z3.StringVal('{c_list[0][2:]}')"
                else:
                    op11 = f"z3.StringVal('{c_list[0]}')"

            if c_list[2][0].isalpha() and not c_list[0].startswith("i_"):
                op12 = f"z3.String('{c_list[2]}')"
            else:
                # op12 = f"z3.StringVal('{c_list[2]}')"
                if c_list[2].startswith("i_"):
                    op12 = f"z3.StringVal('{c_list[2][2:]}')"
                else:
                    op12 = f"z3.StringVal('{c_list[2]}')"
                
            operator1 = c_list[1]
            expr = f"{op11} {operator1} {op12}"
            or_input += expr + ','

        expr = or_input[:-1] + ')'
    
    return expr

def has_redundancy(solver, tau_solver, conditions):
    has_redundant = False

    result = conditions[:]
    
    drop_idx = {}
    dp_arr = []
    for i in range(len(conditions)):
        drop_idx[i] = []
    
    if len(conditions) == 0:
        return has_redundant, result
    
    processed_conditions = {}
    for idx1 in range(len(conditions) - 1):
        expr1 = ""
        if idx1 not in processed_conditions.keys():
            expr1 = initial_z3_variable(conditions[idx1])
            processed_conditions[idx1] = expr1
        else:
            expr1 = processed_conditions[idx1]

        for idx2 in range(idx1+1,len(conditions)):
            expr2 = ""
            if idx2 not in processed_conditions.keys():
                expr2 = initial_z3_variable(conditions[idx2])
                processed_conditions[idx2] = expr2  
            else:
                expr2 = processed_conditions[idx2]
            
            G = Implies(eval(expr1), eval(expr2))
            solver.push()
            solver.add(Not(G))
            re = str(solver.check())
            solver.pop()
            if str(re) == 'unsat':
                drop_idx[idx1].append(idx2)
                if not has_redundant:
                    has_redundant = True

            G = Implies(eval(expr2), eval(expr1))
            solver.push()
            solver.add(Not(G))
            re = str(solver.check())
            solver.pop()
            if str(re) == 'unsat':
                drop_idx[idx2].append(idx1)
                if not has_redundant:
                    has_redundant = True

    if has_redundant:
        drop_result = {}
        for i in range(len(conditions)):
            drop_result[i] = []

        for c1 in list(drop_idx):
            for c2 in drop_idx[c1]:
                if c2 == c1:
                    continue
                drop_idx[c1]+=(drop_idx[c2])
                drop_idx[c1] = list(set(drop_idx[c1]))
                drop_idx[c2] = []
                if c1 in drop_idx[c1]:
                    drop_idx[c1].remove(c1)

        for c1 in list(drop_idx):
            for c2 in drop_idx[c1]:        
                dp_arr.append(c2)

        is_tauto = True
        final_result = []
        for i in range(0, len(result), 1):
            if i not in dp_arr:
                final_result.append(result[i])

                c = "Not({})".format(processed_conditions[i])
                tau_solver.push()
                tau_solver.add(eval(c))
                if tau_solver.check() == z3.sat:
                    is_tauto = False
                tau_solver.pop()
        
        # result = [result[i] for i in range(0, len(result), 1) if i not in dp_arr]
        if is_tauto:
            return has_redundant, '{}'
        return has_redundant, final_result
    else:
        return has_redundant, ""

if __name__ == "__main__":

    size = [7,8,9,10,11,12,13,14, 15,16,17,18,19,20]
    rate = [0.3, 0.3, 0.3, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2, 0.2]
    joins = []
    dat_times = []
    upd_times = []
    z3_times = []
    total = []
    num_physical_tuples = []
    num_overlay_tuples = []

    for i in range(0, len(size)):
        tablename = "test3"
        curr_type = "text"
        physical_path, physical_nodes, overlay_path, overlay_nodes = tableau.gen_large_chain(size=size[i], rate=rate[i])
        physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)
        overlay_tuples, over_self_tuples = tableau.gen_tableau(path=overlay_path, overlay=overlay_nodes)
        group = physical_tuples+phy_self_tuples
        overlay = overlay_tuples+over_self_tuples

        cursor = conn.cursor()
        cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
        cursor.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type))
        for tuple in group:
            cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}');".format(tablename, tuple[0], tuple[1], tuple[2]))
        conn.commit()
        # sql = tableau.convert_tableau_to_sql(group, tablename, overlay_nodes)
        sql = "SELECT * from {} where n1 > '2';".format(tablename)
        tree = generate_tree(sql)

        # pp = pprint.PrettyPrinter(indent=4)
        # print("============Physical================")
        # pp.pprint(group)
        # print("============Overlay================")
        # pp.pprint(overlay)

        # print("============SQL================")
        # print(sql)
        # sql = "select t0.n1, t2.n2 from test2 t0, test2 t1, test2 t2, test2 t3, test2 t4, test2 t5 where t0.n1 = '1' and t0.n2 = t1.n1 and t2.n2 = '2' and t1.n2 = t2.n1 and t3.n1 = '1' and t3.n2 = '1' and t4.n1 = t4.n2 and t1.n1 = t4.n2 and t5.n1 = t5.n2 and t2.n1 = t5.n2"

        count_data_time = 0
        count_upd_time = 0
        count_contrad_time = 0
        count_redun_time = 0

        # for i in range(20):
        #     data_time = data(tree)
        #     count_data_time += data_time

        #     upd_time = upd_condition(tree)
        #     count_upd_time += upd_time

        #     nor_time = normalization()
        #     count_contrad_time += nor_time["contradiction"][1]
        #     tuples_contrad = nor_time["contradiction"][0]
        #     count_redun_time += nor_time["redundancy"][1]
        #     tuples_redun = nor_time["redundancy"][0]

        total_time = count_data_time/10 + count_upd_time/10 + count_contrad_time/10 + count_redun_time/10

        z3_time = count_contrad_time/10+count_redun_time/10

        num_joins = sql.count(tablename)
        joins.append(num_joins)
        dat_times.append(count_data_time/10)
        upd_times.append(count_upd_time/10)
        z3_times.append(z3_time)
        total.append(total_time)
        num_physical_tuples.append(len(group))
        num_overlay_tuples.append(len(overlay_tuples+over_self_tuples))

    conn.close()

    for i in range(0, len(size)):
        print(str(num_physical_tuples[i]) + "," + str(total[i]) + "," + str(dat_times[i]) + "," + str(upd_times[i]) + "," + str(z3_times[i]))
    
    # update output set condition = array_cat(condition, '{"f2.fid || '' == '' || f3.fid", "f1.nid2 || '' == '' || f2.nid1", "f1.fid || '' == '' || f2.fid", "f2.nid2 || '' == '' || f3.nid1"}')
