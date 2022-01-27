import re
import psycopg2 
import copy
import time
from tqdm import tqdm
import z3
from z3 import And, Not, Or, Implies
import databaseconfig as cfg
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
            # f = process_opr(f) # operator to user-defined function
            # f[2][0] = "".join(f[2][0])
            # f[2][1] = "".join(f[2][1])
            # f[2] = ", ".join(f[2])
            f[0] = "".join(f[0])
            f[2] = "".join(f[2])
            where_clause[key][idx] = "".join(f)
        where_part = " {} ".format(key).join(where_clause[key])
        sql_parts.append(where_part)

    sql = " ".join(sql_parts)
    # print(sql)
    return sql
    
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
        
        cond = [left_opr_list, opr, right_opr_list]
        cond_list.append(cond)
    
    
    match = re.search('and|or', clause, flags=re.IGNORECASE)
    keyword = match.group().lower() if match is not None else ""

    return {keyword:cond_list}

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
            elif col[0] == 'condition':
                columns.append([[t[2], '.', col[0]], 'as', 'condition'])
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

def get_extra_columns(select):
    extra_cols = []
    for s in select: # s format: [['t0', '.', 'n1'], '', ''] or [['', '', "'1'"], '', ''] select 1
        col = s[0][2]
        if "'" in col:
            p = re.compile(r"'(.*?)'", re.S)
            col = re.findall(p, col)[0]
        
        if col.isdigit(): # select constant number such as 1
            extra_cols.append([['', '', s[0][2]], 'as', '"{}"'.format(col)])
    return extra_cols           

#create data content
def data(tree):
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
    new_tree['select'] = columns + extra_cols
    sql = "create table output as " + tree_to_str(new_tree)
    print(sql)
    
    cursor.execute("DROP TABLE IF EXISTS output")
    begin = time.time()
    cursor.execute(sql)
    end = time.time()
    print("\ndata executing time: ", end-begin)
    # logging.warning("data execution time: %s" % str(end-begin))
    conn.commit()
    return end-begin