import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)

import time
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2
# import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology
# import Backend.reasoning.Z3.check_tautology.condition_analyze as condition_analyze
# import Backend.reasoning.Z3.z3smt as z3SMTtool
from psycopg2.extras import execute_values

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

OPEN_OUTPUT = False

def merge_tuples(tablename, out_tablename, z3tools, simplification_on=True, information_on=False):
    """
    merge rows which are the same data portion:
    1. Logical OR-ing the conditions of rows
    2. check if the conjunction condition is tautology

    Parameters:
    -----------
    tablename: string
        C-table name which is to be merged

    out_tablename: string
        C-table name which is used to store the merged `tablename` c-table
    
    z3tools: z3SMTTools
        An instance of z3SMTTools

    simplification_on: Boolean

    SELECT column_name FROM information_schema.columns WHERE table_name = 'R';
    """
    if information_on:
        print("\n********************merge tuples******************************")
    # print("tablename", tablename)
    cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_name = '{}';".format(tablename.lower())) # this SQL needs lowercase of tablename
    columns = []
    for (column_name, ) in cursor.fetchall():
        if column_name.lower() == 'id':
            continue
        columns.append(column_name.lower())
    conn.commit()
    # cursor.execute("select * from {tablename} limit 1".format(tablename=tablename))
    # columns = [row[0] for row in cursor.description]
    # print("columns", columns)
    idx_cond = 0 
     
    if 'condition' in columns:
        idx_cond = columns.index('condition')
    else:
        print("No condition column! Check if the target table is correct!")
        exit()
    # if 'id' in columns:
    #     columns.remove('id')

    cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))
    row_count = cursor.rowcount
    tuple_dict = {}
    tauto_keys = []
    for i in tqdm(range(row_count)):
        row = cursor.fetchone()
        conditions = row[idx_cond]
        # print("conditions", conditions)
        t = list(row[0:idx_cond] + row[idx_cond+1:])
        # i = 0
        for i, elem in enumerate(t):
            if isinstance(elem, list):
                t[i] = "{" + str(elem)[1:-1] + "}"
            # i += 1
        t = tuple(t)
        # remove duplicate condition in tuple
        conditions_no_duplicates = []
        for c in conditions:
            if c not in conditions_no_duplicates:
                conditions_no_duplicates.append(c)

        if t not in tuple_dict.keys():
            tuple_dict[t] = [] 

        if len(conditions_no_duplicates) == 0:
            tauto_keys.append(t)
            continue
        elif len(conditions_no_duplicates) == 1:
            tuple_dict[t].append(conditions_no_duplicates[0])
        else:
            tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions_no_duplicates)))
    
    # domain_conditions, domain_time = check_tautology.get_domain_conditions_general(domain, reasoning_type)
    
    new_tuples = []
    for key in tuple_dict.keys():
        tp = list(key)
        if key in tauto_keys:
            tp.insert(idx_cond, '{}')
            new_tuples.append(tp)
            continue
            
        or_cond = None
        conditions = tuple_dict[key]

        if len(conditions) == 0:
            or_cond = "" # alsways true
        elif len(conditions) == 1:
            or_cond = conditions[0]
        else:
            or_cond = 'Or({tuple_conditions})'.format(tuple_conditions=", ".join(tuple_dict[key]))
        # print("or_cond", or_cond)
        
        is_tauto = z3tools.istauto([or_cond])
        # print('is_tauto', is_tauto)
        if is_tauto:
            tp.insert(idx_cond, '{}')
        else:
            if simplification_on:
                simplified_cond = z3tools.simplify_condition(or_cond)
                tp.insert(idx_cond, '{"' + simplified_cond + '"}')
            else:
                tp.insert(idx_cond, '{"' + or_cond + '"}')
        new_tuples.append(tp)

    # print("new_tuples", new_tuples)
    cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    cursor.execute("create table {out_tablename} as select * from {tablename} where 1 = 2".format(out_tablename=out_tablename, tablename=tablename))
    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    execute_values(cursor, sql, new_tuples)
    conn.commit()
    return len(new_tuples)



if __name__ == '__main__':
    tablename = 'output'
    out_tablename = 'r12'
    overlay_nodes = range(1, 11)
    variables_list = ["x{num}".format(num = num) for num in range(1, 41)]
    merge_tuples(tablename, out_tablename, overlay_nodes, variables_list)
