import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)

import time
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology
import Backend.reasoning.Z3.check_tautology.condition_analyze as condition_analyze
from psycopg2.extras import execute_values

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

OPEN_OUTPUT = False

def merge_tuples(tablename, out_tablename, domain, reasoning_type):
    if OPEN_OUTPUT:
        print("\n********************merge tuples******************************")
    cursor.execute("select * from {tablename} limit 1".format(tablename=tablename))
    columns = [row[0] for row in cursor.description]

    idx_cond = columns.index('condition')
    if 'id' in columns:
        columns.remove('id')

    cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))
    row_count = cursor.rowcount
    tuple_dict = {}
    for i in tqdm(range(row_count)):
        row = cursor.fetchone()
        conditions = row[idx_cond]

        t = row[0:idx_cond] + row[idx_cond+1:]

        # remove duplicate condition in tuple
        conditions_no_duplicates = []
        for c in conditions:
            if c not in conditions_no_duplicates:
                conditions_no_duplicates.append(c)

        if t not in tuple_dict.keys():
            tuple_dict[t] = [] 

        if len(conditions_no_duplicates) == 0:
            continue
        elif len(conditions_no_duplicates) == 1:
            tuple_dict[t].append(conditions_no_duplicates[0])
        else:
            tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions_no_duplicates)))
    domain_conditions, domain_time = check_tautology.get_domain_conditions_general(domain, reasoning_type)

    new_tuples = []
    for key in tuple_dict.keys():
        tp = list(key)

        or_cond = None
        conditions = tuple_dict[key]
        if len(conditions) == 0:
            or_cond = "" # alsways true
        elif len(conditions) == 1:
            or_cond = conditions[0]
        else:
            or_cond = 'Or({tuple_conditions})'.format(tuple_conditions=", ".join(tuple_dict[key]))
        prcd_or_cond = check_tautology.analyze(or_cond, reasoning_type)
        is_tauto, check_time, model = check_tautology.check_is_tautology(prcd_or_cond, domain_conditions)
        if is_tauto:
            tp.insert(idx_cond, '{}')
        else:
            tp.insert(idx_cond, '{"' + or_cond + '"}')
        new_tuples.append(tp)
        
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
