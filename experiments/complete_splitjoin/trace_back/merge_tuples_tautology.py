import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'new_experiments', 'util')
sys.path.append(filename)

import time
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2
import check_tautology as check_tautology
import condition_analyze as condition_analyze
from psycopg2.extras import execute_values
from count_condition import preprocessing

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

tau_cond1 = "Or(And(x1 == x2, x2 == x3), And(1 == x2, x2 == x3), x1 == x3, 1 == x3, And(x1 == 1, x2 == x3), And(x1 == 1, x2 == x3), And(x2 == 1, x3 == x2), x2 == 1, And(x2 == 1, x2 == x3), And(x2 == 1, x2 == x3), And(x3 == 1, x3 == x2), x3 == 1)"
pattern = preprocessing(tau_cond1)

def merge_tuples(tablename, out_tablename, overlay_nodes, variables_list):
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

        if len(conditions) == 0:
            continue

        t = row[0:idx_cond] + row[idx_cond+1:]

        # remove duplicate condition in tuple
        conditions_no_duplicates = []
        for c in conditions:
            if c not in conditions_no_duplicates:
                conditions_no_duplicates.append(c)

        if t not in tuple_dict.keys():
            tuple_dict[t] = [] # will remove duplicate condition between tuples

        if len(conditions_no_duplicates) != 0:
            if len(conditions_no_duplicates) == 1:
                tuple_dict[t].append("{conditions_no_dup}".format(conditions_no_dup=", ".join(conditions_no_duplicates)))
            else:
                tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions_no_duplicates)))
        # tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions)))
        
    domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes, variables_list, 'Int')
    new_tuples = []
    total_num = 0
    for key in tuple_dict.keys():
        tp = list(key)
        or_cond = 'Or({tuple_conditions})'.format(tuple_conditions=", ".join(tuple_dict[key]))

        # collect tautology numbers 
        check_or_cond = preprocessing(or_cond)
        res = check_or_cond.count(pattern)
        total_num += res

        prcd_or_cond = condition_analyze.analyze(or_cond)
        # print(prcd_or_cond)
        is_tauto, check_time, model = check_tautology.check_is_tautology(prcd_or_cond, domain_conditions)
        # print(or_cond)
        if is_tauto:
            # print(or_cond)
            tp.insert(idx_cond, '{}')
        else:
            # print("\nanswer solution: ", model)
            tp.insert(idx_cond, '{"' + or_cond + '"}')
        new_tuples.append(tp)
    print("tauto number: ", total_num)
    # print(len(new_tuples))

    cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    cursor.execute("create table {out_tablename} as select * from {tablename} where 1 = 2".format(out_tablename=out_tablename, tablename=tablename))

    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    execute_values(cursor, sql, new_tuples)
    # cursor.executemany(new_tuples)
    conn.commit()
    return len(new_tuples)



if __name__ == '__main__':
    tablename = 'output'
    out_tablename = 'r12'
    overlay_nodes = range(1, 11)
    variables_list = ["x{num}".format(num = num) for num in range(1, 41)]
    merge_tuples(tablename, out_tablename, overlay_nodes, variables_list)
