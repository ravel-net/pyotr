import sys
import os
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2
from psycopg2.extras import execute_values

import BDD_managerModule as bddmm

OPEN_OUTPUT = True


def merge_tuples(tablename, out_tablename):
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(readonly=False, autocommit=True)
    cursor = conn.cursor()

    if OPEN_OUTPUT:
        print("\n********************merge tuples******************************")
    cursor.execute("select * from {tablename} limit 1".format(tablename=tablename))
    columns = [row[0] for row in cursor.description]
    
    if 'id' in columns:
        columns.remove('id')
    idx_cond = columns.index('condition')
    begin_get_condition = time.time()
    cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))
    end_get_condition = time.time()

    begin_merge_tuple = time.time()
    row_count = cursor.rowcount
    tuple_dict = {}
    for i in tqdm(range(row_count)):
        row = cursor.fetchone()
        condition_idx = row[idx_cond]

        t = row[0:idx_cond] + row[idx_cond+1:]

        # collect condition index for whom has the same data portion
        if t not in tuple_dict.keys():
            tuple_dict[t] = [] 
        tuple_dict[t].append(condition_idx)
    end_merge_tuple = time.time()
    total_BDD_time = 0
    new_tuples = []

    # current_directory = os.getcwd()
    # print("current directory:", current_directory)
    # f = open(current_directory+"/merged_condition.txt", "a")
    # f.write("merged_idx sat indexes\n")
    keys = list(tuple_dict.keys())
    for i in tqdm(range(len(keys))):
        key = keys[i]
        tp = list(key)
        condition_indexes = tuple_dict[key]

        merged_idx = condition_indexes[0]
        for i in range(1, len(condition_indexes)):
            begin = time.time()
            merged_idx = bddmm.operate_BDDs(merged_idx, condition_indexes[i], '^')
            # merged_idx = replace(merged_idx)
            end = time.time()
            total_BDD_time += end - begin

        # sat = bddmm.evaluate(merged_idx)
        # print("satisfiable for each merged tuple", sat)
        # f.write("{} {} {}\n".format(merged_idx, sat, ["{}_{}".format(condition_indexes[i], bddmm.evaluate(condition_indexes[i])) for i in range(len(condition_indexes))]))

        tp.insert(idx_cond, merged_idx)
        new_tuples.append(tp)
    # f.close()

    cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    cursor.execute("create table {out_tablename} as select * from {tablename} where 1 = 2".format(out_tablename=out_tablename, tablename=tablename))
    cursor.execute("alter table {out_tablename} drop column if exists id".format(out_tablename=out_tablename))
    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    begin_insert = time.time()
    execute_values(cursor, sql, new_tuples)
    end_insert = time.time()
    # cursor.executemany(new_tuples)
    conn.commit()
    return len(new_tuples), {
        "get_condition":end_get_condition-begin_get_condition, 
        "merge_tuples":end_merge_tuple-begin_merge_tuple, 
        "operate_BDDs":total_BDD_time, 
        "insertion":end_insert-begin_insert
    }
    



if __name__ == '__main__':
    tablename = 'output'
    out_tablename = 'r12'
    overlay_nodes = range(1, 11)
    variables_list = ["x{num}".format(num = num) for num in range(1, 41)]
    merge_tuples(tablename, out_tablename, overlay_nodes, variables_list)
