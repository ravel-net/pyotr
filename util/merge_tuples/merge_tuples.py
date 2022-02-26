import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'new_experiments')
sys.path.append(filename)

import time
from tqdm import tqdm
import databaseconfig as cfg
import psycopg2
from psycopg2.extras import execute_values

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()


def merge_tuples(tablename, out_tablename):
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
            tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions_no_duplicates)))
        # tuple_dict[t].append("And({conditions_no_dup})".format(conditions_no_dup=", ".join(conditions)))
    new_tuples = []
    for key in tuple_dict.keys():
        tp = list(key)
        or_cond = '"Or({tuple_conditions})"'.format(tuple_conditions=", ".join(tuple_dict[key]))
        # print(or_cond)
        tp.insert(idx_cond, '{' + or_cond + '}')
        new_tuples.append(tp)
        
    # print(len(new_tuples))

    cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    cursor.execute("create table {out_tablename} as select * from {tablename} where 1 = 2".format(out_tablename=out_tablename, tablename=tablename))

    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    execute_values(cursor, sql, new_tuples)
    # cursor.executemany(new_tuples)
    conn.commit()



if __name__ == '__main__':
    tablename = 'output'
    out_tablename = 'r12'
    merge_tuples(tablename, out_tablename)
