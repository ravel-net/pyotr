import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

from tqdm import tqdm
import faure_translator.databaseconfig as cfg
import psycopg2
from psycopg2.extras import execute_values

import BDD_managerModule as bddmm

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

OPEN_OUTPUT = True

DOMAIN = ['1', '2']
VARIABLES = []

def set_domain(domain):
    global DOMAIN
    DOMAIN = domain

def set_variables(variables):
    global VARIABLES
    VARIABLES = variables

def merge_tuples(tablename, out_tablename):
    if OPEN_OUTPUT:
        print("\n********************merge tuples******************************")
    cursor.execute("select * from {tablename} limit 1".format(tablename=tablename))
    columns = [row[0] for row in cursor.description]
    
    if 'id' in columns:
        columns.remove('id')
    idx_cond = columns.index('condition')

    cursor.execute("select {attributes} from {tablename}".format(attributes=", ".join(columns), tablename=tablename))
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
        

    new_tuples = []
    for key in tuple_dict.keys():
        tp = list(key)
        condition_indexes = tuple_dict[key]

        merged_idx = condition_indexes[0]
        for i in range(1, len(condition_indexes)):
            merged_idx = bddmm.operate_BDDs(merged_idx, condition_indexes[i], '&')
        
        tp.insert(idx_cond, merged_idx)
        new_tuples.append(tp)
        
    # print(len(new_tuples)

    cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    cursor.execute("create table {out_tablename} as select * from {tablename} where 1 = 2".format(out_tablename=out_tablename, tablename=tablename))
    cursor.execute("alter table {out_tablename} drop column if exists id".format(out_tablename=out_tablename))

    sql = "insert into {out_tablename} values %s".format(out_tablename=out_tablename)
    execute_values(cursor, sql, new_tuples)
    # cursor.executemany(new_tuples)
    conn.commit()
    return len(new_tuples)

