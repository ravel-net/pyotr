import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

from tqdm import tqdm
import time
import databaseconfig as cfg
import psycopg2
from psycopg2.extras import execute_values

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])


def merge_tuples_bdd(tablename, BDDTool, information_on=False):
    """
    merge rows which are the same data portion:
    1. Logical OR-ing the conditions of rows
    2. check if the conjunction condition is tautology

    Parameters:
    -----------
    tablename: string
        C-table name which is to be merged

    information_on: Boolean
    """
    cursor = conn.cursor()

    if information_on:
        print("\n********************merge tuples******************************")

    cursor.execute("ALTER TABLE {} ADD COLUMN if not exists id SERIAL PRIMARY KEY;".format(tablename))
    conn.commit()

    cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_name = '{}';".format(tablename.lower())) # this SQL needs lowercase of tablename
    columns = []
    for (column_name, ) in cursor.fetchall():
        if column_name.lower() == 'id':
            continue
        columns.append(column_name.lower())
    conn.commit()
    
    idx_cond = 0 
     
    if 'condition' in columns:
        idx_cond = columns.index('condition')
    else:
        print("No condition column! Check if the target table is correct!")
        exit()

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
    
    total_BDD_time = 0
    new_tuples = []

    for key in tuple_dict.keys():
        tp = list(key)
        condition_indexes = tuple_dict[key]

        merged_idx = condition_indexes[0]
        for i in range(1, len(condition_indexes)):
            begin = time.time()
            merged_idx = BDDTool.operate_BDDs(merged_idx, condition_indexes[i], '^')
            end = time.time()
            total_BDD_time += end - begin

        tp.insert(idx_cond, merged_idx)
        new_tuples.append(tp)

    cursor.execute("truncate table {}".format(tablename))
    sql = "insert into {tablename} values %s".format(tablename=tablename)
    execute_values(cursor, sql, new_tuples)
    conn.commit()

    return len(new_tuples)
    
def merge_tuples_z3(tablename, information_on=False):
    """
    merge rows which are the same data portion:
    1. Logical OR-ing the conditions of rows
    2. check if the conjunction condition is tautology

    Parameters:
    -----------
    tablename: string
        C-table name which is to be merged

    information_on: Boolean
    """
    cursor = conn.cursor()

    if information_on:
        print("\n********************merge tuples******************************")
    # print("tablename", tablename)

    cursor.execute("ALTER TABLE {} ADD COLUMN if not exists id SERIAL PRIMARY KEY;".format(tablename))
    conn.commit()

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
       
        tp.insert(idx_cond, '{"' + or_cond + '"}')
        new_tuples.append(tp)

    # print("new_tuples", new_tuples)
    cursor.execute("truncate table {}".format(tablename))
    # cursor.execute("drop table if exists {out_tablename}".format(out_tablename=out_tablename))
    # cursor.execute("create table {out_tablename} (like {tablename} including defaults including constraints including indexes)".format(out_tablename=out_tablename, tablename=tablename))
    sql = "insert into {tablename} values %s".format(tablename=tablename)
    execute_values(cursor, sql, new_tuples)
    conn.commit()

    return len(new_tuples)


if __name__ == '__main__':
    tablename = 'output'
    out_tablename = 'r12'
    overlay_nodes = range(1, 11)
    variables_list = ["x{num}".format(num = num) for num in range(1, 41)]
    merge_tuples_bdd(tablename, out_tablename, overlay_nodes, variables_list)

