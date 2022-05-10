"""
minimization algorithm on pyotr system 

Z3 verison
"""
import sys
import math
import os
import time
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import psycopg2
import copy
import Core.Homomorphism.Optimizations.closure_group.closure_group as closure_group
import Core.Homomorphism.Optimizations.split_merge.split_merge as split_merge
import utils.chain_generation.gen_chain as gen_chain 
import databaseconfig as cfg

host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]
curr_type = "int4_faure"

conn = psycopg2.connect(host=host,user=user,password=password,database=database)

output_table_name = 'output'

# creates a new table with the deleted tuple
def deleteTuple(new_table, new_table_name, cur):
    cur.execute('DROP TABLE IF EXISTS {};'.format(new_table_name))
    cur.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(new_table_name, "int4_faure", "int4_faure"))
    for tuple in new_table:
        cur.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(new_table_name, tuple[0], tuple[1]))

    conn.commit()


# given a tablename and an open cursor to a database, returns the table as a list
def getCurrentTable(tablename, cur):
    cur.execute('select * from {};'.format(tablename))
    return cur.fetchall()

def minimize(tablename = 't_v', pos = 0, summary = ['1','2']):
    """
    Convert tableau to corresponding SQL
    Parameters:
    ------------
    tablename : string 
        The name of table stored in postgres that needs to be minimized.
    pos : int
        The current index of tuple that is being tested for removal. When calling this function, pos should be 0
    summary : list
        the summary (beliefs) of the original tableau
    Returns:
    ------------
    tablename : string
        The name of the minimized table in the database. The final minimized table is stored in postgres
    """
    cur = conn.cursor()

    # get current table
    curr_table = getCurrentTable(tablename, cur)
    print("current table:", curr_table)

    # Base condition for recursion
    if (len(curr_table) <= pos):
        return tablename

    # get closure group of tuple in question
    tuple_to_remove = curr_table[pos]
    closure_group_cur = closure_group.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_group.find_variables(curr_table)
    # print("variables",variables)
    # print("summary", summary)
    # print("tuple_to_remove: ", tuple_to_remove)
    # print("closure_group: ", closure_group_cur)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    # print("after remove tuple:", new_table)
    deleteTuple(new_table, new_table_name, cur)

    running_time, output_table = split_merge.split_merge(closure_group_cur, new_table_name, variables, summary, curr_type)
    # print("Verification running time:", running_time, "\n")

    cur = conn.cursor()
    cur.execute("select condition from {}".format(output_table))

    if cur.rowcount != 0 and len(cur.fetchone()[0]) == 0:
        cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
        conn.commit()
        return minimize(new_table_name, pos, summary)
    else:
        cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
        conn.commit()
        return minimize(tablename, pos+1, summary)

# size = 20
# size_single_loop = 2
# rate_variable = size_single_loop/size 
# conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
# conn.set_session(readonly=False, autocommit=True)
# cursor = conn.cursor()

# path, summary_nodes, variable_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate_variable, size_single_loop=size_single_loop)
# tuples = gen_chain.gen_tableau(path, picked_nodes)

# tablename = "chain{}_{}_{}".format(size, math.ceil((1-rate_variable)*10), size_single_loop)
# cursor.execute("drop table if exists {}".format(tablename))
# cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
# cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

# conn.commit()

# current_directory = os.getcwd()
# if not os.path.exists(current_directory+"/results"):
#     os.makedirs(current_directory+"/results")
# f = open(current_directory+"/results/z3_exp_minimization_{}.txt".format(tablename), "a")
# f.write("runtime(sec)\n")

# begin = time.time()
# table_name = minimize(tablename=tablename, pos=0, summary=summary_nodes)
# end = time.time()
# print("\nRUNNING TIME:", end - begin)
# print("table_name:", table_name)
# f.write("{}\n".format(end - begin))
# f.close()

# print(end-begin)