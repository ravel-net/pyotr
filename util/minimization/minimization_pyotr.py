"""
minimization algorithm on pyotr system 

Z3 verison
"""

import sys
from os.path import dirname, abspath, join
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)

import psycopg2
import copy
import util.variable_closure_algo.closure_overhead as closure_overhead
from util.split_merge.split_merge import split_merge
import databaseconfig as cfg

host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]

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
    closure_group = closure_overhead.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_overhead.find_variables(curr_table)
    # print("variables",variables)
    # print("summary", summary)
    # print("tuple_to_remove: ", tuple_to_remove)
    # print("closure_group: ", closure_group)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    # print("after remove tuple:", new_table)
    deleteTuple(new_table, new_table_name, cur)

    running_time, output_table = split_merge(closure_group, new_table_name, variables, summary)
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