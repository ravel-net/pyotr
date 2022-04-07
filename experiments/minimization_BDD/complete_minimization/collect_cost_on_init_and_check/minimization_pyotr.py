import sys
import os
from os.path import dirname, abspath, join
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)

import psycopg2
from tqdm import tqdm 
import time
import copy
import utils.closure_group.closure_overhead as closure_overhead
from minimization_BDD.complete_minimization.collect_cost_on_init_and_check.split_merge import split_merge
import databaseconfig as cfg
from time import time
host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]

conn = psycopg2.connect(host=host,user=user,password=password,database=database)

output_table_name = 'output'
OPEN_OUTPUT = False

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
    if OPEN_OUTPUT:
        print("current table:", curr_table)

    # Base condition for recursion
    if (len(curr_table) <= pos):
        return tablename

    # get closure group of tuple in question
    tuple_to_remove = curr_table[pos]
    closure_group = closure_overhead.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_overhead.find_variables(curr_table)
    if OPEN_OUTPUT:
        print("variables",variables)
        print("summary", summary)
        print("tuple_to_remove: ", tuple_to_remove)
        print("closure_group: ", closure_group)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    if OPEN_OUTPUT:
        print("after remove tuple:", new_table)
    start_delete = time()
    print("delete_called", len(new_table))
    deleteTuple(new_table, new_table_name, cur)
    end_delete = time()
    

    running_time, output_table = split_merge(closure_group, new_table_name, variables, summary)
    print("Verification running time:", running_time, "\n")
    running_time["delete"] = end_delete-start_delete

    current_directory = os.getcwd()
    if not os.path.exists(current_directory+"/results"):
        os.makedirs(current_directory+"/results")
    f = open(current_directory+"/results/Z3_components.txt", "a")
    f.write("{}\n".format(running_time))
    f.close()

    # sql_query = tableau.convert_tableau_to_sql(closure_group, new_table_name, summary)
    
    # print("sql:", sql_query)

    # check for query containment
    # tree = translator.generate_tree(sql_query)
    # conn.commit()
    # conn.close()
    # data_time = translator.data(tree)
    # upd_time = translator.upd_condition(tree)
    # nor_time = translator.normalization()
    # conn.close()

    # conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    cur.execute("select condition from {}".format(output_table))
    # condition = cur.fetchone()[0]
    # print("condition", ", ".join(condition))
    # union_conditions, union_time = check_tautology.get_union_conditions("output", "Int")
    # domain_conditions, domain_time = check_tautology.get_domain_conditions(summary, variables, "Int")
    # print(union_conditions)
    # print(domain_conditions)
    # ans, time, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
    if cur.rowcount != 0 and len(cur.fetchone()[0]) == 0:
        cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
        conn.commit()
        # conn.close()
        return minimize(new_table_name, pos, summary)
    else:
        cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
        conn.commit()
        # conn.close()
        return minimize(tablename, pos+1, summary)

    # if (check_tautology.table_contains_answer(output_table, summary, variables)):
    #     # cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
    #     cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
    #     conn.commit()
    #     conn.close()
    #     return minimize(new_table_name, pos, summary)
    # else:
    #     # cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
    #     # conn.close() # comment this line out for output of complete minimization
    #     # exit() # comment this line out for output of complete minimization
    #     cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
    #     conn.commit()
    #     conn.close()
    #     return minimize(tablename, pos+1, summary)
