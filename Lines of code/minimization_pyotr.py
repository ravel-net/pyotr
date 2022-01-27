import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
import tableau
from os.path import dirname, abspath, join
root = dirname(dirname(abspath(__file__)))
filename = join(root, 'util/variable_closure_algo')
sys.path.append(filename)
filename = join(root, 'util/check_tautology')
sys.path.append(filename)
filename = join(root, 'pyotr_translator')
sys.path.append(filename)
import translator_pyotr
import closure_overhead
import check_tautology
import pprint

host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

output_table_name = 'output'

# creates a new table with the deleted tuple
def deleteTuple(new_table, new_table_name, cur):
    cur.execute('DROP TABLE IF EXISTS {};'.format(new_table_name))
    cur.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(new_table_name, "int4_faure", "int4_faure"))
    for tuple in new_table:
        cur.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(new_table_name, tuple[0], tuple[1]))

# given a tablename and an open cursor to a database, returns the table as a list
def getCurrentTable(tablename, cur):
    cur.execute('select * from {};'.format(tablename))
    return cur.fetchall()

# def table_contains_answer(output, summary, pos):
#     print("pos:", pos)
#     arr = [0, 1, 1, 1, 1, 0]
#     if arr[pos] == 1:
#         return True
#     else:
#         return False

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

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    # get current table
    curr_table = getCurrentTable(tablename, cur)
    conn.commit()

    # Base condition for recursion
    if (len(curr_table) <= pos):
        return tablename

    # get closure group of tuple in question
    tuple_to_remove = curr_table[pos]
    closure_group = closure_overhead.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_overhead.find_variables(curr_table)
    print("tuple_to_remove: ", tuple_to_remove)
    print("closure_group: ", closure_group)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    deleteTuple(new_table, new_table_name, cur)

    sql_query = tableau.convert_tableau_to_sql(closure_group, new_table_name, summary)
    # print("sql:", sql_query)

    # check for query containment
    tree = translator_pyotr.generate_tree(sql_query)
    conn.commit()
    conn.close()
    data_time = translator_pyotr.data(tree)
    upd_time = translator_pyotr.upd_condition(tree)
    nor_time = translator_pyotr.normalization()
    conn.close()

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    if (check_tautology.table_contains_answer(output_table_name, summary, variables)):
        # cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
        cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
        conn.commit()
        conn.close()
        return minimize(new_table_name, pos, summary)
    else:
        # cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
        # conn.close() # comment this line out for output of complete minimization
        # exit() # comment this line out for output of complete minimization
        cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
        conn.commit()
        conn.close()
        return minimize(tablename, pos+1, summary)