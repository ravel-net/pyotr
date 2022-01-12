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

# Given a tuple and a table, returns the closure group of the tuple from the table.
def getClosureGroup(tuple, table):
    variables = closure_overhead.find_variables(table)
    graph = closure_overhead.construct_Graph(variables, table)
    conns = graph.connectedComponents() # TODO: ineffecient. Don't need all connected components
    reverse_conns = graph.reverse_connectComponents(conns) 
    if (tuple[0] in reverse_conns):
    	minimal_tableau_pos = reverse_conns[tuple[0]] - 1
    elif (tuple[1] in reverse_conns):
    	minimal_tableau_pos = reverse_conns[tuple[1]] - 1
    else:
    	return tuple # constants tuple like (1,1) only have themselves in the closure group
    minimal_tableau = closure_overhead.calculate_tableau(table, reverse_conns, len(conns))
    return minimal_tableau[minimal_tableau_pos]

def minimize(tablename = 't_v', pos = 0, summary = ['1','2']):
    """
    Convert tableau to corresponding SQL
    Parameters:
    ------------
    tablename : string 
        The name of table that needs to be minimized
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
    closure_group = getClosureGroup(tuple_to_remove, curr_table)
    # print("tuple_to_remove: ", tuple_to_remove)
    # print("closure_group: ", closure_group)
    if (closure_group == tuple_to_remove):
        return minimize(tablename, pos+1, summary)
        

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    deleteTuple(new_table, new_table_name, cur)

    # check for query containment
    sql_query = tableau.convert_tableau_to_sql(closure_group, new_table_name, summary)
    # print("sql:",sql_query)
    tree = translator_pyotr.generate_tree(sql_query)
    conn.commit()
    conn.close()
    data_time = translator_pyotr.data(tree)
    upd_time = translator_pyotr.upd_condition(tree)
    nor_time = translator_pyotr.normalization()
    conn.close()

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    if (check_tautology.table_contains_answer(output_table_name, summary)):
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

if __name__ == '__main__':
    sizes = [100, 1000, 10000] #, 10000, 100000, 922067]
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cursor = conn.cursor()

    curr_type = "int4_faure"
    tablename = "test_table"
    cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
    cursor.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type))
    conn.commit()
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', '1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', 'y2'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', 'y1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y2'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', '2'))
    conn.commit()
    
    print("Minimized Table: ", minimize(tablename=tablename, pos = 0, summary = ['1','2']))