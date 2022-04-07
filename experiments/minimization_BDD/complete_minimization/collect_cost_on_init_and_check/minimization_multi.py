import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import copy
import util.tableau.tableau as tableau
import pyotr_translator.translator_pyotr as translator
import util.variable_closure_algo.closure_overhead as closure_overhead
import util.minimization.minimization_naive.check_tautology_multi as check_tautology_multi
import databaseconfig as cfg

host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]

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
    print("current_table:", curr_table)
    conn.commit()

    # Base condition for recursion
    if (len(curr_table) <= pos):
        return tablename

    # get closure group of tuple in question
    tuple_to_remove = curr_table[pos]
    closure_group = closure_overhead.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_overhead.find_variables(curr_table)
    print("variables:", variables)
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
    tree = translator.generate_tree(sql_query)
    conn.commit()
    conn.close()
    data_time = translator.data(tree)
    upd_time = translator.upd_condition(tree)
    nor_time = translator.normalization()
    conn.close()

    check_tauto, is_tautology = check_tautology_multi.table_contains_answer(output_table_name, summary, variables)
    running_time = {"normalization":nor_time, "check_tauto":check_tauto}


    print("Verification running time:", running_time, "\n")
    current_directory = os.getcwd()
    if not os.path.exists(current_directory+"/results"):
        os.makedirs(current_directory+"/results")
    f = open(current_directory+"/results/Z3_components.txt", "a")
    f.write("{}\n".format(running_time))
    f.close()

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    if (check_tautology_multi.table_contains_answer(output_table_name, summary, variables)):
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
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cursor = conn.cursor()

    # # Toy example of minimization
    curr_type = "int4_faure"
    tablename = "t_v"
    cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
    cursor.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type))
    conn.commit()    

    # curr_type = "text"
    # tablename = "t_v2"
    # cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
    # cursor.execute("CREATE TABLE {}(fid {}, n1 {}, n2 {}, condition TEXT[]);".format(tablename, "text", curr_type, curr_type))
    # conn.commit()
    # cursor.execute("INSERT INTO {} VALUES ('{}','{}', '{}', array[]::text[]);".format(tablename, 'f', '102', '1'))
    # cursor.execute("INSERT INTO {} VALUES ('{}','{}', '{}', array[]::text[]);".format(tablename, 'f', '1', '1'))
    # cursor.execute("INSERT INTO {} VALUES ('{}','{}', '{}', array[]::text[]);".format(tablename, 'f', '1', '103'))
    # conn.commit()
    # conn.close()
    # exit()

    # One big switch example
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', 'x'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'x', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', '2'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', 'x'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'x', 'z'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'z', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', '2'))

    # # New minimization example
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'x', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'y1'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y2'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'z'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'z', 'z2'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'z', 'z'))

    # Minimization toy example
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', '1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', 'y2'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', 'y1'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y2'))
    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', '2'))
    conn.commit()

    print("Minimized Table: ", minimize(tablename=tablename, pos = 0, summary = ['1','2']))