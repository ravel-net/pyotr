import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import copy
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.translator_pyotr as translator
import Core.Homomorphism.Optimizations.closure_group.closure_group as closure_group
import Backend.reasoning.Z3.check_tautology.check_tautology_multi as check_tautology_multi
import databaseconfig as cfg

host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]
curr_type = "int4_faure"

output_table_name = 'output'

# creates a new table with the deleted tuple
def storeTable(new_table, new_table_name, cur):
	cur.execute('DROP TABLE IF EXISTS {};'.format(new_table_name))
	cur.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(new_table_name, curr_type, curr_type))
	for tuple in new_table:
		cur.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(new_table_name, tuple[0], tuple[1]))

# given a tablename and an open cursor to a database, returns the table as a list
def getCurrentTable(tablename, cur):
    cur.execute('select * from {};'.format(tablename))
    return cur.fetchall()

def minimize_old(tablename = 't_v', pos = 0, summary = ['1','2']):
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
    closure_group_curr = closure_group.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_group.find_variables(curr_table)
    print("variables:", variables)
    print("tuple_to_remove: ", tuple_to_remove)
    print("closure_group: ", closure_group_curr)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    storeTable(new_table, new_table_name, cur)

    sql_query = tableau.convert_tableau_to_sql_distributed(closure_group_curr, new_table_name, summary, ["n1","n2","condition"])
    print("sql:", sql_query)

    # check for query containment
    tree = translator.generate_tree(sql_query)
    conn.commit()
    conn.close()
    data_time = translator.data(tree)
    upd_time = translator.upd_condition(tree, curr_type)
    nor_time = translator.normalization("Int")
    conn.close()

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    if (check_tautology_multi.table_contains_answer(output_table_name, summary, variables)):
        # cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
        cur.execute("DROP TABLE IF EXISTS {}".format(tablename))
        conn.commit()
        conn.close()
        return minimize_old(new_table_name, pos, summary)
    else:
    	# cur.execute("DROP TABLE IF EXISTS {}".format(output_table_name))
        # conn.close() # comment this line out for output of complete minimization
        # exit() # comment this line out for output of complete minimization
        cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
        conn.commit()
        conn.close()
        return minimize_old(tablename, pos+1, summary)

def minimize_recursive(const_tablename = 't_v', pos = 0, summary = ['1','2'], const_table = [(1,2)], var_table = [('y',2)]):
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

    # Base condition for recursion
    if (len(const_table) <= pos):
        return const_tablename

    # get closure group of tuple in question
    tuple_to_remove = var_table[pos]
    closure_group_curr = closure_group.getClosureGroup(tuple_to_remove, var_table)
    variables = closure_group.find_variables(var_table)
    print("variables:", variables)
    print("tuple_to_remove: ", tuple_to_remove)
    print("closure_group: ", closure_group_curr)

    # get new table with removed tuple
    new_table_name = const_tablename+str(pos)
    new_table = copy.deepcopy(const_table)
    new_table.pop(pos)
    storeTable(new_table, new_table_name, cur)
    sql_query = tableau.convert_tableau_to_sql_distributed(closure_group_curr, new_table_name, summary, ["n1","n2","condition"])
    print("sql:", sql_query)

    # check for query containment
    tree = translator.generate_tree(sql_query)
    conn.commit()
    conn.close()
    data_time = translator.data(tree)
    upd_time = translator.upd_condition(tree, curr_type)
    nor_time = translator.normalization("Int")
    conn.close()

    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()
    if (check_tautology_multi.table_contains_answer(output_table_name, summary, variables)):
        cur.execute("DROP TABLE IF EXISTS {}".format(const_tablename))
        conn.commit()
        conn.close()
        var_table.pop(pos)
        return minimize_recursive(new_table_name, pos, summary, new_table, var_table)
    else:
        cur.execute("DROP TABLE IF EXISTS {}".format(new_table_name))
        conn.commit()
        conn.close()
        return minimize_recursive(const_tablename, pos+1, summary, const_table, var_table)

# maps variables in table to constants
def getConstTable(table):
    # find maximum constant to start numbering of variables accordingly
    max = 0
    for tuple in table:
        n1 = tuple[0]
        n2 = tuple[1]
        if n1.isdigit() and int(n1) > max:
            max = int(n1)        
        if n2.isdigit() and int(n2) > max:
            max = int(n2)
    var_mapping_count = max + 1

    # map variables to constants
    var_mapping = {}
    for tuple in table:
        n1 = tuple[0]
        n2 = tuple[1]
        if not n1.isdigit():
            if n1 not in var_mapping:
                var_mapping[n1] = var_mapping_count
                var_mapping_count += 1
        if not n2.isdigit():
            if n2 not in var_mapping:
                var_mapping[n2] = var_mapping_count
                var_mapping_count += 1

    const_table = []
    for tuple in table:
        n1 = tuple[0]
        n2 = tuple[1]
        n1_new = n1
        n2_new = n2
        if not n1.isdigit():
            n1_new = var_mapping[n1]
        if not n2.isdigit():
            n2_new = var_mapping[n2]
        const_table.append((str(n1_new), str(n2_new), []))

    return const_table

def minimize(tablename = 't_v', summary = ['1','2']):
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

    const_table = getConstTable(curr_table)
    print(const_table)
    # exit()
    new_table_name = tablename+"_const"
    storeTable(const_table, new_table_name, cur)
    conn.commit()
    conn.close()
    print(new_table_name, 0, summary, const_table, curr_table)
    return minimize_recursive(new_table_name, 0, summary, const_table, curr_table)


if __name__ == '__main__':
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cursor = conn.cursor()

    # # Toy example of minimization
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

    # print("Minimized Table: ", minimize_old(tablename=tablename,pos=0, summary = ['1','2']))
    print("Minimized Table: ", minimize(tablename=tablename, summary = ['1','2']))