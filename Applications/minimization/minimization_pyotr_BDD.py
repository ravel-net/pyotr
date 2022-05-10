import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2
from tqdm import tqdm 
import copy
import Core.Homomorphism.Optimizations.closure_group.closure_group as closure_group
import Core.Homomorphism.Optimizations.split_merge_BDD as split_merge
import databaseconfig as cfg

host = cfg.postgres["host"]
user = cfg.postgres["user"]
password = cfg.postgres["password"]
database = cfg.postgres["db"]

conn = psycopg2.connect(host=host,user=user,password=password,database=database)
conn.set_session(readonly=False, autocommit=True)
curr_type = "int4_faure"

output_table_name = 'output'

# creates a new table with the deleted tuple
def deleteTuple(new_table, new_table_name, cur):
    cur.execute('DROP TABLE IF EXISTS {};'.format(new_table_name))
    cur.execute("CREATE TABLE {}(n1 {}, n2 {}, condition {});".format(new_table_name, "int4_faure", "int4_faure", "integer"))
    for tuple in new_table:
        cur.execute("INSERT INTO {} VALUES ('{}', '{}', {});".format(new_table_name, tuple[0], tuple[1], tuple[2]))

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
    print("current tablename:", tablename)
    print("current table:", curr_table)

    # Base condition for recursion
    if (len(curr_table) <= pos):
        return tablename

    # get closure group of tuple in question
    tuple_to_remove = curr_table[pos]
    closure_group = closure_group.getClosureGroup(tuple_to_remove, curr_table)
    variables = closure_group.find_variables(curr_table)
    print("variables",variables)
    print("summary", summary)
    print("tuple_to_remove: ", tuple_to_remove)
    print("closure_group: ", closure_group)

    # get new table with removed tuple
    new_table_name = tablename+str(pos)
    new_table = copy.deepcopy(curr_table)
    new_table.pop(pos)
    print("after remove tuple:", new_table)
    deleteTuple(new_table, new_table_name, cur)

    running_time, sat = split_merge(closure_group, new_table_name, variables, summary, curr_type)
    print("Satisfiability:", sat)
    print("Verification running time:", running_time, "\n")

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
    # cur = conn.cursor()
    # cur.execute("select condition from {}".format(output_table))
    # condition = cur.fetchone()[0]
    # print("condition", ", ".join(condition))
    # union_conditions, union_time = check_tautology.get_union_conditions("output", "Int")
    # domain_conditions, domain_time = check_tautology.get_domain_conditions(summary, variables, "Int")
    # print(union_conditions)
    # print(domain_conditions)
    # ans, time, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
    if sat == 1: # sat = 1 for tautology, 0 for contradiction, 2 for satisfiable
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