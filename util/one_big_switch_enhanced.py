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

if __name__ == "__main__":
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cursor = conn.cursor()
	curr_type = "int4_faure"
	tablename = "T_o"
	cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
	cursor.execute("CREATE TABLE {}(F {}, n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type, curr_type))
	conn.commit()    
	
	# a = '\'{"f != 2"}\''
	a = '\'{"Or(f == 2, f == 1)"}\''
	# One big Switch Enhanced example
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', 's', '1'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', {});".format(tablename, 'f', '1', '2', a))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '1', '1'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '2', '2'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '2', 'd'))
	conn.commit()

	# sql = "select t0.F, t0.n1, t3.n2 from T_o t0, T_o t1, T_o t2, T_o t3, T_o t4, T_o t5, T_o t6, T_o t7 where t0.n1 = '10' and t0.n2 = t1.n1 and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '20' and t0.F = t1.F and t1.F = t2.F and t2.F = t3.F"
	sql = "select t0.F, t0.n1, t3.n2 from T_o t0, T_o t1, T_o t2, T_o t3 where t0.n1 = '10' and t0.n2 = t1.n1 and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '20' and t0.F = t1.F and t1.F = t2.F and t2.F = t3.F"

	sql2 = "select t4.F, t4.n1, t7.n2 from T_o t4, T_o t5, T_o t6, T_o t7 where t4.n1 = '30' and t4.n2 = t5.n1 and t5.n2 = t6.n1 and t6.n2 = t7.n1 and t7.n2 = '20' and t4.F = t5.F and t5.F = t6.F and t6.F = t7.F and t5.F = '2'"

	# tree = translator_pyotr.generate_tree(sql)
	tree = translator_pyotr.generate_tree(sql2)
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree)
	nor_time = translator_pyotr.normalization()
	conn.commit()
	datatype = "Int"
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=datatype)
	# domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=[], variables_list=['s', 'd'], datatype=datatype)
	# domain_conditions = "Or(z3.Int('s') == z3.IntVal(30)), Or(z3.Int('d') == z3.IntVal(20)), Or(z3.Int('f') == z3.IntVal(2))"
	domain_conditions = "Or(z3.Int('s') == z3.IntVal(30)), Or(z3.Int('d') == z3.IntVal(20)), Or(z3.Int('f') == z3.IntVal(2), z3.Int('f') == z3.IntVal(1))"

	print(domain_conditions)
	negation_union_conditions = "Not({})".format(union_conditions)
	print(negation_union_conditions)
	# ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	print(ans)
	# upd_time = translator_pyotr.upd_condition(tree)
	conn.close()

	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cur = conn.cursor()

    # if (check_tautology.table_contains_answer(output_table_name, summary, variables)):
    # # New minimization example
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'x', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'y1'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y1', 'y2'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y2', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'y'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'y', 'z'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'z', 'z2'))
    # cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, 'z', 'z'))