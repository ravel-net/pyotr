import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import utils.tableau.tableau
# filename = join(root, 'util/variable_closure_algo')
# filename = join(root, 'util/check_tautology')
# sys.path.append(filename)
# filename = join(root, 'pyotr_translator')
# sys.path.append(filename)
import pyotr_translator.translator_pyotr as translator_pyotr
import utils.closure_group.closure_overhead as closure_overhead
import utils.check_tautology.check_tautology as check_tautology
import pprint

host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'
output_table_name = 'output'

if __name__ == "__main__":
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cursor = conn.cursor()
	curr_type = "inet_faure"
	tablename = "T_o"
	cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
	cursor.execute("CREATE TABLE {}(F {}, n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type, curr_type))
	conn.commit()    
	
	# a = '\'{"f != 2"}\''
	a = '\'{"Or(f == 2.0.0.1, f == 1.0.0.1)"}\''
	# a = '\'{"Or(f == 2.0.0.1, f == 1.0.0.1)"}\''
	# One big Switch Enhanced example
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', 's', '1.0.0.0'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', {});".format(tablename, 'f', '1.0.0.0', '2.0.0.0', a))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '1.0.0.0', '1.0.0.0'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '2.0.0.0', '2.0.0.0'))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, 'f', '2.0.0.0', 'd'))
	conn.commit()

	# sql = "select t0.F, t0.n1, t3.n2 from T_o t0, T_o t1, T_o t2, T_o t3, T_o t4, T_o t5, T_o t6, T_o t7 where t0.n1 = '10' and t0.n2 = t1.n1 and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '20' and t0.F = t1.F and t1.F = t2.F and t2.F = t3.F"
	sql = "select t0.F, t0.n1, t3.n2 from T_o t0, T_o t1, T_o t2, T_o t3 where t0.n1 = '10.0.0.0' and t0.n2 = t1.n1 and t1.n2 = t2.n1 and t2.n2 = t3.n1 and t3.n2 = '20.0.0.0' and t0.F = t1.F and t1.F = t2.F and t2.F = t3.F"

	sql2 = "select t4.F, t4.n1, t7.n2 from T_o t4, T_o t5, T_o t6, T_o t7 where t4.n1 = '30.0.0.0' and t4.n2 = t5.n1 and t5.n2 = t6.n1 and t6.n2 = t7.n1 and t7.n2 = '20.0.0.0' and t4.F = t5.F and t5.F = t6.F and t6.F = t7.F and t5.F = '2.0.0.1'"

	# tree = translator_pyotr.generate_tree(sql)
	tree = translator_pyotr.generate_tree(sql2)
	tree = {'select': [[['t4', '.', 'f'], '', ''], [['t4', '.', 'n1'], '', ''], [['t7', '.', 'n2'], '', '']], 'where': {'and': [[['t4', '.', 'n1'], '=', ['', '', "'30.0.0.0'"]], [['t4', '.', 'n2'], '=', ['t5', '.', 'n1']], [['t5', '.', 'n2'], '=', ['t6', '.', 'n1']], [['t6', '.', 'n2'], '=', ['t7', '.', 'n1']], [['t7', '.', 'n2'], '=', ['', '', "'20.0.0.0'"]], [['t4', '.', 'F'], '=', ['t5', '.', 'F']], [['t5', '.', 'F'], '=', ['t6', '.', 'F']], [['t6', '.', 'F'], '=', ['t7', '.', 'F']], [['t5', '.', 'F'], '=', ['', '', "'2.0.0.1'"]]]}, 'from': [['t_o', ' ', 't4'], ['t_o', ' ', 't5'], ['t_o', ' ', 't6'], ['t_o', ' ', 't7']]}
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree)
	nor_time = translator_pyotr.normalization()
	conn.commit()
	datatype = "Int"
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=datatype)
	# exit()3
	# domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=[], variables_list=['s', 'd'], datatype=datatype)
	# domain_conditions = "Or(z3.Int('s') == z3.IntVal(30)), Or(z3.Int('d') == z3.IntVal(20)), Or(z3.Int('f') == z3.IntVal(2))"
	domain_conditions = "Or(z3.BitVec('s',32) == z3.BitVecVal(503316480,32)), Or(z3.BitVec('d',32) == z3.BitVecVal(335544320,32)), Or(z3.BitVec('f',32) == z3.BitVecVal(33554433,32))"

	negation_union_conditions = "Not({})".format(union_conditions)
	# ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	# print(union_conditions)
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

# 1. Need to change get tableau sql to get conditions from the third column
# 2. Need to change generate tree to support IP addresses
# 3. Need to change get domain function
# 4. Need to make changes to normalization and check tautology