import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import utils.tableau.tableau as tableau
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

SOURCE_VAR = 's'
DEST_VAR = 'd'
F = 'f'

# encodes a firwall rule in a bit-string format
def encodeFirewallRule(firewallRule):
	return firewallRule
	#if (firewallRule == permit):
	# source and destination?

# Creates a one-big-switch table with a middlebox for firwall that contains all firewall rules in the network. The created table is stored as 'tablename' in postgreSQL.
def addFirewallOneBigSwitch(cursor, firewallRules = [""], tablename = "T_o", forwardNodeIP = '1.0.0.0', firewallNodeIP = '2.0.0.0'):
	curr_type = "inet_faure"
	cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
	cursor.execute("CREATE TABLE {}(F {}, n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type, curr_type))
	conn.commit()    
	encodedRules = []
	for firewallRule in firewallRules:
		encodedRules.append(encodeFirewallRule(firewallRule))
	bigFirewallRule = '\'{"Or(' + ",".join(encodedRules) + ')"}\''
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, SOURCE_VAR, forwardNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', {});".format(tablename, F, forwardNodeIP, firewallNodeIP, bigFirewallRule))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, forwardNodeIP, forwardNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, firewallNodeIP, firewallNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, firewallNodeIP, DEST_VAR))
	conn.commit()

	# 

if __name__ == "__main__":
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cursor = conn.cursor()
	tablename = "T_o"
	firewallRules = ["f == 2.0.0.1", "f == 1.0.0.1"]
	addFirewallOneBigSwitch(firewallRules=firewallRules, tablename=tablename, cursor=cursor)

	summary = ['30.0.0.0', '20.0.0.0', 'f2']
	paths = [('30.0.0.0', 'y', 'f2', ''), ('y', 'u', 'f2', 'f2 = 2.0.0.1'), ('u','w', 'f2', ''), ('w', '20.0.0.0', 'f2', '')]

	sql2 = tableau.convert_tableau_to_sql(paths, tablename, summary)
	# tree = translator_pyotr.generate_tree(sql)
	datatype = "BitVec"
	tree = translator_pyotr.generate_tree(sql2)
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree)
	nor_time = translator_pyotr.normalization(datatype)
	conn.commit()
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=datatype)
	# exit()3
	# domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=[], variables_list=[SOURCE_VAR, 'd'], datatype=datatype)
	# domain_conditions = "Or(z3.Int(SOURCE_VAR) == z3.IntVal(30)), Or(z3.Int('d') == z3.IntVal(20)), Or(z3.Int('f') == z3.IntVal(2))"

	domains = {
		SOURCE_VAR:["{} == 30.0.0.0".format(SOURCE_VAR)], 
		DEST_VAR:["{} == 20.0.0.0".format(DEST_VAR)], 
		F:["{} == 2.0.0.1".format(F)]
	}

	domain_conditions = check_tautology.get_domain_conditions_from_list(domains, datatype)
	print(domain_conditions)

	# ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	# print(union_conditions)
	ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	print(ans)
	# upd_time = translator_pyotr.upd_condition(tree)
	conn.close()

	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cur = conn.cursor()