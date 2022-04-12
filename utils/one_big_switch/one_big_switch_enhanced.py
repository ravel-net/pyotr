import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
import re
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
def encodeFirewallRule(acl):
	return 'And(' + ",".join(acl) + ')'
	#if (firewallRule == permit):
	# source and destination?

# Creates a one-big-switch table with a middlebox for firwall that contains all firewall rules in the network. The created table is stored as 'tablename' in postgreSQL.
def addFirewallOneBigSwitch(cursor, aclList = [""], tablename = "T_o", forwardNodeIP = '1.0.0.0', firewallNodeIP = '2.0.0.0'):
	curr_type = "inet_faure"
	cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
	cursor.execute("CREATE TABLE {}(F {}, n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type, curr_type))
	conn.commit()    
	encodedRules = []
	for acl in aclList:
		encodedRules.append(encodeFirewallRule(acl))
	bigFirewallRule = '\'{"Or(' + ",".join(encodedRules) + ')"}\''
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, SOURCE_VAR, forwardNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, forwardNodeIP, firewallNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, forwardNodeIP, forwardNodeIP))
	# cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, firewallNodeIP, firewallNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', {});".format(tablename, F, firewallNodeIP, DEST_VAR, bigFirewallRule))
	conn.commit()

def extractFlows(F_variable, paths, conditionColumn):
	rules = []
	for path in paths:
		if len(path[conditionColumn]) > 1:
			flow = path[conditionColumn].split(",")
			for rule in flow:
			    rule = rule.strip()
			    match = re.search('!=|<=|>=|<>|<|>|==', rule)
			    left_opd = rule[:match.span()[0]].strip()
			    opr = match.group()
			    right_opd = rule[match.span()[1]:].strip()
			    rules.append("{} {} {}".format(F_variable, opr, right_opd))
	return rules

def extractSummary(paths, source_col, dest_col, flow_col):
	lengthPaths = len(paths)
	return paths[0][source_col], paths[lengthPaths-1][dest_col], paths[0][flow_col]

if __name__ == "__main__":
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cursor = conn.cursor()
	tablename = "T_o"
	datatype = "BitVec"
	aclList = [["f < 4.0.0.0"], ["f > 2.0.0.0", "f < 30.0.0.0"]]
	addFirewallOneBigSwitch(aclList=aclList, tablename=tablename, cursor=cursor)

	paths = [('30.0.0.0', 'y', 'f2', ''), ('y', 'u', 'f2', ''), ('u','w', 'f2', ''), ('w', '20.0.0.0', 'f2', '')]
	flows = extractFlows(F_variable=F, paths=paths, conditionColumn=3)

	sourceIP, destIP, flowID = extractSummary(paths=paths, source_col=0, dest_col=1, flow_col=2)
	summary = [sourceIP, destIP, flowID]

	sql2 = tableau.convert_tableau_to_sql(paths, tablename, summary, ['n1', 'n2', 'F'])
	# tree = translator_pyotr.generate_tree(sql)
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
		SOURCE_VAR:["{} == {}".format(SOURCE_VAR, sourceIP)], 
		DEST_VAR:["{} == {}".format(DEST_VAR, destIP)], 
		# F:["{} == 2.0.0.1".format(F)]
		F: flows
	}

	domain_conditions = check_tautology.get_domain_conditions_from_list(domains, datatype)
	print(domain_conditions)

	# ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
	# print(union_conditions)
	if union_conditions != "Or()":
		ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
		print(model)
	else:
		ans = False
	print(ans)
	# upd_time = translator_pyotr.upd_condition(tree)
	conn.close()

	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cur = conn.cursor()