import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
import re
import shortest_paths
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import utils.tableau.tableau as tableau
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
SOURCE = '192.168.1.1'
DEST = '192.168.1.2'
F = 'f'
source_col=0
dest_col=1
flow_col=2
condition_col =3

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
	encodedRules = []
	for acl in aclList:
		encodedRules.append(encodeFirewallRule(acl))
	bigFirewallRule = '\'{"Or(' + ",".join(encodedRules) + ')"}\''
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, SOURCE, firewallNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', {});".format(tablename, F, firewallNodeIP, forwardNodeIP, bigFirewallRule))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, forwardNodeIP, DEST))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, forwardNodeIP, forwardNodeIP))
	cursor.execute("INSERT INTO {} VALUES ('{}', '{}', '{}', array[]::text[]);".format(tablename, F, firewallNodeIP, firewallNodeIP))

def extractFlows(F_variable, paths, condition_col):
	rules = []
	for path in paths:
		if len(path[condition_col]) > 1:
			flow = path[condition_col].split(",")
			for rule in flow:
			    rule = rule.strip()
			    match = re.search('!=|<=|>=|<>|<|>|==', rule)
			    left_opd = rule[:match.span()[0]].strip()
			    opr = match.group()
			    right_opd = rule[match.span()[1]:].strip()
			    rules.append("{} {} {}".format(F_variable, opr, right_opd))
	return rules

def extractSummary(paths, source_col, dest_col, flow_col):
	sourceIPs = set()
	destIPs = set()
	flowIDs = set()
	for tuple in paths:
		if tuple[source_col][0].isdigit():
			sourceIPs.add(tuple[source_col])		
		if tuple[dest_col][0].isdigit():
			destIPs.add(tuple[dest_col])
		flowIDs.add(tuple[flow_col])
	return list(sourceIPs), list(destIPs), list(flowIDs)


# Extracts num_paths number of paths from the AS defined
def getPaths(ISP_path, AS, num_paths):
	nodes = join(ISP_path,AS+"_nodes.txt")
	edges = join(ISP_path,AS+"_edges.txt")
	f = open(nodes,"r")
	lines = f.readlines()
	num_vertices = len(lines)
	nodes = []
	for node in lines:
		nodes.append(node.strip())
	mapping = shortest_paths.createNodeMappings(nodes)
	f.close()
	f = open(edges,"r")
	edgeslines = f.readlines()
	f.close()
	g = shortest_paths.makeGraph(edgeslines, num_vertices, mapping, num_paths)
	currentPathList = shortest_paths.getShortestPaths(g, num_vertices, num_paths)
	print(currentPathList)
	allPathsTableau = shortest_paths.getTableauWithFlowID(num_vertices, num_paths,currentPathList)
	return allPathsTableau

# Adds flow id to path list
# def addFlowID(paths):
# 	pathsWithFlowID = []
# 	for i, path in enumerate(paths):
# 		curr_path = []
# 		for tuple in path:
# 			print(tuple)
# 			curr_tuple = tuple + ("f"+str(i),)
# 			curr_path.append(curr_tuple)
# 		pathsWithFlowID.append(curr_path)
# 	return pathsWithFlowID

# Given a node to ACL list mapping (distributed firewall) with paths, produces a tableau with conditions added
def addConditions(closureGroups, nodeACLMapping, condition_col):
	pathsWithConditions = [] 
	for group in closureGroups:
		curr_group = []
		for tuple in group:
			if (tuple[0] in nodeACLMapping):
				curr_group.append(tuple + (nodeACLMapping[tuple[0]],))
			else:
				curr_group.append(tuple + ('',))
		pathsWithConditions.append(curr_group)
	return pathsWithConditions

# used to get a list of domain conditions
def getIPConditions(var, IPs): 
	conditions = []
	for ip in IPs:
		conditions.append(["{} == {}".format(var, ip)])
	return conditions

# Makes the sources and destinations variables. Returns the sources and destinations
def makeEndNodesVariable(paths, source_col, dest_col):
	source_list = []
	dest_list = []
	for pathNum, path in enumerate(paths):
		source = SOURCE_VAR+str(pathNum)
		dest = DEST_VAR+str(pathNum)
		path[0] = path[0][0:source_col] + (source,) + path[0][source_col+1:]
		path[-1] = path[-1][0:dest_col] + (dest,) + path[-1][dest_col+1:]
		source_list.append(source)
		dest_list.append(dest)
	return source_list, dest_list

# Takes nodes as an input and divides ACL randomly to them. Each nodes can get 0,1,2, or 3 ACLs
def getNodeACLMapping(nodes, aclList):
	nodeACLMapping = {}
	for acl in aclList:
		random_index = random.randint(0,len(nodes)-1) # select random node
		selected_node = nodes[random_index]
		if selected_node not in nodeACLMapping:
			nodeACLMapping[selected_node] = []
		nodeACLMapping[selected_node].append()

if __name__ == "__main__":
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	conn.set_session(readonly=False, autocommit=True)
	cursor = conn.cursor()

	tablename = "T_o"
	datatype = "BitVec"
	aclList = [["f < 4.0.0.0"], ["f == 192.168.0.0/16"]]
	# accessListDest = getAccessListDest("/path/to/accesslist")
	# aclList = partitionAccessList(accessListDest)
	addFirewallOneBigSwitch(aclList=aclList, tablename=tablename, cursor=cursor)
	conn.commit()
	conn.close()
	# num_paths = 3
	# AS = "4755"
	# ISP_path = join(root, 'topo/ISP_topo/')
	# paths = getPaths(ISP_path, AS, num_paths)
	# paths = [('s1', 'y', 'f0'), ('y', 'u', 'f0'), ('u','w', 'f0'), ('w', 'd', 'f0'), ('s2', 'x', 'f1'), ('x', 'z', 'f1'), ('z','n', 'f1'), ('n', 'd', 'f1')]
	paths = [[('3.0.0.0', 'y', 'f2'), ('y', 'u', 'f2'), ('u','w', 'f2'), ('w', '4.0.0.0', 'f2')]]
	# nodes = getNodes(paths)
	# nodeACLMapping = getNodeACLMapping(nodes, aclList)
	source_sumaries, dest_summaries = makeEndNodesVariable(paths, source_col, dest_col)
	nodeACLMapping = {"x":', '.join(aclList[0]), "y":','.join(aclList[1]).replace("f","f2")}
	pathsClosureGroups = closure_overhead.getAllClosureGroups(paths)
	pathsWithConditions = addConditions(pathsClosureGroups, nodeACLMapping, condition_col)
	# for pathsTableau in paths:
	i = 0
	for pathsTableau in pathsWithConditions:
		# i += 1
		# if (i == 1):
		# 	continue
		print(pathsTableau)
		sourceIPs, destIPs, flowIDs = extractSummary(paths=pathsTableau, source_col=source_col, dest_col=dest_col, flow_col=flow_col)
		print(sourceIPs, destIPs, flowIDs)
		flows = extractFlows(F_variable=F, paths=pathsTableau, condition_col=condition_col)
		summary = sourceIPs + destIPs + flowIDs + source_sumaries + dest_summaries
		print("flows", flows)
		print(pathsTableau)
		sql = tableau.convert_tableau_to_sql_distributed(pathsTableau, tablename, summary, ['n1', 'n2', 'F', 'conditions'])
		print(sql)
		# sql = "select t0.n1, t4.n1, t4.F, t0.F, t3.n2 from T_o t0, T_o t1, T_o t2, T_o t3, T_o t4, T_o t5, T_o t6, T_o t7 where t1.F > '2.0.0.0' and t1.F < '30.0.0.0' and t0.n2 = t1.n1 and t0.F = t1.F and t1.n2 = t2.n1 and t1.F = t2.F and t3.n2 = '20.0.0.0' and t2.n2 = t3.n1 and t2.F = t3.F and t5.F < '4.0.0.0' and t4.n2 = t5.n1 and t4.F = t5.F and t5.n2 = t6.n1 and t5.F = t6.F and t7.n2 = '20.0.0.0' and t6.n2 = t7.n1 and t6.F = t7.F and t1.n2 = t5.n2 and t3.n1 = t7.n1"
		domains = {
			# SOURCE_VAR: getIPConditions(SOURCE_VAR, sourceIPs),
			# [["{} == {}".format(SOURCE_VAR, sourceIP)], ["{} == {}".format(SOURCE_VAR, '40.0.0.0')]], 
			# DEST_VAR: getIPConditions(DEST_VAR, destIPs),
			F: [flows]
			# F: aclList
		}

		domain_conditions = check_tautology.get_domain_conditions_from_list(domains, datatype, F)
		tree = translator_pyotr.generate_tree(sql)
		data_time = translator_pyotr.data(tree)
		upd_time = translator_pyotr.upd_condition(tree)
		nor_time = translator_pyotr.normalization(datatype)
		union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=datatype)
		# exit()3
		# domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=[], variables_list=[SOURCE_VAR, 'd'], datatype=datatype)
		# domain_conditions = "Or(z3.Int(SOURCE_VAR) == z3.IntVal(30)), Or(z3.Int('d') == z3.IntVal(20)), Or(z3.Int('f') == z3.IntVal(2))"



		# ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
		# print(union_conditions)
		if union_conditions != "Or()": # i.e. Empty table
			ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
			print(model)
		else:
			ans = False
		print(ans)
		print("Data time", data_time)
		print("Update time", upd_time)
		print("Normalization time", nor_time)
		print("Check Tautology time", runtime)
		# print("Total time", runtime+nor_time+upd_time+data_time)
		# upd_time = translator_pyotr.upd_condition(tree)
# Or(
# 	And(And(z3.BitVec('s',32) == z3.BitVecVal('503316480',32))), 
# 	And(And(z3.BitVec('s',32) == z3.BitVecVal('671088640',32)))), 
# Or(And(And(z3.BitVec('d',32) == z3.BitVecVal('335544320',32)))), 
# Or(
# 	And(
# 		And(z3.BitVec('f',32) > z3.BitVecVal('33554432',32)), 
# 		And(z3.BitVec('f',32) < z3.BitVecVal('503316480',32))), 
# 	And(And(z3.BitVec('f',32) < z3.BitVecVal('67108864',32))))
