import psycopg2
from tqdm import tqdm 
import time
import sys
import copy
import random
import re
from os.path import dirname, abspath, join
import json
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import databaseconfig as cfg
import utils.graphs.shortest_paths as shortest_paths
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.translator_pyotr as translator_pyotr
import Core.Homomorphism.Optimizations.closure_group.closure_group as closure_group
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology
import pprint

output_table_name = 'output'

SOURCE_VAR = 's'
DEST_VAR = 'd'
# SOURCE = 's'
# DEST = 'd'
SOURCE = '192.168.1.1'
DEST = '192.168.1.2'
F = 'f'
SUMMARY_INSTANCE = [F, SOURCE, DEST]
SOURCE_COL=0
DEST_COL=1
FLOW_COL=2
CONDITION_COL =3
curr_type = "inet_faure"

# encodes a firwall rule. This is OR if we are using an allow list. It would be and for a deny list
def encodeFirewallRule(acl):
	return 'And(' + ",".join(acl) + ')'
	#if (firewallRule == permit):
	# source and destination?

# Creates a one-big-switch table with a middlebox for firwall that contains all firewall rules in the network. The created table is stored as 'tablename' in postgreSQL.
def addFirewallOneBigSwitch(cursor, aclList = [""], tablename = "T_o", forwardNodeIP = '1.0.0.0', firewallNodeIP = '2.0.0.0'):
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

def extractSummary(paths, source_summaries, dest_summaries, flow_col):
	sourceIPs = set()
	destIPs = set()
	flowIDs = set()
	for tuple in paths:
		for col, val in enumerate(tuple):
			if col == flow_col:
				flowIDs.add(tuple[flow_col])
			elif val in source_summaries:
				sourceIPs.add(val)
			elif val in dest_summaries:
				destIPs.add(val)
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
def addConditions(closureGroups, nodeACLMapping, condition_col, source_col, flow_col, flow_var):
	pathsWithConditions = [] 
	for group in closureGroups:
		curr_group = []
		for tuple in group:
			if (tuple[source_col] in nodeACLMapping):
				curr_condition = ",".join(nodeACLMapping[tuple[0]])
				curr_condition = curr_condition.replace(flow_var, tuple[flow_col])
				curr_group.append(tuple + (curr_condition,))
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
def makeEndNodesVariable(path, source_col, dest_col, flow_col):
	source_list = []
	dest_list = []
	for i, tuple in enumerate(path):
		if tuple[source_col][0].isdigit():
			source = SOURCE_VAR+tuple[flow_col]
			path[i] = path[i][0:source_col] + (source,) + path[i][source_col+1:] 
			source_list.append(source)
		if tuple[dest_col][0].isdigit():
			dest = DEST_VAR+tuple[flow_col]
			path[i] = path[i][0:dest_col] + (dest,) + path[i][dest_col+1:] 
			dest_list.append(dest)
	return source_list, dest_list

# Takes nodes as an input and divides ACL randomly to them. Each nodes can get 0,1,2, or 3 ACLs
def getNodeACLMapping(nodes, aclList, numberOfACLs):
	nodeACLMapping = {}
	for acl in aclList[0:numberOfACLs]:
		random_index = random.randint(0,len(nodes)-1) # select random node
		selected_node = nodes[random_index]
		if selected_node not in nodeACLMapping:
			nodeACLMapping[selected_node] = []
		nodeACLMapping[selected_node].append(acl)
	return nodeACLMapping

# iterates over paths and returns all distinct variable nodes
def getNodes(path, source_col, dest_col, flow_col):
	nodes = []
	for i in range(len(path)-1):
		curr_tuple = path[i]
		next_tuple = path[i+1]
		node_to_add = ""
		if (i == len(path)-2):
			node_to_add = next_tuple[source_col]
		elif (curr_tuple[flow_col] != next_tuple[flow_col]):
			node_to_add = curr_tuple[source_col]
		if (node_to_add != "" and node_to_add not in nodes):
			nodes.append(node_to_add)
	return nodes

# List of acls
def getDividedAccessList(nodeACLMapping):
	dividedAccessList = []
	for var in nodeACLMapping:
		dividedAccessList.append(nodeACLMapping[var])
	return dividedAccessList

# listType is either "deny" or "allow"
def getAccessListDest(filename, listType, F_variable):
    access_list = []
    opr = "=="
    if listType == "deny":
    	opr = "!="
    with open(filename) as d:
        rule_list = []
        for line in d:
            if line not in rule_list:
                rule_list.append(line)
                data = json.loads(line.strip())
                if len(data) == 2:
                    # if data["source"] == "0.0.0.0/32" and data["destination"] == "0.0.0.0/32":
                    #     continue
                    if data["destination"] == "0.0.0.0/32":
                        continue
                    rule = "{} {} {}".format(F_variable, opr, data["destination"])
                    access_list.append(rule)
    return access_list

# Separates flows for paths
def separateFlows(paths, flow_col):
	pathFlows = []
	curr_path = []
	for i in range(len(paths)-1):
		curr_tuple = paths[i]
		next_tuple = paths[i+1]
		if curr_tuple[flow_col] == next_tuple[flow_col]:
			curr_path.append(curr_tuple)
		else:
			curr_path.append(curr_tuple)
			pathFlows.append(copy.deepcopy(curr_path))
			curr_path = []
	curr_path.append(paths[-1])
	pathFlows.append(copy.deepcopy(curr_path))
	return pathFlows

if __name__ == "__main__":
	# experimentFile = open("4755_const_norm.txt", "a")
	# experimentFile.write("Path Length\t\tTotal Time\n")
	runtimes = 1
	for time in range(runtimes):
		conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
		conn.set_session(readonly=False, autocommit=True)
		cursor = conn.cursor()
		tablename = "T_o"
		datatype = "BitVec"
		num_paths = 3
		AS = "4755"
		ISP_path = join(root, 'topo/ISP_topo/')
		allow_list_path = join(root, 'experiments/arch_query/access_list/permit_list.txt')
		deny_list_path = join(root, 'experiments/arch_query/access_list/deny_list.txt')
		paths = getPaths(ISP_path, AS, num_paths)
		# aclList = getAccessListDest(allow_list_path, "allow", F) + getAccessListDest(deny_list_path, "deny", F) 
		aclList = getAccessListDest(deny_list_path, "deny", F) 
		nodes = getNodes(paths, SOURCE_COL, DEST_COL, FLOW_COL)
		nodeACLMapping = getNodeACLMapping(nodes, aclList, len(aclList))
		dividedAccessList = getDividedAccessList(nodeACLMapping)
		addFirewallOneBigSwitch(aclList=dividedAccessList, tablename=tablename, cursor=cursor)
		conn.commit()
		# conn.close()

		source_summaries, dest_summaries = makeEndNodesVariable(paths, SOURCE_COL, DEST_COL, FLOW_COL)
		# pathsClosureGroups = closure_group.getAllClosureGroups(paths)
		pathFlows = separateFlows(paths, FLOW_COL)
		pathsWithConditions = addConditions(pathFlows, nodeACLMapping, CONDITION_COL, SOURCE_COL, FLOW_COL,F)

		for pathsTableau in pathsWithConditions:
			sourceIPs, destIPs, flowIDs = extractSummary(paths=pathsTableau, source_summaries=source_summaries, dest_summaries=dest_summaries, flow_col=FLOW_COL)
			flows = extractFlows(F_variable=F, paths=pathsTableau, condition_col=CONDITION_COL)
			summary = flowIDs + sourceIPs + destIPs
			substituted_tableau = tableau.summary_substitutions(pathsTableau, summary, SUMMARY_INSTANCE)
			sql = tableau.general_convert_tableau_to_sql(substituted_tableau, tablename, SUMMARY_INSTANCE, ['n1', 'n2', 'F', 'condition'])
			# sql = tableau.convert_tableau_to_sql_distributed(pathsTableau, tablename, summary, ['n1', 'n2', 'F', 'condition'])
			print(sql)
			domains = {
				F: [flows]
			}

			tree = translator_pyotr.generate_tree(sql)
			data_time = translator_pyotr.data(tree)
			upd_time = translator_pyotr.upd_condition(tree, curr_type)
			nor_time = translator_pyotr.normalization(datatype)
			union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=datatype)
			domain_conditions = check_tautology.get_domain_conditions_from_list(domains, datatype)
			runtime = 0
			if union_conditions != "Or()": # i.e. Empty table
				ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
				print(model)
			else:
				ans = False
			print(ans)
			print(flows)
			total_time = data_time+upd_time+runtime+nor_time["contradiction"][1]+nor_time["redundancy"][1]
			# total_time = data_time+upd_time+runtime
			print("Data time", data_time)
			print("Update time", upd_time)
			print("Normalization time", nor_time)
			print("Check Tautology time", runtime)
			print("Total time", total_time)
			print("Length of path", len(pathsTableau))
			print("=======================================")