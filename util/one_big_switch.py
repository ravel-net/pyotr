import random_graph
import pprint
import sys
import tableau
import psycopg2
import shortest_paths
import statistics
# from memory_profiler import profile
# import tracemalloc
import time
from os.path import dirname, abspath, join
root = dirname(dirname(abspath(__file__)))
filename = join(root, 'util/check_tautology')
sys.path.append(filename)
filename = join(root, 'pyotr_translator')
sys.path.append(filename)
filename = join(root, 'util/variable_closure_algo')
sys.path.append(filename)
import translator_pyotr
import check_tautology
import closure_overhead


host = '127.0.0.1'
user = 'postgres'
password = 'mubashir'
database = 'test'

def generatePaths(g, depth, tries):
	# g = random_graph.RandomGraph(vertices, probability_of_edge, numHosts)
	print("Adj Matrix")
	g.printAdjMatrix()
	paths = g.randomPaths(depth, tries) # generates random paths between two nodes
	print("paths:", paths)
	print("length of paths:", len(paths))
	return paths

def value(pre_processed_val, constants):
	if pre_processed_val in constants:
		return str(pre_processed_val)
	else:
		return "x" + str(pre_processed_val)

def generateOneBigSwitchTopo(g, depth, tries):
	# paths = generatePaths(vertices, probability_of_edge, depth, tries, numHosts)
	paths = g.randomPaths(depth, tries)
	pathNum = 0
	allPaths = []
	for path in paths:
		pathNum += 1
		curr_path = []
		for i in range(0, len(path)-1):
			n1 = value(path[i], g.hosts)
			n2 = value(path[i+1], g.hosts)
			# f = "f"+str(pathNum)
			# newTuple = (f, n1, n2)
			newTuple = (n1, n2)
			curr_path.append(newTuple)
		allPaths.append(curr_path)
	return allPaths


def addOneBigSwitchTable(tablename, constants):
	curr_type = 'int4_faure'
	conn = psycopg2.connect(host=host,user=user,password=password,database=database)
	cursor = conn.cursor()
	cursor.execute("DROP TABLE IF EXISTS {};".format(tablename))
	cursor.execute("CREATE TABLE {}(n1 {}, n2 {}, condition TEXT[]);".format(tablename, curr_type, curr_type))
	conn.commit()
	for hostSwitch in constants:
	    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, str(hostSwitch), '1'))
	    cursor.execute("INSERT INTO {} VALUES ('{}', '{}', array[]::text[]);".format(tablename, '1', str(hostSwitch)))
	cursor.execute("INSERT INTO {} VALUES ('1', '1', array[]::text[]);".format(tablename))
	conn.commit()
	conn.close()

def getCurrentTable(tablename, cur):
    cur.execute('select * from {};'.format(tablename))
    return cur.fetchall()

def nonEmpty(tablename):
    conn = psycopg2.connect(host=host,user=user,password=password,database=database)
    cur = conn.cursor()

    # get current table
    curr_table = getCurrentTable(tablename, cur)
    conn.commit()
    return len(curr_table)>0

def getConstants(table):
	constants = []
	for tuple in table:
		if tuple[0].isdigit() and tuple[0] not in constants:
			constants.append(tuple[0])
		if tuple[1].isdigit() and tuple[1] not in constants:
			constants.append(tuple[1])
	return constants

# @profile
def runExperiment():
	tableName = "t_v"
	# as_files = ["4755","3356","2914", "7018"]
	as_files = ["7018"]
	num_paths = 3
	runs = 1
	experimentFile = open("experiment_stats.txt", "w")

	for as_file in as_files:
		root = dirname(dirname(abspath(__file__)))
		filename = join(root, 'ISP_topo/')
		nodes = join(filename,as_file+"_nodes.txt")
		edges = join(filename,as_file+"_edges.txt")
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

		dat_times_sums = []
		closure_group_length = []
		closure_group_num = []
		all_dat_times = []
		run = 0
		while run < runs:
			g = shortest_paths.makeGraph(edgeslines, num_vertices, mapping, num_paths)
			currentPathList = shortest_paths.getIndPaths(g, num_vertices, num_paths)
			allPathsTableau = shortest_paths.getTableau(num_vertices, num_paths,currentPathList)
			constants = getConstants(allPathsTableau)
			addOneBigSwitchTable(tableName, constants)
			pp = pprint.PrettyPrinter(indent=4)
			closure_groups = closure_overhead.getAllClosureGroups(allPathsTableau)
			if (len(closure_groups) < num_paths):
				continue
			run += 1
			dat_times = []
			i = 0
			closure_group_num.append(len(closure_groups))
			for group in closure_groups:
				# addOneBigSwitchTableau(tableName, summary[i][1], summary[i][2])
				# print(summary[i][1], summary[i][2])
				summary = getConstants(group)
				closure_group_length.append(len(group))
				print(summary)
				sql = tableau.convert_tableau_to_sql(group, tableName, summary) + " LIMIT 1"
				# print(sql)
				conn = psycopg2.connect(host=host,user=user,password=password,database=database)
				cur = conn.cursor()
				begin = time.time()
				cur.execute(sql)
				end = time.time()
				dat_times.append(end-begin)
				result = cur.fetchall()
				conn.close()
				if (len(result) > 0):
					print("TRUE")
				else:
					print("FALSE")
					pp.pprint(allPaths[i])
					exit()
				i += 1

			all_dat_times += dat_times
			dat_times_sums.append(sum(dat_times))

		pp.pprint(closure_groups)
		print("===============STATS=============")
		experimentFile.write("as_file: " + as_file)
		experimentFile.write("\n")
		experimentFile.write("Length of closure groups: " + ' '.join(str(v) for v in closure_group_length))
		experimentFile.write("\n")
		experimentFile.write("Number of closure groups: " + ' '.join(str(v) for v in closure_group_num))
		experimentFile.write("\n")
		experimentFile.write("Individual closure group timings: " + ' '.join(str(v) for v in all_dat_times))
		experimentFile.write("\n")
		# print("Data Time:", dat_times)
		# print("Update Time:", update_times)
		experimentFile.write("Data Time Sum (seconds): " + ' '.join(str(v) for v in dat_times_sums))
		experimentFile.write("\n")
		experimentFile.write("Data Time Average (seconds): " + str(statistics.mean(dat_times_sums)))
		experimentFile.write("\n")
		experimentFile.write("Standard Deviation: " + str(statistics.pstdev(dat_times_sums)))
		experimentFile.write("\n")
		experimentFile.write("\n")

	experimentFile.close()
		# print("Update Time Sum (s):", sum(update_times))

if __name__ == "__main__":
	# starting the monitoring
	# tracemalloc.start()
	 
	# function call
	runExperiment()
	 
	# displaying the memory
	# print(tracemalloc.get_traced_memory())
	 
	# stopping the library
	# tracemalloc.stop()