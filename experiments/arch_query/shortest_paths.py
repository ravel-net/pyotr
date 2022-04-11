from igraph import *
import random
from os.path import dirname, abspath, join

def addNodes(num_vertices, numNodes):
    extraNodes = []
    for node in range(num_vertices, num_vertices+numNodes):
        extraNodes.append(node)
        self.adj.append([])
        randomNode = random.randint(0, num_vertices-1)
        self.add_edge(randomNode, node)
    return extraNodes

def getPaths(g, num_vertices):
	# currentPathList = []
	source = random.randint(0, num_vertices-1)
	dest = random.randint(0, num_vertices-1)
	paths = g.get_all_shortest_paths(source,dest)
	# print(source)
	# print(dest)
	# i = 0
	# for path in paths:
	# 	i += 1
	# 	if (i == len(paths)):
	# 		currentPathList += path
	# 		break
	# 	list1_as_set = set(currentPathList)
	# 	intersection = list1_as_set.intersection(path)	
	# 	if len(intersection) > 0: # Only non-overlapping paths selected
	# 		# print("intersection found")
	# 		# print(path)
	# 		# print(currentPathList)
	# 		continue
	# 	else:
	# 		currentPathList += path
			# break
	return paths, source, dest

def value(node, constants):
	if node in constants:
		return str(node)
	else:
		return 'x'+str(node)


def getTableau(num_vertices, num_paths, paths):
	tableau = []
	constants = range(num_vertices, num_vertices+(2*num_paths))
	for i in range(len(paths)-1):
		node1 = value(paths[i], constants)
		node2 = value(paths[i+1], constants)
		if (node1.isdigit() and node2.isdigit()):
			continue
		tableau.append(tuple((node1, node2)))
	return tableau

        
def makeGraph(edges, num_vertices, mapping):
	g = Graph()
	g.add_vertices(num_vertices)
	list_of_edges = []
	for line in edges:
		edge = line.split()
		# print(edge)
		if ((mapping[edge[0]], mapping[edge[1]]) not in list_of_edges
			and (mapping[edge[1]], mapping[edge[0]]) not in list_of_edges):
			list_of_edges.append((mapping[edge[0]], mapping[edge[1]]))
	g.add_edges(list_of_edges)
	return g

def createNodeMappings(nodes):
    mapping = {}
    # map nodes to 0 to number of nodes
    i = 0
    for node in nodes:
        mapping[node.strip()] = i    
        i += 1
    return mapping


# root = dirname(dirname(abspath(__file__)))
# filename = join(root, 'ISP_topo/')
# as_file = "7018"
# nodes = join(filename,as_file+"_nodes.txt")
# edges = join(filename,as_file+"_edges.txt")
# print(nodes)
# f = open(nodes,"r")
# lines = f.readlines()
# num_vertices = len(lines)
# nodes = []
# for node in lines:
# 	nodes.append(node.strip())
# mapping = createNodeMappings(nodes)
# f = open(edges,"r")
# edgeslines = f.readlines()
# num_paths = 3
# g = makeGraph(edgeslines, num_vertices, mapping, num_paths)
# # currentPathList = getIndPaths(g, num_vertices, num_paths)
# currentPathList = g.get_all_shortest_paths(v=11292, to=11293, weights=None, mode='out')
# print(currentPathList)
# print(g.neighbors(11292))
# print(g.neighbors(currentPathList[0][1]))
# print(g.neighbors(11293))
# print(g.neighbors(currentPathList[0][-2]))
# print(getTableau(num_vertices, num_paths,currentPathList))