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

def getShortestPaths(g, num_vertices, num_paths):
	currentPathList = []
	for extraNode in range(num_paths):
		source = num_vertices+(2*extraNode)
		dest = num_vertices+(2*extraNode)+1
		paths = g.get_shortest_paths(source,dest)
		currentPathList += paths
	return currentPathList


def getIndPaths(g, num_vertices, num_paths):
	currentPathList = []
	for extraNode in range(num_paths):
		source = num_vertices+(2*extraNode)
		dest = num_vertices+(2*extraNode)+1
		paths = g.get_all_shortest_paths(source,dest)
		# print(source)
		# print(dest)
		i = 0
		for path in paths:
			i += 1
			if (i == len(paths)):
				currentPathList += path
				break
			list1_as_set = set(currentPathList)
			intersection = list1_as_set.intersection(path)	
			if len(intersection) > 0:
				# print("intersection found")
				# print(path)
				# print(currentPathList)
				continue
			else:
				currentPathList += path
				break
	return currentPathList

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

def getTableauWithFlowID(num_vertices, num_paths, paths):
	tableau = []
	for f, path in enumerate(paths):
		constants = range(num_vertices, num_vertices+(2*num_paths))
		for i in range(len(path)-1):
			node1 = value(path[i], constants)
			node2 = value(path[i+1], constants)
			if (node1.isdigit() and node2.isdigit()):
				continue
			tableau.append(tuple((node1, node2, 'f'+str(f))))
	return tableau

        
def makeGraph(edges, num_vertices, mapping, num_paths):
	g = Graph()
	g.add_vertices(num_vertices+(2*num_paths))
	list_of_edges = []
	for line in edges:
		edge = line.split()
		# print(edge)
		if ((mapping[edge[0]], mapping[edge[1]]) not in list_of_edges
			and (mapping[edge[1]], mapping[edge[0]]) not in list_of_edges):
			list_of_edges.append((mapping[edge[0]], mapping[edge[1]]))
		# g.add_edges(list_of_edges)
	# Add source and destination nodes
	for extraNode in range(num_paths):
		randomNode = random.randint(0, num_vertices-1)
		randomNode2 = random.randint(0, num_vertices-1)
		list_of_edges.append((num_vertices+(2*extraNode),randomNode))
		list_of_edges.append((num_vertices+(2*extraNode)+1,randomNode2))
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