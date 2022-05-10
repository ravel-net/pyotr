import pprint
import random
import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import utils.closure_group.closure_group as closure_group

class Graph:
    def __init__(self, nodeFile, edgesFile):
        f = open(nodeFile,"r")
        lines = f.readlines()
        self.mapping = {}
        self.nodes = []
        # map nodes to 0 to number of nodes
        i = 0
        for node in lines:
            self.nodes.append(i)  
            self.mapping[int(node.strip())] = i    
            i += 1  
        self.num = len(self.nodes)
        self.adj = [[] for i in range(self.num)]
        # print(self.adj)
        # print(self.mapping)
        # print(self.nodes)
        f = open(edgesFile,"r")
        lines = f.readlines()
        for edge in lines:
            n1 = self.mapping[int(edge.split()[0])]
            n2 = self.mapping[int(edge.split()[1])]
            # print(n1, n2)
            self.add_edge(n1, n2)
        # print(self.adj)
        # self.mapping = {}
        # self.reverse_mapping = []
        # self.variables = variables
        # for i in range(0,self.V):
        #   self.mapping[variables[i]] = i #maps variables to i
        #   self.reverse_mapping.append(variables[i])
 
    def calcShortestPath(self, source, dest):
        explored = []
        queue = [[source]]
        if (source == dest):
            print("Same Source and Dest:", source)
            exit()
        while queue:
            path = queue.pop(0)     
            node = path[-1]
            if node not in explored:
                neighbours = self.adj[node]
                for neighbour in neighbours:
                    new_path = list(path)     
                    new_path.append(neighbour)
                    queue.append(new_path)

                    if neighbour == dest:
                        return new_path
                explored.append(node)
        # print("So sorry, but a connecting"\
                # "path doesn't exist :(")
        return [-1]

    def calcShortestPaths(self, nodePairs):
        allPaths = []
        for nodePair in nodePairs:
            source = nodePair[0]
            dest = nodePair[1]
            path = self.calcShortestPath(source, dest)
            if (path == [-1]):
                print("No path found between " + str(source) + " and " + str(dest))
                continue
            allPaths.append(path)
        return allPaths

    # method to add an undirected edge
    def add_edge(self, v, w):
        # v = self.mapping[v]
        # w = self.mapping[w]
        self.adj[v].append(w)
        self.adj[w].append(v)
 
    def addNodes(self, numNodes):
        extraNodes = []
        for node in range(self.num, self.num+numNodes):
            extraNodes.append(node)
            self.adj.append([])
            randomNode = random.randint(0, self.num-1)
            self.add_edge(randomNode, node)
        return extraNodes

    def value(self, pre_processed_val, constants):
        if pre_processed_val in constants:
            return str(pre_processed_val)
        else:
            return "x" + str(pre_processed_val)

    def generateTableau(self, paths, constants):
        # paths = generatePaths(vertices, probability_of_edge, depth, tries, numHosts)
        pathNum = 0
        allPaths = []
        for path in paths:
            pathNum += 1
            curr_path = []
            for i in range(0, len(path)-1):
                n1 = self.value(path[i], constants)
                n2 = self.value(path[i+1], constants)
                # f = "f"+str(pathNum)
                # newTuple = (f, n1, n2)
                newTuple = (n1, n2)
                curr_path.append(newTuple)
            allPaths.append(curr_path)
        flat_list = [item for sublist in allPaths for item in sublist]
        return flat_list
 
# Driver Code
if __name__ == "__main__":
    # Create a graph given in the above diagram
    # 5 vertices numbered from 0 to 4
    as_file = "7018"
    g = Graph(as_file+"_nodes.txt", as_file+"_edges.txt")
    extraNodes = g.addNodes(6)
    src = [extraNodes[0],extraNodes[1],extraNodes[2]]
    dest = [extraNodes[3],extraNodes[4],extraNodes[5]]
    paths = g.calcShortestPaths([(src[0],dest[0]),(src[1],dest[1]),(src[2],dest[2])])
    print("paths", paths)
    allPaths = g.generateTableau(paths, extraNodes)
    print("allPaths", allPaths)
    f = open(as_file+"_paths.txt", "w")
    for path in allPaths:
        f.write(path[0] + " " + path[1] + "\n")
    f.close()
    closure_groups = closure_group.getAllClosureGroups(allPaths)
    pp = pprint.PrettyPrinter(indent=4)
    pp.pprint(allPaths)
    pp.pprint(len(closure_groups))
    pp.pprint(closure_groups)

    # f = open("1221_paths.txt", "a")
    # f.write(allPaths)
    # f.close()
