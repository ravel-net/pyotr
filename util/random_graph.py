import pprint
import random

def decision(probability):
    return random.random() < probability

class RandomGraph:
    def __init__(self, num_vertices, probability):
        self.n = num_vertices # number of vertices
        self.p = probability # probability of connection
        while True:
            self.adj = [[] for i in range(self.n)]
            for i in range(self.n):
                for j in range(i+1, self.n):
                    if (i == 0 and j == self.n-1): # no direct connection between source and dest
                        continue
                    if (decision(self.p)):
                        self.add_edge(i,j)
            # source and destination should be reachable
            print("reachable:", self.reachable(0, self.n-1))
            if self.reachable(0, self.n-1):
                break
        
    def printAdjMatrix(self):
        pp = pprint.PrettyPrinter(indent=4)
        pp.pprint(self.adj)
 
    def DFSUtil(self, temp, v, visited):
        visited[v] = True # Mark visited
        temp.append(v)
        # Repeat for all vertices adjacent
        # to this vertex v
        for i in self.adj[v]:
            if visited[i] == False:
                # Update the list
                temp = self.DFSUtil(temp, i, visited)
        return temp

    # Returns true if i and j are reachable
    def reachable(self, i, j):
        temp = []
        visited = []
        for k in range(self.n):
            visited.append(False)
        dfs = self.DFSUtil(temp, i, visited)
        return (j in dfs)

    # method to add an undirected edge
    def add_edge(self, i, j):
        self.adj[i].append(j)
        self.adj[j].append(i)
 
    # Method to retrieve connected components
    # in an undirected graph
    def connectedComponents(self):
        visited = []
        cc = []
        for i in range(self.V):
            visited.append(False)
        for v in range(self.V):
            if visited[v] == False:
                temp = []
                cc.append(self.DFSUtil(temp, v, visited))
        return cc

    # def reverse_connectComponents(self, cc):
    #     reverse_cc = {}
    #     component_number = 0
    #     for component in cc:
    #         component_number += 1
    #         for var in component:
    #             if (var in self.variables):
    #                 reverse_cc[var] = component_number
    #     return reverse_cc
    def chooseVertex(self, number_links, tries, visited, v):
        for d in range(0, tries):
            vertexIndexToVisit = random.randint(0, number_links-1)
            vertexToVisit = self.adj[v][vertexIndexToVisit]
            if (not visited[vertexToVisit]):
                return vertexToVisit
        return -1

    def tryRandomWalk(self, dest, depth, curr_depth, temp, visited, v):
        if (curr_depth >= depth):
            return []

        visited[v] = True # Mark visited
        temp.append(v)
        num_links = len(self.adj[v])
        # put a limit on the length of path
        # Choose a vertex to traverse
        vertexVal = self.chooseVertex(num_links, depth, visited, v)
        if (vertexVal == -1):
            return []
        if (vertexVal == dest):
            temp.append(dest)
            return temp

        temp = self.tryRandomWalk(dest, depth, curr_depth+1, temp, visited, vertexVal)
        return temp

    def randomPaths(self, source, dest, depth, tries):
        pathsSet = set()
        paths = []
        for i in range(tries):
            temp = []
            visited = [False for num in range(self.n)]
            curr_path = self.tryRandomWalk(dest, depth, 0, temp, visited, 0)
            string_ints = [str(int) for int in curr_path]
            pathStr = "".join(string_ints)
            if (curr_path != [] and pathStr not in pathsSet):
                paths.append(curr_path)
                pathsSet.add(pathStr)
        return paths
 
# Driver Code
if __name__ == "__main__":
    # Create a graph given in the above diagram
    # 5 vertices numbered from 0 to 4
    g = RandomGraph(20, 0.4)
    g.printAdjMatrix()
    depth = 40
    tries = 8
    paths = g.randomPaths(0, g.n - 1, depth, tries) # generates random paths between two nodes
    print("paths:", paths)
    print("length of paths:", len(paths))