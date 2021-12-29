import pprint

class Graph:
    def __init__(self, variables):
        self.V = len(variables) # variable list
        self.adj = [[] for i in range(self.V)]
        self.mapping = {}
        self.reverse_mapping = []
        for i in range(0,self.V):
          self.mapping[variables[i]] = i #maps variables to i
          self.reverse_mapping.append(variables[i])
 
    def DFSUtil(self, temp, v, visited):
        visited[v] = True # Mark visited
        temp.append(self.reverse_mapping[v])
 
        # Repeat for all vertices adjacent
        # to this vertex v
        for i in self.adj[v]:
            if visited[i] == False:
                # Update the list
                temp = self.DFSUtil(temp, i, visited)
        return temp
 
    # method to add an undirected edge
    def add_edge(self, v, w):
        v = self.mapping[v]
        w = self.mapping[w]
        self.adj[v].append(w)
        self.adj[w].append(v)
 
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

    def reverse_connectComponents(self, cc):
        reverse_cc = {}
        component_number = 0
        for component in cc:
            component_number += 1
            for var in component:
                reverse_cc[var] = component_number
        return reverse_cc

 
 
# Driver Code
# if __name__ == "__main__":
#     # Create a graph given in the above diagram
#     # 5 vertices numbered from 0 to 4
#     g = Graph(['a','b','c','d','e','f'])
#     g.addEdge('b', 'a')
#     g.addEdge('c', 'd')
#     g.addEdge('d', 'e')
#     cc = g.connectedComponents()
#     print("Following are connected components")
#     print(cc)
