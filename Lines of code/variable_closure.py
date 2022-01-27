import pprint

class Graph:
    def __init__(self, variables):
        self.V = len(variables) # variable list
        self.adj = [[] for i in range(self.V)]
        self.mapping = {}
        self.reverse_mapping = []
        self.variables = variables
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
                if (var in self.variables):
                    reverse_cc[var] = component_number
        return reverse_cc
        

def find_variables(tuples):
	variables = []
	for tuple in tuples:
		if not tuple[0].isnumeric() and tuple[0] not in variables:
			variables.append(tuple[0])	
		if not tuple[1].isnumeric() and tuple[1] not in variables:
			variables.append(tuple[1])
	return variables

def construct_Graph(variables, path):
	graph = DFS.Graph(variables)
	variables_dict = set()
	for var in variables:
		variables_dict.add(var)
	for tuple in path:
		if tuple[0] in variables_dict and tuple[1] in variables_dict:
			graph.add_edge(tuple[0], tuple[1])
	return graph

def get_longest_group(conns):
	max_size = 0
	for con in conns:
		if len(con) > max_size:
			max_size = len(con)
	return max_size

def calculate_tableau(tuples, reverse_conns, number_components):
    tableau = []
    for i in range(0, number_components):
        tableau.append([])
    for tuple in tuples:
    	if (tuple[0] in reverse_conns):
    		component_number = reverse_conns[tuple[0]]-1
    		tableau[component_number].append((tuple[0], tuple[1]))
    	elif (tuple[1] in reverse_conns):
    		component_number = reverse_conns[tuple[1]]-1
    		tableau[component_number].append((tuple[0], tuple[1]))
    return tableau

# Given a tuple and a table, returns the closure group of the tuple from the table.
def getClosureGroup(tuple, table):
    variables = find_variables(table)
    graph = construct_Graph(variables, table)
    conns = graph.connectedComponents() # TODO: ineffecient. Don't need all connected components
    reverse_conns = graph.reverse_connectComponents(conns) 
    if (tuple[0] in reverse_conns):
        minimal_tableau_pos = reverse_conns[tuple[0]] - 1
    elif (tuple[1] in reverse_conns):
        minimal_tableau_pos = reverse_conns[tuple[1]] - 1
    else:
        return [tuple] # constants tuple like (1,1) only have themselves in the closure group
    minimal_tableau = calculate_tableau(table, reverse_conns, len(conns))
    return minimal_tableau[minimal_tableau_pos]

# Returnsn all closure groups from a given table
def getAllClosureGroups(table):
    variables = find_variables(table)
    graph = construct_Graph(variables, table)
    conns = graph.connectedComponents() # TODO: ineffecient. Don't need all connected components
    reverse_conns = graph.reverse_connectComponents(conns) 
    # if (tuple[0] in reverse_conns):
    #     minimal_tableau_pos = reverse_conns[tuple[0]] - 1
    # elif (tuple[1] in reverse_conns):
    #     minimal_tableau_pos = reverse_conns[tuple[1]] - 1
    # else:
    #     return [tuple] # constants tuple like (1,1) only have themselves in the closure group
    minimal_tableau = calculate_tableau(table, reverse_conns, len(conns))
    return minimal_tableau



