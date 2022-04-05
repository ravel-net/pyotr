# Shortest Paths
To get a tableau with a given number of independent paths in any rocket fuel topology in the form of tableau, call the following functions:<br/>
1. `mapping = shortest_paths.createNodeMappings(nodes)` // Takes the list of nodes in the graph as input <br/>
2. `f = open(edges,"r")`<br/>
`edgeslines = f.readlines()` <br/>
`g = shortest_paths.makeGraph(edgeslines, num_vertices, mapping, extra_nodes)` // `edgeslines` is the list of edges in the topology, `num_vertices` is the number of vertices in the graph, and `num_paths` is the required number of paths in the topology (for one_big_switch this meant adding extra nodes outside the topology))<br/>
3. `currentPathList = shortest_paths.getIndPaths(g, num_vertices, num_paths)` // gets `num_paths` number of independent (non-overlapping) paths between the added nodes
4. `allPathsTableau = shortest_paths.getTableau(num_vertices, num_paths,currentPathList)` // Returns the resulting tableau from the paths

It might be a good idea to check the main funciton in one_big_switch.py to see the usage of shortest paths. 
