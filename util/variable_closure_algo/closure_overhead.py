import sys
import pprint
import time
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'util')
sys.path.append(filename)
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
import tableau as tableau
import DFS


def find_variables(nodes):
	variables = []
	for node in nodes:
		# if not node.isnumeric():
		if type(node) is not int:
			variables.append(node)
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




if __name__ == '__main__':
    size = 10 # the number of nodes in physical network path
    rate = 0.3 # the percentage of constant nodes in physical network path (the number of nodes in overlay path)

    physical_path, physical_nodes, overlay_path, overlay_nodes = tableau.gen_large_chain(size=size, rate=rate)
    physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)

    variables = find_variables(physical_nodes)
    graph = construct_Graph(variables, physical_tuples)

    stats = {}
    start = time.time()
    conns = graph.connectedComponents()
    reverse_conns = graph.reverse_connectComponents(conns)
    minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))
    end = time.time()

    stats["time_overhead"] = end - start
    stats["longest_group_size"] = get_longest_group(conns) 
    stats["total_groups"] = len(conns) 
    stats["total_variables"] = len(variables) 
    stats["total_tuples"] = len(physical_tuples) 

    pp = pprint.PrettyPrinter(indent=4)
    print("\n================Tableau==================")
    pp.pprint(minimal_tableau)
    print("\n================Connected Components==================")
    pp.pprint(conns)
    print("\n================Stats==================")
    pp.pprint(stats)
    print("\n================Description==================")
    print("Note: 1) Execution time is in seconds. 2) Not counting self-tuples")
    # print("==============Physical Tuples====================")
    # print(physical_tuples)


