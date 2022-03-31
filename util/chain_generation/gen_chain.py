"""
Generate chain with loops
"""
import math

def gen_chain_with_loop(size=15, rate_summary=0.6, size_single_loop=4):   
    """
    Parameters:
    -------------
    size: integer
        The number of nodes in the topology
    rate_summary: float
        the percentage of nodes that appears in the summary; ranges [0, 1]
    size_single_loop:integer
        the number of variable nodes in a single loop; It is the upper bound of a single loop.
    """
    path = []
    num_summary_nodes = math.ceil(size * rate_summary)
    num_variable_nodes = size - num_summary_nodes

    '''
    generate summary(constant) nodes and path for summary nodes
    '''
    summary_nodes = ["{}".format(num+1) for num in range(num_summary_nodes)]
    for i in range(num_summary_nodes-1):
        path.append((summary_nodes[i], summary_nodes[i+1]))

    # generate variable nodes
    variable_nodes = ["x{}".format(num+1) for num in range(num_variable_nodes)]

    '''
    generate path for loops
    '''
    picked_nodes = []
    i = 0
    k = 0
    while k < num_variable_nodes:
        s_node = summary_nodes[i % num_summary_nodes] # pick summary node in order, if i over the num of summary nodes, go back to the first summary node(like iterating circular queue) 
        bunch_variable = [] # picked a batch of variables with size_single_loop number from variable list(variable nodes)
        pos = i*size_single_loop
        if pos+size_single_loop < num_variable_nodes: 
            bunch_variable = variable_nodes[pos:pos+size_single_loop]
        else: # if remaining number of variables is less than size_single_loop
            bunch_variable =variable_nodes[pos:]

        for j in range(len(bunch_variable)):
            v_node = bunch_variable[j]
            if j == 0:
                path.append((s_node, v_node))
                if len(bunch_variable) == 1:
                    path.append((v_node, s_node))
                    continue
            elif j == len(bunch_variable)-1:
                path.append((v_node, s_node))
                continue
            
            nv_node = bunch_variable[j+1]
            path.append((v_node, nv_node))
        if i < num_summary_nodes:
            picked_nodes.append(s_node)
        k += len(bunch_variable)
        i += 1
    print(path)
    return path, summary_nodes, variable_nodes, picked_nodes

def gen_tableau(path, picked_nodes):
    tuples = []
    for pair in path:
        n1 = pair[0]
        n2 = pair[1]
        tuples.append((n1, n2, '{}'))

    for node in picked_nodes:
        tuples.append((node, node, '{}'))
    
    return tuples


if __name__ == "__main__":
    path, summary_nodes, variable_nodes, picked_nodes = gen_chain_with_loop(size=10, rate_summary=0.3, size_single_loop=2)
    tuples = gen_tableau(path, picked_nodes)
    print(tuples)
