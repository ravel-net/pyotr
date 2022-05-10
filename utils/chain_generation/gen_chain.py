"""
Generate chain with loops
"""
import math
import random


"""
 /- u -\
1       2 - w - 3
 \_ v _/ 
"""
def gen_tableau_overlay(path, overlay):
    """
    Generate tableau table

    Parameters:
    ------------
    path : list
        a list of pairwise link in forward path

    ovelay : list
        a list of nodes in overlay network

    Returns:
    ------------
    tuples : list
        the list of links with n1, n2

    self_tuples : list
        the list of links with self-connected
    """
    max_val = get_max(overlay)
    self_tuples = []
    tuples = []
    i = 0
    while i < len(path) - 1:
        (n1, n2) = path[i]
        (n3, n4) = path[i+1]
        
        self_tuples.append((n1, n1, '{}'))

        if n2 in overlay:
            tuples.append((n1, "{}".format(int(n2)+max_val), '{}'))
            tuples.append(("{}".format(int(n2)+max_val), n3, '{}'))
        else:
            tuples.append((n1, n2, '{}'))
        
        i += 1

    (n1, n2) = path[i]
    self_tuples.append((n1, n1, '{}'))
    tuples.append((n1, n2, '{}'))

    return tuples, self_tuples

def gen_large_chain(size=10, rate=0.3):
    """
    Generate chain with size and rate

    Parameters:
    ------------
    size : integer, default=10
        the number of nodes(including variable nodes and constant nodes) in physical path

    rate : float, default=0.3
    the percentage of constant nodes in physical path 

    Returns
    ------------
    forward_path : list
        the list of pairwise link in physical path

    node_list : list
        the nodes(including variable nodes and constant nodes) of physical path in forwarding order

    overlay_path : list
        the list of pairwise link in overlay path

    overlay_nodes : list
        the constant nodes of overlay path in forwarding order
    """
    cons_size = int(size * rate)
    var_size = size - cons_size

    var_list = ["x{}".format(i) for i in range(1, var_size+1)]
    cons_list = [str(i) for i in range(1, cons_size+1)]

    # set the first node and the last node
    first = cons_list.pop(0)
    last = cons_list.pop()
    
    # shuffle the variable nodes and constant node except the first and last constant nodes
    node_list = var_list + cons_list
    random.shuffle(node_list)

    # insert the first and last constant nodes back to node list
    node_list.insert(0, first)
    node_list.append(last)
    
    # generate pairwise path list for physical path
    forward_path = []
    overlay_nodes = [] # store the constant nodes in physical path order
    for i in range(size-1):
        forward_path.append((node_list[i], node_list[i+1]))
        if type(node_list[i]) is int or node_list[i].isdigit():
            overlay_nodes.append(node_list[i])
    if type(node_list[size-1]) is int or node_list[size-1].isdigit():
        overlay_nodes.append(node_list[size-1])

    # generate pairwise path list for overlay path
    overlay_path = []
    for i in range(cons_size-1):
        overlay_path.append((overlay_nodes[i], overlay_nodes[i+1]))

    # print(node_list)
    # print(forward_path)
    # print(overlay_nodes)
    # print(overlay_path)
    return forward_path, node_list, overlay_path, overlay_nodes

def gen_chain_even_group(size=10, rate=0.5):
    cons_size = int(size * rate)

    node_list = []
    if cons_size < 2:
        var_size = size - 2
        cons_size = 2
        var_list = ["x{}".format(i) for i in range(1, var_size+1)]
        node_list = ["1"] + var_list + ["2"]
    else:
        var_size = size - cons_size
        # print("var_size", var_size)
        group_num = cons_size - 1
        # print("group_num", group_num)
        avg_group_size = int(var_size / group_num)
        # print("avg_group_size", avg_group_size)

        j = 1 
        for i in range(group_num-1):
            lower = avg_group_size-1 if avg_group_size-1 >= 0 else 0
            upper = avg_group_size+2
            # print(lower, upper)
            size_per_group = random.choice(range(lower, upper))
            # print(size_per_group)
            node_list.append(str(i+1))
            s = 0
            while s < size_per_group:
                node_list.append("x{}".format(j))
                j += 1
                s += 1
        node_list.append(str(group_num))
        s = 0
        # print("j", j)
        final_group_size = var_size-(j-1)
        # print("final_group", final_group_size)
        while s < final_group_size:
            node_list.append("x{}".format(j))
            j += 1
            s += 1    
        node_list.append(str(group_num+1))
        # print(node_list)

    var_list = ["x{}".format(i) for i in range(1, var_size+1)]
    cons_list = [str(i) for i in range(1, cons_size+1)]
    
    forward_path = []
    for i in range(size-1):
        forward_path.append((node_list[i], node_list[i+1]))

    overlay_path = []
    for i in range(cons_size-1):
        overlay_path.append((cons_list[i], cons_list[i+1]))

    return forward_path, node_list, overlay_path, cons_list


def gen_chain_with_loop(size=15, rate_summary=0.6, size_single_loop=4):   
    """
    Generate chain topology with loops. 
    Configure size of chain topology, size of summary nodes and the number of variable nodes in a single loop.

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

def gen_chain_with_loop_control_position(size=15, rate_summary=0.3, rate_loops=0.6):   
    """
    Generate chain topology with loops. 
    Configure size of chain topology, size of summary nodes and the number of summary nodes who are connected to loops.

    Parameters:
    -------------
    size: integer
        The number of nodes in the topology
    rate_summary: float
        the percentage of nodes that appears in the summary; ranges [0, 1]
    rate_loops:float
        the percentage of summay nodes that contains the loop; ranges [0, 1]
    
    """
    path = []
    num_summary_nodes = math.ceil(size * rate_summary)
    summary_nodes = ["{}".format(num+1) for num in range(num_summary_nodes)]
    for i in range(num_summary_nodes-1):
        path.append((summary_nodes[i], summary_nodes[i+1]))
    print(path)

    total_num_loops = math.ceil(num_summary_nodes * rate_loops)
    avg_num_nodes_in_loop = math.ceil((size - num_summary_nodes) / total_num_loops)

    picked_nodes = random.sample(summary_nodes, total_num_loops)
    print(picked_nodes)
    numbers = []
    count = 0
    for i in range(total_num_loops-1):
        # num = random.randint(avg_num_nodes_in_loop-1, avg_num_nodes_in_loop+1)
        num = avg_num_nodes_in_loop
        count += num
        numbers.append(num)
    numbers.append((size - num_summary_nodes) - count)
    print(numbers)
    i = 1
    loop_nodes = []
    for idx, node in enumerate(picked_nodes):
        if numbers[idx] == 1:
            path.append((node, "y{}".format(i+j)))
            path.append(("y{}".format(i+j), node))
            continue
        for j in range(numbers[idx]):
            if j == 0:
                path.append((node, "y{}".format(i+j)))
                path.append(("y{}".format(i+j), "y{}".format(i+j+1)))
            elif j == numbers[idx] - 1:
                path.append(("y{}".format(i+j), node))
            else:
                path.append(("y{}".format(i+j), "y{}".format(i+j+1)))
            loop_nodes.append("y{}".format(i+j))
        # path.append(("y{}".format(i+j+1), node))
        i += numbers[idx]
    return path, summary_nodes, loop_nodes, picked_nodes


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
    path, summary_nodes, variable_nodes, picked_nodes = gen_chain_with_loop(size=20, rate_summary=0.95, size_single_loop=2)
    tuples = gen_tableau(path, picked_nodes)
    print(variable_nodes)
    print(tuples)
