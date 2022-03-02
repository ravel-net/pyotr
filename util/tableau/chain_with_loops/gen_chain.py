"""
Generate chain with loops

"""
import math
import random
import sys

def gen_chain_with_loop(size=15, rate_summary=0.3, rate_loops=0.6):   
    """
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

    # random.seed(20)
    # seed = random.randrange(sys.maxsize)
    # rng = random.Random(seed)
    # print("Seed was:", seed)
    picked_nodes = random.sample(summary_nodes, total_num_loops)
    # print("Picked Nodes:",picked_nodes)
    picked_nodes = ['3']
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
    path, summary_nodes, loop_nodes, picked_nodes = gen_chain_with_loop(size=15, rate_summary=0.5, rate_loops=0.5)
    tuples = gen_tableau(path, picked_nodes)
    print(tuples)
