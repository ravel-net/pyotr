import sys
import pprint
import time
import json
from tqdm import tqdm
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'util')
sys.path.append(filename)
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
filename = join(root, 'faure_translator')
sys.path.append(filename)

import tableau as tableau
import DFS
from closure_overhead import find_variables, construct_Graph, calculate_tableau
# import logging
# logging.basicConfig(filename='data/exp_closure.log', level=logging.DEBUG)

sizes = [100]#, 1000, 10000]
rate = 0.2

# logging.info("+++++++++++++++++++++++++++++++++++Running Date:{}+++++++++++++++++++++++++++++++++++".format(time.asctime( time.localtime(time.time()) )))

f = open("data/exp_close_data.txt", "a")
row = "#nodes closure_overhead \n"
f.write(row)
for size in sizes:
    print(size)
    row = "{} ".format(size)
    # logging.info("Size of chain: {}".format(size))
    count_time = 0
    for i in tqdm(range(10)):
        physical_path, physical_nodes, overlay_path, overlay_nodes = tableau.gen_large_chain(size=size, rate=rate)
        physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)

        variables = find_variables(physical_nodes)
        graph = construct_Graph(variables, physical_tuples)

        start = time.time()
        conns = graph.connectedComponents()
        reverse_conns = graph.reverse_connectComponents(conns)
        minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))
        end = time.time()

        count_time += end - start
        if i == 9:
            data = {}
            data['physical_path'] = physical_path
            data['physical_nodes'] = physical_nodes
            data['overlay_path'] = overlay_path
            data['overlay_nodes'] = overlay_nodes
            with open('data/chain{}.json'.format(size), 'w') as outfile:
                json.dump(data, outfile)

    
    row += " {}\n".format(count_time/10)
    f.write(row)
    # logging.warning("Variable closure groups execution time: {}".format(count_time/10))

f.close()
