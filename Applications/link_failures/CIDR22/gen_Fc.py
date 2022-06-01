import networkx as nx
from collections import OrderedDict
from sortedcontainers import SortedSet
import numpy as np
import matplotlib.pyplot as plt
import gen_connected_graph as gen_cgraph
import psycopg2

 
example = {1: {2: {'weight': 1},
               3: {'weight': 1},
               5: {'weight': 1}},
           2: {1: {'weight': 1},
               3: {'weight': 1},
               4: {'weight': 1}},
           3: {1: {'weight': 1},
               2: {'weight': 1}},
           4: {2: {'weight': 1},
               5: {'weight': 1}},
           5: {1: {'weight': 1},
               4: {'weight': 1}}
               }

example = [
    (1,2),
    (1,3),
    (1,5),
    (2,1),
    (2,3),
    (2,4),
    (3,1),
    (3,2),
    (4,2),
    (4,5),
    (5,1),
    (5,4),

]


output = gen_cgraph.tuple_to_nxdict(example)

# print(output)
# for i in output:
#     print(i)
graph = nx.Graph(output)

# retrieve all minimum spanning trees 
graph_yamada = gen_cgraph.Yamada(graph)
all_msts = graph_yamada.spanning_trees()

    
gen_cgraph.gen_fc_table(all_msts,5)
