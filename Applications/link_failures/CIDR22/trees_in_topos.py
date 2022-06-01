"""
This python script used to automatically calculate the totoal number of spanning tree in topo
"""

from networkx.classes.function import edges
from db import DB
from count_spanning_tree import CountTrees
import networkx as nx

as_numbers = [4755, 3356, 2914, 7018]

for as_num in as_numbers:
    print("AS number: ", as_num)
    db = DB(db='cidr')

    sql = "select * from topo_{} where n1 != n2;".format(as_num)
    db.select(sql)

    pairs = db._cursor.fetchall()

    # generate graph
    graph = nx.Graph()
    graph.add_edges_from(pairs)

    # calculate the number of instances in each subgraph
    total_num = 0
    for g in nx.connected_components(graph):
        g = graph.subgraph(g).copy()

        edges = list(g.edges)

        calculator = CountTrees()

        print("Load data ...")
        subgraph, nodes_dict, edges_dict = calculator.load_topo(edges)
        print("Done!\n")

        print("create Matrix ...")
        matrix = calculator.laplacian_matrix(subgraph, nodes_dict, edges_dict)
        print("Done!\n")

        print("Calculate Det ...")
        det = calculator.det(matrix)
        print("Done!\n")

        print("det: ", det)
        total_num = total_num + det

    print("The total number of spanning trees in AS {}: {}".format(as_num, total_num))