from tqdm import tqdm
import networkx as nx
import numpy as np

class CountTrees:

    def load_topo(self, tuples):
        
        # generate tree
        G = nx.Graph()
        G.add_edges_from(tuples)
        # tree = nx.minimum_spanning_tree(G)

        # transform directed graph to undirected
        G = G.to_directed()

        nodes = list(G.nodes)
        links = list(G.edges)

        # create dict for nodes {node: index}
        nodes_dict = {}
        for count in tqdm(range(len(nodes))):
            node = nodes[count]
            nodes_dict[node] = count

        # create dict for edges (node: [neighbor1, neighbor2, ...])
        edges_dict = {}
        for count in tqdm(range(len(links))):
            edge = links[count]
            if edge[0] in edges_dict.keys():
                node_list = edges_dict[edge[0]]
                edges_dict[edge[0]].append(edge[1])
            else:
                node_list = [edge[1]]
                edges_dict[edge[0]] = node_list
        
        return G, nodes_dict, edges_dict

    def laplacian_matrix(self, graph, nodes_dict, edges_dict):
        num = len(nodes_dict)
        '''
        if i == j, matrix[i][j] = degree[node]
        else if i != j, matrix = -1
        otherwise, matrix = 0
        '''
        matrix = np.zeros(shape=(num, num), dtype=int)
        for node, i in nodes_dict.items():
            matrix[i][i] = graph.degree[node]

            adjacent_nodes = edges_dict[node]
            for n in adjacent_nodes:
                j = nodes_dict[n]
                matrix[i][j] = -1       
        return matrix

    """
    Calculate the total number of spanning trees in a graph
    """
    def det(self, matrix):
        matrix = np.delete(matrix, 0, 0)
        matrix_ = np.delete(matrix, 0, 1)

        if matrix_.shape[0] > 10:
            sign, logdet = np.linalg.slogdet(matrix_)
            det = sign * np.exp(logdet)
        else:
            det = np.linalg.det(matrix_)
        return det

if __name__ == '__main__':
    toy_example = [
        (1, 2),
        (1, 3),
        (1, 5),
        (2, 1),
        (2, 3),
        (2, 4),
        (3, 1),
        (3, 2),
        (4, 2),
        (4, 5),
        (5, 1),
        (5, 4)
    ]

    # sql = "select * from topo_{};".format(self.AS_NUMBER)
    # self.db.select(sql)

    # edges_list = self.db._cursor.fetchall()

    calculator = CountTrees()

    print("Load data ...")
    graph, nodes_dict, edges_dict = calculator.load_topo(toy_example)
    print("Done!\n")

    print(nodes_dict)
    print(edges_dict)

    print("create Matrix ...")
    matrix = calculator.laplacian_matrix(graph, nodes_dict, edges_dict)
    print("Done!\n")

    print(matrix)

    print("Calculate Det ...")
    det = calculator.det(matrix)
    print("Done!\n")

    print(det)
