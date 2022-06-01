from db import DB
import networkx as nx
import random
from tqdm import tqdm
import math
import os
from rtable import Rtable

class Main:
    def __init__(self, db_name, f_table, graph_table, rate):
        self.db = DB(db=db_name)
        self.db_name = db_name
        self.F_TABLE = f_table
        self.GRAPH_TABLE = graph_table
        self.RATE = rate


    # db = DB()
    # F_TABLE = 'f'
    # GRAPH_TABLE = 'topo'

    '''
    Load ISP topology into database
    '''
    def load_topo(self, file_dir):
        """
        param: db instance of DB
        param: file_dir ISP topology stored in txt file
        """
        sql = "Drop table if exists {};".format(self.GRAPH_TABLE)
        self.db.common(sql)

        sql = "create table {} (n1 integer, n2 integer);".format(self.GRAPH_TABLE)
        self.db.common(sql)

        file = open(os.getcwd() +file_dir, 'r')

        while True:
            line = file.readline()
            if not line:
                break

            line = line.strip()

            args = line.split(' ')
            # print("insert into graph values({}, {})".format(args[0], args[1]))
            self.db.insert("insert into {} values({}, {})".format(self.GRAPH_TABLE, args[0], args[1]))
        print("Done!")

    def min_spanning_tree(self, edges_list):
        G = nx.Graph()
        G.add_edges_from(edges_list)
        return nx.minimum_spanning_tree(G)
    
    def get_largest_connected_network(links):
        print("original links", len(links))
        G = nx.Graph()
        G.add_edges_from(links)

        graph = nx.DiGraph()
        if not nx.is_connected(G):
            print("not connected")
            max_comp = 0
            max_len = 0
            components = nx.connected_components(G)

            for idx, comp in enumerate(components):
                size = len(comp)
                print(idx, size)
                if size > max_len:
                    max_len = size
                    max_comp = comp

            print("max_len", max_len)
            # print("max_comp", max_comp)
            '''
            get all links which nodes are in max_comp
            cannot use G.subgraph() directly, because some links are missing, 
            such as link (1, 2) and (2, 1) that only keep one of them after creating undirected graph
            '''
            sub_links = []
            for idx, link in enumerate(links):
                if link[0] in max_comp or link[1] in max_comp:
                    sub_links.append(link) 
                    
            # print("sub_links", sub_links)      
            # graph.add_edges_from(sub_links)

            return sub_links, max_comp # links, nodes
        else:
            return links, list(G.nodes)


    def load_tree_in_f(self, tree):
        fc_table = self.F_TABLE

        sql = "Drop table if exists {} ;".format(self.F_TABLE)
        self.db.common(sql)

        sql = "create table {} (n1 integer, n2 integer, s integer[], condition text[]);".format(self.F_TABLE)
        self.db.common(sql)

        
        root = sorted(tree.degree, key=lambda x: x[1], reverse=True)[0][0]

        # choose the subgraph which contains root
        for index, sub in enumerate(nx.connected_components(tree)):
            H = tree.subgraph(sub)
            if root in list(H.nodes):
                subgraph = H.copy()
                break
        
        # randomly pick dest(better the degree of node is max)
        edges = subgraph.edges()
        edges = list(edges)

        fc_graph = []
        count = 0
        i = 0
        # initial edges
        while count <= len(edges):
            if edges[i][0] == root:
                fc_graph.append((edges[i][1],edges[i][0], [], [])) 
                edges.pop(i)
                i = i - 1
            elif edges[i][1] == root: 
                fc_graph.append((edges[i][0],edges[i][1], [], []))
                edges.pop(i)
                i = i - 1
            i+=1
            count +=1
        count = 0
        i = 0
        # Loop: add edges to graph
        while len(edges) != 0 :
            count = 0
            i = 0
            max = len(edges)
            while count <= len(edges):
                for fc_edges in fc_graph:
                    if edges[i][0] == fc_edges[0]:
                        fc_graph.append((edges[i][1],edges[i][0], [], []))
                        edges.pop(i)
                        i -= 1
                        break

                    elif edges[i][1] == fc_edges[0]:
                        fc_graph.append((edges[i][0],edges[i][1], [], [])) 
                        edges.pop(i)   
                        i-= 1    
                        break                 
                count +=1
                i += 1
        # fc_tables.append(fc_graph)

        self.db.insertmany("insert into {} values(%s, %s, %s, %s)".format(fc_table), fc_graph)

        # update condition who is more that one link
        sql = "update {} set condition = array_append(condition, 'l' || n1 || ' == ' || n2) where n1 in (\
            select n1 from {} group by n1 having count(*) > 1)".format(self.F_TABLE, self.F_TABLE)

        self.db.common(sql)
        
    def add_link(self, tree):
        f_table = self.F_TABLE
        graph = self.GRAPH_TABLE
        

        # get root node
        root = sorted(tree.degree, key=lambda x: x[1], reverse=True)[0][0]

        # get all nodes who have multiple neighbors in graph except root node

        # nodes = list(tree.nodes())

        self.db.select("select n1 from {} group by n1 having count(*) > 1".format(graph))
        nodes = self.db._cursor.fetchall()
        nodes = [node[0] for node in nodes]

        if root in nodes:
            nodes = set(nodes)
            nodes.remove(root)

        # num = len(nodes)

        # percentage of picking node
        count = math.ceil(len(nodes) * self.RATE)

        # random pick k nodes
        picked_nodes = random.sample(nodes, k = count)

        for i in tqdm(range(len(picked_nodes))):
            node = picked_nodes[i]
            # randomly pick one node in tree not equal to root
            # index = random.randint(0, num - 1)
            # # print(nodes[index])
            # while nodes[index] == root:
            #     index = random.randint(0, num - 1)

            # node = nodes[index]
            # print("node: ",node)
            
            # get all neighbors
            self.db.select("select distinct n2 from {} where n1 = {}".format(graph, node))
            neighbors = self.db._cursor.fetchall()
            neighbors = set([row[0] for row in neighbors])
            # print(neighbors)

            # get linked neighbors
            linked_neighbor_db = DB(db=self.db_name)
            linked_neighbor_db.select("select distinct n2 from {} where n1 = {}".format(f_table, node)) 
            linked_neighbors = linked_neighbor_db._cursor.fetchall()
            linked_neighbors = set([row[0] for row in linked_neighbors])
            # print(linked_neighbors)

            # get unlinked neighbors
            unlinked_neighbors = neighbors - linked_neighbors
            
            if len(unlinked_neighbors) == 0:
                continue

            if root in unlinked_neighbors:
                unlinked_neighbors.remove(root)

            # randomly pick one unlinked neighbor node
            index = random.randint(0, len(unlinked_neighbors) - 1)
            n = list(unlinked_neighbors)[index]

            # check if there are tuples already in f that n1 = node
            # edge(node, n)
            check_db = DB(db=self.db_name)
            check_db.select("select * from {} where n1 = {}".format(f_table, node))

            count = check_db._cursor.rowcount
            # print('count: ', count)
            if count >= 1:
                row = check_db._cursor.fetchone()
                # print(row)
                while row is not None:
                    if len(row[3]) == 0:
                        cond = "l{} == {}".format(row[0], row[1])
                        # print("update f set condition = array_cat(condition, ARRAY['{}']) where n1 = {} and n2 = {}".format(cond, row[0], row[1]))
                        DB(db=self.db_name).update("update {} set condition = array_cat(condition, ARRAY['{}']) where n1 = {} and n2 = {}".format(f_table, cond, row[0], row[1]))
                    
                    row = check_db._cursor.fetchone()

                cond = "l{} == {}".format(node, n)
                # print("insert into f values({}, {}, ARRAY[{}], ARRAY['{}'])".format(e[1], e[0], e[1], cond))
                # DB().insert("insert into f values({}, {}, ARRAY[{}], ARRAY['{}'])".format(e[1], e[0], e[1], cond))
                DB(db=self.db_name).insert("insert into {} values({}, {}, ARRAY[]::integer[], ARRAY['{}'])".format(f_table, node, n, cond))
            else:
                # print("insert into f values({}, {}, ARRAY[{}], ARRAY[]::text[])".format(e[1], e[0], e[1]))
                # DB().insert("insert into f values({}, {}, ARRAY[{}], ARRAY[]::text[])".format(e[1], e[0], e[1]))
                DB(db=self.db_name).insert("insert into {} values({}, {}, ARRAY[]::integer[], ARRAY[]::text[])".format(f_table, node, n))


    def add_filter(self, tree):
        """
        Randomly add ACL(filter) to node in Graph
        """
        table = self.F_TABLE
        graph = self.GRAPH_TABLE

        # get root node
        root = sorted(tree.degree, key=lambda x: x[1], reverse=True)[0][0]

        # get all nodes in graph except root node
        nodes = set(tree.nodes())
        nodes.remove(root)

        # percentage of picking node
        count = math.ceil(len(nodes) * 0.5)

        # random pick k nodes
        picked_nodes = random.sample(nodes, k = count)

        for i in tqdm(range(len(picked_nodes))):
            n = picked_nodes[i]

            # find n's neighbors that have already set filter
            self.db.select("select n1 from {} where n2 = {} and s = '{{}}'".format(self.F_TABLE, n))
            neighbor_filter_nodes = self.db._cursor.fetchall()
            neighbor_filter_nodes = [tuple[0] for tuple in neighbor_filter_nodes]

            # find n's all neighbors 
            self.db.select("select n2 from {} where n1 = {} and s = '{{}}'".format(self.F_TABLE, n))
            all_filter_nodes = self.db._cursor.fetchall()
            all_filter_nodes = [tuple[0] for tuple in all_filter_nodes]

            # remove neighbor who has set filter
            need_to_filter_nodes = set(all_filter_nodes) - set(neighbor_filter_nodes)
            need_to_filter_nodes = list(need_to_filter_nodes)

            for node in need_to_filter_nodes:
            # print("update {} set s = array_append(s, {}) where n1 = {} and s = '{{}}'".format(table, n, n))
                self.db.update("update {} set s = array_append(s, {}) where n1 = {} and n2 = {} and s = '{{}}'".format(table, n, n, node))

if __name__ == '__main__':
    # file_dir = './topo/2914_edges.txt'
    # load_topo(db, file_dir)

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
    func = Main(f_table='f', graph_table='topo', db_name='test', rate=0.2)

    db = DB(db='test')
    # db.insertmany("insert into toy values(%s, %s)", toy_example)
    # db.select("select n1, n2 from f_4755")
    # T = func.min_spanning_tree(db._cursor.fetchall())
    T = func.min_spanning_tree(toy_example)
    print(nx.is_tree(T))

    print(sorted(T.edges()))
    root = sorted(T.degree, key=lambda x: x[1], reverse=True)[0]

    func.load_tree_in_f(T)
    print("Done: load_tree_in_f")
    
    func.add_link(T)
    print("Done: add_link")

    func.add_filter(T)
    print("Done: add_filter")

    print("root: ", root)

     # generate R table 
    print("Generating R")
    r_gene = Rtable(db=DB(db='test'), f_table='f', as_number=0)

    r_gene.r1()
    count = r_gene.rn()

    r_gene.union(count=count)
    print("Done.")

    




