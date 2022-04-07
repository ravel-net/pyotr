import networkx as nx
import random
from tqdm import tqdm
import math
import os
import psycopg2
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()


'''
Load ISP topology into database
'''
def load_topo(file_dir, out_tablename):
    """
    param: db instance of DB
    param: file_dir ISP topology stored in txt file
    """
    sql = "Drop table if exists {};".format(out_tablename)
    cursor.execute(sql)

    sql = "create table {} (n1 integer, n2 integer);".format(out_tablename)
    cursor.execute(sql)

    file = open(os.getcwd() +file_dir, 'r')

    while True:
        line = file.readline()
        if not line:
            break

        line = line.strip()

        args = line.split(' ')
        # print("insert into graph values({}, {})".format(args[0], args[1]))
        cursor.execute("insert into {} values({}, {})".format(out_tablename, args[0], args[1]))
    print("Done!")

def min_spanning_tree(edges_list):
    G = nx.Graph()
    G.add_edges_from(edges_list)
    return nx.minimum_spanning_tree(G)

def get_largest_connected_network(links):
    # print("original links", len(links))
    G = nx.Graph()
    G.add_edges_from(links)

    if not nx.is_connected(G):
        print("not connected")
        max_comp = 0
        max_len = 0
        components = nx.connected_components(G)

        for idx, comp in enumerate(components):
            size = len(comp)
            # print(idx, size)
            if size > max_len:
                max_len = size
                max_comp = comp

        # print("max_len", max_len)
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

        return sub_links, max_comp # links, nodes
    else:
        return links, list(G.nodes)

def gen_spanning_tree(links):
    graph = nx.DiGraph()
    graph.add_edges_from(links)

    out_degrees = sorted(graph.out_degree, key=lambda x: x[1], reverse=True)
    root = out_degrees[0][0]
    # print(root)
            
    spanning_links = spanning_tree_bfs(graph, root) # root ='190'
    # print("spanning_links", len(spanning_links))
    return spanning_links, root

def spanning_tree_bfs(graph, node): # node = '190'
    links = []
    visited = [] # List to keep track of visited nodes.
    queue = []     #Initialize a queue
    visited.append(node)
    queue.append(node)

    while queue:
        s = queue.pop(0) 
        # print (s, end = " ") 
        neigs = [n for n in graph.neighbors(s)]
        for neighbour in neigs:
            if neighbour not in visited:
                visited.append(neighbour)
                queue.append(neighbour)
                links.append((s, neighbour))
    return links


def load_tree_in_f(links, ftable_name):

    G = nx.DiGraph()
    G.add_edges_from(links)

    # print(G.edges)
    rG = G.reverse()
    # print(rG.edges)

    tuples = []
    for edge in rG.edges:
        tuples.append([edge[0], edge[1], '{}', '{}'])

    sql = "Drop table if exists {}".format(ftable_name)
    cursor.execute(sql)

    sql = "create table {} (n1 integer, n2 integer, s integer[], condition text[]);".format(ftable_name)
    cursor.execute(sql)

    cursor.executemany("insert into {} values(%s, %s, %s, %s)".format(ftable_name), tuples)

    # update condition the node who is more than one link
    sql = "update {} set condition = array_append(condition, 'l' || n1 || ' == ' || n2) where n1 in (\
        select n1 from {} group by n1 having count(*) > 1)".format(ftable_name, ftable_name)

    cursor.execute(sql)
    conn.commit()
    
def add_link(dest, topo_tablename, forward_tablename, pick_rate):

    # get all nodes who have multiple neighbors in graph except root node
    cursor.execute("select n1 from {} group by n1 having count(*) > 1".format(topo_tablename))
    nodes = cursor.fetchall()
    nodes = [node[0] for node in nodes]
    # print(len(nodes))
    if dest in nodes:
        # nodes = set(nodes)
        nodes.remove(dest)

    # percentage of picking node
    count = math.ceil(len(nodes) * pick_rate)

    # random pick k nodes
    picked_nodes = random.sample(nodes, k = count)

    linked_neighbor_cur  = conn.cursor()
    check_cur = conn.cursor()
    upd_cur = conn.cursor()
    insert_cur = conn.cursor()
    for i in tqdm(range(len(picked_nodes))):
        node = picked_nodes[i]
        
        # get all neighbors
        cursor.execute("select distinct n2 from {} where n1 = {}".format(topo_tablename, node))
        neighbors = cursor.fetchall()
        neighbors = set([row[0] for row in neighbors])
        # print(neighbors)

        # get linked neighbors
        linked_neighbor_cur.execute("select distinct n2 from {} where n1 = {}".format(forward_tablename, node)) 
        linked_neighbors = linked_neighbor_cur.fetchall()
        linked_neighbors = set([row[0] for row in linked_neighbors])
        # print(linked_neighbors)

        # get unlinked neighbors
        unlinked_neighbors = neighbors - linked_neighbors
        
        if len(unlinked_neighbors) == 0:
            continue

        if root in unlinked_neighbors:
            unlinked_neighbors.remove(root)

        # randomly pick one unlinked neighbor node
        n = random.sample(unlinked_neighbors, k = 1)[0]

        # check if there are tuples already in f that n1 = node, update condition
        # edge(node, n)
        check_cur.execute("select * from {} where n1 = {}".format(forward_tablename, node))

        count = check_cur.rowcount
        # print('count: ', count)
        
        if count >= 1:
            row = check_cur.fetchone()
            # print(row)
            while row is not None:
                if len(row[3]) == 0:
                    cond = 'l{} == {}'.format(row[0], row[1])
                    # print("update f set condition = array_cat(condition, ARRAY['{}']) where n1 = {} and n2 = {}".format(cond, row[0], row[1]))
                    upd_cur.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {}".format(forward_tablename, cond, row[0], row[1]))
                
                row = check_cur.fetchone()

            cond = "l{} == {}".format(node, n) # condition for new added backup link
            # sql = "insert into {} values({}, {}, '{{}}', '{}')".format(forward_tablename, node, n, "{"+ cond + "}")
            # print(sql)
            insert_cur.execute("insert into {} values({}, {}, '{{}}', '{}')".format(forward_tablename, node, n, "{"+ cond + "}"))
        else:
            insert_cur.execute("insert into {} values({}, {}, '{{}}', '{}')".format(forward_tablename, node, n, "{}"))
        
        conn.commit()


def add_filter(nodes, root, rate, forward_tablename):
    """
    Randomly add ACL(filter) to node in Graph
    """

    # get all nodes in graph except root node
    nodes.remove(root)

    # percentage of picking node
    count = math.ceil(len(nodes) * rate)

    # random pick k nodes
    picked_nodes = random.sample(nodes, k = count)
    # print("picked_nodes:", picked_nodes)

    filtered_neig_cur = conn.cursor()
    all_neig_cur = conn.cursor()
    upd_cur = conn.cursor()
    for i in tqdm(range(len(picked_nodes))):
        n = picked_nodes[i]

        # find n's neighbors that have already set filter
        filtered_neig_cur.execute("select n1 from {} where n2 = {} and cardinality(s) != 0".format(forward_tablename, n)) # s = '{{}}'
        neighbor_filter_nodes = filtered_neig_cur.fetchall()
        neighbor_filter_nodes = [tuple[0] for tuple in neighbor_filter_nodes]
        # print("filtered neig:", neighbor_filter_nodes)

        # find n's all neighbors 
        all_neig_cur.execute("select n2 from {} where n1 = {} and s = '{{}}'".format(forward_tablename, n))
        all_filter_nodes = all_neig_cur.fetchall()
        all_filter_nodes = [tuple[0] for tuple in all_filter_nodes]
        # print("all neighbors:", all_filter_nodes)

        # remove neighbor who has set filter
        need_to_filter_nodes = set(all_filter_nodes) - set(neighbor_filter_nodes)
        need_to_filter_nodes = list(need_to_filter_nodes)

        for neigh in need_to_filter_nodes:
        # print("update {} set s = array_append(s, {}) where n1 = {} and s = '{{}}'".format(table, n, n))
            upd_cur.execute("update {} set s = array_append(s, {}) where n1 = {} and n2 = {} and cardinality(s) = 0".format(forward_tablename, n, n, neigh))
        
    conn.commit()

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
    as_num = 2914
    as_tablename = "as{}".format(as_num)
    load_topo("/topo/{}_edges.txt".format(as_num), as_tablename)

    cursor.execute("select * from {}".format(as_tablename))
    all_links = cursor.fetchall()
    print("all links:", len(all_links))
    connected_links, connected_nodes = get_largest_connected_network(all_links)
    print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

    topo_tablename = "topo_{}".format(as_num)
    fwd_tablename = "fwd_{}".format(as_num)
    cursor.execute("drop table if exists {}".format(topo_tablename))
    cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
    conn.commit()

    spanning_links, root = gen_spanning_tree(connected_links)
    print("root", root)
    print("spanning tree links:", len(spanning_links))
    
    load_tree_in_f(spanning_links, fwd_tablename)

    add_link(root, topo_tablename, fwd_tablename, 0.2)

    add_filter(connected_nodes, root, 0.5, fwd_tablename)

