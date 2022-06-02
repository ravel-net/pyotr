import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import databaseconfig as cfg
import random
import os
import networkx as nx
from networkx.algorithms import tournament

'''
Load ISP topology into database
'''
def load_topo(file_dir, out_tablename):
    """
    param: db instance of DB
    param: file_dir ISP topology stored in txt file
    """
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

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
    
    conn.commit()
    conn.close()
    print("Done!")

def add_backup_links_and_filters(dest, path_nodes, topo_tablename, forward_tablename, pick_num):
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    # get all nodes who have multiple neighbors in graph except root node
    cursor.execute("select n1 from {} group by n1 having count(*) > 1".format(topo_tablename))
    nodes = cursor.fetchall()
    nodes = [node[0] for node in nodes]
    # print(len(nodes))
    if dest in nodes:
        # nodes = set(nodes)
        nodes.remove(dest)

    # picked nodes should locate before the second last node
    nodes1 = set(nodes)
    nodes2 = set(path_nodes[:-2])

    suitable_nodes = nodes1.intersection(nodes2)

    # random pick count nodes
    count = pick_num
    if len(suitable_nodes) < pick_num:
        count = len(suitable_nodes)
    picked_nodes = random.sample(list(suitable_nodes), k = count)

    # store the variable of flag for backup links and its domain (in case there are multiple backup links for a primary link)
    flag_variables = {}

    linked_neighbor_cur  = conn.cursor()
    check_cur = conn.cursor()
    upd_cur = conn.cursor()
    insert_cur = conn.cursor()
    i = 0
    while i < count:
        node = random.sample(list(suitable_nodes), k = 1)[0]
        
        # get all neighbors
        cursor.execute("select distinct n2 from {} where n1 = {}".format(topo_tablename, node))
        neighbors = cursor.fetchall()
        neighbors = set([row[0] for row in neighbors])
        # print(neighbors)

        # get linked neighbors
        # node -> ?
        linked_neighbor_cur.execute("select distinct n2 from {} where n1 = {}".format(forward_tablename, node)) 
        linked_neighbors = linked_neighbor_cur.fetchall()
        linked_neighbors = set([row[0] for row in linked_neighbors])

        # get unlinked neighbors
        unlinked_neighbors = neighbors - linked_neighbors
        
        if len(unlinked_neighbors) == 0:
            continue

        # the neighbor node should locate after this node
        loc_node = path_nodes.index(node)
        nodes3 = set(path_nodes[loc_node+1:])

        allowed_nodes = unlinked_neighbors.intersection(nodes3)

        if len(allowed_nodes) == 0:
            continue

        # if dest in unlinked_neighbors:
        #     unlinked_neighbors.remove(dest)

        # randomly pick one unlinked neighbor node
        n = random.sample(list(allowed_nodes), k = 1)[0]
        
        '''
        # update condition of primary link (currently only one primary link from node to next node)
        add ACL for picked nodes
        '''
        check_cur.execute("select * from {} where n1 = {}".format(forward_tablename, node))
        row = check_cur.fetchone()

        # store flag variable and its domain
        flag_var = "l{}_{}".format(row[0], row[1])
        domain_var = [0, 1]
        flag_variables[flag_var] = domain_var

        # condition and acl for primary link
        cond = "{} == {}".format(flag_var, 1)
        upd_cur.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {}".format(forward_tablename, cond, row[0], row[1]))
        upd_cur.execute("update {} set s = array_append(s, {}) where n1 = {} and n2 = {}".format(forward_tablename, node, row[0], row[1]))
        conn.commit()

        # condition for backup link (one backup link for a primary link)
        bp_cond = "{} == {}".format(flag_var, 0)
        insert_cur.execute("insert into {} values({}, {}, '{}', '{}')".format(forward_tablename, node, n, "{"+str(node)+"}", "{"+ bp_cond + "}"))

        conn.commit()

        i += 1
        suitable_nodes.remove(node) # remove picked node from waitlist
    conn.close()

def load_tree_in_f(links, ftable_name):
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()
    
    tuples = []
    for link in links:
        tuples.append((link[0], link[1], '{}', '{}'))

    sql = "Drop table if exists {}".format(ftable_name)
    cursor.execute(sql)

    sql = "create table {} (n1 integer, n2 integer, s integer[], condition text[]);".format(ftable_name)
    cursor.execute(sql)

    cursor.executemany("insert into {} values(%s, %s, %s, %s)".format(ftable_name), tuples)
    conn.commit()

def gen_hamiltonian_path(links):
    G = nx.DiGraph()
    G.add_edges_from(links)

    # calculate hamiltonian path
    path_nodes = tournament.hamiltonian_path(G)

    source = path_nodes[0]
    dest = path_nodes[-1]
    edges = []
    for i in range(len(path_nodes)-1):
        edges.append((path_nodes[i], path_nodes[i+1]))

    return edges, path_nodes, source, dest

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

if __name__ == '__main__':
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    file_dir  = '/../../topo/ISP_topo/'
    filename = "4755_edges.txt"

    as_tablename = 'as_4755'

    load_topo(file_dir+filename, as_tablename)

    # calculate the largest component of topology graph (here is the whole topology)
    cursor.execute("select * from {}".format(as_tablename))
    all_links = cursor.fetchall()
    print("all links:", len(all_links))
    connected_links, connected_nodes = get_largest_connected_network(all_links)
    print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

    # Store the largest component into db and use it as the experimental topology
    topo_tablename = "topo_4755"
    fwd_tablename = "fwd_4755"
    cursor.execute("drop table if exists {}".format(topo_tablename))
    cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
    conn.commit()

    # calculate the spanning tree, return tree links and its root
    path_links, path_nodes, source, dest  = gen_hamiltonian_path(connected_links)
    print("source", source)
    print("dest", dest)
    print("hamiltonian path:", len(path_links))

    # load spanning tree into db (without backup and filters)
    load_tree_in_f(path_links, fwd_tablename)

    # conn.close()
    # add backup links to spanning tree
    add_backup_links_and_filters(dest, path_nodes, topo_tablename, fwd_tablename, 2)

