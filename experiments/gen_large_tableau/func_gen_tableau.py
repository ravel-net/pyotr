from ntpath import join
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg
import random
import os
import networkx as nx
from networkx.algorithms import tournament
from ipaddress import IPv4Address

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

def add_backup_links_and_filters(path_nodes, forward_tablename, pick_num):
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    if pick_num > len(path_nodes[:-2]):
        print("invalid pick_num! Please decrease pick_num or rerun script")
        exit()

    # randomly pick `pick_num` nodes to set backup links
    picked_nodes = random.sample(path_nodes[:-2], pick_num)

    flag_variables = {}
    bp_links = []
    for picked_node in picked_nodes:
        idx_picked_node = path_nodes.index(picked_node)
        # print("pickde_node", picked_node)
        # print("idx_picked_node", idx_picked_node)

        '''
        # update condition of primary link (currently only one primary link from `picked_node` to its next node)
        add ACL for picked nodes
        '''
        # store flag variable and its domain
        flag_var = "l{}_{}".format(picked_node, path_nodes[idx_picked_node+1])
        domain_var = [0, 1]
        flag_variables[flag_var] = domain_var

        # condition and acl for primary link
        cond = "{} == {}".format(flag_var, 1)
        cursor.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {}".format(forward_tablename, cond, picked_node, path_nodes[idx_picked_node+1]))
        cursor.execute("update {} set s = array_append(s, {}) where n1 = {} and n2 = {}".format(forward_tablename, picked_node, picked_node, path_nodes[idx_picked_node+1]))
        conn.commit()

        bp_next_node = random.sample(path_nodes[idx_picked_node+2:], 1)[0]
        bp_links.append((picked_node, bp_next_node))

        # condition for backup link (one backup link for a primary link)
        bp_cond = "{} == {}".format(flag_var, 0)
        cursor.execute("insert into {} values({}, {}, '{}', '{}')".format(forward_tablename, picked_node, bp_next_node, "{"+str(picked_node)+"}", "{"+ bp_cond + "}"))

        conn.commit()
    conn.close()

    return flag_variables, bp_links

def load_tree_in_f(links, ftable_name):
    """
    Load the primary path into database

    Parameters:
    -----------
    links: list[tuple]
        The links of the primary forwarding path
    
    ftable_name: string
        the name of database table to store `links`, the forwarding table
    """
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
    conn.close()

def gen_hamiltonian_path(links):
    G = nx.DiGraph()
    G.add_edges_from(links)

    is_dag = nx.is_directed_acyclic_graph(G)
    print(is_dag)

    # calculate hamiltonian path
    path_nodes = tournament.hamiltonian_path(G)

    source = path_nodes[0]
    dest = path_nodes[-1]
    edges = []
    for i in range(len(path_nodes)-1):
        edges.append((path_nodes[i], path_nodes[i+1]))

    return edges, path_nodes, source, dest

def gen_shortest_path(links):
    G = nx.Graph()
    G.add_edges_from(links)

    nodes = G.nodes

    two_nodes = random.sample(nodes, 2)

    source = two_nodes[0]
    dest = two_nodes[1]

    path_nodes = nx.dijkstra_path(G, source, dest)

    edges = []
    for i in range(len(path_nodes)-1):
        edges.append((path_nodes[i], path_nodes[i+1]))

    return edges, path_nodes, source, dest


def get_largest_connected_network(links):
    # print("original links", len(links))
    G = nx.Graph()
    G.add_edges_from(links)

    if not nx.is_connected(G):
        # print("not connected")
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

def gen_connectivity_view(path_nodes, tablename, table_attributes, table_datatypes):
    """
    generate connectivity view for chase

    Parameters:
    ------------
    path_nodes: list[integer/string]. The list of nodes in path. E.g., path 1->2->3. the path_nodes is [1, 2, 3].

    tableaname: string. The name of database table that stores the connectivity view.

    table_attributes: list[string]. The attributes of the database table <tablename>.

    table_datatypes: list[string]. The datatype of each attribute of the databse table <tablename>.

    """
    tuples = []
    tuples.append(('f', 's0', 'd0', 's', str(path_nodes[0]), '{}'))

    for i in range(len(path_nodes)-1):
        s = "s{}".format(i+1)
        d = "d{}".format(i+1)

        tuples.append(('f', s, d, str(path_nodes[i]), str(path_nodes[i+1]), '{}'))
    tuples.append(('f', 's{}'.format(len(path_nodes)), 'd{}'.format(len(path_nodes)), str(path_nodes[-1]), 'd', '{}'))
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    cursor.execute("Drop table if exists {}".format(tablename))

    attributes = ["{} {}".format(table_attributes[i], table_datatypes[i]) for i in range(len(table_attributes))]
    cursor.execute("create table {} ({})".format(tablename, ", ".join(attributes)))
    execute_values(cursor, "insert into {} values %s".format(tablename), tuples)

    conn.commit()
    conn.close()

def convert_symbol_to_IP(ftable_name, IP_address_begin='1.0.0.1'):
    """
    Convert symbolic integers to realistic IP address

    Parameters:
    -----------
    ftable_name: string
        the name of symbolic forwarding table
    """
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    cursor.execute("select * from {}".format(ftable_name))

    ftable_tuples = cursor.fetchall()
    
    IP_tuples = []
    symbol_to_IP_mapping = {}
    IPaddr = int(IPv4Address(IP_address_begin)) 
    for tuple in ftable_tuples:
        n1 = tuple[0]
        n2 = tuple[1]
        s = tuple[2]
        condition = tuple[3]

        if n1 in symbol_to_IP_mapping.keys():
            n1 = symbol_to_IP_mapping[n1]
        else:
            n1_IP = str(IPv4Address(IPaddr))
            IPaddr += 1

            symbol_to_IP_mapping[n1] = n1_IP
            n1 = n1_IP
        
        if n2 in symbol_to_IP_mapping.keys():
            n2 = symbol_to_IP_mapping[n2]
        else:
            n2_IP = str(IPv4Address(IPaddr))
            IPaddr += 1

            symbol_to_IP_mapping[n2] = n2_IP
            n2 = n2_IP

        # s_IP = []
        # for acl in s:
        #     if acl in symbol_to_IP_mapping.keys():
        #         s_IP.append(symbol_to_IP_mapping[acl])
        #     else:
        #         acl_ip = str(IPv4Address(IPaddr))
        #         IPaddr += 1

        #         symbol_to_IP_mapping[acl] = acl_ip
        #         s_IP.append(acl_ip)
        
        # s = s_IP

        IP_tuples.append((n1, n2, '{'+"{}".format(", ".join([str(acl) for acl in s]))+'}', '{'+"{}".format(", ".join(condition))+'}'))
    
    print("IP_tuples", IP_tuples)
    print("symbol_to_IP_mapping", symbol_to_IP_mapping)

    return IP_tuples, symbol_to_IP_mapping

def convert_symbol_to_IP_from_path_nodes(path_nodes, IP_address_begin='1.0.0.1'):
    """
    Convert symbol to IP address from a list of nodes who form a path. It is used to the experiment of the chase on policies impact analysis.

    Parameters:
    -----------
    path_nodes: list
        a list of nodes who forms a path
    
    IP_address_begin: string(IP-address like)
        the begin of IP addresses that used to mapping the symbolic integer to the real IP address

    Returns:
    --------
    IP_tuples: list(tuple)
        the encoding of E table
    
    symbolic_IP_mapping: dict
        the mapping between symbolic integers and read IP addresses
    
    """
    symbolic_IP_mapping = {}
    IP_tuples = []
    IPaddr = int(IPv4Address(IP_address_begin)) 
    for idx, node in enumerate(path_nodes):
        symbolic_IP_mapping[node] = str(IPv4Address(IPaddr))
        IPaddr += 1

        if idx == 0:
            IP_tuples.append(('f', 's{}'.format(idx), 'd{}'.format(idx), 's', symbolic_IP_mapping[node], '{}'))
            continue
        elif idx == len(path_nodes) - 1:
            IP_tuples.append(('f', 's{}'.format(idx), 'd{}'.format(idx), symbolic_IP_mapping[path_nodes[idx-1]], symbolic_IP_mapping[node], '{}'))
            IP_tuples.append(('f', 's{}'.format(idx+1), 'd{}'.format(idx+1), symbolic_IP_mapping[node], 'd', '{}'))
            continue
        
        IP_tuples.append(('f', 's{}'.format(idx), 'd{}'.format(idx), symbolic_IP_mapping[path_nodes[idx-1]], symbolic_IP_mapping[node], '{}'))
    return IP_tuples, symbolic_IP_mapping

def gen_hosts_IP_address(num_hosts, IP_address_begin='1.0.0.1'):
    """
    Generate a number of hosts' IP addresses. 

    Parameters:
    -----------
    num_hosts: inetger
        the number of hosts generated
    
    IP_address_begin: string(IP-address like)
        the begin of IP addresses that used to mapping the symbolic integer to the real IP address

    Returns:
    --------
    hosts_IPs: list
        a list of IP addresses whose size is `num_hosts`.
    
    """
    hosts_IPs = []
    IPaddr = int(IPv4Address(IP_address_begin))
    for i in range(num_hosts):
        hosts_IPs.append(str(IPv4Address(IPaddr)))
        IPaddr += 1

    return hosts_IPs


def load_table(tablename, attributes, tuples):
    """
    Stores tuples into database

    Parameters:
    -----------
    tablename: string
        name of database table
    
    attributes: dict
        the attributes and their corresponding datatype of the table `tablename`. e.g., {"src":"inet", ...}

    tuples: list[tuple]
        the tuples of table `tablename`    
    """
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    sql = "Drop table if exists {};".format(tablename)
    cursor.execute(sql)

    cols = []
    for attr in attributes.keys():
        cols.append("{} {}".format(attr, attributes[attr]))
    
    sql = "create table {} ({});".format(tablename, ", ".join(cols))
    cursor.execute(sql)

    execute_values(cursor, "insert into {} values %s".format(tablename), tuples)
    conn.commit()
    conn.close()

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
    # load_tree_in_f(path_links, fwd_tablename)

    # conn.close()
    # add backup links to spanning tree
    # add_backup_links_and_filters(dest, path_nodes, topo_tablename, fwd_tablename, 2)
    tablename = "E"
    table_attributes = ["f", 'src', 'dst', 'n', 'x', 'condition']
    table_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    gen_connectivity_view(path_nodes, tablename, table_attributes, table_datatypes)

