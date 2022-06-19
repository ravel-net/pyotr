import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import databaseconfig as cfg
import experiments.gen_large_tableau.func_gen_tableau as func_linkfail

def gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num):
    """
    Script for generating large forwarding table with backup links and ACLs

    Parameters:
    ------------
    file_dir: string. The file path for the edges of Rocketfuel topology file.

    filename: string. The file name for the edges of Rocketfuel topology file.

    as_tablename: string. The database table name. This table stores the original Rocketfuel topology.

    topo_tablename: string. The database table name. This table stores the largest component of a Rocketfuel topology and using this component as the topology to add backup links and ACLs.

    fwd_tablename: string. The database table name. This table stores all possible forwarding behaviors. 

    pick_num: integer. The number of nodes who are added the backup link and ACL.

    """

    func_linkfail.load_topo(file_dir+filename, as_tablename)

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    # calculate the largest component of topology graph (here is the whole topology)
    cursor.execute("select * from {}".format(as_tablename))
    all_links = cursor.fetchall()
    print("all links:", len(all_links))
    connected_links, connected_nodes = func_linkfail.get_largest_connected_network(all_links)
    print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

    # Store the largest component into db and use it as the experimental topology
    cursor.execute("drop table if exists {}".format(topo_tablename))
    cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
    conn.commit()
    conn.close()

    
    # calculate the shortest path, ransomly select source and dest
    path_links, path_nodes, source, dest  = func_linkfail.gen_shortest_path(connected_links)
    while len(path_nodes) - 2 < pick_num:
        path_links, path_nodes, source, dest  = func_linkfail.gen_shortest_path(connected_links)
    # source = 4
    # dest = 1
    # path_nodes = [4, 2, 1]
    # path_links = [(4, 2), (2, 1)]
    print("source", source)
    print("dest", dest)
    print("path nodes", path_nodes)
    print("lenght of path:", len(path_links))

    # load spanning tree into db (without backup and filters)
    func_linkfail.load_tree_in_f(path_links, fwd_tablename)

    # add backup links to spanning tree
    flag_variables, bp_links = func_linkfail.add_backup_links_and_filters(path_nodes, fwd_tablename, pick_num)

    IP_tuples, symbolic_IP_mapping = func_linkfail.convert_symbol_to_IP(fwd_tablename)
    attributes = {
        'n1': 'inet_faure', 
        'n2': 'inet_faure',
        's':'integer[]',
        'condition':'text[]'
    }
    func_linkfail.load_table(fwd_tablename, attributes, IP_tuples)

    return path_nodes, IP_tuples, symbolic_IP_mapping[source], symbolic_IP_mapping[dest], symbolic_IP_mapping, bp_links

def gen_dependencies_for_link_failures_on_chase(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num):
    """
    Script for generating large forwarding table with backup links and ACLs

    Parameters:
    ------------
    file_dir: string. 
        The file path for the edges of Rocketfuel topology file.

    filename: string. 
        The file name for the edges of Rocketfuel topology file.

    as_tablename: string. 
        The database table name. This table stores the original Rocketfuel topology.

    topo_tablename: string. 
        The database table name. This table stores the largest component of a Rocketfuel topology and using this component as the topology to add backup links and ACLs.

    fwd_tablename: string. 
        The database table name. This table stores all possible forwarding behaviors. 

    pick_num: integer. 
        The number of nodes who are added the backup link and ACL.

    """

    func_linkfail.load_topo(file_dir+filename, as_tablename)

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    # calculate the largest component of topology graph (here is the whole topology)
    cursor.execute("select * from {}".format(as_tablename))
    all_links = cursor.fetchall()
    # print("all links:", len(all_links))
    connected_links, connected_nodes = func_linkfail.get_largest_connected_network(all_links)
    # print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

    # Store the largest component into db and use it as the experimental topology
    cursor.execute("drop table if exists {}".format(topo_tablename))
    cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
    conn.commit()
    conn.close()

    
    # calculate the shortest path, ransomly select source and dest
    path_links, path_nodes, source, dest  = func_linkfail.gen_shortest_path(connected_links)
    while len(path_nodes) - 2 < pick_num:
        path_links, path_nodes, source, dest  = func_linkfail.gen_shortest_path(connected_links)

    # print("source", source)
    # print("dest", dest)
    # print("path nodes", path_nodes)
    # print("lenght of path:", len(path_links))

    # load spanning tree into db (without backup and filters)
    func_linkfail.load_tree_in_f(path_links, fwd_tablename)

    # add backup links to spanning tree
    _, bp_links = func_linkfail.add_backup_links_and_filters(path_nodes, fwd_tablename, pick_num)

    IP_tuples, symbolic_IP_mapping = func_linkfail.convert_symbol_to_IP(fwd_tablename)
    attributes = {
        'n1': 'inet_faure', 
        'n2': 'inet_faure',
        's':'integer[]',
        'condition':'text[]'
    }
    func_linkfail.load_table(fwd_tablename, attributes, IP_tuples)

    link_failures_dependencies, preserving_dependencies, sigma3 = func_generate_dependencies_for_link_failure_chase(path_nodes, bp_links, source, dest, symbolic_IP_mapping)

    f = open("./dependencies/record.txt", "a")
    f.write("path nodes: {}\n".format(path_nodes))
    f.write("symbolic_IP_mapping:{}\n".format(symbolic_IP_mapping))
    f.write("bp_links:{}\n".format(bp_links))
    f.write("link_failures_dependencies: {}\n".format(link_failures_dependencies))
    f.write("preserving dependencies: {}\n".format(preserving_dependencies))
    f.write("sigma3:{}\n".format(sigma3))
    f.write("----------------------\n")
    f.close()

    return link_failures_dependencies, preserving_dependencies, sigma3, path_nodes, bp_links, symbolic_IP_mapping

def func_generate_dependencies_for_link_failure_chase(path_nodes, bp_links, source, dest, symbolic_IP_mapping):
    """
    Parameters:
    -----------
    path_nodes: list
        the list of nodes which forms the path

    bp_links: list[tuple]
        the list of backup links(symbolic)

    source: string
        the source node(symbolic)
    
    dest: string
        the dest node(symbolic)
    
    symbolic_IP_mapping: dict
        the mapping between symbolic integer and real IP address

    Returns:
    --------
    link_failures_dependencies: list[dict]
        the list of dependencies. 
        Each dependency is stored in a dictionary, it's format is {"dependency_tuple": tuple, "dependency_bp_next_node": string, "dependency_insert_acl": string}
    
    sigma3: dict
        sigma3 dependency
        It is stored in a dictionary. It's format is {"sigma3_tuples": list[tuple], "sigma3_summary": list}
    """
    link_failures_dependencies = {}
    acls = []
    index_mapping = {}
    for link in bp_links:
        n1 = link[0]
        n1_IP = symbolic_IP_mapping[n1]

        n2 = link[1]
        n2_IP = symbolic_IP_mapping[n2]

        # find index of impact nodes
        n1_idx = path_nodes.index(n1)
        n2_idx = path_nodes.index(n2)

        # impact node mapping to its next nodes of backup link
        index_mapping[n1_idx] = n2_idx

        dependency_tuple = ('f', n1_IP, 'acl')
        dependency_bp_next_node = n2_IP
        dependency_insert_acl = n1

        dependency = {
            "dependency_tuple": dependency_tuple,
            "dependency_bp_next_node": dependency_bp_next_node,
            "dependency_insert_acl": dependency_insert_acl
        }
        # link_failures_dependencies.append(dependency)
        link_failures_dependencies[n1_idx] = dependency

        acls.append(str(n1))
    
    
    preserving_dependencies = gen_preserving_dependency(index_mapping, symbolic_IP_mapping, path_nodes)
            
    
    source_IP = symbolic_IP_mapping[source]
    dest_IP = symbolic_IP_mapping[dest]

    sigma3_tuples = [('f', '{}'.format(source_IP), '{}')]
    sigma3_summary = ['f', '{}'.format(dest_IP), '{'+", ".join(acls)+'}']

    sigma3 = {
        "sigma3_tuples": sigma3_tuples,
        "sigma3_summary": sigma3_summary
    }
    
    return link_failures_dependencies, preserving_dependencies, sigma3

def gen_preserving_dependency(index_mapping, symbolic_IP_mapping, path_nodes):
    index_nodes = sorted(list(index_mapping.keys()))
    m = 0
    preserving_area = []
    for idx in index_nodes:
        if m < idx:
            preserving_area.append((m, idx))
            m = index_mapping[idx]
        elif m == idx:
            m = index_mapping[idx]
        else:
            idx_bp_next_node = index_mapping[idx]
            if m <= idx_bp_next_node:
                m = idx_bp_next_node

    if m < len(path_nodes) - 1:
        preserving_area.append((m, len(path_nodes)-1))
    
    preserving_dependencies = {}
    for area in preserving_area:
        n1_idx = area[0]
        n1 = path_nodes[n1_idx]
        n1_IP = symbolic_IP_mapping[n1]

        n2_idx = area[1]
        n2 = path_nodes[n2_idx]
        n2_IP = symbolic_IP_mapping[n2]

        dependency_tuple = ('f', n1_IP, 'acl')
        dependency_bp_next_node = n2_IP
        dependency_insert_acl = None

        dependency = {
            "dependency_tuple": dependency_tuple,
            "dependency_bp_next_node": dependency_bp_next_node,
            "dependency_insert_acl": dependency_insert_acl
        }
        preserving_dependencies[n1_idx] = dependency
    
    return preserving_dependencies

def gen_tableau_for_distributed_invariants(file_dir, filename, as_tablename, topo_tablename):
    """
    Script for generating large forwarding table with hosts for distributed invariants

    Parameters:
    ------------
    file_dir: string. 
        The file path for the edges of Rocketfuel topology file.

    filename: string. 
        The file name for the edges of Rocketfuel topology file.

    as_tablename: string. 
        The database table name. This table stores the original Rocketfuel topology.

    topo_tablename: string. 
        The database table name. This table stores the largest component of a Rocketfuel topology and using this component as the topology to add backup links and ACLs.

    Returns:
    --------
    path_nodes: list
        a list of nodes forms the path. symbolic.
    
    source: string
        the source IP address
    
    dest: string
        the destinationi IP address
    
    symbolic_IP_mapping: dict
        the mapping between symbolic integers and real IP addresses.

    """

    func_linkfail.load_topo(file_dir+filename, as_tablename)

    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    cursor = conn.cursor()

    # calculate the largest component of topology graph (here is the whole topology)
    cursor.execute("select * from {}".format(as_tablename))
    all_links = cursor.fetchall()
    print("all links:", len(all_links))
    connected_links, connected_nodes = func_linkfail.get_largest_connected_network(all_links)
    print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

    # Store the largest component into db and use it as the experimental topology
    cursor.execute("drop table if exists {}".format(topo_tablename))
    cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
    cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
    conn.commit()
    conn.close()

    
    # calculate the shortest path, ransomly select source and dest
    path_links, path_nodes, source, dest  = func_linkfail.gen_shortest_path(connected_links)
    # source = 4
    # dest = 1
    # path_nodes = [4, 2, 1]
    # path_links = [(4, 2), (2, 1)]
    print("source", source)
    print("dest", dest)
    print("path nodes", path_nodes)
    print("lenght of path:", len(path_links))

    # # load spanning tree into db (without backup and filters)
    # func_linkfail.load_tree_in_f(path_links, fwd_tablename)

    # # add backup links to spanning tree
    # func_linkfail.add_backup_links_and_filters(path_nodes, fwd_tablename, pick_num)

    IP_tuples, symbolic_IP_mapping = func_linkfail.convert_symbol_to_IP_from_path_nodes(path_nodes, '11.0.0.1')
    print("IP_tuples", IP_tuples)
    print("symbolic_IP_mapping", symbolic_IP_mapping)
    # attributes = {
    #     'n1': 'inet_faure', 
    #     'n2': 'inet_faure',
    #     's':'inet_faure[]',
    #     'condition':'text[]'
    # }
    # func_linkfail.load_table(fwd_tablename, attributes, IP_tuples)

    return IP_tuples, symbolic_IP_mapping[source], symbolic_IP_mapping[dest], path_nodes, symbolic_IP_mapping



if __name__ == '__main__':
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)
    fwd_tablename = "fwd_{}".format(AS_num)

    pick_num = 2

    # gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)
    gen_tableau_for_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, 2)