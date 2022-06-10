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
    func_linkfail.add_backup_links_and_filters(path_nodes, fwd_tablename, pick_num)

    IP_tuples, symbolic_IP_mapping = func_linkfail.convert_symbol_to_IP(fwd_tablename)
    attributes = {
        'n1': 'inet_faure', 
        'n2': 'inet_faure',
        's':'inet_faure[]',
        'condition':'text[]'
    }
    func_linkfail.load_table(fwd_tablename, attributes, IP_tuples)

    return IP_tuples, symbolic_IP_mapping[source], symbolic_IP_mapping[dest]

if __name__ == '__main__':
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)
    fwd_tablename = "fwd_{}".format(AS_num)

    pick_num = 2

    gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)