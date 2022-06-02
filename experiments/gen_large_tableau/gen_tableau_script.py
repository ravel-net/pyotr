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
import experiments.gen_large_tableau.func_gen_tableau_link_failure as func_linkfail

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

    # calculate the spanning tree, return tree links and its root
    path_links, path_nodes, source, dest  = func_linkfail.gen_hamiltonian_path(connected_links)
    print("source", source)
    print("dest", dest)
    print("hamiltonian path:", len(path_links))

    # load spanning tree into db (without backup and filters)
    func_linkfail.load_tree_in_f(path_links, fwd_tablename)

    # add backup links to spanning tree
    func_linkfail.add_backup_links_and_filters(dest, path_nodes, topo_tablename, fwd_tablename, pick_num)

if __name__ == '__main__':
    file_dir  = '/../../topo/ISP_topo/'
    filename = "4755_edges.txt"

    as_tablename = 'as_4755'
    topo_tablename = "topo_4755"
    fwd_tablename = "fwd_4755"

    pick_num = 2

    gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)