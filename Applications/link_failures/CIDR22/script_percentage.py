"""
This python script is used to generate the c-table-based F table and R table
run in different rates of adding backup links
"""

import gen_forward_table_with_backup as Ftable
from rtable import Rtable
import psycopg2
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

as_numbers = [4755, 3356, 7018, 2914] #, 2914
# as_numbers = [3356] #, 2914
# rates = [0.2, 0.6]
rates = [0.2]

for r in rates:
    # generate f table
    print("In rate: ", r)
    # generate f table
    for number in as_numbers:
        print("\nDoing AS number: ", number)
        f_table = "f_{}".format(number)
        graph_table = "topo_{}".format(number)
        file_dir = "/topo/{}_edges.txt".format(number)

        # generator = Main(f_table=f_table, graph_table=graph_table)

        # load topo
        Ftable.load_topo(file_dir, graph_table)

        cursor.execute("select * from {}".format(graph_table))
        connected_links, connected_nodes = Ftable.get_largest_connected_network(cursor.fetchall())

        topo_tablename = "topo_{}".format(number)
        fwd_tablename = "fwd_{}".format(number)
        cursor.execute("drop table if exists {}".format(topo_tablename))
        cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
        cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
        conn.commit()

        spanning_links, root = Ftable.gen_spanning_tree(connected_links)
        print("root", root)
        print("spanning tree links:", len(spanning_links))
        
        Ftable.load_tree_in_f(spanning_links, fwd_tablename)
        print("Done: load_tree_in_f")

        Ftable.add_link(root, topo_tablename, fwd_tablename, 0.6)
        print("Done: add_link")

        Ftable.add_filter(connected_nodes, root, 0.5, fwd_tablename)
        print("Done: add_filter")
        
        print("root: ", root)

        # generate R table 
        print("Generating R_{}".format(number))
        r_gene = Rtable(dbname=cfg.postgres["db"], f_table=f_table, as_number=number)

        r_gene.r1()
        count = r_gene.rn()

        r_gene.union(count=count)
        print("Done.")


