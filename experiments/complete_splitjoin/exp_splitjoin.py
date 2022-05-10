from itertools import chain
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'new_experiments', 'support_int')
sys.path.append(filename)
filename = join(root, 'new_experiments', 'util')
sys.path.append(filename)

import time 
from util.reorder_tableau import gen_splitjoin_sql, reorder_closure_group
from gen_tableau import gen_chain_even_group, gen_tableau
from closure_group import find_variables, construct_Graph, calculate_tableau
import support_int.translator_int as translator
import translator_naive as translator_naive
import splitjoin.merge_tuples_tautology as merge_tuples_tautology
import splitjoin.merge_tuples as merge_tuples
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

def group_query_splitjoin_tauto(size, runtimes, chain_topology, datatype):
    f = open("./data/chain{}_splitjoin_tauto.txt".format(size), "a")
    f.write("rate_summary runtime(sec)\n")
    for i in range(runtimes):
        # path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate, rate_loops=rate_loops)
        
        # physical_path, physical_nodes, overlay_path, overlay_nodes = gen_chain_even_group(size=size, rate=rate)

        physical_tuples, phy_self_tuples = gen_tableau(path= chain_topology['physical_path'], overlay=chain_topology['overlay_nodes'])
        physical = physical_tuples+phy_self_tuples

        tablename = "chain{}".format(size)
        cursor.execute("drop table if exists {}".format(tablename))
        cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
        cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), physical)

        t = physical.copy()
        t.remove(('x1', 'x1', '{}'))
        t_prime = t
        print("current: ", physical)
        print("len t", len(physical))
        print("len t_prime", len(t_prime))

        cursor.execute("drop table if exists T_prime")
        cursor.execute("create table T_prime (n1 int4_faure, n2 int4_faure, condition text[])")
        cursor.executemany("insert into T_prime values(%s, %s, %s)", t_prime)
        conn.commit()

        variables = find_variables(physical_tuples+phy_self_tuples)
        graph = construct_Graph(variables, physical_tuples+phy_self_tuples)
        conns = graph.connectedComponents()
        reverse_conns = graph.reverse_connectComponents(conns)
        minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))

        group = minimal_tableau[0]

        ordered_group = reorder_closure_group(group)
        sqls, output_tables = gen_splitjoin_sql(ordered_group, tablename, chain_topology['overlay_nodes'])

        total_running_time = 0
        f.write("data condition #input_contrd contradiction #input_redun redundancy merge total_time output_rows\n")
        for idx, sql in enumerate(sqls):
            print(sql)
            try:
                tree = translator.generate_tree(sql)
                data_time = translator.data(tree)
                upd_time = translator.upd_condition(tree, datatype)
                nor_time = translator.normalization()
                merge_begin = time.time()
                rows = merge_tuples_tautology.merge_tuples("output", output_tables[idx], chain_topology['overlay_nodes'], variables)
                merge_end = time.time()
                # print("Total time: ", merge_end-merge_begin)

                total_running_time += data_time + upd_time + nor_time["contradiction"][1] + nor_time["redundancy"][1] + (merge_end - merge_begin)
                f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
                    nor_time["redundancy"][1],  merge_end-merge_begin, total_running_time, rows))
            except Exception as e:
                f.write("{}\n".format(e))
                f.close()
                break
    f.close()

def group_query_splitjoin(size, runtimes, chain_topology, datatype):
    f = open("./data/chain{}_splitjoin.txt".format(size), "a")
    f.write("rate_summary runtime(sec)\n")
    for i in range(runtimes):
        # path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate, rate_loops=rate_loops)
        
        # physical_path, physical_nodes, overlay_path, overlay_nodes = gen_chain_even_group(size=size, rate=rate)

        physical_tuples, phy_self_tuples = gen_tableau(path= chain_topology['physical_path'], overlay=chain_topology['overlay_nodes'])
        physical = physical_tuples+phy_self_tuples

        tablename = "chain{}".format(size)
        cursor.execute("drop table if exists {}".format(tablename))
        cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
        cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), physical)

        t = physical.copy()
        t.remove(('x1', 'x1', '{}'))
        t_prime = t
        print("current: ", physical)
        print("len t", len(physical))
        print("len t_prime", len(t_prime))

        cursor.execute("drop table if exists T_prime")
        cursor.execute("create table T_prime (n1 int4_faure, n2 int4_faure, condition text[])")
        cursor.executemany("insert into T_prime values(%s, %s, %s)", t_prime)
        conn.commit()

        variables = find_variables(physical_tuples+phy_self_tuples)
        graph = construct_Graph(variables, physical_tuples+phy_self_tuples)
        conns = graph.connectedComponents()
        reverse_conns = graph.reverse_connectComponents(conns)
        minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))

        group = minimal_tableau[0]

        ordered_group = reorder_closure_group(group)
        sqls, output_tables = gen_splitjoin_sql(ordered_group, tablename, chain_topology['overlay_nodes'])

        total_running_time = 0
        f.write("data condition #input_contrd contradiction merge total_time output_rows\n")
        for idx, sql in enumerate(sqls):
            print(sql)
            try:
                tree = translator_naive.generate_tree(sql)
                data_time = translator_naive.data(tree)
                upd_time = translator_naive.upd_condition(tree, datatype)
                nor_time = translator_naive.normalization()
                merge_begin = time.time()
                rows = merge_tuples.merge_tuples("output", output_tables[idx])
                merge_end = time.time()
                # print("Total time: ", merge_end-merge_begin)

                total_running_time += data_time + upd_time + nor_time["contradiction"][1] + (merge_end - merge_begin)
                f.write("{} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], \
                    merge_end-merge_begin, total_running_time, rows))
            except Exception as e:
                f.write("{}\n".format(e))
                f.close()
                break
    f.close()

if __name__ == "__main__":
    runtimes = 1
    sizes = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    rate = 0.3
    for idx, size in enumerate(sizes):
        physical_path, physical_nodes, overlay_path, overlay_nodes = gen_chain_even_group(size=size, rate=rate)
        chain_topology = {}
        chain_topology["physical_path"] = physical_path
        chain_topology["physical_nodes"] = physical_nodes
        chain_topology["overlay_path"] = overlay_path
        chain_topology["overlay_nodes"] = overlay_nodes
        group_query_splitjoin_tauto(size, runtimes, chain_topology, "int4_faure")
        # group_query_splitjoin(size, runtimes, chain_topology)