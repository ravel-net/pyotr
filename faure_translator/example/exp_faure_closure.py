import sys
import json
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'util')
sys.path.append(filename)
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
filename = join(root, 'faure_translator')
sys.path.append(filename)

import tableau as tableau
import DFS
import psycopg2
import databaseconfig as cfg
from closure_overhead import find_variables, construct_Graph, calculate_tableau
from translator import generate_tree, data, upd_condition, normalization
# import logging
# logging.basicConfig(filename='data/exp_faure_closure.log', level=logging.DEBUG)

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

sizes = [100]#, 1000, 10000]
rate = 0.2

# logging.info("+++++++++++++++++++++++++++++++++++Running Date:{}+++++++++++++++++++++++++++++++++++".format(time.asctime( time.localtime(time.time()) )))


for size in sizes:
    f = open("data/exp_faure_close_data{}.txt".format(size), "a")
    row = "#nodes group length data_time condition_time contradiction_time #input_contradiction redundacy_time #input z3_time total_time \n"
    f.write(row)
    
    
    # logging.info("Size of chain: {}".format(size))
    # physical_path, physical_nodes, overlay_path, overlay_nodes = tableau.gen_large_chain(size=size, rate=rate)
    
    with open('data/chain{}.json'.format(size)) as fc:
        chain_data = json.load(fc)
    
    physical_tuples, phy_self_tuples = tableau.gen_tableau(path=chain_data['physical_path'], overlay=chain_data['overlay_nodes'])

    cursor.execute("drop table if exists Tpt{}".format(size))
    cursor.execute("create table Tpt{} (n1 text, n2 text, condition text[])".format(size))
    cursor.executemany("insert into Tpt{} values(%s, %s, %s)".format(size), physical_tuples+phy_self_tuples)
    conn.commit()

    overlay_tuples, olay_self_tuples = tableau.gen_tableau(path=chain_data['overlay_path'], overlay=chain_data['overlay_nodes'])

    cursor.execute("drop table if exists Tvt{}".format(size))
    cursor.execute("create table Tvt{} (n1 text, n2 text, condition text[])".format(size))
    cursor.executemany("insert into Tvt{} values(%s, %s, %s)".format(size), overlay_tuples+olay_self_tuples)
    conn.commit()

    variables = find_variables(chain_data['physical_nodes'])
    graph = construct_Graph(variables, physical_tuples)
    conns = graph.connectedComponents()
    reverse_conns = graph.reverse_connectComponents(conns)
    minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))

    time_groups = 0
    for idx, group in enumerate(minimal_tableau):
        print("Size {}, Group {}, length {}: {}".format(size, idx+1, len(group), group))
        row = "{} {} {} ".format(size, idx+1, len(group))
        # logging.info("Group {}, length {}: {}".format(idx+1, len(group), group))

        sql = tableau.convert_tableau_to_sql(group, "Tvt{}".format(size), chain_data['overlay_nodes'])
        tree = generate_tree(sql)
        # logging.info("SQL for group {} on size {}: {}".format(idx+1, size, sql))
        count_data_time = 0
        count_upd_time = 0
        count_contrad_time = 0
        count_redun_time = 0
        tuples_contrad = 0
        tuples_redun = 0
        for i in range(10):
            data_time = data(tree)
            count_data_time += data_time

            upd_time = upd_condition(tree)
            count_upd_time += upd_time

            nor_time = normalization()
            count_contrad_time += nor_time["contradiction"][1]
            tuples_contrad = nor_time["contradiction"][0]
            count_redun_time += nor_time["redundancy"][1]
            tuples_redun = nor_time["redundancy"][0]
        total_time = count_data_time/10 + count_upd_time/10 + count_contrad_time/10 + count_redun_time/10
        z3_time = count_contrad_time/10+count_redun_time/10
        time_groups += total_time
        row += " {} {} {} {} ".format(count_data_time/10, count_upd_time/10, count_contrad_time/10, tuples_contrad)
        row += " {} {} {} {} \n".format(count_redun_time/10, tuples_redun, z3_time, total_time)
        f.write(row)
        # logging.warning("Execution time on sql for group {} on size {}: {}".format(idx+1, size, total_time))
    f.write("Total groups running time: {}\n".format(time_groups))
    f.close()
    break
    # logging.warning("Total execution time on size {}: {}".format(size, time_groups))
    # logging.info("-------------------------------\n")
