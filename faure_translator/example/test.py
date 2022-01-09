import sys
import pprint
import time
import json
from tqdm import tqdm
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'util')
sys.path.append(filename)
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
filename = join(root, 'faure_translator')
sys.path.append(filename)

import psycopg2
import tableau as tableau
import databaseconfig as cfg
from translator import generate_tree, data, upd_condition, normalization


conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

sizes = [15]#, 1000, 10000]
rate = 0.2

# logging.info("+++++++++++++++++++++++++++++++++++Running Date:{}+++++++++++++++++++++++++++++++++++".format(time.asctime( time.localtime(time.time()) )))


for size in sizes:
    print(size)
    row = "{} ".format(size)
    physical_path, physical_nodes, overlay_path, overlay_nodes = tableau.gen_large_chain(size=size, rate=rate)
    physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)

    overlay_tuples, olay_self_tuples = tableau.gen_tableau(path=overlay_path, overlay=overlay_nodes)

    print("overlay")
    cursor.execute("drop table if exists Tvt{}".format(size))
    cursor.execute("create table Tvt{} (n1 text, n2 text, condition text[])".format(size))
    cursor.executemany("insert into Tvt{} values(%s, %s, %s)".format(size), overlay_tuples+olay_self_tuples)
    conn.commit()

    print(overlay_tuples)
    sql = tableau.convert_tableau_to_sql(physical_tuples+phy_self_tuples, "Tvt{}".format(size), overlay_nodes)
    # print(sql)
    tree = generate_tree(sql)
    data_time = data(tree)
    upd_time = upd_condition(tree)
    nor_time = normalization()

