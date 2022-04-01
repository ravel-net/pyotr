import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)

import time 
import util.chain_generation.gen_chain as gen_chain 
import databaseconfig as cfg
import psycopg2
import util.minimization.minimization_pyotr as minimization_pyotr

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

def exp_minimization_chain(size, rate_summary, rate_loops, runtimes):
    f = open("./data/exp_minimization_{}node.txt".format(size), "a")
    f.write("rate_summary runtime(sec)\n")
    for i in range(runtimes):
        path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate, rate_loops=rate_loops)
        tuples = gen_chain.gen_tableau(path, picked_nodes)

        tablename = "chain{}_{}".format(size, int(rate_summary*10))
        cursor.execute("drop table if exists {}".format(tablename))
        cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
        cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

        conn.commit()

        begin = time.time()
        minimization_pyotr.minimize(tablename=tablename, pos=0, summary=summary_nodes)
        end = time.time()
        print("\nRUNNING TIME:", end - begin)
        f.write("{} {}\n".format(rate_summary, end - begin))

        if end - begin > 5 * 60:
            f.write("{} Over-5-min\n".format(rate_summary))
            f.close()
            print("Over 5 min")
            exit()
    f.close()

if __name__ == "__main__":
    runtimes = 1
    sizes = [15, 20, 25, 30]
    # rate_summary = 0.3
    # rates_summary = [0.8, 0.4, 0.2]
    rates_summary = [0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1]
    # rate_loops = 0.6
    # rates_loops = [[0.05, 0.2, 1], [0.05, 0.15, 1], [0.05, 0.1, 0.8], [0.08, 0.16, 1]]
    rates_loops = [[0.08, 0.09, 0.22, 0.25, 0.5, 0.6, 1, 1]]
    for idx, size in enumerate(sizes):
        rate_loops = rates_loops[idx]
        for index, rate in enumerate(rates_summary):
            exp_minimization_chain(size, rate, rate_loops[index], runtimes)
            # break
        break