"""
BDD conditin version 
"""
import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)


import databaseconfig as cfg
import psycopg2
import BDD_managerModule as bddmm
import util.minimization.minimization_pyotr_BDD as minimization_pyotr_BDD
import pyotr_translator_BDD.translator_pyotr_BDD as translator

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()


nf_tableau = [
    ('1', '2', '{}'),
    ('2', 'y1', '{}'),
    ('y1', 'y2', '{}'),
    ('y2', '2', '{}'),
    ('2', '2', '{}'),
    ('2', '3', '{}'),
    ('3', 'z2', '{}'),
    ('z2', '3', '{}'),
    ('3', '3', '{}')
]

summary = ['1', '2', '3']
variables_list = ['y1', 'y2', 'z2']

cursor.execute("drop table if exists nf_t")
cursor.execute("create table nf_t (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into nf_t values(%s, %s, %s)", nf_tableau)
conn.commit()

bddmm.initialize(len(variables_list), len(summary))
translator.set_domain(summary)
translator.set_variables(variables_list)
converted_table = translator.process_condition_on_ctable("nf_t")

minimization_pyotr_BDD.minimize(tablename=converted_table, pos=0, summary=summary)

# size = 15
# # rate_summary = 0.3
# rates_summary = [0.8, 0.6, 0.2]
# # rate_loops = 0.6
# rates_loops = [0.05, 0.2, 1]

# f = open("./data/exp_minimization_{}node.txt".format(size), "a")
# f.write("rate_var runtime(sec)\n")
# for idx, rate in enumerate(rates_summary):
#     path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate, rate_loops=rates_loops[idx])
#     tuples = gen_chain.gen_tableau(path, picked_nodes)
#     print(tuples)

#     tablename = "chain{}_{}".format(size, int(rate*10))
#     cursor.execute("drop table if exists {}".format(tablename))
#     cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
#     cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

#     conn.commit()

#     begin = time.time()
#     minimization_pyotr.minimize(tablename=tablename, pos=0, summary=summary_nodes)
#     end = time.time()
#     print("\n RUNNING TIME:", end - begin)
#     f.write("{} {}\n".format(rate, end - begin))
#     break
# f.close()
