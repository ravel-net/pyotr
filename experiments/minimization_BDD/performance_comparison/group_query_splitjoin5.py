import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time 
import json
import pyotr_translator_BDD.translator_pyotr_BDD as translator
import util.tableau.tableau as tableau
import util.merge_tuples.merge_tuples_BDD as merge_tuples
from util.variable_closure_algo.closure_group import find_variables, construct_Graph, calculate_tableau
import BDD_managerModule as bddmm
import pyotr_translator_BDD.BDD_manager.encodeCUDD as encodeCUDD

import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

size = 5

with open('../chain_data/chain{}.json'.format(size)) as fc:
    chain_data = json.load(fc)

physical_tuples, phy_self_tuples = tableau.gen_tableau(path=chain_data['physical_path'], overlay=chain_data['overlay_nodes'])
physical = physical_tuples+phy_self_tuples

overlay_tuples, ovr_self_tuples = tableau.gen_tableau(path=chain_data['overlay_path'], overlay=chain_data['overlay_nodes'])

variables = find_variables(physical_tuples+phy_self_tuples)
graph = construct_Graph(variables, physical_tuples+phy_self_tuples)
conns = graph.connectedComponents()
reverse_conns = graph.reverse_connectComponents(conns)
minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))

# for idx, group in enumerate(minimal_tableau):
#     print("group:", idx, "length:", len(group), group)
#     break

cursor.execute("drop table if exists T")
cursor.execute("create table T (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T values(%s, %s, %s)", physical_tuples+phy_self_tuples)
conn.commit()

group = minimal_tableau[0]
print("group:", group) #  [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x4'), ('x4', 'x5'), ('x5', '5'), ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3'), ('x4', 'x4'), ('x5', 'x5')]
# print(overlay_tuples[:2])
"""
R1(1, x1), R2(x1, x2), R3(x2, x3), R4(x3, 22), R5(x1, x1), R6(x2, x2), R7(x3, x3)
R15(1, x1) <- R1(1, x1), R5(x1, x1)
R12(1, x2) <- R15(1, x1), R2(x1, x2)
R16(1, x2) <- R12(1, x2), R6(x2, x2)
R13(1, x3) <- R16(1, x2), R3(x2, x3)
R17(1, x3) <- R13(1, x3), R7(x3, x3)
R14(1, 22) <- R17(1, x3), R4(x3, 22)

"""
# tableau.convert_tableau_to_sql(group, "t_prime", chain_data['overlay_nodes'])

t = physical.copy()
# t.remove(('x9', 'x9', '{}'))
t.remove(('x1', 'x1', '{}'))
t_prime = t
print("len t", len(physical))
print("len t_prime", len(t_prime))

cursor.execute("drop table if exists T_prime")
cursor.execute("create table T_prime (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T_prime values(%s, %s, %s)", t_prime)
conn.commit()

domain = ['1', '2']
bddmm.initialize(len(variables), len(domain))
translator.set_domain(domain)
translator.set_variables(variables)

converted_table = translator.process_condition_on_ctable('T_prime') # convert string version condition to BDD version

sqls = [
    "select 1, t2.n2 as n2 from {tablename} t1, {tablename} t2 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n1 = t2.n2".format(tablename=converted_table),
    "select 1, t2.n2 as n2 from r1_2 t1, {tablename} t2 where t1.n2 = t2.n1".format(tablename=converted_table),
    "select 1, t2.n2 as n2 from r1_3 t1, {tablename} t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2".format(tablename=converted_table),
    "select 1, t2.n2 as n2 from r1_4 t1, {tablename} t2 where t1.n2 = t2.n1".format(tablename=converted_table),
    "select 1, t2.n2 as n2 from r1_5 t1, {tablename} t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2".format(tablename=converted_table),
    "select 1, 2 from r1_6 t1, {tablename} t2 where t1.n2 = t2.n1 and t2.n2 = '2'".format(tablename=converted_table)
]

output_tables = ["r1_2", "r1_3", "r1_4", "r1_5", "r1_6", "r1_7"]

f = open("./running_time.txt", "a")
total_running_time = 0
for idx, out_table in enumerate(output_tables):
    begin = time.time()
    tree = translator.generate_tree(sqls[idx])
    translator.data(tree)
    upd_BDD_time = translator.upd_condition(tree)

    merge_tuples.merge_tuples("output", out_table)
    end = time.time()
    total_running_time += end - begin
    print("\n{}: {}\n".format(out_table, end - begin))
    f.write("{}:{:.4f}\n".format(out_table, end - begin))
f.close()
print("total running time:", total_running_time)

