import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'support_int')
sys.path.append(filename)

import time 
import json
import translator_int as translator
import gen_tableau as tableau
import splitjoin.merge_tuples_tautology as merge_tuples_tautology
from closure_overhead import find_variables, construct_Graph, calculate_tableau
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

# size = 50

# with open('../variable_closure/data/chain{}.json'.format(size)) as fc:
#     chain_data = json.load(fc)
physical_nodes = ['1', 'u1', 'u2', '2', 'v1', 'v2', '3']
overlay_nodes = ['1', '2', '3']
physical_path = [('1', 'u1'), ('u1', 'u2'), ('u2', '2'), ('2', 'v1'), ('v1', 'v2'), ('v2', '3')]
overlay_path = [('1', '2'), ('2', '3')]

physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)
physical = physical_tuples+phy_self_tuples
print(physical) 
# physical = [('1', 'u1', '{}'), ('u1', 'u2', '{}'), ('u2', '5', '{}'), ('5', '2', '{}'), ('2', 'v1', '{}'), ('v1', 'v2', '{}'), ('v2', '3', '{}'), ('1', '1', '{}'), ('u1', 'u1', '{}'), ('u2', 'u2', '{}'), ('2', '2', '{}'), ('v1', 'v1', '{}'), ('v2', 'v2', '{}')]

# overlay_tuples, ovr_self_tuples = tableau.gen_tableau(path=overlay_path, overlay=overlay_nodes)

variables = find_variables(physical)
graph = construct_Graph(variables, physical)
conns = graph.connectedComponents()
reverse_conns = graph.reverse_connectComponents(conns)
minimal_tableau = calculate_tableau(physical, reverse_conns, len(conns))

# for idx, group in enumerate(minimal_tableau):
#     print("group:", idx, "length:", len(group), group)
#     break

cursor.execute("drop table if exists T")
cursor.execute("create table T (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T values(%s, %s, %s)", physical)
conn.commit()

group = minimal_tableau[0]
# sql = tableau.convert_tableau_to_sql(group, 't_prime', overlay_nodes)
# print(sql)
print("group:", group)  # [('1', 'u1'), ('u1', 'u2'), ('u2', '5'), ('u1', 'u1'), ('u2', 'u2')]
# R1(1, u1), R2(u1, u2), R3(u2, 5), R4(u1, u1), R5(u2, u2)
"""
R14(1, u1) <- R1(1, u1), R4(u1, u1)
R12(1, u2) <- R14(1, u1), R2(u1, u2)
R15(1, u2) <- R12(1, u2), R5(u2, u2)
R13(1, 5) <- R15(1, u2), R3(u2, 5)
"""

t = physical.copy()
# t.remove(('x9', 'x9', '{}'))
t.remove(('u1', 'u1', '{}'))
t_prime = t
print("len t", len(physical))
print("len t_prime", len(t_prime))

cursor.execute("drop table if exists T_prime")
cursor.execute("create table T_prime (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T_prime values(%s, %s, %s)", t_prime)
conn.commit()

f = open("./split_toy_tauto.txt", "a")

# R14(1, u1) <- R1(1, u1), R4(u1, u1)
sql = "select 1, t2.n2 as n2 from T_prime t1, T_prime t2 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n1 = t2.n2"
# sql = "select * from T t1, T t2 where t1.n1 = '1' and t1.n2 = t2.n1"
f.write("R14 sql: {}\n".format(sql))


tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

variables_list = [node for node in physical_nodes if not node.isdigit()]
r14_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r14", overlay_nodes, variables_list)
r14_end = time.time()
print("Total time: ", r14_end-r14_begin)

f.write("data condition #input_contrd contradiction #input_redun redundancy join merge output_rows\n")
f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r14_end-r14_begin, rows))

# R12(1, u2) <- R14(1, u1), R2(u1, u2)
sql = "select 1, t2.n2 as n2 from r14 t1, T_prime t2 where t1.n2 = t2.n1"
f.write("R12 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r12_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r12", overlay_nodes, variables_list)
r12_end = time.time()
print("Total time: ", r12_end-r12_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r12_end-r12_begin, rows))


# R15(1, u2) <- R12(1, u2), R5(u2, u2)
sql = "select 1, t2.n2 as n2 from r12 t1, T_prime t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2"
f.write("R15 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r15_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r15", overlay_nodes, variables_list)
r15_end = time.time()
print("Total time: ", r15_end-r15_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r15_end-r15_begin, rows))

# R13(1, 5) <- R15(1, u2), R(u2, 5)
sql = "select 1, 5 from r15 t1, T_prime t2 where t1.n2 = t2.n1 and t2.n2 = '5'"
f.write("R13 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r13_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r13", overlay_nodes, variables_list)
r13_end = time.time()
print("Total time: ", r13_end-r13_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r13_end-r13_begin, rows))
