import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time 
import json
import pyotr_translator.translator_pyotr as translator
import util.tableau.tableau as tableau
import util.merge_tuples.merge_tuples_tautology as merge_tuples_tautology
from util.variable_closure_algo.closure_overhead import find_variables, construct_Graph, calculate_tableau
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

size = 50

with open('../../variable_closure/data/chain{}.json'.format(size)) as fc:
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
print("group:", group) #  [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', '22'), ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3')]
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
tableau.convert_tableau_to_sql(group, "t_prime", chain_data['overlay_nodes'])

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

f = open("./chain50_complete_split_tauto.txt", "a")

# R15(1, x1) <- R1(1, x1), R5(x1, x1)
sql = "select 1, t2.n2 as n2 from T_prime t1, T_prime t2 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n1 = t2.n2"
# sql = "select * from T t1, T t2 where t1.n1 = '1' and t1.n2 = t2.n1"
f.write("R15 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

variables_list = [node for node in chain_data['physical_nodes'] if not node.isdigit()]
r15_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r15", chain_data['overlay_nodes'], variables_list)
r15_end = time.time()
print("Total time: ", r15_end-r15_begin)

f.write("data condition #input_contrd contradiction #input_redun redundancy join merge output_rows\n")
f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r15_end-r15_begin, rows))

# R12(1, x2) <- R15(1, x), R2(x1, x2)
sql = "select 1, t2.n2 as n2 from r15 t1, T_prime t2 where t1.n2 = t2.n1"
f.write("R12 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r12_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r12", chain_data['overlay_nodes'], variables_list)
r12_end = time.time()
print("Total time: ", r12_end-r12_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r12_end-r12_begin, rows))


# R16(1, x2) <- R12(1, x2), R6(x2, x2)
sql = "select 1, t2.n2 as n2 from r12 t1, T_prime t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2"
f.write("R16 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r16_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r16", chain_data['overlay_nodes'], variables_list)
r16_end = time.time()
print("Total time: ", r16_end-r16_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r16_end-r16_begin, rows))

# R13(1, x3) <- R16(1, x2), R3(x2, x3)
sql = "select 1, t2.n2 as n2 from r16 t1, T_prime t2 where t1.n2 = t2.n1"
f.write("R13 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r13_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r13", chain_data['overlay_nodes'], variables_list)
r13_end = time.time()
print("Total time: ", r13_end-r13_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r13_end-r13_begin, rows))

# R17(1, x3) <- R13(1, x3), R7(x3, x3)
sql = "select 1, t2.n2 as n2 from r13 t1, T_prime t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2"
f.write("R17 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r17_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r17", chain_data['overlay_nodes'], variables_list)
r17_end = time.time()
print("Total time: ", r17_end-r17_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r17_end-r17_begin, rows))

# R14(1, 22) <- R17(1, x3), R4(x3, 22)
sql = "select 1, 22 from r17 t1, T_prime t2 where t1.n2 = t2.n1 and t2.n2 = '22'"
f.write("R14 sql: {}\n".format(sql))

tree = translator.generate_tree(sql)
data_time = translator.data(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()
print("Contradiciton time: ", nor_time["contradiction"][1])
print("Redundancy time: ", nor_time["redundancy"][1])
print("Total time: ", data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1])

r14_begin = time.time()
rows = merge_tuples_tautology.merge_tuples("output", "r14", chain_data['overlay_nodes'], variables_list)
r14_end = time.time()
print("Total time: ", r14_end-r14_begin)

f.write("{} {} {} {} {} {} {} {} {}\n".format(data_time, upd_time, nor_time["contradiction"][0], nor_time["contradiction"][1], nor_time["redundancy"][0], \
    nor_time["redundancy"][1], \
    data_time+upd_time+nor_time["contradiction"][1]+nor_time["redundancy"][1], r14_end-r14_begin, rows))
