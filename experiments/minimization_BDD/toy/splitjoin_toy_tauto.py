import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time 
import json
import utils.BDD_translator.translator_pyotr_BDD as translator
import utils.tableau.gen_tableau as tableau
import utils.merge_tuples.merge_tuples_BDD as merge_tuples
from utils.closure_group.closure_overhead import find_variables, construct_Graph, calculate_tableau
import BDD_managerModule as bddmm
import utils.BDD_translator.BDD_manager.encodeCUDD as encodeCUDD

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
print(variables)
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

domain = ['1', '2', '5', '3']
bddmm.initialize(len(variables), len(domain))
translator.set_domain(domain)
translator.set_variables(variables)

converted_table= translator.process_condition_on_ctable('T_prime') # convert string version condition to BDD version


# R12(1, u1) <- R1(1, u1), R2(u1, u1)
sql = "select 1, t2.n2 as n2 from {tablename} t1, {tablename} t2 where t1.n1 = '1' and t1.n2 = t2.n1 and t2.n1 = t2.n2".format(tablename=converted_table)

tree = translator.generate_tree(sql)
translator.data(tree)
translator.upd_condition(tree)

merge_tuples.merge_tuples("output", "r12")

# R13(1, u2) <- R12(1, u1), R3(u1, u2)
sql = "select 1, t2.n2 as n2 from r12 t1, {tablename} t2 where t1.n2 = t2.n1".format(tablename=converted_table)

tree = translator.generate_tree(sql)
translator.data(tree)
translator.upd_condition(tree)

merge_tuples.merge_tuples("output", "r13")



# R14(1, u2) <- R13(1, u2), R4(u2, u2)
sql = "select 1, t2.n2 as n2 from r13 t1, {tablename} t2 where t1.n2 = t2.n1 and t2.n1 = t2.n2".format(tablename=converted_table)

tree = translator.generate_tree(sql)
translator.data(tree)
translator.upd_condition(tree)

merge_tuples.merge_tuples("output", "r14")


# R15(1, 5) <- R14(1, u2), R(u2, 5)
sql = "select 1, 5 from r14 t1, {tablename} t2 where t1.n2 = t2.n1 and t2.n2 = '5'".format(tablename=converted_table)

tree = translator.generate_tree(sql)
translator.data(tree)
translator.upd_condition(tree)

merge_tuples.merge_tuples("output", "r15")

