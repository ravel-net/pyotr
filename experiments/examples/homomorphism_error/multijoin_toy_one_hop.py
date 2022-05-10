import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
filename = join(root, 'pyotr_translator')
sys.path.append(filename)
filename = join(root, 'util')
sys.path.append(filename)

import translator_pyotr as translator
import tableau.tableau as tableau
import check_tautology.check_tautology as check_tautology
from variable_closure_algo.closure_group import find_variables, construct_Graph, calculate_tableau
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

physical_nodes = ['1', 'u1', 'u2', '2']
overlay_nodes = ['1', '2']
physical_path = [('1', 'u1'), ('u1', 'u2'), ('u2', '2')]
overlay_path = [('1', '2')]

physical_tuples, phy_self_tuples = tableau.gen_tableau(path=physical_path, overlay=overlay_nodes)
physical = physical_tuples+phy_self_tuples
print(physical) 
# physical = [('1', 'u1', '{}'), ('u1', 'u2', '{}'), ('u2', '5', '{}'), ('5', '2', '{}'), ('2', 'v1', '{}'), ('v1', 'v2', '{}'), \
# ('v2', '3', '{}'), ('1', '1', '{}'), ('u1', 'u1', '{}'), ('u2', 'u2', '{}'), ('2', '2', '{}'), ('v1', 'v1', '{}'), ('v2', 'v2', '{}')]

# overlay_tuples, ovr_self_tuples = tableau.gen_tableau(path=chain_data['overlay_path'], overlay=chain_data['overlay_nodes'])

variables = find_variables(physical_tuples+phy_self_tuples)
graph = construct_Graph(variables, physical_tuples+phy_self_tuples)
conns = graph.connectedComponents()
reverse_conns = graph.reverse_connectComponents(conns)
minimal_tableau = calculate_tableau(physical_tuples+phy_self_tuples, reverse_conns, len(conns))

# for idx, group in enumerate(minimal_tableau):
#     print("group:", idx, "length:", len(group), group)
#     break

cursor.execute("drop table if exists T_oh")
cursor.execute("create table T_oh (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T_oh values(%s, %s, %s)", physical)
conn.commit()

group = minimal_tableau[0]
print("group:", group) #  [('1', 'u1'), ('u1', 'u2'), ('u2', '2'), ('u1', 'u1'), ('u2', 'u2')]


t = physical.copy()
t.remove(('u1', 'u1', '{}'))
t_prime = t
print("len t", len(physical))
print("len t_prime", len(t_prime))

cursor.execute("drop table if exists T_prime_oh")
cursor.execute("create table T_prime_oh (n1 int4_faure, n2 int4_faure, condition text[])")
cursor.executemany("insert into T_prime_oh values(%s, %s, %s)", t_prime)
conn.commit()

sql = tableau.convert_tableau_to_sql(group, "T_prime_oh", overlay_nodes)

tree = translator.generate_tree(sql)

data_time = translator.data(tree)
# tree_to_str(tree)
upd_time = translator.upd_condition(tree)
nor_time = translator.normalization()

print("Data execution time: ", data_time)
print("Condition execution time: ", upd_time)
print("Normalization time: ", nor_time["contradiction"][1])
print("Total running time(3 steps): ", data_time + upd_time + nor_time["contradiction"][1])


union_conditions, union_time = check_tautology.get_union_conditions('output', 'Int')
print("Union time: ", union_time)

variables_list = [node for node in physical_nodes if not node.isdigit()]
domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes, variables_list, 'Int')

print("Domain time: ", domain_time)

ans, z3_time, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)

print("Answer: ", ans, "model: ", model)
print("z3 time: ", z3_time)
print("Total running time(checking tautology): ", union_time+domain_time+z3_time)
