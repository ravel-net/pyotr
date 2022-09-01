import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import BDD_managerModule as bddmm
from tqdm import tqdm
import encodeCUDD as encodeCUDD
import psycopg2 
import databaseconfig as cfg

# conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

# BDD_managerModule.initialize(3)

# tauto = "^(&($(4,2),$(2,3)),^(&(~(2),$(2,3)),^($(4,3),^(~(3),^(&(~(4),$(2,3)),^(&(~(4),$(2,3)),^(&(~(2),$(3,2)),^(~(2),^(&(~(2),$(2,3)),^(&(~(2),$(2,3)),^(&(~(3),$(3,2)),~(3))))))))))))"
# tauto_idx = BDD_managerModule.str_to_BDD(tauto)
# print("tauto:", BDD_managerModule.evaluate(tauto_idx))

# contrd = "&(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),&(~(3),3))"
# contrd_idx = BDD_managerModule.str_to_BDD(contrd)
# print("contrd:", BDD_managerModule.evaluate(contrd_idx))

# sat = "^(&(^(^(^(^(~(2),^(&(~(2),~(4)),^(&(~(4),~(3)),^(~(4),~(3))))),^(~(3),^(~(4),^(~(2),^(&(~(4),&(~(3),~(2))),^(~(2),^(&(~(2),~(4)),^(&(~(4),~(2)),&(~(3),~(2)))))))))),^(~(3),^(~(4),~(2)))),^(~(3),^(~(4),^(&(~(3),~(2)),^(&(~(4),~(2)),^(~(2),~(2))))))),&($(2,3),3)),^(&($(4,3),3),^(3,3)))"
# sat_idx = BDD_managerModule.str_to_BDD(sat)

# OR_idx = BDD_managerModule.operate_BDDs(tauto_idx, sat_idx, '^')
# res = BDD_managerModule.evaluate(OR_idx)
# print("res:", res)

# And_idx = BDD_managerModule.operate_BDDs(contrd_idx, sat_idx, '&')
# print(BDD_managerModule.evaluate(And_idx))

# sql = "select t1_n1 || ' == ' || '1', t1_n2 || ' == ' || t2_n1, t1_condition, t2_condition from output;"

# cursor = conn.cursor()



# cursor.execute(sql)
# count_row = cursor.rowcount

# for i in tqdm(range(count_row)):
#     row = cursor.fetchone()
#     condition = 'And({})'.format(", ".join(row[:-2]))
#     print(condition)
#     encoded_condition, variable_array = encodeCUDD.convertToCUDD(condition, domain, variables_list)
#     print(encoded_condition)
#     bdd_idx = BDD_managerModule.str_to_BDD(encoded_condition)
#     print("bdd_c_idx:", bdd_idx)

domain = ['1', '2']
variables_list = ['d2']
bddmm.initialize(1, len(domain))

condition1 = "Or(And(d2 == 2, And(4 == 4, Or(d2 == 1, d2 == 2))), And(d2 == 2, And(4 == 4, Or(d2 == 1, d2 == 2))))"
condition2 = "d2 == 1"
# print(condition)
encoded_condition1, variable_array1 = encodeCUDD.convertToCUDD(condition1, domain, variables_list)
encoded_condition2, variable_array2 = encodeCUDD.convertToCUDD(condition2, domain, variables_list)
print(encoded_condition1)
print(encoded_condition2)

bdd_idx1 = bddmm.str_to_BDD(encoded_condition1)
bdd_idx2 = bddmm.str_to_BDD(encoded_condition2)

print("bdd_idx1", bdd_idx1)
print("bdd_idx2", bdd_idx2)
res1 = bddmm.is_implication(bdd_idx1, bdd_idx2)
res2 = bddmm.is_implication(bdd_idx2, bdd_idx1)

print('res1', res1)
print('res2', res2)
print("res", res1 and res2)

