import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

import BDD_managerModule
from tqdm import tqdm
import encodeCUDD as encodeCUDD
import psycopg2 
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

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

sql = "select t1_n1 || ' == ' || '1', t1_n2 || ' == ' || t2_n1, t1_condition, t2_condition from output;"

cursor = conn.cursor()

domain = ['1', '2']
BDD_managerModule.initialize(3)

cursor.execute(sql)
count_row = cursor.rowcount

# f1 = open('../pure_BDD_manager/condition.txt', 'w')
# f2 = open('../pure_BDD_manager/encd_condition.txt', 'w')
for i in tqdm(range(count_row)):
    row = cursor.fetchone()
    condition = 'And({})'.format(", ".join(row[:-2]))
    print(condition)
    encoded_condition, variable_array = encodeCUDD.convertToCUDD(condition, domain)
    print(encoded_condition)
    # f1.write("{}\n".format(condition))
    # f2.write("{}\n".format(encoded_condition))
    bdd_idx = BDD_managerModule.str_to_BDD(encoded_condition)
    print("bdd_c_idx:", bdd_idx)
# f1.close()
# f2.close()

