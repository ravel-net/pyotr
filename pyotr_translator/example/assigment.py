import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
filename = join(root, 'new_experiments')
sys.path.append(filename)
filename = join(root, 'new_experiments', 'support_int')
sys.path.append(filename)

import time 
import translator as translator
import gen_tableau as tableau
import databaseconfig as cfg
# import check_tautology as check_tautology
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database="faure", user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

t = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('1', '1', '{}'), ('y1', 'y1', '{}'), ('y2', 'y2', '{}')]
t_prime = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('1', '1', '{}'), ('y2', 'y2', '{}')]
group = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('y1', 'y1', '{}'), ('y2', 'y2', '{}')]
# t_prime = [('1', 'z1', '{}'), ('z1', 'z2', '{}'), ('z2', '2', '{}'), ('z2', 'z2', '{}')]
# t = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('1', '1', '{}'), ('y1', 'y1', '{}'), ('y2', 'y2', '{}')]
# t_prime = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('y2', 'y2', '{}')]
# y1_closure = [('1', 'y1', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'),('y1', 'y1', '{}'), ('y2', 'y2', '{}')]

cursor.execute("drop table if exists t")
cursor.execute("create table t(n1 text, n2 text, condition text[])")
cursor.executemany("insert into t values(%s, %s, %s)", t)

cursor.execute("drop table if exists t_prime")
cursor.execute("create table t_prime(n1 text, n2 text, condition text[])")
cursor.executemany("insert into t_prime values(%s, %s, %s)", t_prime)
conn.commit()

sql = tableau.convert_tableau_to_sql(group, "t_prime", ['1', '2'])
# sql = "select 1, 2 from t_prime t0, t_prime t1, t_prime t2, t_prime t3, t_prime t4 where t0.n1 = '1' and t0.n2 = t1.n1 and t2.n2 = '2' and t1.n2 = t2.n1 and t3.n1 = t3.n2 and t1.n1 = t3.n2 and t4.n1 = t4.n2 and t2.n1 = t4.n2"
# sql = "select 1, 2 from t_prime t0, t_prime t1, t_prime t2, t_prime t3, t_prime t4, t_prime t5 where t0.n1 = '1' and t0.n2 = t1.n1 and t2.n2 = '2' and t1.n2 = t2.n1 and t4.n1 = t4.n2 and t1.n1 = t4.n2 and t5.n1 = t5.n2 and t2.n1 = t5.n2"
# sql = "select 1, 2 from t_prime t0, t_prime t1, t_prime t2, t_prime t3, t_prime t4 where t0.n1 = '1' and t0.n2 = t1.n1 and t2.n2 = '2' and t1.n2 = t2.n1 and t3.n1 = t3.n2 and t1.n1 = t3.n2 and t4.n1 = t4.n2 and t2.n1 = t4.n2"
tree = translator.generate_tree(sql)

begin = time.time()
translator.data(tree)
# tree_to_str(tree)
translator.upd_condition(tree)
translator.normalization()
print("execution time: ", time.time() - begin)

# print()
# union_conditions, union_time = check_tautology.get_union_conditions('output', 'Int')
# print("Union time: ", union_time)

# variables_list = ['y1', 'y2']
# domain_conditions, domain_time = check_tautology.get_domain_conditions(['1', '2'], variables_list, 'Int')

# print("Domain time: ", domain_time)

# ans, z3_time, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)

# print("Answer: ", ans, "model: ", model)
# print("z3 time: ", z3_time)
# print("Total running time(checking tautology): ", union_time+domain_time+z3_time)