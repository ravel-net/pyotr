import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
# filename = join(root, 'new_experiments')
# sys.path.append(filename)
# filename = join(root, 'new_experiments/support_int')
# sys.path.append(filename)

import time 
import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.translator_pyotr as translator
import utils.tableau.tableau as tableau
import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.merge_tuples_tautology as merge_tuples_tautology
import utils.split_merge.reorder_tableau as reorder_tableau
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

def split_merge(group, tablename, variables_list, summary):
    
    ordered_group = reorder_tableau.reorder_closure_group(group)
    sqls, output_tables = reorder_tableau.gen_splitjoin_sql(ordered_group, tablename, summary)

    total_running_time = 0
    for idx, sql in enumerate(sqls):
        print(sql)
        tree = translator.generate_tree(sql)
        data_time = translator.data(tree)
        upd_time = translator.upd_condition(tree)
        nor_time = translator.normalization()
        merge_begin = time.time()
        rows, check_tauto = merge_tuples_tautology.merge_tuples("output", output_tables[idx], summary, variables_list)
        merge_end = time.time()
        # print("Total time: ", merge_end-merge_begin)

        # total_running_time += data_time + upd_time + nor_time["contradiction"][1] + nor_time["redundancy"][1] + (merge_end - merge_begin)
    return {"normalization":nor_time, "check_tauto":check_tauto}, output_tables[-1]


if __name__ == '__main__':
    t = [('1', '2', '{}'), ('2', '3', '{}'), ('3', '4', '{}'), ('4', '5', '{}'), ('y2', 'y3', '{}'), ('y3', 'y4', '{}'), ('y4', 'y5', '{}'), ('y5', '3', '{}'), ('1', 'y6', '{}'), ('y7', 'y8', '{}'), ('y8', 'y9', '{}'), ('y9', '1', '{}'), ('2', 'y10', '{}'), ('3', '3', '{}'), ('1', '1', '{}'), ('2', '2', '{}')]

    t_prime = [('1', '2', '{}'), ('y1', 'y2', '{}'), ('y2', '2', '{}'), ('2', '2', '{}'), ('2', '3', '{}'), ('3', 'z2', '{}'), ('z2', '3', '{}'), ('3', '3', '{}')]

    cursor.execute("drop table if exists T_prime")
    cursor.execute("create table T_prime (n1 int4_faure, n2 int4_faure, condition text[])")
    cursor.executemany("insert into T_prime values(%s, %s, %s)", t_prime)
    conn.commit()

    group = [('2', 'y1'), ('y1', 'y2'), ('y2', '2')]
    summary = ['1', '2', '3']
    variable_lists = ['y1', 'y2', 'z2']
    # split_merge(group, 't_prime', variable_lists, summary)

    sql = tableau.convert_tableau_to_sql(group, "t_prime", summary)
    tree = translator.generate_tree(sql)
    data_time = translator.data(tree)
    upd_time = translator.upd_condition(tree)
    nor_time = translator.normalization()

    merge_tuples_tautology.merge_tuples("output", "toy", summary, variable_lists)


