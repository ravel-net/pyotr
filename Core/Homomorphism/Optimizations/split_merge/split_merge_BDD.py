"""
BDD version of complete split-merge algorithm
"""
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time 
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_BDD as merge_tuples_BDD
# from utils.variable_closure_algo.closure_group import find_variables, construct_Graph, calculate_tableau
import Core.Homomorphism.Optimizations.split_merge.reorder_tableau as reorder_tableau
import databaseconfig as cfg
import psycopg2

import BDD_managerModule as bddmm
import Core.Homomorphism.translator_pyotr_BDD as translator

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

OPEN_OUTPUT = True

def split_merge(group, tablename, variables_list, summary, datatype):    
    print("DOMAIN", translator.DOMAIN)
    print("VARIABLES", translator.VARIABLES)
    ordered_group = reorder_tableau.reorder_closure_group(group)
    sqls, output_tables = reorder_tableau.gen_splitjoin_sql(ordered_group, tablename, summary)

    total_running_time = 0
    for idx, sql in enumerate(sqls):
        print(sql)
        begin = time.time()
        tree = translator.generate_tree(sql)
        translator.data(tree)
        translator.upd_condition(tree, datatype)

        rows = merge_tuples_BDD.merge_tuples("output", output_tables[idx])
        end = time.time()
        # print("Total time: ", merge_end-merge_begin)
        total_running_time += end-begin
    
    # get the satisfiability of the conditin at the final stage for checking
    # In theory, the resulting table at final stage only contains only tuple 
    cursor.execute("select condition from {tablename}".format(tablename=output_tables[-1]))
    row_num = cursor.rowcount
    
    sat = 0
    if row_num  != 0: # when output table is empty, it means no tuple meets the condition requirements
        row = cursor.fetchone()
        condition_idx = row[0]
        begin_eval = time.time()
        sat = bddmm.evaluate(condition_idx) # sat = 1 for tautology, 0 for contradiction, 2 for satisfiable
        end_eval = time.time()
        if OPEN_OUTPUT:
            print("Evaluation time of condition {}: {} s".format(condition_idx, end_eval-begin_eval))

    return total_running_time, sat


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
    upd_time = translator.upd_condition(tree, "int4_faure")
    nor_time = translator.normalization("int4_faure")

    merge_tuples_tautology.merge_tuples("output", "toy", summary, variable_lists)


