"""
BDD version of complete split-merge algorithm
"""
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

import time 
import merge_tuples_BDD as merge_tuples_BDD
import utils.split_merge.reorder_tableau as reorder_tableau
import databaseconfig as cfg
import psycopg2

import BDD_managerModule as bddmm
import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.translator_pyotr_BDD as translator

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def split_merge(group, tablename, variables_list, summary, datatype):    
    #print("DOMAIN", translator.DOMAIN)
    #print("VARIABLES", translator.VARIABLES)
    ordered_group = reorder_tableau.reorder_closure_group(group)
    sqls, output_tables = reorder_tableau.gen_splitjoin_sql(ordered_group, tablename, summary)

    total_running_time = 0
    total_data = 0
    total_condition = 0
    total_merged = 0
    data_time = []
    condition_time = []
    merge_time = []
    for idx, sql in enumerate(sqls):
        #print(sql)
        begin = time.time()
        tree = translator.generate_tree(sql)

        begin_data = time.time()
        data = translator.data(tree)
        end_data = time.time()
        data_time.append(data)
        total_data += end_data - begin_data

        begin_condition = time.time()
        condition = translator.upd_condition(tree, datatype)
        end_condition = time.time()
        condition_time.append(condition)
        total_condition += end_condition - begin_condition

        begin_merged = time.time()
        rows, merge = merge_tuples_BDD.merge_tuples("output", output_tables[idx])
        end_merged = time.time()
        merge_time.append(merge)
        total_merged += end_merged - begin_merged

        end = time.time()
        # print("Total time: ", merge_end-merge_begin)
        total_running_time += end-begin
    
    
    # get the satisfiability of the conditin at the final stage for checking
    # In theory, the resulting table at final stage only contains only tuple 
    cursor.execute("select condition from {tablename}".format(tablename=output_tables[-1]))
    row_num = cursor.rowcount
    
    sat = 0
    BDD_checking = 0
    if row_num  != 0: # when output table is empty, it means no tuple meets the condition requirements
        row = cursor.fetchone()
        condition_idx = row[0]
        begin_checking = time.time()
        sat = bddmm.evaluate(condition_idx) # sat = 1 for tautology, 0 for contradiction, 2 for satisfiable
        end_checking = time.time()
        BDD_checking = end_checking-begin_checking
    return {
        "total":total_running_time, "data":total_data, "condition":total_condition, "merged":total_merged, "checking":BDD_checking,
        "data_details":data_time, "condition_details":condition_time, "merged_details":merge_time
    }, sat



