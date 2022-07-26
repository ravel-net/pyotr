import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
# filename = join(root, 'new_experiments')
# sys.path.append(filename)
# filename = join(root, 'new_experiments/support_int')
# sys.path.append(filename)

import time 
import Core.Homomorphism.translator_pyotr as translator
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_tautology as merge_tuples_tautology
import Core.Homomorphism.Optimizations.split_merge.reorder_tableau as reorder_tableau
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

def split_merge(group, tablename, table_attributes, domain, summary, storage_types, reasoning_type):
    """
    Parameters:
    -----------
    group: list[tuple]
        A list of variable closure group.

    tablename: string
        The table name of the tableau which contains the `group`
    
    domain: dict
        domain of the variables. e.g. {"u":["1","2"], "v":["1","2"]}
    
    summary: list
        the summary of the tableau
    
    storage_types: list
        a list of attributes datatype
    
    reasoning_type: string
        the Z3 datatype of the variables when reasoning.
    
    """
    
    ordered_group = reorder_tableau.reorder_closure_group(group)
    print("ordered_group", ordered_group)
    sqls, output_tables = reorder_tableau.gen_splitjoin_sql(ordered_group, tablename, table_attributes, summary)
    
    total_data_time, total_upd_time, total_simplification_time, total_checktime = 0, 0, {'contradiction': [0, 0], 'redundancy': [0, 0]}, 0
    for idx, sql in enumerate(sqls):
        print(sql)
        tree = translator.generate_tree(sql)
        data_time = translator.data(tree)
        upd_time = translator.upd_condition(tree, storage_types[0])
        simplification_time = translator.normalization(reasoning_type)
        merge_begin = time.time()
        rows = merge_tuples_tautology.merge_tuples("output", output_tables[idx], domain, reasoning_type)
        merge_end = time.time()
        
        total_data_time += data_time + (merge_end - merge_begin)
        total_upd_time += upd_time
        total_simplification_time["contradiction"][0] += simplification_time["contradiction"][0]
        total_simplification_time["contradiction"][1] += simplification_time["contradiction"][1]
        total_simplification_time["redundancy"][0] += simplification_time["redundancy"][0]
        total_simplification_time["redundancy"][1] += simplification_time["redundancy"][1]
        total_checktime += total_checktime
        # print("Total time: ", merge_end-merge_begin)

    return total_data_time, total_upd_time, total_simplification_time, total_checktime, output_tables[-1]


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
    nor_time = translator.normalization()

    merge_tuples_tautology.merge_tuples("output", "toy", summary, variable_lists)


