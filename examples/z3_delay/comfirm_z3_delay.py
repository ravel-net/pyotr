import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)

import copy
import faure_translator.databaseconfig as cfg
import psycopg2
import util.tableau.chain_with_loops.gen_chain as gen_chain
import util.split_merge.split_merge as split_merge
import util.variable_closure_algo.closure_overhead as closure_overhead

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

sizes = [5, 10, 15]

for size in sizes:
    rate_summary = 3 / size
    rate_loops = 1 / 3  

    """
    generate chain topology with 3 summary nodes and 1 loop which consists of all variable nodes  
    """
    path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate_summary, rate_loops=rate_loops)
    print(path)
    print(loop_nodes)

    """
    generate tableau for the chain topology
    """
    tuples = gen_chain.gen_tableau(path, picked_nodes)
    print("T: ", tuples)

    tablename = "chain{}".format(size)
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

    """
    try to eliminate tuple('y1', 'y2', '{}')

    here we only try to eliminate one tuple which contains variable node because if eliminating that tuple can run to completion then eliminating the next tuple must run to completion. 
    """
    tuple_to_remove = ('y1', 'y2', '{}')
    t_prime_tuples = copy.deepcopy(tuples)
    t_prime_tuples.remove(tuple_to_remove)
    print("t_prime: ", t_prime_tuples)
    
    t_prime_tablename = "{}_prime".format(tablename)

    cursor.execute("drop table if exists {}".format(t_prime_tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(t_prime_tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(t_prime_tablename), t_prime_tuples)

    conn.commit()

    closure_group = closure_overhead.getClosureGroup(tuple_to_remove, tuples)
    print("closure_group: ", closure_group)
    variables = closure_overhead.find_variables(tuples)

    running_time, output_table = split_merge.split_merge(closure_group, t_prime_tablename, variables, summary_nodes)
