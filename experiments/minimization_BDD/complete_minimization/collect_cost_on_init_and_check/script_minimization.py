"""
Script for minimization experiment

the chain topology is generated by gen_chain_with_loop(), which configure size of a single loop 
"""
import sys
import os
from os.path import dirname, abspath, join, isfile

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

import time 
import math
import utils.chain_generation.gen_chain as gen_chain 
import databaseconfig as cfg
import psycopg2
import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.minimization_pyotr as minimization_pyotr
# import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.minimization_pyotr_BDD as minimization_pyotr_BDD
# import minimization_BDD.complete_minimization.collect_cost_on_init_and_check.translator_pyotr_BDD as translator_BDD
# import BDD_managerModule as bddmm

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def exp_minimization_chain_Z3(size, rate_summary, size_single_loop):

    path, summary_nodes, variable_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate_summary, size_single_loop=size_single_loop)
    tuples = gen_chain.gen_tableau(path, picked_nodes)

    tablename = "chain{}_{}_{}".format(size, math.ceil((1-rate_summary)*10), size_single_loop)
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

    conn.commit()

    current_directory = os.getcwd()
    if not os.path.exists(current_directory+"/results"):
        os.makedirs(current_directory+"/results")
    f = open(current_directory+"/results/z3_exp_minimization_{}.txt".format(tablename), "a")
    f.write("runtime(sec)\n")

    begin = time.time()
    minimization_pyotr.minimize(tablename=tablename, pos=0, summary=summary_nodes)
    end = time.time()
    print("\nRUNNING TIME:", end - begin)

    f.write("{}\n".format(end - begin))
    f.close()

    return end-begin

def exp_minimization_chain_BDD(size, rate_summary, size_single_loop):

    path, summary_nodes, variable_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate_summary, size_single_loop=size_single_loop)
    tuples = gen_chain.gen_tableau(path, picked_nodes)
    tablename = "chain{}_{}_{}".format(size, math.ceil((1-rate_summary)*10), size_single_loop)
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

    conn.commit()

    bddmm.initialize(len(variable_nodes), len(summary_nodes))
    translator_BDD.set_domain(summary_nodes)
    translator_BDD.set_variables(variable_nodes)
    begin_ctable = time.time()
    converted_table = translator_BDD.process_condition_on_ctable(tablename)
    end_ctable = time.time()

    current_directory = os.getcwd()
    if not os.path.exists(current_directory+"/results"):
        os.makedirs(current_directory+"/results")
    f = open(current_directory+"/results/BDD_exp_minimization_{}.txt".format(tablename), "a")
    f.write("process_condition_on_ctable: {:.4f}\n".format(end_ctable - begin_ctable))   

    begin = time.time()
    minimization_pyotr_BDD.minimize(tablename=converted_table, pos=0, summary=summary_nodes)
    end = time.time()
    print("\nRUNNING TIME:", end - begin)

    f.write("Total RUNNING TIME: {:.4f}\n".format(end - begin))
    f.close()
    
    return end-begin

def exp_minimization_chain_naive(size, rate_summary, size_single_loop):

    path, summary_nodes, variable_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate_summary, size_single_loop=size_single_loop)
    # path, summary_nodes, loop_nodes, picked_nodes = gen_chain.gen_chain_with_loop(size=size, rate_summary=rate, rate_loops=rate_loops)
    tuples = gen_chain.gen_tableau(path, picked_nodes)

    tablename = "chain{}_{}_{}".format(size, int((1-rate_summary)*10), size_single_loop)
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples)

    conn.commit()

    current_directory = os.getcwd()
    if not os.path.exists(current_directory+"/results"):
        os.makedirs(current_directory+"/results")
    f = open(current_directory+"/results/naive_exp_minimization_{}.txt".format(tablename), "a")
    f.write("runtime(sec)\n")

    begin = time.time()
    minimization_naive.minimize(tablename=tablename, pos=0, summary=summary_nodes)
    end = time.time()
    print("\nRUNNING TIME:", end - begin)

    f.write("{}\n".format(end - begin))
    f.close()

    return end-begin

if __name__ == "__main__":
    runtimes = 1
    size = 15
    rate_variable = 0.8
    size_single_loop = 4
    runtime_upper_bound = 30 # minutes

    total_time = 0
    actual_rounds = 0 # actually runs
    for i in range(runtimes):
        running_time = exp_minimization_chain_Z3(size, 1 - rate_variable, size_single_loop)
        total_time += running_time

        actual_rounds = i+1
        print("round {}: {:.4f}".format(i+1, running_time))

        if running_time > runtime_upper_bound * 60:
            print("Over {} min, script Done!".format(runtime_upper_bound))
            break
    print("Average runntime time: ", total_time/actual_rounds)

    # for i in range(runtimes):
    #     running_time = exp_minimization_chain_BDD(size, 1 - rate_variable, size_single_loop)
    #     total_time += running_time

    #     actual_rounds = i+1
    #     print("round {}: {:.4f}".format(i+1, running_time))

    #     if running_time > runtime_upper_bound * 60:
    #         print("Over {} min, script Done!".format(runtime_upper_bound))
    #         break
    # print("Average runntime time: ", total_time/actual_rounds)