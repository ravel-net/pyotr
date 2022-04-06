"""
Script for minimization experiment on z3 version

large topology with few variables
"""

import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

# import time 
# import utils.chain_generation.gen_chain as gen_chain 
# import databaseconfig as cfg
# import psycopg2
# import utils.minimization.minimization_pyotr as minimization_pyotr
import minimization_BDD.complete_minimization.script_minimization as script_mini


runtimes = 1
# size = 15
sizes = [15, 20, 25, 30, 35, 40, 45]
rate_variable = 0.2
size_single_loop = 4
runtime_upper_bound = 30 # minutes

total_time = 0
actual_rounds = 0 # actually runs
for i in range(runtimes):
    for size in sizes:
        running_time = script_mini.exp_minimization_chain_Z3(size, 1 - rate_variable, size_single_loop)
        total_time += running_time

        actual_rounds = i+1
        print("round {}: {:.4f}".format(i+1, running_time))

        if running_time > runtime_upper_bound * 60:
            print("Over {} min, script Done!".format(runtime_upper_bound))
            break

    print("Average runntime time: ", total_time/actual_rounds)