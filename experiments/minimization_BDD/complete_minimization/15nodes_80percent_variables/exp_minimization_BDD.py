"""
Script for minimization experiment of BDD version
"""
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import experiments.minimization_BDD.complete_minimization.script_minimization as script_mini


runtimes = 1
size = 15
rate_variable = 0.8
size_single_loop = 4
runtime_upper_bound = 30 # minutes

total_time = 0
actual_rounds = 0 # actually runs
for i in range(runtimes):
    running_time = script_mini.exp_minimization_chain_BDD(size, 1 - rate_variable, size_single_loop)
    total_time += running_time

    actual_rounds = i+1
    print("round {}: {:.4f}".format(i+1, running_time))

    if running_time > runtime_upper_bound * 60:
        print("Over {} min, script Done!".format(runtime_upper_bound))
        break

print("Average runntime time: ", total_time/actual_rounds)