"""
Script for minimization experiment on z3 version
"""
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(dirname(dirname(dirname(abspath(__file__))))))
print(root)
sys.path.append(root)

import script_minimization as script_mini

if len(sys.argv) < 4:
    print("Requires {} arguments but only {} given. Format: ./exp_minimization_z3 [size] [loops] [runtimes]")


# sizes = [*range(5, 76, 5)]
sizes = [int(sys.argv[1])]
loops = [int(sys.argv[2])]
runtimes = int(sys.argv[3])
runtime_upper_bound = 60 # minutes

total_time = 0
actual_rounds = 0 # actually runs
for i in range(runtimes):
    for size in sizes:
        for size_single_loop in loops:
            print("\n\n=================NEW RUN================")
            print(size, size_single_loop)
            print("\n\n")
            rate_variable = size_single_loop/size            
            running_time = script_mini.exp_minimization_chain_Z3(size, 1 - rate_variable, size_single_loop)
            total_time += running_time

            actual_rounds = i+1
            print("round {}: {:.4f}".format(i+1, running_time))

            if running_time > runtime_upper_bound * 60:
                print("Over {} min, script Done!".format(runtime_upper_bound))
                break

#print("Average runntime time: ", total_time/actual_rounds)
