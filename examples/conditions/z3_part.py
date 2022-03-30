import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import math
import z3
from z3 import Or, And, Not

from time import time
from util.check_tautology.condition_analyze import analyze
from util.check_tautology.check_tautology import get_domain_conditions

def time_list_condition(filename, output, domain_condition):
    """
    timing the z3 reasoning time for a file of conditions

    Parameters:
    -----------
    filename: string
        the location of the filename which stores the conditions
    output: string
        the location of the output filename which stores the running time for each condition
    domain_condition: string
        the domain condition

    Output:
    ----------
    output: file
        the file stores the running time for each condition, the name is determined by output attribute

    Return:
    ----------
    total_running_time: seconds
        the total running time for all conditions in the file
    """
    f = open(output, 'w')
    f.write("case\t\tmemory(mb)\t\ttotal_time(ms)\n")
    solver = z3.Solver()

    # exclude exception running time
    solver.push()
    solver.add(z3.Int('x') == z3.IntVal(1))
    solver.check()
    solver.pop()
    total_running_time = 0
    with open(filename) as file:
        while line := file.readline():
            # print(line.rstrip())
            begin_time = time()

            variable_begin = time()
            prcd_condition = analyze(line.strip())
            z3_expr_cond = eval(prcd_condition)
            z3_expr_domain = eval(domain_condition)
            variable_end = time()

            # check whether it is a tautology
            checking_begin = time()
            solver.push()
            solver.add(Not(z3_expr_cond))
            solver.add(z3_expr_domain)
            ans = solver.check()
            mem = 0
            for k, v in solver.statistics():
                if (k == "max memory"):
                    mem = v
            if ans == z3.unsat:
                solver.pop()
                checking_end = time()
                end_time = time()
                total_running_time += end_time - begin_time
                f.write("{}\t\t\t{}\t\t\t{}\n".format(1, mem, math.floor((end_time-begin_time)*1000)))
                continue
            solver.pop()

            # check whether it is a contradiction
            solver.push()
            solver.add(z3_expr_cond)
            ans = solver.check()

            if ans == z3.unsat:
                solver.pop()
                checking_end = time()
                end_time = time()
                total_running_time += end_time - begin_time
                f.write("{}\t\t\t{}\t\t\t{}\n".format(0, mem, math.floor((end_time-begin_time)*1000)))
                continue
            else:
                solver.pop()
                checking_end = time()
                end_time = time()
                total_running_time += end_time - begin_time
                f.write("{}\t\t\t{}\t\t\t{}\n".format(2, mem, math.floor((end_time-begin_time)*1000)))
                continue
    return total_running_time
            
def time_one_condition(condition, domain_condition):
    """
    timing a single condition 

    Para
    
    """
    solver = z3.Solver()

    # exclude exception running time
    solver.push()
    solver.add(z3.Int('x') == z3.IntVal(1))
    solver.check()
    solver.pop()

    begin_time = time()

    prcd_condition = analyze(condition)
    z3_expr_cond = eval(prcd_condition)
    z3_expr_domain = eval(domain_condition)

    # check whether it is a tautology
    solver.push()
    solver.add(Not(z3_expr_cond))
    solver.add(z3_expr_domain)
    ans = solver.check()
    if ans == z3.unsat:
        solver.pop()
        end_time = time()
        print("tautology")
        return end_time-begin_time
    solver.pop()

    # check whether it is a contradiction
    solver.push()
    solver.add(z3_expr_cond)
    ans = solver.check()

    if ans == z3.unsat:
        print("contradiction")        
    else:
        print("satisfiable")
    end_time = time()
    return end_time-begin_time

path = "../../check_repeated_constraint/constraints/"

domain_condition, domain_time = get_domain_conditions(['1', '2', '3', '4', '5'], ['y1', 'y2', 'y3', 'y4', 'y5', 'y6', 'y7', 'y8', 'y9', 'y10'], "Int")

time_list_condition("larger_conditions10var5val.txt", "./z3_larger_conditions10var5val.txt", domain_condition)
# condition = "And(x3 == 1, 2 == x3, x3 == 2)"

# time_one_condition(condition, domain_condition)