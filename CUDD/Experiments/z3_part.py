import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)

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
    f.write("case variable_time solving_time total_time\n")
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
            if ans == z3.unsat:
                solver.pop()
                checking_end = time()
                end_time = time()
                total_running_time += end_time - begin_time
                f.write("{} {} {} {}\n".format("tautology", variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
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
                f.write("{} {} {} {}\n".format("contradiction", variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
                continue
            else:
                solver.pop()
                checking_end = time()
                end_time = time()
                total_running_time += end_time - begin_time
                f.write("{} {} {} {}\n".format("satisfiable", variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
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
    # print(solver.model())
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

path = "benchmarks/"

domain_condition, domain_time = get_domain_conditions(['1', '2'], ['x1', 'x2', 'x3','x4','x5','x6','x7','x8','x9','x10'], "Int")
print(domain_condition)
time_list_condition(path+"newCond.txt", "./z3_contrad.txt", domain_condition)
# condition = "And(x == 1)"
# time_one_condition(condition, domain_condition)