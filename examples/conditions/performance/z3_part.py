import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)

import z3
from z3 import Or, And, Not

from time import time
from utils.check_tautology.condition_analyze import analyze
from utils.check_tautology.check_tautology import get_domain_conditions

path = "../../check_repeated_constraint/constraints/"

def time_list_condition(filename, output, domain_condition):
    f = open(output, 'w')
    f.write("case variable_time solving_time total_time\n")
    solver = z3.Solver()

    # exclude exception running time
    solver.push()
    solver.add(z3.Int('x') == z3.IntVal(1))
    solver.check()
    solver.pop()

    with open(path+filename) as file:
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
                f.write("{} {} {} {}\n".format(1, variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
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
                f.write("{} {} {} {}\n".format(0, variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
                continue
            else:
                solver.pop()
                checking_end = time()
                end_time = time()
                f.write("{} {} {} {}\n".format(2, variable_end-variable_begin+domain_time, checking_end-checking_begin, end_time-begin_time))
                continue
            
def time_one_condition(condition, domain_condition):
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

domain_condition, domain_time = get_domain_conditions(['1', '2'], ['x1', 'x2', 'x3'], "Int")

time_list_condition("larger_conditions.txt", "./z3_larger.txt")
condition = "And(x3 == 1, 2 == x3, x3 == 2)"

time_one_condition(condition, domain_condition)