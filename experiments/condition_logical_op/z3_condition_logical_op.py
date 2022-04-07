import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
print(root)
import z3
from z3 import Or, And, Not

from time import time
from utils.check_tautology.condition_analyze import analyze
from utils.check_tautology.check_tautology import get_domain_conditions
import pyotr_translator_BDD.BDD_manager.encodeCUDD as encodeCUDD

def time_one_condition(condition, domain_condition):
    """
    timing a single condition 

    Para
    
    """
    variable_time = 0
    checking_time = 0

    # exclude exception running time
    solver = z3.Solver()
    solver.push()
    solver.add(z3.Int('x') == z3.IntVal(1))
    solver.check()
    solver.pop()

    variable_begin = time()
    begin_time = time()

    prcd_condition = analyze(condition)
    z3_expr_cond = eval(prcd_condition)
    z3_expr_domain = eval(domain_condition)
    variable_end = time()
    variable_time = variable_end-variable_begin

    # check whether it is a tautology
    checking_begin = time()
    solver.push()
    solver.add(Not(z3_expr_cond))
    solver.add(z3_expr_domain)
    ans = solver.check()
    if ans == z3.unsat:
        solver.pop()
        end_time = time()
        checking_end = time()
        checking_time = checking_end - checking_begin
        # print("tautology")
        return variable_time, checking_time
    solver.pop()

    # check whether it is a contradiction
    solver.push()
    solver.add(z3_expr_cond)
    ans = solver.check()

    # if ans == z3.unsat:
    #     print("contradiction")        
    # else:
    #     print("satisfiable")
    end_time = time()
    checking_end = time()
    checking_time = checking_end - checking_begin
    return variable_time, checking_time


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Not enough arguments provided")
    else:
        DOMAIN = ['1', '2']
        input_fileName = sys.argv[1]
        with open(input_fileName) as f_input:
            lines = f_input.readlines()
            VARIABLES = encodeCUDD.findVariables(lines[0])
            print("Time in seconds")
            print("Variable\tChecking")
            domain_condition, domain_time = get_domain_conditions(DOMAIN, VARIABLES, "Int")
            for i in range(0, len(lines)-1, 2):
            #for i in range(0,4,2):
                unencodedCond1 = lines[i].strip()
                unencodedCond2 = lines[i+1].strip()
                finalCondition = "And({},{})".format(unencodedCond1, unencodedCond2)
                variable_time, checking_time = time_one_condition(finalCondition, domain_condition)
            
                variable_time = (str(round(variable_time, 4)))
                checking_time = (str(round(checking_time, 4)))
                print("{}\t\t{}".format(variable_time, checking_time))
