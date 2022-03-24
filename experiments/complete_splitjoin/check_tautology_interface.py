import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
filename = join(root, 'util')
sys.path.append(filename)

from tqdm import tqdm
import re
import time
import z3
from z3 import Or, And, Not
import databaseconfig as cfg
import psycopg2
from condition_analyze import analyze

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

# datatype = "String"
# datatype = "Int"

def get_max(overlay):
    max_val = 0
    for node in overlay:
        if int(node) > max_val:
            max_val = int(node)
    return max_val


def get_union_conditions(tablename='output', datatype='Int'):
    begin = time.time()
    cursor.execute("select condition from {}".format(tablename))
    union_cond = []
    row = cursor.fetchone()
    while row is not None:
        conditions = row[0]
        prced_conditions = []
        for c in conditions:
            expr = analyze(c)
            prced_conditions.append(expr)
        # print(prced_conditions)
        and_cond = "And({})".format(", ".join(prced_conditions)) # LogicaL And for all conditions in one tuple
        union_cond.append(and_cond)
        row = cursor.fetchone()
        
    union_condition = "Or({})".format(", ".join(union_cond)) # logical Or for every tuples' condition
    end = time.time()
    return union_condition, end - begin

def get_domain_conditions(overlay_nodes, variables_list, datatype):
    begin = time.time()
    max_node = get_max(overlay_nodes)
    var_domain_list = []
    for var in variables_list:
        var_domain = []
        
        for idx, val in enumerate(overlay_nodes):
            condition = ""
            # interface encoding
            if idx != 0 and idx != len(overlay_nodes) - 1:
                interface_val = str(int(val) + max_node)
                condition = "z3.{}('{}') == z3.{}Val({})".format(datatype, var, datatype , interface_val)
                var_domain.append(condition)
            condition = "z3.{}('{}') == z3.{}Val({})".format(datatype, var, datatype , val)
            var_domain.append(condition)
        var_domain_list.append("Or({})".format(", ".join(var_domain)))
    domain_conditions = ", ".join(var_domain_list)  
    end = time.time()
    # print(domain_conditions)
    return domain_conditions, end - begin

def check_is_tautology(union_conditions, domain_conditions):

    negation_union_conditions = "Not({})".format(union_conditions)
    z3_begin = time.time()
    solver = z3.Solver()
    
    solver.add(eval(domain_conditions)) # set domain for variables
    solver.add(eval(negation_union_conditions)) # set negation union conditions
    
    ans = solver.check() # check the answer, if it answers sat, that means it is not a tautology
    z3_end = time.time()

    # print("total execution time: ", z3_end - z3_begin)

    if ans == z3.sat:
        model = solver.model()
        # print(model)
        return False, z3_end - z3_begin, model
    else:
        return True, z3_end - z3_begin, ""
    

if __name__ == '__main__':
    datatype = "Int"
    # union_conditions, union_time = get_union_conditions(tablename="output", datatype=datatype)
    domain_conditions, domain_time = get_domain_conditions(overlay_nodes=['1', '2', '3'], variables_list=['y1', 'y2', 'y3'], datatype=datatype)
    print(domain_conditions)
    # ans, runtime, model = check_is_tautology(union_conditions, domain_conditions)
    # print(ans)

    # cursor.execute("select distinct 1, 2, condition from output")

    # begin = time.time()
    # union_cond = []
    # row = cursor.fetchone()
    # while row is not None:
    #     conditions = row[2]
    #     prced_conditions = []
    #     for c in conditions:
    #         op1, operator, op2 = analyze(c)
    #         expr = "{} {} {}".format(op1, operator, op2)
    #         prced_conditions.append(expr)
    #     # print(prced_conditions)
    #     and_cond = "And({})".format(", ".join(prced_conditions)) # LogicaL And for all conditions in one tuple
    #     union_cond.append(and_cond)
    #     row = cursor.fetchone()
        
    # union_condition = "Or({})".format(", ".join(union_cond)) # logical Or for every tuples' condition
    # # print(condition)

    # # domain_conditions = "Or(z3.Int('y1') == z3.IntVal('1'), z3.Int('y1') == z3.IntVal('2')), Or(z3.Int('y2') == z3.IntVal('1'), z3.Int('y2') == z3.IntVal('2'))"
    # domain_conditions = "Or(z3.{}('y1') == z3.{}Val('1'), z3.{}('y1') == z3.{}Val('2')), \
    #             Or(z3.{}('y2') == z3.{}Val('1'), z3.{}('y2') == z3.{}Val('2'))".format(datatype, datatype, datatype, datatype, datatype, datatype, datatype, datatype)

    # # domain_conditions.append(condition)
    # final_condition = "Not({})".format(union_condition) # add negation to union condition
    # print(final_condition)
    # # print(union_cond)
    # solver = z3.Solver()
    
    # solver.add(eval(domain_conditions)) # set domain for y1 and y2
    # solver.add(eval(final_condition)) # set 
    # z3_begin = time.time()
    # ans = solver.check() # check the answer, if it answers sat, that means it is not a tautology
    # if ans == z3.sat:
    #     model = solver.model()
    #     print(model)
    # z3_end = time.time()
    # print("Answer:", ans, "z3 execution time:", z3_end - z3_begin)
    # print("total execution time: ", z3_end - begin)
    
