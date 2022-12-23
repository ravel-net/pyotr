import time
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
from Core.Homomorphism.Datalog.program import DT_Program
from Backend.reasoning.CUDD.BDDTools import BDDTools
from Backend.reasoning.Z3.z3smt import z3SMTTools

def unit_test3():
    # ====================================== c-variable data part test  =====================================
    # Tests is_head_contained_faure
    p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    # bddtool = BDDTools(variables=['h3'], domains={'h3':['10', '20']}, reasoning_type='Int')
    # program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains={'h3':['10', '20']}, c_variables=['h3'], reasoning_engine='bdd', reasoning_type='Int', datatype='int4_faure', simplification_on=False, c_tables=["R", "l"], reasoning_tool=bddtool)

    z3tool = z3SMTTools(variables=['h3'], domains={'h3':['10', '20']}, reasoning_type='Int')
    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains={'h3':['10', '20']}, c_variables=['h3'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=False, c_tables=["R", "l"], reasoning_tool=z3tool)
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(a2,h3,[h3],1) :- l(a2,h3)\nR(e1,h3,[a3, x],2) :- R(a3,h3,[x],1),l(a3,e1)\nR(a1,h3,[e1, x, y],3)[h3 == 10] :- R(e1,h3,[x, y],2)[h3 == 10],l(a1,e1)\nR(h2,h3,[a1, x, y, z],4) :- R(a1,h3,[x, y, z],3),l(a1,h2)"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))

def unit_test_containment():
    # ==================================== test: recursive ====================================
    p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
    p2 = "G(x,y,z) :- G(x,w,z), A(w,z), A(z,z), A(z,y)"
    databases = {
        'G':['int4_faure', 'int4_faure', 'int4_faure', 'text[]'],
        'A':['int4_faure', 'int4_faure', 'int4_faure', 'text[]']
        }
    domains = {
        # 'x':[1, 2, 3],
        # 'y':[1, 2, 3],
        # 'z':[1, 2, 3],
        # 'w':[1, 2, 3]
    }
    simplification_on = True
    z3Tool = z3SMTTools(variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_type='Int')
    program1 = DT_Program(p1, databaseTypes=databases, c_variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=simplification_on, c_tables=["A", "G"], reasoning_tool=z3Tool)
    program2 = DT_Program(p2, databaseTypes=databases, c_variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=simplification_on, c_tables=["A", "G"], reasoning_tool=z3Tool)
    # bddTool = BDDTools(variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_type='Int')
    # program1 = DT_Program(p1, databaseTypes=databases, c_variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_engine='bdd', reasoning_type='Int', datatype='int4_faure', simplification_on=simplification_on, c_tables=["A", "G"], reasoning_tool=bddTool)
    # program2 = DT_Program(p2, databaseTypes=databases, c_variables=['x', 'y', 'z', 'w'], domains=domains, reasoning_engine='bdd', reasoning_type='Int', datatype='int4_faure', simplification_on=simplification_on, c_tables=["A", "G"], reasoning_tool=bddTool)

    # program1 = program.DT_Program(p1)
    # program2 = program.DT_Program(p2)
    start_time = time.time()
    print(program1.contains(program2))
    print("runtimes:", time.time()-start_time)

def unit_test_IP():
    # ==================================== test: Route Aggregation with IP ====================================
    """
    Program P
    p1: R(z, d1)[d1 == 10.0.0.0] :- R(x, d1)[d1 == 10.0.0.0], R(y, d2), L(z, x), L(z, y) 
    p2: R(z, d2)[d2 == 10.0.0.1] :- R(x, d1), R(y, d2)[d2 == 10.0.0.1], L(z, x), L(z, y)

    Program Q
    q1: R(v, d)[d == 10.0.0.0/31] :- R(u, d)[d == 10.0.0.0/31], L(v, u)
    """
    p1 = "R(z, d1)[d1 == 10.0.0.0] :- R(x, d1)[d1 == 10.0.0.0], R(y, d2), L(z, x), L(z, y)\nR(z, d2)[d2 == 10.0.0.1] :- R(x, d1), R(y, d2)[d2 == 10.0.0.1], L(z, x), L(z, y)"
    p2 = "R(v, d)[d == 10.0.0.0/31] :- R(u, d)[d == 10.0.0.0/31], L(v, u)"
    databases = {
        'R':['inet_faure', 'inet_faure', 'text[]'],
        'L':['inet_faure', 'inet_faure', 'text[]']
        }
    domains = {
        # 'd1':[1, 2, 3],
        # 'y':[1, 2, 3],
        # 'z':[1, 2, 3],
        # 'w':[1, 2, 3]
    }
    simplification_on = True
    program1 = DT_Program(p1, databaseTypes=databases, c_variables=['d', 'd1', 'd2'], domains=domains, reasoning_engine='bdd', reasoning_type='BitVec', datatype='inet_faure', simplification_on=simplification_on, c_tables=["R", "L"])
    program2 = DT_Program(p2, databaseTypes=databases, c_variables=['d', 'd1', 'd2'], domains=domains, reasoning_engine='bdd', reasoning_type='BitVec', datatype='inet_faure', simplification_on=simplification_on, c_tables=["R", "L"])

    # program1 = program.DT_Program(p1)
    # program2 = program.DT_Program(p2)
    start_time = time.time()
    print(program1.contains(program2))
    print("runtimes:", time.time()-start_time)


if __name__ == "__main__":
    # unit_test3()
    # unit_test_containment()
    unit_test_IP()


    


    