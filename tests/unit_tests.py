import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Datalog.program import DT_Program
import psycopg2 
import databaseconfig as cfg

# ====================================== Example 6 - Containment ========================================
def unit_test1():
    p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
    p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
    program1 = DT_Program(p1)
    program2 = DT_Program(p2)
    start = time.time()
    if not program1.contains(program2):
        print("Test 1.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 1.1 passed in {} seconds".format(end-start))

    start = time.time()
    if program2.contains(program1):
        print("Test 1.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 1.2 passed in {} seconds".format(end-start))

# ===================================== Example 7 - Minimization ========================================
def unit_test2():
    p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
    program1 = DT_Program(p1)
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"):
        print("Test 2 failed")
        exit()
    else:
        end = time.time()
        print("Test 2 passed in {} seconds".format(end-start))

# ======================================== ACL Example ========================================
def unit_test3():
    p1 = "R(a3, h3, a || [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains={'h3':['10', '20']}, c_variables=['h3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(a2,h3,[h3],1) :- l(a2,h3)\nR(e1,h3,[a3, x],2) :- R(a3,h3,[x],1),l(a3,e1)\nR(a1,h3,[e1, x, y],3)[h3 == 10] :- R(e1,h3,[x, y],2)[h3 == 10],l(a1,e1)\nR(h2,h3,[a1, x, y, z],4) :- R(a1,h3,[x, y, z],3),l(a1,h2)"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))

# ====================================== c-variable data part test  =====================================
# Tests is_head_contained_faure
def unit_test4():
    p1 = "R(x, y) :- l(x,y)\nR(x,z) :- R(x,y), l(y,z)"
    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure"], "l":["int4_faure", "int4_faure"]}, domains={'x':['1', '2'],'y':['1', '2'],'z':['1', '2']}, c_variables=['x','y','z'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(x,y) :- l(x,y)\nR(x,z) :- R(x,y),l(y,z)"):
        print("Test 4 failed")
        exit()
    else:
        end = time.time()
        print("Test 4 passed in {} seconds".format(end-start))

# ======================================= c-variable as header test  ====================================
# Tests c-variable appearing in header that does not appear anywhere in the body
def unit_test5():
    p1 = "R(x,y) :- L(x,q,z), Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, {"R":["integer", "int4_faure"], "L":["integer", "integer", "int4_faure"], "Q":["int4_faure"]}, domains={'z':['1', '2'], 'y':['1', '2']}, c_variables=['z','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "L", "Q"])
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(x,y) :- L(x,q,z),Q(z)"):
        print("Test 5 failed")
        exit()
    else:
        end = time.time()
        print("Test 5 passed in {} seconds".format(end-start))

# ==================================== New Condition Format Test  ======================================
# Note that the brackets in the conditions are curly brackets. TODO: Fix constraint parser so that they don't have to be square brackets
def unit_test6():
    p1 = "R(x,y)[And(y = 10, y < 20)] :- L(x,y,z)[And(y = 10, y < 20)], Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, {"R":["integer", "int4_faure"], "L":["integer", "int4_faure", "int4_faure"], "Q":["int4_faure"]}, domains={'z':['1', '2'], 'y':['1', '2']}, c_variables=['z','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "L", "Q"])
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(x,y)[And(y == 10, y < 20)] :- L(x,y,z)[And(y == 10, y < 20)],Q(z)\nR(x,y) :- L(x,q,z),Q(z)"):
        print("Test 6 failed")
        exit()
    else:
        end = time.time()
        print("Test 6 passed in {} seconds".format(end-start))


# ======================================== Route Aggregation ========================================
def unit_test7():
    p1 = "R(1,x)[x == 10] :- l(1,2), l(1,3), l(1,4), R(2,x)[x == 10]\nR(1,x)[x == 20] :- l(1,2), l(1,3), l(1,4), R(3,x)[x == 20]\nR(1,x)[x == 30] :- l(1,2), l(1,3), l(1,4), R(4,x)[x == 30]"

    p2 = "R(1,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))]  :- l(1,2), l(1,3), l(1,4), R(y,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4 , x == 30))]"

    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure"], "l":["integer", "integer"]}, domains={'x':[10,20,30],'y':[2,3,4]}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])
    program2 = DT_Program(p2, {"R":["int4_faure", "int4_faure"], "l":["integer", "integer"]}, domains={'x':[10,20,30],'y':[2,3,4]}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])
    start = time.time()
    if (not program2.contains(program1)):
        print("Text 7.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 7.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (not program1.contains(program2)):
        print("Text 7.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 7.2 passed in {} seconds".format(end-start))

# ======================================== C-variable Implication Behaviour ========================================
def unit_test8():
    p1 = "l(3,4) :- l(1,3), k(2,1,3), l(1,5)"
    p2 = "l(3,4) :- l(y,c), k(d,y,e), l(f,g)"

    
    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"], "k":["int4_faure", "int4_faure", "int4_faure"]}, domains={}, c_variables=['a','b','c','d','e','f','g','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","k"])
    program2 = DT_Program(p2, {"l":["int4_faure", "int4_faure"], "k":["int4_faure", "int4_faure", "int4_faure"], "m":["int4_faure", "int4_faure"]}, domains={}, c_variables=['a','b','c','d','e','f','g','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","k","m"])

    start = time.time()
    if (not program2.contains(program1)):
        print("Text 8.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 8.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (program1.contains(program2)):
        print("Text 8.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 8.2 passed in {} seconds".format(end-start))

def unit_test9():
    p1 = "l(1,x)[x == 1] :- R(x)[x == 1]\nl(1,x)[x == 2] :- R(x)[x == 2]"
    p2 = "l(1,x)[Or(x == 1, x == 2)] :- R(x)[Or(x == 1, x == 2)]"

    
    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"])
    program2 = DT_Program(p2, {"l":["int4_faure", "int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"])

    start = time.time()
    if (not program2.contains(program1)):
        print("Text 9.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 9.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (not program1.contains(program2)):
        print("Text 9.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 9.2 passed in {} seconds".format(end-start))

def unit_test10():
    p1 = "l(x)[And(x > 2, x  < 7)] :- R(x)[And(x > 0, x  < 10)], R(x)[And(x > 2, x  < 7)]"
    p2 = "l(x)[And(x > 2, x  < 7)] :- R(x)[And(x > 2, x  < 7)], R(x)[And(x > 0, x  < 10)]"

    
    program1 = DT_Program(p1, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"], faure_evaluation_mode='implication')
    program2 = DT_Program(p2, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"], faure_evaluation_mode='implication')

    start = time.time()
    program1.minimize()
    program2.minimize()
    print("Program 1 after minimization:", program1)
    print("Program 2 after minimization:", program2)
    if (str(program1) != str(program2)):
        print("Text 10 failed")
        exit()
    else:
        end = time.time()
        print("Test 10 passed in {} seconds".format(end-start))

def unit_test11():
    p1 = "l(x)[And(x != 2, x != 3)] :- R(x)[x != 2], R(x)[x != 3]\nl(x)[x != 2] :- R(x)[x != 2], R(x)"
    program1 = DT_Program(p1, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"], faure_evaluation_mode='implication')
    start = time.time()
    program1.minimize(False, True)
    print("Program 1 after minimization:", program1)
    if (str(program1) != "l(x)[x != 2] :- R(x)[x != 2],R(x)"):
        print("Text 11.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 11.1 passed in {} seconds".format(end-start))

    p2 = "l(x)[x != 2] :- R(x)[x != 2], R(x)[x != 2]\nl(x)[x != 2] :- R(x)[x != 2], R(x)"
    program2 = DT_Program(p2, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"], faure_evaluation_mode='implication')
    start = time.time()
    program2.minimize(False, True)
    print("Program 2 after minimization:", program2)
    if (str(program2) != "l(x)[x != 2] :- R(x)[x != 2],R(x)"):
        print("Text 11.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 11.2 passed in {} seconds".format(end-start))

    p3 = "l(x)[And(x != 2, x != 3)] :- R(x)[x != 2], R(x)[x != 3]\nl(x)[And(x != 2, x != 4)] :- R(x)[x != 2], R(x)[x != 4]"
    program3 = DT_Program(p3, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"], faure_evaluation_mode='implication')
    program3_orig = str(program3)
    start = time.time()
    program3.minimize(False, True)
    print("Program 3 after minimization:", program3)
    if (str(program3) != program3_orig):
        print("Text 11.3 failed")
        exit()
    else:
        end = time.time()
        print("Test 11.3 passed in {} seconds".format(end-start))

def unit_test12():
    p1 = "R(4323,D,3356)[And(And(D != 216.186.192.0/22,D != 64.153.32.0/20))] :- l(4323,b,D),l(b,c,D)[And(D != 216.186.192.0/22,D != 64.153.32.0/20)],l(c,e,D),l(e,3356,D)\nR(4323,D,3356)[And(And(D != 216.186.192.0/22,D != 64.153.32.0/20))] :- l(4323,b,D),l(b,d,D)[And(D != 216.186.192.0/22,D != 64.153.32.0/20)],l(d,e,D),l(e,3356,D)"
    
    program1 = DT_Program(p1, {"R":["integer", "inet_faure", "integer"], "l":["integer", "integer", "inet_faure"]}, domains={}, c_variables=['D'], reasoning_engine='z3', reasoning_type={'D':'BitVec'}, datatype='inet_faure', simplification_on=False, c_tables=["R", "l"], faure_evaluation_mode='implication')

    start = time.time()
    program1.minimize(False, True)
    print("Program 1 after minimization:")
    print(program1)
    if (str(program1) != "R(4323,D,3356)[And(And(D != 216.186.192.0/22,D != 64.153.32.0/20))] :- l(4323,b,D),l(b,d,D)[And(D != 216.186.192.0/22,D != 64.153.32.0/20)],l(d,e,D),l(e,3356,D)"):
        print("Text 12.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 12.1 passed in {} seconds".format(end-start))

# execution with array concatination
def unit_test13():
    p1 = "R(10, 100, n, ['100', n]) :- F(10, 100, n)\nR(10, 100, n, p || [n]) :- R(10, 100, n2, p)[n != n2], F(10, n2, n)"
    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure", "int4_faure[]"], "F":["int4_faure", "int4_faure", "int4_faure"]}, domains={}, c_variables=['x1','x2','x3','x4','x5','y1','y2','y3','y4','y5'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["R", "F"])
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    program1.initiateDB(conn)
    conn.commit()
    variableConstants = []
    sql = "insert into F values ('x1', 100, 'y1', '{\"Or(y1 == 1, y1 == 2)\"}'), ('x2', 1, 'y2', '{\"Or(y2 == 100, y2 == 3)\"}'), ('x3', 2, 'y3', '{\"Or(y3 == 100, y3 == 3)\"}'), ('10', 3, 400, '{}'), ('10', 400, 401, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    # manually checking for answer by running query twice. The query does not finish otherwise because of loops
    changed = program1.execute(conn)
    changed = program1.execute(conn)

# execution with array concatination (Faure hack)
def unit_test14():
    p1 = "R(10, 100, n, [100, n]) :- F(10, 100, n)\nR(10, 100, n, p || [n]) :- R(10, 100, n2, p)[n != n2], F(10, n2, n)"
    program1 = DT_Program(p1, {"R":["integer", "integer","integer", "integer[]"], "F":["integer", "integer", "integer"]}, domains={}, c_variables=['x1','x2','x3','y1','y2','y3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["R", "F"])
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    program1.initiateDB(conn)
    conn.commit()
    variableConstants = []
    sql = "insert into F values (-1, 100, -10, '{\"Or(y1 == 1, y1 == 2)\"}'), (-2, 1, -20, '{\"Or(y2 == 100, y2 == 3)\"}'), (-3, 2, -30, '{\"Or(y3 == 100, y3 == 3)\"}'), (10, 3, 400, '{}'), (10, 400, 401, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    # manually checking for answer by running query twice. The query does not finish otherwise because of loops
    changed = program1.execute(conn)
    changed = program1.execute(conn)    

def unit_test15():
    p1 = "R(x1,x4) :- P(x1,x2),P(x2,x3),P(x3,x4),P(u,u)\nP(x,y) :- P(x,z), P(z,y)"
    p2 = "R(y1,y2) :- P(y1,y2),P(u,u)\nP(x,y) :- P(x,z), P(z,y)"

    
    program1 = DT_Program(p1)
    program2 = DT_Program(p2)

    start = time.time()
    if (not program2.contains(program1)):
        print("Text 15.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 15.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (not program1.contains(program2)):
        print("Text 15.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 15.2 passed in {} seconds".format(end-start))

if __name__ == "__main__":
    # unit_test1()
    # unit_test2()
    # # unit_test3()
    # unit_test4()
    # unit_test5()
    # unit_test6()
    # unit_test7()
    # unit_test8()
    # unit_test9()
    # unit_test10()
    # unit_test11()
    # unit_test12()
    # unit_test13()
    unit_test14()
    # unit_test15()




