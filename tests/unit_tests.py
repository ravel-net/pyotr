import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Datalog.program import DT_Program
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
import psycopg2 
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])

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
    p1 = "R(a3, h3, [a, h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    program1 = DT_Program(p1, {"R":["integer_faure", "integer_faure","integer_faure[]", "integer_faure"], "l":["integer_faure", "integer_faure"]}, domains={'h3':['10', '20']}, c_variables=['h3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"], cVarMapping={"-2":"h3"}, faure_evaluation_mode="implication")
    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(a3,h3,[a, h3],1)[h3 == 10] :- l(a3,h3)[h3 == 10],l(a,e1)\nR(a2,h3,[h3],1) :- l(a2,h3)\nR(e1,h3,[a3, x],2) :- R(a3,h3,[x],1),l(a3,e1)\nR(a1,h3,[e1, x, y],3)[h3 == 10] :- R(e1,h3,[x, y],2)[h3 == 10],l(a1,e1)\nR(h2,h3,[a1, x, y, z],4) :- R(a1,h3,[x, y, z],3),l(a1,h2)"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))

# ====================================== c-variable data part test  =====================================
# Tests is_head_contained_faure
def unit_test4():
    R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"x":"c0", "y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})

    l = DT_Table(name="l", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"x":"c0", "y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})

    database = DT_Database(tables=[R,l])
    p1 = "R(x, y) :- l(x,y)\nR(x,z) :- R(x,y), l(y,z)"
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.minimize()
    database.delete(conn)
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
    R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    L = DT_Table(name="L", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    Q = DT_Table(name="Q", columns={"c0":"integer_faure"}, cvars={"y":"c0", "z":"c0"}, domain={"c0":['1', '2']})
    database = DT_Database(tables=[R,L,Q])
    p1 = "R(x,y) :- L(x,q,z), Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.minimize()
    database.delete(conn)
    print(program1)
    if (str(program1) != "R(x,y) :- L(x,q,z),Q(z)"):
        print("Test 5 failed")
        exit()
    else:
        end = time.time()
        print("Test 5 passed in {} seconds".format(end-start))

# ==================================== New Condition Format Test  ======================================
def unit_test6():
    R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    L = DT_Table(name="L", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure"}, cvars={"y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    Q = DT_Table(name="Q", columns={"c0":"integer_faure"}, cvars={"y":"c0", "z":"c0"}, domain={"c0":['1', '2']})
    
    database = DT_Database(tables=[R,L,Q])
    p1 = "R(x,y)[And(y = 10, y < 20)] :- L(x,y,z)[And(y = 10, y < 20)], Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, database)    
    start = time.time()
    program1.minimize(False, True)
    database.delete(conn)
    print(program1)
    if (str(program1) != "R(x,y)[And(y == 10, y < 20)] :- L(x,y,z)[And(y == 10, y < 20)],Q(z)\nR(x,y) :- L(x,q,z),Q(z)"):
        print("Test 6 failed")
        exit()
    else:
        end = time.time()
        print("Test 6 passed in {} seconds".format(end-start))


# ======================================== Route Aggregation ========================================
# With implication mode, test 7.2 fails because early exit when one rule's condition does not imply the old condition. Need to think about how to approach this.
def unit_test7():
    R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"x":"c0", "y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    l = DT_Table(name="l", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"x":"c0", "y":"c1", "z":"c1"}, domain={"c0":['1', '2'], "c1":['1', '2']})
    database = DT_Database(tables=[R,l])

    p1 = "R(1,x)[x == 10] :- l(1,2), l(1,3), l(1,4), R(2,x)[x == 10]\nR(1,x)[x == 20] :- l(1,2), l(1,3), l(1,4), R(3,x)[x == 20]\nR(1,x)[x == 30] :- l(1,2), l(1,3), l(1,4), R(4,x)[x == 30]"

    p2 = "R(1,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4, x == 30))]  :- l(1,2), l(1,3), l(1,4), R(y,x)[Or(And(y == 2, x == 10), And(y == 3, x == 20), And(y == 4, x == 30))]"

    program1 = DT_Program(p1, database)
    program2 = DT_Program(p2, database)
    database.delete(conn)
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
    k = DT_Table(name="k", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure"}, cvars={"d":"c0", "y":"c1", "e":"c1"})
    
    l = DT_Table(name="l", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"y":"c0", "c":"c1", "f":"c1", "g":"c1"})

    database = DT_Database(tables=[k,l])
    p1 = "l(3,4) :- l(1,3), k(2,1,3), l(1,5)"
    p2 = "l(3,4) :- l(y,c), k(d,y,e), l(f,g)"

    
    program1 = DT_Program(p1, database)
    program2 = DT_Program(p2, database)

    start = time.time()
    if (not program2.contains(program1)):
        print("Text 8.1 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 8.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (program1.contains(program2)):
        print("Text 8.2 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 8.2 passed in {} seconds".format(end-start))
    database.delete(conn)

def unit_test9():
    R = DT_Table(name="R", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
    l = DT_Table(name="l", columns={"c0":"integer_faure", "c1":"integer_faure"}, cvars={"x":"c0", "y":"c1", "z":"c1"})
    database = DT_Database(tables=[R,l])

    p1 = "l(1,x)[x == 1] :- R(x)[x == 1]\nl(1,x)[x == 2] :- R(x)[x == 2]"
    # p2 = "l(1,x)[And(Or(x == 1, x == 2), x == 5)] :- C(x)[x == 2], C(x)[And(Or(x == 1, x == 2), x == 5)], C(x), B(x)"
    p2 = "l(1,x)[Or(x == 1, x == 2)] :- R(x)[Or(x == 1, x == 2)]"

    
    program1 = DT_Program(p1, database)
    program2 = DT_Program(p2,database)
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    start = time.time()
    if (not program2.contains(program1)):
        print("Text 9.1 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 9.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (not program1.contains(program2)):
        print("Text 9.2 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 9.2 passed in {} seconds".format(end-start))
    database.delete(conn)

def unit_test10():
    R = DT_Table(name="R", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
    l = DT_Table(name="l", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
    database = DT_Database(tables=[R,l])

    p1 = "l(x)[And(x > 2, x  < 7)] :- R(x)[And(x > 0, x  < 10)], R(x)[And(x > 2, x  < 7)]"
    p2 = "l(x)[And(x > 2, x  < 7)] :- R(x)[And(x > 2, x  < 7)], R(x)[And(x > 0, x  < 10)]"

    
    program1 = DT_Program(p1, database)
    program2 = DT_Program(p2, database)

    start = time.time()
    program1.minimize()
    program2.minimize()
    print("Program 1 after minimization:", program1)
    print("Program 2 after minimization:", program2)
    if (str(program1) != str(program2)):
        print("Text 10 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 10 passed in {} seconds".format(end-start))
    database.delete(conn)

def unit_test11():
    R = DT_Table(name="R", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
    l = DT_Table(name="l", columns={"c0":"integer_faure"}, cvars={"x":"c0", "y":"c0", "z":"c0"})
    database = DT_Database(tables=[R,l])

    p1 = "l(x)[And(x != 2, x != 3)] :- R(x)[x != 2], R(x)[x != 3]\nl(x)[x != 2] :- R(x)[x != 2], R(x)"
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.minimize(False, True)
    print("Program 1 after minimization:", program1)
    if (str(program1) != "l(x)[x != 2] :- R(x)[x != 2],R(x)"):
        print("Text 11.1 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 11.1 passed in {} seconds".format(end-start))
    database.delete(conn)

    p2 = "l(x)[x != 2] :- R(x)[x != 2], R(x)[x != 2]\nl(x)[x != 2] :- R(x)[x != 2], R(x)"
    program2 = DT_Program(p2, database)
    start = time.time()
    program2.minimize(False, True)
    print("Program 2 after minimization:", program2)
    if (str(program2) != "l(x)[x != 2] :- R(x)[x != 2],R(x)"):
        print("Text 11.2 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 11.2 passed in {} seconds".format(end-start))
    database.delete(conn)

    p3 = "l(x)[And(x != 2, x != 3)] :- R(x)[x != 2], R(x)[x != 3]\nl(x)[And(x != 2, x != 4)] :- R(x)[x != 2], R(x)[x != 4]"
    program3 = DT_Program(p3, database)
    program3_orig = str(program3)
    start = time.time()
    program3.minimize(False, True)
    print("Program 3 after minimization:", program3)
    if (str(program3) != program3_orig):
        print("Text 11.3 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 11.3 passed in {} seconds".format(end-start))
    database.delete(conn)

def unit_test12():
    R = DT_Table(name="R", columns={"c0":"integer", "c1":"inet_faure", "c2":"integer"}, cvars={"D":"c1"})
    l = DT_Table(name="l", columns={"c0":"integer", "c1":"integer", "c2":"inet_faure"}, cvars={"D":"c2"})
    database = DT_Database(tables=[R,l])

    p1 = "R(4323,D,3356)[And(And(D != '216.186.192.0/22',D != '64.153.32.0/20'))] :- l(4323,b,D),l(b,c,D)[And(D != '216.186.192.0/22',D != '64.153.32.0/20')],l(c,e,D),l(e,3356,D)\nR(4323,D,3356)[And(And(D != '216.186.192.0/22',D != '64.153.32.0/20'))] :- l(4323,b,D),l(b,c,D)[And(D != '216.186.192.0/22',D != '64.153.32.0/20')],l(c,e,D),l(e,3356,D)"
    
    program1 = DT_Program(p1,database)

    start = time.time()
    program1.minimize(False, True)
    print("Program 1 after minimization:")
    print(program1)
    if (str(program1) != "R(4323,D,3356)[And(And(D != '216.186.192.0/22',D != '64.153.32.0/20'))] :- l(4323,b,D),l(b,c,D)[And(D != '216.186.192.0/22',D != '64.153.32.0/20')],l(c,e,D),l(e,3356,D)"):
        print("Text 12.1 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 12.1 passed in {} seconds".format(end-start))
    database.delete(conn)

# execution with array concatination
def unit_test13():
    p1 = "R(10, 100, n, ['100', n]) :- F(10, 100, n)\nR(10, 100, n, p || [n]) :- R(10, 100, n2, p)[n != n2], F(10, n2, n)"
    program1 = DT_Program(p1, {"R":["integer_faure", "integer_faure","integer_faure", "integer_faure[]"], "F":["integer_faure", "integer_faure", "integer_faure"]}, domains={}, c_variables=['x1','x2','x3','y1','y2','y3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["R", "F"], faure_evaluation_mode='contradiction', cVarMapping={'-1':"x1", '-2':'x2', '-3':'x3', '-10':"y1", '-20':'y2', '-30':'y3'})
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    program1.initiateDB(conn)
    conn.commit()
    variableConstants = []
    sql = "insert into F values ('-1', 100, '-10', '{\"Or(y1 == 1, y1 == 2)\"}'), ('-2', 1, '-20', '{\"Or(y2 == 100, y2 == 3)\"}'), ('-3', 2, '-30', '{\"Or(y3 == 100, y3 == 3)\"}'), ('10', 3, 400, '{}'), ('10', 400, 401, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    # manually checking for answer by running query twice. The query does not finish otherwise because of loops
    changed = program1.execute(conn)
    changed = program1.execute(conn)

# execution with array concatination (Faure hack)
def unit_test14():
    p1 = "R(10, 100, n, [100, n]) :- F(10, 100, n)\nR(10, 100, n, p || [n]) :- R(10, 100, n2, p)[n != n2], F(10, n2, n)"
    program1 = DT_Program(p1, {"R":["integer_faure", "integer_faure","integer_faure", "integer_faure[]"], "F":["integer_faure", "integer_faure", "integer_faure"]}, domains={}, c_variables=['x1','x2','x3','y1','y2','y3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["R", "F"])
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
    if (program1.contains(program2)):
        print("Text 15.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 15.2 passed in {} seconds".format(end-start))

def unit_test16():
    p1 = "R(x1,x4) :- P(x1,x2),P(x2,x3),P(x3,x4)\nP(x,y) :- P(x,z), P(z,y)\nP(x,x) :- P(x,z)"
    p2 = "R(y1,y2) :- P(y1,y2)\nP(x,y) :- P(x,z), P(z,y)\nP(x,x) :- P(x,z)"

    
    program1 = DT_Program(p1)
    program2 = DT_Program(p2)
    program1.minimize()
    # print(program1)
    # exit()

    start = time.time()
    if (not program2.contains(program1)):
        print("Text 16.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 16.1 passed in {} seconds".format(end-start))

    start = time.time()
    if (not program1.contains(program2)):
        print("Text 16.2 failed")
        exit()
    else:
        end = time.time()
        print("Test 16.2 passed in {} seconds".format(end-start))

# testing faure queries
def unit_test17():
    T1 = DT_Table(name="T1", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "q":"c2"})
    R = DT_Table(name="R", columns={"c0":"integer_faure", "c1":"integer_faure", "c2":"integer_faure", "condition":"text[]"}, domain={"condition":['0', '1']}, cvars={"x":"condition", "y":"condition", "z":"condition", "q":"c2"})
    database = DT_Database(tables=[R,T1])
    T1.initiateTable(conn)
    R.initiateTable(conn)
    conn.commit()
    cursor = conn.cursor()
    cursor.execute("INSERT INTO R VALUES (1,2,3),(4,5,6)")
    conn.commit()

    p1 = "T1(f, n1, q)[And(q > 3, x+y+z=1)] :- R(f,n1,q)[q > 3],(x+y+z=1)"
    program1 = DT_Program(p1, database)
    program1.execute(conn)

if __name__ == "__main__":
    unit_test1()
    unit_test2()
    # # unit_test3()
    # # unit_test4()
    unit_test5()
    unit_test6()

    # # unit_test7()
    # # unit_test9()

    unit_test8()
    unit_test10()
    unit_test11()
    unit_test12()
    # unit_test13()
    # unit_test14()
    # unit_test15()

    unit_test16()
    unit_test17()




