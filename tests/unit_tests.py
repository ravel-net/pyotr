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
from tabulate import tabulate
from copy import deepcopy

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
    p1 = "R(a3, h3, [a, h3], 1)[h3 == 10] :- l(a3,h3)[h3 == 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 == 10] :- R(e1, h3, [x, y], 2)[h3 == 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    # p1 = "R(a3, h3, [a, h3], 1)[h3 == 10] :- l(a3,h3)[h3 == 10], l(a,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"

    # R = DT_Table(name="R", columns={"source":"integer_faure", "destination":"integer_faure", "path":"integer_faure[]", "hops":"integer_faure","condition":"text[]"}, domain={"destination":[10,20]}, cvars={"h3":"destination"})
    R = DT_Table(name="R", columns={"source":"integer_faure", "destination":"integer_faure", "path":"integer_faure[]", "hops":"integer_faure"}, domain={"destination":[10,20]}, cvars={"h3":"destination"})

    l = DT_Table(name="l", columns={"node1":"integer_faure", "node2":"integer_faure"}, cvars={"h3":"node2"})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[R,l])
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.minimize()
    print(program1)
    database.delete(conn)
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
    p1 = "R(x,y)[And(y == 10, y < 20)] :- L(x,y,z)[And(y == 10, y < 20)], Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
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
    if (str(program1) != "R(4323,D,3356)[And(And(D != '216.186.192.0/22', D != '64.153.32.0/20'))] :- l(4323,b,D),l(b,c,D)[And(D != '216.186.192.0/22', D != '64.153.32.0/20')],l(c,e,D),l(e,3356,D)"):
        print("Text 12.1 failed")
        database.delete(conn)
        exit()
    else:
        end = time.time()
        print("Test 12.1 passed in {} seconds".format(end-start))
    database.delete(conn)

# execution with array concatination
# S = 100
# A = 1, B = 2, T = 3
# D = 400
# host1 = 401
# x1 = -1, x2 = -2, x3 = -3
# y1 = -10, y2 = -20, y3 = -30
def unit_test13():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    V = DT_Table(name="V", columns={"violation":"integer"})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"x1":"header","x2":"header","x3":"header","y1":"next_hop","y2":"next_hop","y3":"next_hop"}, domain={"next_hop":[100,1,2,3,400,401],"node":[100,1,2,3,400,401]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-10':"y1",'-20':"y2",'-30':"y3",'-1':"x1",'-2':"x2",'-3':"x3",'-100':"p"})

    p1 = "R(10, 100, n, ['100', n]) :- F(10, 100, n)"
    p2 = "R(10, 100, n, p || [n]) :- R(10, 100, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, 100, 400, p)[And(1 != p, 400 == p)]"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    sql = "insert into F values ('-1', 100, '-10', '{\"Or(y1 == 1, y1 == 2)\"}'), ('-2', 1, '-20', '{\"Or(y2 == 100, y2 == 3)\"}'), ('-3', 2, '-30', '{\"Or(y3 == 100, y3 == 3)\"}'), ('10', 3, 400, '{}'), ('10', 400, 401, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    
    start = time.time()
    program1.executeonce(conn)
    program2.execute(conn)
    end = time.time()
    cursor.execute("select * from V")
    V_values = cursor.fetchall()
    if len(V_values) > 0 and len(V_values[0]) > 0 and V_values[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

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

    p1 = "T1(f, n1, n2)[x+y+z=1] :- R(f,n1,n2),(x+y+z=1)"
    program1 = DT_Program(p1, database)
    start = time.time()
    program1.execute(conn)
    end = time.time()
    cursor.execute("select * from T1")
    T1_data = cursor.fetchall()
    if len(T1_data) == 1 and T1_data[0] == (4, 5, 6, ['And(6 > 3)', 'x+y+z=1']):
        print("Test 17 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 17 failed in {} seconds".format(end-start))
        database.delete(conn)

# # ordering example 1
# v = 1, u = 2, x = 3, y = 4, d = 5
# y1 = -1, y2 = -2, y3 = -3, y3 = -4, y5 = -5
def unit_test18():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    V = DT_Table(name="V", columns={"violation":"integer", "path":"integer_faure[]"}, cvars={"p":"path"})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"y4":"next_hop","y5":"next_hop","y1":"next_hop","y2":"next_hop","y3":"next_hop"}, domain={"next_hop":[5,1,2,3,4,401],"node":[5,1,2,3,4,401]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"y1",'-2':"y2",'-3':"y3",'-4':"y4",'-5':"y5"})
    
    p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nV(1, p) :- R(10, X, n2, p), F(10, n2, n)[n == p]\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)"
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)\nV(1, p) :- R(10, 100, 400, p)[p[array_upper(p, 1)] == p]"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    program1.execute(conn)

    sql = "insert into F values (10, 1, 3, '{}'), (10, 2, -2, '{\"Or(y2 == 1, y2 == 3)\"}'), (10, 3, -3, '{\"Or(y3 == 5, y3 == 4)\"}'), (10, 4, -4, '{\"Or(y4 == 3, y4 == 5)\"}'), (10, 5, 401, '{}')"
    input()

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program1.executeonce(conn)
    conn.commit()
    input()
    end = time.time()
    database.delete(conn)
    exit()
    cursor.execute("select * from V")
    if cursor.fetchall()[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

# ordering example 2
# v = 1, u = 2, w = 3, d = 4
# y1 = -1, y2 = -2, y3 = -3, y3 = -4, y5 = -5
def unit_test19():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"})

    V = DT_Table(name="V", columns={"violation":"integer"})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"C4":"next_hop","C5":"next_hop","C1":"next_hop","C2":"next_hop","C3":"next_hop"}, domain={"next_hop":[1,2,3,4,401],"node":[1,2,3,4,401]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"C1",'-2':"C2",'-3':"C3",'-4':"C4",'-5':"C5"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p), F(10, n2, n)"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    sql = "insert into F values (10, 1, -1, '{\"Or(C1 == 4, C1 == 3)\"}'), (10, 2, -2, '{\"Or(C2 == 4, C2 == 1)\"}'), (10, 3, -3, '{\"Or(C3 == 2, C3 == 4)\"}'),(10, 4, 401, '{}')"
    input()

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program1.executeonce(conn)
    conn.commit()
    input()
    end = time.time()
    database.delete(conn)
    exit()
    cursor.execute("select * from V")
    if cursor.fetchall()[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

# Anduo's example 
# X = 1, W = 2, A = 3, B = 4, Y = 5, E = 6, C = 7
# alpha = -1, beta = -2, gamma = -3, t_one = -4, t_two = -5
def unit_test20():
    R = DT_Table(name="R", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"source":[1,2,3,4,5,6,7],"dest":[1,2,3,4,5,6,7]})

    V = DT_Table(name="V", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"}, domain={"source":[1,2,3,4,5,6,7],"dest":[1,2,3,4,5,6,7]})

    F = DT_Table(name="F", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"next_hop", "beta":"next_hop","gamma":"next_hop","t_one":"header","t_two":"header"}, domain={"next_hop":[1,2,3,4,5,6,7],"node":[1,2,3,4,5,6,7], "header":[10,2,0,1]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F,R,V], cVarMapping = {'-1':"alpha",'-2':"beta",'-3':"gamma",'-4':"t_one",'-5':"t_two",'-100':"p"})

    p1 = "R(10, S, n, [S, n]) :- F(10, S, n)"
    p2 = "V(10, 1, n, p || [n]) :- R(10, 1, n2, p)[And(2 != p, 5 != p, n != p, n == 7)], F(10, n2, n)\nR(10, S, n, p || [n]) :- R(10, S, n2, p)[n != p], F(10, n2, n)"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []
# X = 1, W = 2, A = 3, B = 4, Y = 5, E = 6, C = 7
# alpha = -1, u = -2, t_one = -3, t_two = -4
    
    sql = "insert into F values (10, 1, '-1', '{\"Or(alpha == 3, alpha == 2)\"}'), (10, 2, '-2', '{\"Or(beta == 3, beta == 4)\"}'), (10, 3, '-3', '{\"Or(gamma == 2, gamma == 4)\"}'), (10, 4, 6, '{\"And(t_one == 0, And(alpha == 3, beta == 3, gamma == 4))\"}'), (10, 4, 5, '{\"t_one != 0\"}'), (10, 6, 7, '{\"t_two == 0\"}'), (10, 6, 5, '{\"And(t_two != 3, And(alpha == 3, beta == 3, gamma == 4))\"}'), (10, 5, 7, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    input()
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program2.execute(conn)
    end = time.time()
    cursor.execute("select * from V")
    V_values = cursor.fetchall()
    printTable("V", database, {1:'X',2:'W',3:'A',4:'B',5:'Y',6:'E',7:'C'})
    input()
    # if len(V_values) > 0 and len(V_values[0]) > 0 and V_values[0][0] == 1:
    #     print("Test 13 passed in {} seconds".format(end-start))
    #     database.delete(conn)
    # else:
    #     print("Test 13 failed in {} seconds".format(end-start))
    #     database.delete(conn)
    #     exit()


def replaceVal(val, mapping):
    if val in mapping:
        return mapping[val]
    elif str(val) in mapping:
        return mapping[str(val)]
    elif type(val) == str:
        for replaceable in mapping:
            if str(replaceable) in val:
                val = val.replace(str(replaceable), mapping[replaceable])
        return val
    else:
        return val
    
# move this to table class
def printTable(tableName, db, nodeIntMappingReverse, condition = None):
    cursor = conn.cursor()
    # cursor.execute("SELECT * from {} where source = 1 and dest = 7".format(tableName))
    if condition:
        cursor.execute("SELECT * from {} where {}".format(tableName, condition))
    else:
        cursor.execute("SELECT * from {}".format(tableName))

    table = cursor.fetchall()
    newTable = []
    mapping = deepcopy(nodeIntMappingReverse)
    mapping.update(db.cVarMapping)
    for row in table:
        newRow = []
        for colm in row:
            if type(colm) == list:
                colmArray = []
                for item in colm:
                    colmArray.append(replaceVal(item, mapping))
                newRow.append(colmArray)
            else:
                newRow.append(replaceVal(colm, mapping))
        newTable.append(newRow)
    cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_schema = 'public' AND table_name = '{}'".format(tableName.lower()))
    headers = cursor.fetchall()
    headerInArray = []
    for colm in headers:
        headerInArray.append(colm[0])
    print(tabulate(newTable, headers=headerInArray))


# ordering example 3
# s = 11, v1 = 22, v2 = 33, v3 = 44, d = 55
# C1 = -1, C2 = -2, C3 = -3, C4 = -4, C5 = -5
# https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=8500100&casa_token=BnSkzZ8MHcgAAAAA:BdUDVVwmYi_p-szvbrSQKISQPPQT6FoTXlgclcGZmLDluKkaSevytPYSMA2NnlB5BO2vEfjk7Bc
def unit_test21():
    R1 = DT_Table(name="R1", columns={"header":"integer_faure", "source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"})

    V1 = DT_Table(name="V1", columns={"header":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F1 = DT_Table(name="F1", columns={"header":"integer_faure", "node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"v1_next":"next_hop","v2_next":"next_hop","v3_next":"next_hop"}, domain={"next_hop":[11,22,33,44,55],"node":[11,22,33,44,55]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F1,R1,V1], cVarMapping = {'-2':"v1_next",'-3':"v2_next",'-4':"v3_next"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p1 = "R1(10, X, n, [X, n]) :- F1(10, X, n)"
    p2 = "V1(10, p) :- R1(10, X, n2, p), F1(10, n2, n)[n != p]\nR1(10, X, n, p || [n]) :- R1(10, X, n2, p), F1(10, n2, n)[n != p]"

    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    nodeMapping = {'11':"s","22":"v1","33":"v2","44":"v3","55":"d"}
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

    sql = "insert into F1 values (10, 11, 22, '{}'),(10, 22, -2, '{\"Or(v1_next == 33, v1_next == 55)\"}'),(10, 33, -3, '{\"Or(v2_next == 44, v2_next == 22)\"}'),(10, 44, -4, '{\"Or(v3_next == 55, v3_next == 33)\"}')"

    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()
    printTable("F1",database,nodeMapping)
    input()
    
    start = time.time()
    program1.executeonce(conn)
    conn.commit()
    input()
    program2.execute(conn)
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    printTable("V1",database,nodeMapping)
    # input()
    database.delete(conn)
    exit()
    cursor.execute("select * from V")
    if cursor.fetchall()[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

# ordering example 4
# X = 11, W = 22, A = 33, E = 44, Y = 55, B = 66, C = 77, D = 88
# alpha = -1, beta = -2, u = -11, gamma = -3, sigma = -4, v = -22, t_one = -101, t_two = -201, t_three = -301, t_four = -401, l = -1111
# Anduo's email on July 29 with 3 admins
def unit_test22():
    M1 = DT_Table(name="M1", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M2 = DT_Table(name="M2", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M12 = DT_Table(name="M12", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M23 = DT_Table(name="M23", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})
    M123 = DT_Table(name="M123", columns={"node":"integer","condition":"text[]"}, domain={"node":[11,22,33,44,55,66,77,88]})

    R_admins = DT_Table(name="R_admins", columns={"source":"integer_faure", "dest":"integer_faure","path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path", "alpha":"source", "beta":"source","gamma":"source","sigma":"source", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"source":[11,22,33,44,55,66,77,88],"dest":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    V_admins = DT_Table(name="V_admins", columns={"path":"integer_faure[]","condition":"text[]"}, cvars={"p":"path"})

    F1 = DT_Table(name="F1", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F2 = DT_Table(name="F2", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F3 = DT_Table(name="F3", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    F_admins = DT_Table(name="F_admins", columns={"node":"integer_faure", "next_hop":"integer_faure","condition":"text[]"}, cvars={"alpha":"node", "beta":"node","gamma":"node","sigma":"node", "u":"condition", "v":"condition", "t_one":"condition", "t_two":"condition", "t_three":"condition", "t_four":"condition", "l":"condition"}, domain={"node":[11,22,33,44,55,66,77,88],"next_hop":[11,22,33,44,55,66,77,88], "condition":[0,1]})

    # database = DT_Database(tables=[F,R], cVarMapping = {"y1":-10,"y2":-20,"y3":-30,"x1":-1,"x2":-2,"x3":-1})
    database = DT_Database(tables=[F1,F2,F3,M1,M2,M12,M23,M123,V_admins, R_admins, F_admins], cVarMapping = {'-1':"alpha",'-2':"beta",'-3':"gamma",'-4':"sigma",'-4=101':"t_one",'-201':"t_two",'-1123':"p",'-301':"t_three",'-401':"t_four",'-1111':"l"})
    
    # p1 = "R(10, X, n, [X, n]) :- F(10, X, n)\nR(10, X, n, p || [n]) :- R(10, X, n2, p)[n != p], F(10, n2, n)\nV(1) :- R(10, X, 5, p)[And(1 != p, 400 == p)]"
    p0 = "F_admins(x,y) :- F1(x,y), M1(x)\nF_admins(x,y) :- F2(x,y), M2(x)\nF_admins(x,y) :- F1(x,y), F2(x,y), M12(x)\nF_admins(x,y) :- F2(x,y), F3(x,y), M23(x)\nF_admins(x,y) :- F1(x,y), F2(x,y), F3(x,y), M123(x)"

    p1 = "R_admins(11, n, [11, n]) :- F_admins(11, n)"
    p2 = "R_admins(11, n, p || [n]) :- R_admins(11, n2, p), F_admins(n2, n)[n != p]\nV_admins(p) :- R_admins(11, n2, p)[And(44 == p, 55 == p, 88 == p)]"
    # p2 = "V_admins(p) :- R_admins(11, n2, p), F_admins(n2, n)[n == p]\nR_admins(11, n, p || [n]) :- R_admins(11, n2, p), F_admins(n2, n)[n != p]"

    program0 = DT_Program(p0, database=database, optimizations={"simplification_on":True})
    program1 = DT_Program(p1, database=database, optimizations={"simplification_on":True})
    program2 = DT_Program(p2, database=database, optimizations={"simplification_on":True})
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
    nodeMapping = {'11':"X","22":"W","33":"A","44":"E","55":"Y","66":"B","77":"C","88":"D"}
    database.delete(conn)
    database.initiateDB(conn)
    conn.commit()
    variableConstants = []

# X = 11, W = 22, A = 33, E = 44, Y = 55, B = 66, C = 77, D = 88
# alpha = -1, beta = -2, u = -11, gamma = -3, sigma = -4, v = -22, t_one = -101, t_two = -201, t_three = -301, t_four = -401, l = -1111
# Anduo's email on July 29 with 3 admins

    # Correction: E goes to Y or B
    sql = "insert into F1 values (33, -1, '{\"Or(alpha == 55, alpha == 22)\"}'),(55, -2, '{\"Or(beta == 77, beta == 44)\"}'),(11, 33, '{\"And(And(alpha == 55, beta == 77),t_one == 0)\"}'),(11, 22, '{\"t_one != 0\"}'),(22,33,'{\"And(And(alpha == 55, beta == 77),t_two == 0)\"}'),(22,44,'{\"t_two != 0\"}'),(44,55,'{\"And(And(alpha == 55, beta == 77),t_three == 0)\"}'),(44,66,'{\"t_three != 0\"}')"
    cursor = conn.cursor()
    cursor.execute(sql)
    conn.commit()

    sql = "insert into F2 values (44,-3,'{\"Or(gamma == 55, gamma == 66)\"}'), (55,-4,'{\"Or(sigma == 77, sigma == 44)\"}'), (66,44,'{\"And(And(gamma == 55, sigma == 77),t_four == 0)\"}'), (66,77,'{\"t_four != 0\"}'), (77,88,'{}')"
    # sql = "insert into F2 values (44,-3,'{\"Or(gamma == 55, gamma == 66)\"}'), (55,-4,'{\"Or(sigma == 77, sigma == 44)\"}'), (66,44,'{}'), (77,88,'{}')" # B always goes to E
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into F3 values (66, 77, '{\"l == 1\"}'),(66, 44, '{\"l == 0\"}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M1 values (11, '{}'),(22, '{}'),(33, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M12 values (44, '{}'),(55, '{}')"    
    cursor = conn.cursor()
    cursor.execute(sql)

    # sql = "insert into M23 values (44, '{}'),(66, '{}'),(77, '{}')"
    # Corrections: M23 only has B
    sql = "insert into M23 values (66, '{}')"
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M123 values (44, '{}')"  
    cursor = conn.cursor()
    cursor.execute(sql)

    sql = "insert into M2 values (77, '{}')"  
    cursor = conn.cursor()
    cursor.execute(sql)

    printTable("F1", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("F2", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("F3", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M1", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M12", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M23", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M123", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    printTable("M2", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    conn.commit()
    input()

    start = time.time()
    program0.execute(conn)
    program0.reasoning_tool.simplification("F_admins", conn)
    conn.commit()
    printTable("F_admins", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'})
    input()
    program1.executeonce(conn)
    printTable("R_admins", db=database, nodeIntMappingReverse={11:'X',22:'W',33:'A',44:'E',55:'Y',66:'B',77:'C',88:'D'}, condition="dest = 88")

    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    # printTable("V",database,nodeMapping)
    # input()
    # program2.executeonce(conn)
    # conn.commit()
    program2.execute(conn, violationTables=[V_admins])
    conn.commit()
    printTable("V_admins",database,nodeMapping)
    printTable("R_admins",database,nodeMapping)
    # input()
    input()
    database.delete(conn)
    exit()
    cursor.execute("select * from V")
    if cursor.fetchall()[0][0] == 1:
        print("Test 13 passed in {} seconds".format(end-start))
        database.delete(conn)
    else:
        print("Test 13 failed in {} seconds".format(end-start))
        database.delete(conn)
        exit()

if __name__ == "__main__":
    unit_test1()
    unit_test2()
    unit_test3()
    # # unit_test4()
    unit_test5()
    unit_test6()
    # # unit_test7()
    unit_test8()
    # # unit_test9()
    unit_test10()
    unit_test11()
    unit_test12() 
    # unit_test13()
    # # unit_test14()
    # # unit_test15()
    unit_test16()
    # unit_test17()
    # unit_test18()
    # unit_test19()
    # unit_test20()