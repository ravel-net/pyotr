import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Homomorphism.Datalog.program import DT_Program


# ====================================== Router Aggregation ========================================
def unit_test1():
    p1 = "R(1,x)[x == 10] :- l(1,2),l(1,3),l(1,4),R(2,x)[x == 10]\nR(1,y)[y == 20] :- l(1,2),l(1,3),l(1,4),R(3,y)[y == 20]\nR(1,x)[x == 30] :- l(1,2),l(1,3),l(1,4),R(4,x)[x == 30]"
    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"R":["int4_faure", "int4_faure"]}, domains={}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["l","R"])
    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "R(1,x)[Or(Or(And(r0-3-R_0 == 2,x == 10),And(x == 20,r0-3-R_0 == 3,True)),And(x == 30,r0-3-R_0 == 4,True))] :- l(1,2),l(1,3),l(1,4),R(r0-3-R_0,x),((Or(And(r0-3-R_0 == 2,x == 10),And(x == 20,r0-3-R_0 == 3,True),And(x == 30,r0-3-R_0 == 4,True)))"):
        print("Test 1 failed")
        exit()
    else:
        end = time.time()
        print("Test 1 passed in {} seconds".format(end-start))  

# ====================================== Toy Example ========================================
def unit_test2():
    p1 = "l(3,4) :- l(w,1), k(2,w,3), l(1,5)\nl(3,4) :- l(1,3), k(2,1,3), l(1,5)"

    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"m":["int4_faure", "int4_faure"], "k":["int4_faure", "int4_faure", "int4_faure"]}, domains={}, c_variables=['a','b','c','d','e','f','g'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=True, c_tables=["l","k","m"])

    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "l(3,4)[Or(r0-0-l_1 == 1,And(w` == 1,r0-0-l_1 == 3))] :- l(w`,r0-0-l_1),k(2,w`,3),l(1,5),(Or(r0-0-l_1 == 1,And(w` == 1,r0-0-l_1 == 3)))"):
        print("Test 2 failed")
        exit()
    else:
        end = time.time()
        print("Test 2 passed in {} seconds".format(end-start))


# ====================================== Toy Example 2 ========================================
def unit_test3():
    p1 = "R(2)[And(y > 0, y < 10)] :- l(y)[And(y > 0, y < 10)]\nR(2)[And(z > -1, z < 5)] :- l(z)[And(z > -1, z < 5)]"

    program1 = DT_Program(p1, {"R":["int4_faure"], "l":["int4_faure"]}, domains={}, c_variables=['y','z'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])

    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)

    if (str(program1) != "R(2)[Or(And(y > 0, y < 10),And(And(y > -1, y < 5),True))] :- l(y),(Or(And(y > 0, y < 10),And(And(y > -1, y < 5),True)))"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))

# ====================================== Wrong variable example ========================================
def unit_test4():
    p1 = "R(x,y)[And(y = 10, y < 20)] :- L(x,y,z)[And(y = 10, y < 20)], Q(z)\nR(x,y) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, {"R":["integer", "int4_faure"], "L":["integer", "int4_faure", "int4_faure"], "Q":["int4_faure"]}, domains={'z':['1', '2'], 'y':['1', '2']}, c_variables=['z','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "L", "Q"])
    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "R(x,y)[And(y == 10, y < 20)] :- L(x,y,z)[And(y == 10, y < 20)],Q(z)\nR(x,y) :- L(x,q,z),Q(z)"):
        print("Test 4 failed")
        exit()
    else:
        end = time.time()
        print("Test 4 passed in {} seconds".format(end-start))

# ====================================== Correct variable example ========================================
def unit_test5():
    p1 = "R(x,y)[And(y = 10, y < 20)] :- L(x,y,z)[And(y = 10, y < 20)], Q(z)\nR(x,q) :- L(x,q,z), Q(z)"
    program1 = DT_Program(p1, {"R":["integer", "int4_faure"], "L":["integer", "int4_faure", "int4_faure"], "Q":["int4_faure"]}, domains={'z':['1', '2'], 'y':['1', '2']}, c_variables=['z','y'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "L", "Q"])
    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "R(x`,y)[Or(And(y == 10, y < 20),True)] :- L(x`,y,z),Q(z),(Or(And(y == 10, y < 20),True))"):
        print("Test 5 failed")
        exit()
    else:
        end = time.time()
        print("Test 5 passed in {} seconds".format(end-start))

# ====================================== Router Aggregation IP ========================================
def unit_test6():
    p1 = "R(1.1.1.1,x)[x == 10.1.1.1/24] :- l(1.1.1.1,2.2.2.2),l(1.1.1.1,3.3.3.3),l(1.1.1.1,4.4.4.4),R(2.2.2.2,x)[x == 10.1.1.1/24]\nR(1.1.1.1,y)[y == 20.1.1.1/24] :- l(1.1.1.1,2.2.2.2),l(1.1.1.1,3.3.3.3),l(1.1.1.1,4.4.4.4),R(3.3.3.3,y)[y == 20.1.1.1/24]\nR(1.1.1.1,x)[x == 30.1.1.1/24] :- l(1.1.1.1,2.2.2.2),l(1.1.1.1,3.3.3.3),l(1.1.1.1,4.4.4.4),R(4.4.4.4,x)[x == 30.1.1.1/24]"
    program1 = DT_Program(p1, {"l":["inet_faure", "inet_faure"],"R":["inet_faure", "inet_faure"]}, domains={}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type={'x':'BitVec', 'y':'BitVec'}, datatype='inet_faure', simplification_on=True, c_tables=["l","R"])
    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "R(1.1.1.1,x)[Or(Or(And(r0-3-R_0 == 2.2.2.2,x == 10.1.1.1/24),And(x == 20.1.1.1/24,r0-3-R_0 == 3.3.3.3,True)),And(x == 30.1.1.1/24,r0-3-R_0 == 4.4.4.4,True))] :- l(1.1.1.1,2.2.2.2),l(1.1.1.1,3.3.3.3),l(1.1.1.1,4.4.4.4),R(r0-3-R_0,x),((Or(And(r0-3-R_0 == 2.2.2.2,x == 10.1.1.1/24),And(x == 20.1.1.1/24,r0-3-R_0 == 3.3.3.3,True),And(x == 30.1.1.1/24,r0-3-R_0 == 4.4.4.4,True)))"):
        print("Test 6 failed")
        exit()
    else:
        end = time.time()
        print("Test 6 passed in {} seconds".format(end-start))

# ====================================== Router Aggregation IP + Int ========================================
def unit_test7():
    p1 = "R(1,x)[x == 10.1.1.1/24] :- l(1,2),l(1,3),l(1,4),R(2,x)[x == 10.1.1.1/24]\nR(1,y)[y == 20.1.1.1/24] :- l(1,2),l(1,3),l(1,4),R(3,y)[y == 20.1.1.1/24]\nR(1,x)[x == 30.1.1.1/24] :- l(1,2),l(1,3),l(1,4),R(4,x)[x == 30.1.1.1/24]"
    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"R":["int4_faure", "inet_faure"]}, domains={}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type={'x':'BitVec', 'y':'BitVec'}, datatype='inet_faure', simplification_on=True, c_tables=["l","R"])
    start = time.time()
    program1.minimize(False, False, "Const")
    print(program1)
    if (str(program1) != "R(1,x)[Or(Or(And(r0-3-R_0 == 2,x == 10.1.1.1/24),And(x == 20.1.1.1/24,r0-3-R_0 == 3,True)),And(x == 30.1.1.1/24,r0-3-R_0 == 4,True))] :- l(1,2),l(1,3),l(1,4),R(r0-3-R_0,x),((Or(And(r0-3-R_0 == 2,x == 10.1.1.1/24),And(x == 20.1.1.1/24,r0-3-R_0 == 3,True),And(x == 30.1.1.1/24,r0-3-R_0 == 4,True)))"):
        print("Test 7 failed")
        exit()
    else:
        end = time.time()
        print("Test 7 passed in {} seconds".format(end-start))

def unit_test8():
    p1 = "R(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
    program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains={'h3':['10', '20']}, c_variables=['h3'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])
    start = time.time()
    program1.minimize(False, False, "Const")
    end = time.time()
    print(program1)
    if (str(program1) != "R(h1`,h3,[a1`, x`, y`, z`],4)[True] :- R(a1`,h3,[x`, y`, z`],3),l(a1`,h1`),(True)"):
        print("Test 8 failed")
        exit()
    else:
        end = time.time()
        print("Test 8 passed in {} seconds".format(end-start))

if __name__ == "__main__":
    unit_test1()
    unit_test2()
    unit_test3()
    unit_test4()
    unit_test5()
    unit_test6()
    unit_test7()
    unit_test8()