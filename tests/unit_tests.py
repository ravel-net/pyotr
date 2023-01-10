import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Homomorphism.Datalog.program import DT_Program

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
    p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"
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

    
    program1 = DT_Program(p1, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"])
    program2 = DT_Program(p2, {"l":["int4_faure"], "R":["int4_faure"]}, domains={}, c_variables=['x'], reasoning_engine='z3', reasoning_type={}, datatype='int4_faure', simplification_on=False, c_tables=["l","R"])

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


if __name__ == "__main__":
    unit_test1()
    unit_test2()
    unit_test3()
    unit_test4()
    unit_test5()
    unit_test6()
    unit_test7()
    unit_test8()
    # unit_test9()
    unit_test10()




