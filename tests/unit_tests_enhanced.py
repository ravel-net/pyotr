import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Homomorphism.Datalog.program import DT_Program


if __name__ == "__main__":
    # ====================================== Router Aggregation ========================================
    p1 = "R(1,x)[x == 10] :- l(1,2),l(1,3),l(1,4),R(2,x)[x == 10]\nR(1,y)[y == 20] :- l(1,2),l(1,3),l(1,4),R(3,y)[y == 20]\nR(1,x)[x == 30] :- l(1,2),l(1,3),l(1,4),R(4,x)[x == 30]"
    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"R":["int4_faure", "int4_faure"]}, domains={}, c_variables=['x','y'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["l","R"])
    start = time.time()
    program1.minimize(False, False, True)
    print(program1)
    if (str(program1) != "R(1,x)[Or(And(Or(And(r0-3-R_0 == 2,x == 10),And(x == 20,r0-3-R_0 == 3))),And(x == 30,r0-3-R_0 == 4))] :- l(1,2),l(1,3),l(1,4),R(r0-3-R_0,x),(Or(And(r0-3-R_0 == 2,x == 10),And(x == 20,r0-3-R_0 == 3)),Or(And(),And(x == 30,r0-3-R_0 == 4)),Or(And(r0-3-R_0 == 2,x == 10),And(x == 20,r0-3-R_0 == 3)))))"):
        print("Test 1 failed")
        exit()
    else:
        end = time.time()
        print("Test 1 passed in {} seconds".format(end-start))    


    # ====================================== Toy Example ========================================
    p1 = "l(3,4) :- l(w,1), k(2,w,3), l(1,5)\nl(3,4) :- l(1,3), k(2,1,3), l(1,5)"

    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"m":["int4_faure", "int4_faure"], "k":["int4_faure", "int4_faure", "int4_faure"]}, domains={}, c_variables=['a','b','c','d','e','f','g'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["l","k","m"])

    start = time.time()
    program1.minimize(False, False, True)
    print(program1)
    if (str(program1) != "l(3,4)[Or(And(r0-0-l_1 == 1),And(w` == 1,r0-0-l_1 == 3))] :- l(w`,r0-0-l_1),k(2,w`,3),l(1,5),(Or(And(r0-0-l_1 == 1),And(w` == 1,r0-0-l_1 == 3))))"):
        print("Test 2 failed")
        exit()
    else:
        end = time.time()
        print("Test 2 passed in {} seconds".format(end-start))    


    # ====================================== Toy Example 2 ========================================
    p1 = "R(2)[And{y > 0, y < 10}] :- l(y)[And{y > 0, y < 10}]\nR(2)[And{z > -1, z < 5}] :- l(z)[And{z > -1, z < 5}]"

    program1 = DT_Program(p1, {"R":["int4_faure"], "l":["int4_faure"]}, domains={}, c_variables=['y','z'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=False, c_tables=["R", "l"])

    start = time.time()
    program1.minimize(False, False, True)
    print(program1)
    if (str(program1) != "R(2)[Or(And(And(y > 0, y < 10)),And(And(y > -1, y < 5)))] :- l(y),(Or(And(And(y > 0, y < 10)),And(And(y > -1, y < 5)))))"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))