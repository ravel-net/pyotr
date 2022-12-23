import time

import sys
from os.path import dirname, abspath
root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)
from Core.Homomorphism.Datalog.program import DT_Program
from utils.converter.recursion_converter import RecursiveConverter



def unit_test1():
    """
    R(x, y) :- l(x,y)
    R(x,z) :- R(x,y), l(y,z)
    =============================
    WITH RECURSIVE 
    temp_R1 AS (
        select t0.c0 as c0, t0.c1 as c1 
        from l t0 
        UNION 
        select t0.c0 as c0, t1.c1 as c1 
        from temp_R1 t0, l t1 
        where t0.c1 = t1.c0
    ) 
    insert into R (select * from temp_R1)
    """
    p1 = "R(x, y) :- l(x,y)\nR(x,z) :- R(x,y), l(y,z)"
    program1 = DT_Program(p1)
    print(RecursiveConverter(program1).program_sqls)

def unit_test2():
    """
    R(x4, x5) :- L(x4, x5)
    R(x2, x5) :- R(x4, x5), L(x2, x4)
    R(x3, x5) :- R(x4, x5), L(x3, x4)
    R(x1, x5) :- R(x2, x5), L(x1, x2)
    R(x1, x5) :- R(x3, x5), L(x1, x3)
    ======================================
    WITH RECURSIVE 
    temp_R1 AS (
        select t0.c0 as c0, t0.c1 as c1 
        from L t0 
        UNION 
        select t1.c0 as c0, t0.c1 as c1 
        from temp_R1 t0, L t1 
        where t0.c0 = t1.c1
        ), 
    temp_R2 AS (
        select * from temp_R1 
        UNION 
        select t1.c0 as c0, t0.c1 as c1 
        from temp_R2 t0, L t1 
        where t0.c0 = t1.c1
        ), 
    temp_R3 AS (
        select * from temp_R2 
        UNION 
        select t1.c0 as c0, t0.c1 as c1 
        from temp_R3 t0, L t1 
        where t0.c0 = t1.c1
        ), 
    temp_R4 AS (
        select * from temp_R3 
        UNION 
        select t1.c0 as c0, t0.c1 as c1 
        from temp_R4 t0, L t1 
        where t0.c0 = t1.c1
        ) 
    insert into R (
        select * from temp_R1 UNION 
        select * from temp_R2 UNION 
        select * from temp_R3 UNION 
        select * from temp_R4)
    """
    p1 = "R(x4, x5) :- L(x4, x5)\nR(x2, x5) :- R(x4, x5), L(x2, x4)\nR(x3, x5) :- R(x4, x5), L(x3, x4)\nR(x1, x5) :- R(x2, x5), L(x1, x2)\nR(x1, x5) :- R(x3, x5), L(x1, x3)"
    program1 = DT_Program(p1)
    print(RecursiveConverter(program1).program_sqls)

def unit_test3():
    """
    test program with no base rules

    G(x,y,z) :- G(x,w,z), A(w,y), A(w,z), A(z,z), A(z,y)

    WITH RECURSIVE 
    temp_G1 AS (
        select t0.c0 as c0, 'y' as c1, t0.c2 as c2 from G t0 
        UNION 
        select t0.c0 as c0, t1.c1 as c1, t0.c2 as c2 
        from temp_G1 t0, A t1, A t2, A t3, A t4 
        where t0.c1 = t1.c0 and t1.c0 = t2.c0 and 
            t0.c2 = t2.c1 and t2.c1 = t3.c0 and 
            t3.c0 = t3.c1 and t3.c1 = t4.c0 and 
            t1.c1 = t4.c1
    ) 
    insert into G (select * from temp_G1)
    
    """
    p1 = "G(x,y,z) :- G(x,w,z), A(w,y), A(w,z), A(z,z), A(z,y)"
    program1 = DT_Program(p1)
    print(RecursiveConverter(program1).program_sqls)

def unit_test4():
    """
    R(x, y) :- L(x, y) 
    T(x, y) :- R(x, z), L(z, y)
    T(x, y) :- T(x, z), R(z, y) 

    WITH temp_R1 as (
        select t0.c0 as c0, t0.c1 as c1 from L t0
    ) 
    insert into R (select * from temp_R1)

    WITH RECURSIVE 
    temp_T1 AS (
        select t0.c0 as c0, t1.c1 as c1 
        from R t0, L t1 
        where t0.c1 = t1.c0 
        UNION 
        select t0.c0 as c0, t1.c1 as c1 
        from temp_T1 t0, R t1 
        where t0.c1 = t1.c0
    ) 
    insert into T (select * from temp_T1)
    """
    p1 = "R(x, y) :- L(x, y)\nT(x, y) :- R(x, z), L(z, y)\nT(x, y) :- T(x, z), R(z, y)"
    program1 = DT_Program(p1)
    print(RecursiveConverter(program1).program_sqls)

def unit_test5():
    """
    R(x4, x5, 1) :- L(x4, x5)
    R(x2, x5, 2) :- R(x4, x5, 1), L(x2, x4)
    R(x3, x5, 2) :- R(x4, x5, 1), L(x3, x4)
    R(x1, x5, 3) :- R(x2, x5, 2), L(x1, x2)
    R(x1, x5, 3) :- R(x3, x5, 2), L(x1, x3)
    ==========================================
    WITH RECURSIVE 
    temp_R1 AS (
        select t0.c0 as c0, t0.c1 as c1, 1 as c2 from L t0 
        UNION 
        select t1.c0 as c0, t0.c1 as c1, 2 as c2 
        from temp_R1 t0, L t1 
        where t0.c2 = 1 and t0.c0 = t1.c1
    ), temp_R2 AS (
        select * from temp_R1 
        UNION 
        select t1.c0 as c0, t0.c1 as c1, 2 as c2 
        from temp_R2 t0, L t1 
        where t0.c2 = 1 and t0.c0 = t1.c1
    ), temp_R3 AS (
        select * from temp_R2 
        UNION 
        select t1.c0 as c0, t0.c1 as c1, 3 as c2 
        from temp_R3 t0, L t1 
        where t0.c2 = 2 and t0.c0 = t1.c1
    ), temp_R4 AS (
        select * from temp_R3 
        UNION 
        select t1.c0 as c0, t0.c1 as c1, 3 as c2 
        from temp_R4 t0, L t1 
        where t0.c2 = 2 and t0.c0 = t1.c1
    ) 
    insert into R (
        select * from temp_R1 UNION 
        select * from temp_R2 UNION 
        select * from temp_R3 UNION 
        select * from temp_R4)
    """
    p1 = "R(x4, x5, 1) :- L(x4, x5)\nR(x2, x5, 2) :- R(x4, x5, 1), L(x2, x4)\nR(x3, x5, 2) :- R(x4, x5, 1), L(x3, x4)\nR(x1, x5, 3) :- R(x2, x5, 2), L(x1, x2)\nR(x1, x5, 3) :- R(x3, x5, 2), L(x1, x3)"
    program1 = DT_Program(p1)
    print(RecursiveConverter(program1).program_sqls)

def unit_test6():
    # ====================================== Example 6 - Containment ========================================
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

def unit_test7():
    # ===================================== Example 7 - Minimization ========================================
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

def unit_test8():
    """
    R(x4, x5, 1) :- L(x4, x5)
    R(x2, x5, 2) :- R(x4, x5, 1), L(x2, x4)
    R(x3, x5, 2) :- R(x4, x5, 1), L(x3, x4)
    R(x1, x5, 3) :- R(x2, x5, 2), L(x1, x2)
    R(x1, x5, 3) :- R(x3, x5, 2), L(x1, x3)
    """
    p1 = "R(x4, x5, 1) :- L(x4, x5)\nR(x2, x5, 2) :- R(x4, x5, 1), L(x2, x4)\nR(x3, x5, 2) :- R(x4, x5, 1), L(x3, x4)\nR(x1, x5, 3) :- R(x2, x5, 2), L(x1, x2)\nR(x1, x5, 3) :- R(x3, x5, 2), L(x1, x3)"
    program1 = DT_Program(p1)

    start = time.time()
    program1.minimize()
    print(program1)
    if (str(program1) != "R(x4,x5,1) :- L(x4,x5)\nR(x3,x5,2) :- R(x4,x5,1),L(x3,x4)\nR(x1,x5,3) :- R(x3,x5,2),L(x1,x3)"):
        print("Test 3 failed")
        exit()
    else:
        end = time.time()
        print("Test 3 passed in {} seconds".format(end-start))

def unit_test9():
    """
    P1:
    R(x, y) :- L(x, y)
    R(x, y) :- R(x, z), L(z, y)
    P2:
    R(x, y) :- R(x, z), L(z, y)

    I = {R(x0, z0), L(z0, y0)}

    incorrect
    WITH RECURSIVE temp_R1 AS (
        select t0.c0 as c0, t0.c1 as c1 from L t0 
        UNION 
        select t0.c0 as c0, t1.c1 as c1 
        from temp_R1 t0, L t1 
        where t0.c1 = t1.c0
    )
    insert into R (select * from temp_R1)

    I = {R(x0, z0), L(z0, y0), R(z0, y0)}

    WITH RECURSIVE temp_R1 AS (
        select t0.c0 as c0, t0.c1 as c1 from L t0 
        UNION
        values (100, 101)
        UNION 
        select t0.c0 as c0, t1.c1 as c1 
        from temp_R1 t0, L t1 
        where t0.c1 = t1.c0
    )
    select * from temp_R1;
    insert into R (select * from temp_R1)

    WITH RECURSIVE temp_R1(c0, c1) AS (
        select * from (
            values (100, 101)
            UNION
            select t0.c0 as c0, t0.c1 as c1 from L t0 
        ) as foo
        UNION 
        select t0.c0 as c0, t1.c1 as c1 
        from temp_R1 t0, L t1 
        where t0.c1 = t1.c0
    )
    select * from temp_R1;
    """

    p1 = "R(x, y) :- L(x, y)\nR(x, y) :- R(x, z), L(z, y)"
    p2 = "R(x, y) :- R(x, z), L(z, y)"
    program1 = DT_Program(p1)
    program2 = DT_Program(p2)

    start = time.time()
    if not program1.contains(program2):
        print("Test 4.1 failed")
        exit()
    else:
        end = time.time()
        print("Test 4.1 passed in {} seconds".format(end-start))

    # start = time.time()
    # if program2.contains(program1):
    #     print("Test 4.2 failed")
    #     exit()
    # else:
    #     end = time.time()
    #     print("Test 4.2 passed in {} seconds".format(end-start))

if __name__ == "__main__":
    # unit_test1()
    # unit_test2()
    # unit_test3()
    # unit_test4()
    # unit_test5()
    # unit_test6()
    # unit_test7()
    # unit_test8()
    unit_test9()
    
