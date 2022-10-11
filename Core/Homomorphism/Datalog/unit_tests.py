import program as program

if __name__ == "__main__":
    ################################# Example 6 - Containment ##################################
    p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
    p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
    # print(p1)
    # print(p2)
    program1 = program.DT_Program(p1)
    program2 = program.DT_Program(p2)
    if not program1.contains(program2):
        print("Test 1.1 failed")
        exit()
    else:
        print("Test 1.1 passed")

    if program2.contains(program1):
        print("Test 1.2 failed")
        exit()
    else:
        print("Test 1.2 passed")


    ################################ Example 7 - Minimization################################
    p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
    # p2 = "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"
    program1 = program.DT_Program(p1)
    # program2 = DT_Program(p2)
    # print(program1.contains(program2))
    # print(program2.contains(program1))    
    # print(program1)
    program1.minimize()
    if (str(program1) != "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"):
        print("Test 2 failed")
        exit()
    else:
        print("Test 2 passed")

    ########################################## ACL Example:  ######################################
    p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"

    # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,e1)\nR(a2, h3, [h3], 1)[h3 = 20]:- l(a2,h3)[{h3 = 20 and h3 = 30} or h3 = 40], l(a2, e1)"

    program1 = program.DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains=['10', '20'], c_variables=['h3'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])

    program1.minimize()
    if (str(program1) != "R(a2,h3,[h3],1) :- l(a2,h3),l(a2,h4),l(a2,e1)\nR(e1,h3,[a3, x],2) :- R(a3,h3,[x],1),l(a3,e1)\nR(a1,h3,[e1, x, y],3)[h3 == 10] :- R(e1,h3,[x, y],2)[h3 == 10],l(a1,e1)\nR(h2,h3,[a1, x, y, z],4) :- R(a1,h3,[x, y, z],3),l(a1,h2)"):
        print("Test 3 failed")
        exit()
    else:
        print("Test 3 passed")

    ########################################## c-variable data part test  ######################################
    # Tests is_head_contained_faure
    p1 = "R(x, y) :- l(x,y)\nR(x,z) :- R(x,y), l(y,z)"
    program1 = program.DT_Program(p1, {"R":["int4_faure", "int4_faure"], "l":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['x','y','z'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])

    program1.minimize()
    if (str(program1) != "R(x,y) :- l(x,y)\nR(x,z) :- R(x,y),l(y,z)"):
        print("Test 4 failed")
        exit()
    else:
        print("Test 4 passed")
    # =============================== Route Agg
#     p2 = "R(v,d)[d > 10] :- R(u,d)[d > 10], l(v,u)"
# # 
#     program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure"], "l":["int4_faure", "int4_faure"]}, domains=['10', '20', '30'], c_variables=['d'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])
#     program2 = DT_Program(p2, {"R":["int4_faure", "int4_faure"], "l":["int4_faure", "int4_faure"]}, domains=['10', '20', '30'], c_variables=['d'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])
#     # program1 = DT_Program(p1, {"R":["integer", "integer","integer[]", "integer"], "l":["integer", "integer"]})

#     print(program1)
#     program1.minimize()
#     print("After Minimization")
#     print(program1)
#     print("\n\n CHECKING CONTAINMENT")
#     # print(program1.contains(program2))
#     print(program2.contains(program1))