import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

from Core.Homomorphism.Datalog.program import DT_Program

"""
example datalog program
# routing for hosts
r1: R(h1, xd, h1 o p) :- R(e1, xd, p), link(h1, e1), link(e1, a1), link(e1, a2), p = e1 o a1 o p'
r2: R(h1, xd, h1 o p) :- R(e1, xd, p), link(h1, e1), link(e1, a1), link(e1, a2), p = e1 o a2 o p'
# routing for edge switches
r3: R(e1, xd, e1 o p1) :- R(a1, xd, p1), R(a2, xd, p2), R(h2, xd, p3), link(e1, a1), link(e1, a2), link(e1, h2)
r4: R(e1, xd, e1 o p2) :- R(a1, xd, p1), R(a2, xd, p2), R(h2, xd, p3), link(e1, a1), link(e1, a2), link(e1, h2)
r5: R(e1, xd, e1 o p3) :- R(a1, xd, p1), R(a2, xd, p2), R(h2, xd, p3), link(e1, a1), link(e1, a2), link(e1, h2)
# routing for aggregation switches
r6: R(a1, xd, a1 o p1) :- R(c1, xd, p1), R(c2, xd, p2), R(e2, xd, p3), link(a1, e1), link(a1, c1), link(a1, c2)
r7: R(a1, xd, a1 o p2) :- R(c1, xd, p1), R(c2, xd, p2), R(e2, xd, p3), link(a1, e1), link(a1, c1), link(a1, c2)
r8: R(a1, xd, a1 o p3) :- R(c1, xd, p1), R(c2, xd, p2), R(e2, xd, p3), link(a1, e1), link(a1, c1), link(a1, c2)
# routing for core switches
r9: R(c1, xd, c1 o p1) :- R(a1, xd, p1), R(a3, xd, p2), R(a5, xd, p3), R(a7, xd, p4), link(c1, a1), link(c1, a3), link(c1, a5), link(c1, a7), c1 \not_in p1
r10: R(c1, xd, c1 o p2) :- R(a1, xd, p1), R(a3, xd, p2), R(a5, xd, p3), R(a7, xd, p4), link(c1, a1), link(c1, a3), link(c1, a5), link(c1, a7), c1 \not_in p2
r11: R(c1, xd, c1 o p3) :- R(a1, xd, p1), R(a3, xd, p2), R(a5, xd, p3), R(a7, xd, p4), link(c1, a1), link(c1, a3), link(c1, a5), link(c1, a7), c1 \not_in p3
r12: R(c1, xd, c1 o p4) :- R(a1, xd, p1), R(a3, xd, p2), R(a5, xd, p3), R(a7, xd, p4), link(c1, a1), link(c1, a3), link(c1, a5), link(c1, a7), c1 \not_in p4
"""

def read_program(file='./toy_program.txt'):
    rules = []
    with open(file, 'r') as f:
        for line in f:
            rule = line.strip()
            if rule.startswith('//') or rule.startswith('#') or len(rule) == 0:
                continue
            rules.append(rule)
    
    f.close()

    program = "\n".join(rules)
    return program

def minimize_toy(program):
    dt_program = DT_Program(program)
    print("Before minimizing...")
    print(dt_program)

    dt_program.minimize()

    print("After minimizing...")
    print(dt_program)

if __name__ == '__main__':
    # p_program = read_program('./P_.txt')
    # P = DT_Program(p_program, {"R":["integer", "integer","integer[]"]})
    # r_program = read_program('./R.txt')
    # R = DT_Program(r_program, {"R":["integer", "integer","integer[]"]})
    # print(P.contains(R))

    # p_program = read_program('./P.txt')
    # P = DT_Program(p_program, {"R":["int4_faure", "int4_faure"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d1', 'd2'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True)
    # r_program = read_program('./Q.txt')
    # Q = DT_Program(r_program, {"R":["int4_faure", "int4_faure"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True)
    # res1 = P.contains(Q)
    # print("P contains Q:", res1)
    # res2 = Q.contains(P)
    # print("Q contains P:", res2)
    # print("P equivalent Q:", res1 and res2)
    # print(P)
    # P.minimize()
    # print(P)

    # toy_program = read_program('./anduo_program.txt')
    # # toy_program1 = "R(h1, xd, h1 || p) :- R(e1, xd, p), link(h1, e1), link(e1, a1), link(e1, a2)"
    # print("before minimization,", toy_program)
    # tp = DT_Program(toy_program, {"R":["integer", "integer", "integer[]", "integer"]})
    # tp.minimize()
    # print("after minimizing", tp)

    # anduo_program = read_program('./fattree_program1.txt')
    # # toy_program1 = "R(h1, xd, h1 || p) :- R(e1, xd, p), link(h1, e1), link(e1, a1), link(e1, a2)"
    # ap = DT_Program(anduo_program, {"R":["integer", "integer", "integer", "integer", "integer[]", "integer"]})
    # print("before minimization,", ap)
    # ap.minimize()
    # print("after minimizing", ap)

    # anduo_program = read_program('./fattree_program2.txt')
    # # toy_program1 = "R(h1, xd, h1 || p) :- R(e1, xd, p), link(h1, e1), link(e1, a1), link(e1, a2)"
    # ap = DT_Program(anduo_program, {"R":["integer", "integer", "integer", "integer[]", "integer"]})
    # print("before minimization,", ap)
    # ap.minimize()
    # print("after minimizing", ap)

    anduo_program = read_program('./fattree_program2_2.txt')
    ap = DT_Program(anduo_program, 
                    {"R":["integer", "integer", "integer", "integer[]", "integer"], "pod":["integer", "int4_faure"]}, 
                    domains=[1, 2, 3, 4], 
                    c_variables=['p1', 'p2'], 
                    reasoning_engine='z3', 
                    reasoning_type='Int', simplification_on=True)
    print("before minimization,", ap)
    ap.minimize()
    print("after minimizing", ap)

    # toy_program4 = read_program('./toy_program9.txt')
    # tp4 = DT_Program(toy_program4, {"R":["integer", "integer","integer[]"]})

    # toy_program5 = read_program('./toy_program10.txt')
    # tp5 = DT_Program(toy_program5, {"R":["integer", "integer","integer[]"]})
    # print(tp4.contains(tp5))
    # print(tp5.contains(tp4))

    # P = "R(x2,xd,x2 || xp) :- link(x2,x3), link(x2,x4), R(x3,xd,xp), x2 \\not_in xp\n \
    #     R(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), link(x2,x4), R(x2,xd,xp), x1 \in xp & x3 \in xp"

    # P_dt = DT_Program(P, {"R":["integer", "integer","integer[]"]})
    # P_dt.minimize()
    # print(P_dt)
