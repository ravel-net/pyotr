import time
import z3
from z3 import Or, And, Not
import databaseconfig as cfg
import psycopg2
datatype = "String"
# datatype = "Int"
def analyze(condition):
    c_list = condition.split()

    if c_list[0][0].isalpha():
        op1 = f"z3.{datatype}('{c_list[0]}')"
    else: 
        op1 = f"z3.{datatype}Val('{c_list[0]}')"
    
    if c_list[2][0].isalpha():
        op2 = f"z3.{datatype}('{c_list[2]}')"
    else:
        op2 = f"z3.{datatype}Val('{c_list[2]}')"
    
    operator = c_list[1]
    return op1, operator, op2
        
def calcDomainConditions(domain, variables):
	conditions = []
	for var in variables:
		for val in domain:
			conditions.append("z3.{}('{}') == z3.{}Val('{}')".format(datatype, var, datatype, str(val)))
	domain_conditions = "Or("+ ",".join(conditions) + ")"
	print(domain_conditions)
	return domain_conditions

def table_contains_answer(tablename, domain, variables):
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()
    cursor.execute("select distinct 1, 2, condition from output")

    begin = time.time()
    union_cond = []
    row = cursor.fetchone()
    while row is not None:
        conditions = row[2]
        prced_conditions = []
        for c in conditions:
            op1, operator, op2 = analyze(c)
            expr = "{} {} {}".format(op1, operator, op2)
            prced_conditions.append(expr)
        # print(prced_conditions)
        and_cond = "And({})".format(", ".join(prced_conditions)) # LogicaL And for all conditions in one tuple
        union_cond.append(and_cond)
        row = cursor.fetchone()
        
    union_condition = "Or({})".format(", ".join(union_cond)) # logical Or for every tuples' condition
    # print(condition)

    domain_conditions = calcDomainConditions(domain, variables)
    # domain_conditions = "Or(z3.Int('y1') == z3.IntVal('1'), z3.Int('y1') == z3.IntVal('2')), Or(z3.Int('y2') == z3.IntVal('1'), z3.Int('y2') == z3.IntVal('2'))"
    # domain_conditions = "Or(z3.{}('y1') == z3.{}Val('1'), z3.{}('y1') == z3.{}Val('2')), \
                # Or(z3.{}('y2') == z3.{}Val('1'), z3.{}('y2') == z3.{}Val('2'))".format(datatype, datatype, datatype, datatype, datatype, datatype, datatype, datatype)

    print(domain_conditions)
    # domain_conditions.append(condition)
    final_condition = "Not({})".format(union_condition) # add negation to union condition
    print(final_condition)
    # print(union_cond)
    solver = z3.Solver()
    
    solver.add(eval(domain_conditions)) # set domain for y1 and y2
    solver.add(eval(final_condition)) # set 
    z3_begin = time.time()
    ans = solver.check() # check the answer, if it answers sat, that means it is not a tautology
    z3_end = time.time()
    print("Answer:", ans, "z3 execution time:", z3_end - z3_begin)
    print("total execution time: ", z3_end - begin)
    conn.commit()
    conn.close()
    if ans == z3.sat:
        model = solver.model()
        print(model)
        return False
    else:
        return True