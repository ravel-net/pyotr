import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
from ipaddress import IPv4Address, IPv4Network
import time
import z3
from z3 import Or, And, Not
import databaseconfig as cfg
import psycopg2

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

# datatype = "String"
# datatype = "Int"
def convert_z3_variable(condition, datatype):
	if datatype == "BitVec":
		return convert_z3_variable_bit(condition, datatype, 32)

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
	return "{} {} {}".format(op1, operator, op2)


def convertIPToBits(IP, bits):
	IP_stripped = IP.split(".")
	bitValue = 0
	i = bits-8
	for rangeVals in IP_stripped:
		bitValue += (int(rangeVals) << i)
		i -= 8 
	return (bitValue)

# Breaks IP into a range if it is subnetted
def getRange(var, op, IP): 
	net = IPv4Network(IP)
	if (net[0] != net[-1]): # subnet
		if op == "==":
			return [var + " >= " + str(net[0]), var + " <= " + str(net[-1])]
		elif op == "!=":
			return [var + " < " + str(net[0]), var + " > " + str(net[-1])]
		else:
			print("Error, illegal operation in", condition)
			exit()
	else:
		return ["{} {} {}".format(var,op,IP)]

def convert_z3_variable_bit(condition, datatype, bits):
    conditionSplit = condition.split()
    constraints = [condition]
    if not conditionSplit[2][0].isalpha():
        constraints = getRange(conditionSplit[0], conditionSplit[1], conditionSplit[2])
    elif not conditionSplit[0][0].isalpha():
        constraints = getRange(conditionSplit[2], conditionSplit[1], conditionSplit[0])
    conditionFinal = "And("
    for i, constraint in enumerate(constraints):
	    c_list = constraint.split()
	    if c_list[0][0].isalpha():
	        op1 = f"z3.{datatype}('{c_list[0]}',{bits})"
	    else: 
	    	val = convertIPToBits(c_list[0], 32)
	    	op1 = f"z3.{datatype}Val('{val}',{bits})"
	    
	    if c_list[2][0].isalpha():
	        op2 = f"z3.{datatype}('{c_list[2]}',{bits})"
	    else:
	    	val = convertIPToBits(c_list[2], 32)
	    	op2 = f"z3.{datatype}Val('{val}',{bits})"
	    operator = c_list[1]
	    conditionFinal += "{} {} {}".format(op1, operator, op2)
	    if i < len(constraints)-1:
	    	conditionFinal += ","
    conditionFinal += ')'
    return conditionFinal

def get_domain_conditions_from_list(domains, datatype, flow_var):
	expressions = []
	expressionsStr = []
	var_domain_list = []
	for var in domains:
		var_list = []
		for conds in domains[var]:
			conditions = []
			for cond in conds:
				prcd_cond = convert_z3_variable(cond, datatype)
				conditions.append(prcd_cond)
			var_list.append("And({})".format(", ".join(conditions)))
		var_domain_list.append("Or({})".format(", ".join(var_list)))
	domain_conditions = ", ".join(var_domain_list)
	return domain_conditions

def analyze(condition, datatype):
    cond_str = condition
    prcd_cond = ""
    if 'And' in cond_str or 'Or' in cond_str:
        stack_last_post = []
        i = 0
        stack_last_post.insert(0, i)
        condition_positions = []
        while i < len(cond_str):
            if cond_str[i] == '(':
                if len(stack_last_post) != 0:
                    stack_last_post.pop()
                stack_last_post.insert(0, i+1)
            elif cond_str[i] == ')' or cond_str[i] == ',':
                begin_idx = stack_last_post.pop()
                if i != begin_idx:
                    condition_positions.append((begin_idx, i))
                stack_last_post.insert(0, i+1)      
            i += 1
            
        if len(stack_last_post) != 0:
            begin_idx = stack_last_post.pop()
            if begin_idx !=  len(cond_str):
                condition_positions.append((begin_idx, len(cond_str)))
        # print(cond_str[51:])
        # print(stack_last_post)
        # print(condition_positions)
        for idx, pair in enumerate(condition_positions):
            if idx == 0:
                prcd_cond += cond_str[0:pair[0]]
            else:
                prcd_cond += cond_str[condition_positions[idx-1][1]:pair[0]]
            
            c = cond_str[pair[0]: pair[1]].strip()
            prcd_cond += convert_z3_variable(c, datatype)
            # for num in range(len(op1)):# TODO: assert that length of op1, operator and op2 is the same
            #     prcd_cond += "{} {} {}".format(op1[num], operator[num], op2[num])
            #     if num < len(op1)-1:
            #         prcd_cond += ","
        prcd_cond += cond_str[condition_positions[-1][1]:]
        # print(prcd_cond)
    else:
        prcd_cond += convert_z3_variable(condition, datatype)
        # for num in range(len(op1)):# TODO: assert that length of op1, operator and op2 is the same
        #     prcd_cond += "{} {} {}".format(op1[num], operator[num], op2[num])
        #     if num < len(op1)-1:
        #         prcd_cond += ","
    return prcd_cond

def get_max(overlay):
    max_val = 0
    for node in overlay:
        if int(node) > max_val:
            max_val = int(node)
    return max_val

def get_union_conditions(tablename='output', datatype='Int'):
    begin = time.time()
    cursor.execute("select condition from {}".format(tablename))
    union_cond = []
    row = cursor.fetchone()
    while row is not None:
        conditions = row[0]
        prced_conditions = []
        for c in conditions:
        	expr = analyze(c, datatype)
        	prced_conditions.append(expr)
        # print(prced_conditions)
        and_cond = "And({})".format(", ".join(prced_conditions)) # LogicaL And for all conditions in one tuple
        union_cond.append(and_cond)
        row = cursor.fetchone()
        
    union_condition = "Or({})".format(", ".join(union_cond)) # logical Or for every tuples' condition
    end = time.time()
    conn.commit()
    return union_condition, end - begin

def get_domain_conditions(overlay_nodes, variables_list, datatype):
    begin = time.time()
    max_node = get_max(overlay_nodes)
    var_domain_list = []
    for var in variables_list:
        var_domain = []
        
        for idx, val in enumerate(overlay_nodes):
            condition = ""
            # if idx != 0 and idx != len(overlay_nodes) - 1:
            #     interface_val = str(int(val) + max_node)
            #     condition = "z3.{}('{}') == z3.{}Val({})".format(datatype, var, datatype , interface_val)
            #     var_domain.append(condition)
            condition = "z3.{}('{}') == z3.{}Val({})".format(datatype, var, datatype , val)
            var_domain.append(condition)
        var_domain_list.append("Or({})".format(", ".join(var_domain)))
    domain_conditions = ", ".join(var_domain_list)  
    end = time.time()
    # print(domain_conditions)
    return domain_conditions, end - begin

def check_is_tautology(union_conditions, domain_conditions):

    negation_union_conditions = "Not({})".format(union_conditions)
    z3_begin = time.time()
    solver = z3.Solver()
    solver.add(eval(domain_conditions)) # set domain for variables
    solver.add(eval(negation_union_conditions)) # set negation union conditions
    ans = solver.check() # check the answer, if it answers sat, that means it is not a tautology
    z3_end = time.time()

    # print("total execution time: ", z3_end - z3_begin)

    for k, v in solver.statistics():
        if (k == "max memory"):
            print ("Check_Taut Max Memory: %s : %s" % (k, v))
    if ans == z3.sat:
        model = solver.model()
        # print(model)
        return False, z3_end - z3_begin, model
    else:
        return True, z3_end - z3_begin, ""

if __name__ == '__main__':
    # datatype = "Int"
    # union_conditions, union_time = get_union_conditions(tablename="output", datatype=datatype)
    # domain_conditions, domain_time = get_domain_conditions(overlay_nodes=['1', '2'], variables_list=['y1', 'y2'], datatype=datatype)
    # print(union_conditions)
    # print(domain_conditions)
    condition1 = "Or(z3.BitVec('x',3) == z3.BitVecVal(1, 3), z3.BitVec('x',3) == z3.BitVecVal(3, 3))"
    condition1_before = "Or(x == 1, x == 3)"
    condition1 = analyzeBitVector(condition1_before, 3)
    # condition2 = "Or(z3.Int('x1') == z3.IntVal(1), z3.Int('x1') == z3.IntVal(2)), Or(z3.Int('x2') == z3.IntVal(1), z3.Int('x2') == z3.IntVal(2))"
    solver = z3.Solver()
    solver.add(eval(condition1)) # set negation union conditions
    print(z3.solve(eval(condition1)))
    ans = solver.check() 
    # ans, time, _ = check_is_tautology(condition1, condition2)
    # solver.add(eval(negation_union_conditions)) # set negation union conditions
    
    print(ans)

    # cursor.execute("select distinct 1, 2, condition from output")

    # begin = time.time()
    # union_cond = []
    # row = cursor.fetchone()
    # while row is not None:
    #     conditions = row[2]
    #     prced_conditions = []
    #     for c in conditions:
    #         op1, operator, op2 = analyze(c)
    #         expr = "{} {} {}".format(op1, operator, op2)
    #         prced_conditions.append(expr)
    #     # print(prced_conditions)
    #     and_cond = "And({})".format(", ".join(prced_conditions)) # LogicaL And for all conditions in one tuple
    #     union_cond.append(and_cond)
    #     row = cursor.fetchone()
        
    # union_condition = "Or({})".format(", ".join(union_cond)) # logical Or for every tuples' condition
    # # print(condition)

    # # domain_conditions = "Or(z3.Int('y1') == z3.IntVal('1'), z3.Int('y1') == z3.IntVal('2')), Or(z3.Int('y2') == z3.IntVal('1'), z3.Int('y2') == z3.IntVal('2'))"
    # domain_conditions = "Or(z3.{}('y1') == z3.{}Val('1'), z3.{}('y1') == z3.{}Val('2')), \
    #             Or(z3.{}('y2') == z3.{}Val('1'), z3.{}('y2') == z3.{}Val('2'))".format(datatype, datatype, datatype, datatype, datatype, datatype, datatype, datatype)

    # # domain_conditions.append(condition)
    # final_condition = "Not({})".format(union_condition) # add negation to union condition
    # print(final_condition)
    # # print(union_cond)
    # solver = z3.Solver()
    
    # solver.add(eval(domain_conditions)) # set domain for y1 and y2
    # solver.add(eval(final_condition)) # set 
    # z3_begin = time.time()
    # ans = solver.check() # check the answer, if it answers sat, that means it is not a tautology
    # if ans == z3.sat:
    #     model = solver.model()
    #     print(model)
    # z3_end = time.time()
    # print("Answer:", ans, "z3 execution time:", z3_end - z3_begin)
    # print("total execution time: ", z3_end - begin)