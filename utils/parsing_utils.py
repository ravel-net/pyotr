import sys
import re
from copy import copy
from os.path import dirname, abspath
root = dirname(abspath(__file__))
sys.path.append(root)

from collections import deque
from utils.logging import timeit

logicalOpsConversion = {"^":"Or", "&":"And"}

# Input: Conditions as conjunctive array (e.g. ['t0.c0 == t1.c0', 't1.c0 == t2.c0', 't2.c0 == t3.c0', ['t0.c0 == 2', 'And(Or(t0.c0 == 1, t0.c0 == 2), t0.c0 == 5)']])
# Output Example: Array['And(' || t0.c0 || ' == ' || t1.c0 || ', ' || t1.c0 || ' == ' || t2.c0 || ', ' || t2.c0 || ' == ' || t3.c0 || ', ' || t0.c0 || ' == ' || 2 || ', ' || 'And(' || 'Or(' || t0.c0 || ' == ' || 1 || ', ' || t0.c0 || ' == ' || 2 || ')' || ', ' || t0.c0 || ' == ' || 5 || ')' || ')']
@timeit
def getArrayPart(conditions, operators = ["==", "!=", ">", ">=", "<", "<="]):
	if len(conditions) > 0:
		conditionSQL = "And(" + ", ".join(conditions)+")"
		conditionComponents = []
		conditionSQLSplit = conditionSQL.split(" ")
		for item in conditionSQLSplit:
			i = 0
			j = 0
			while i < len(item):
				if item[i:i+4] == "And(":
					conditionComponents.append("'And('")
					i += 4
					j = i
				elif item[i:i+3] == "Or(":
					conditionComponents.append("'Or('")
					i += 3
					j = i
				elif item[i] == ")":
					if (j != i and item[j:i] != ')'):
						conditionComponents.append(item[j:i])
					conditionComponents.append("')'")
					i += 1
					j = i
				elif item[i] == ",":
					if (j != i):
						conditionComponents.append(item[j:i])
					conditionComponents.append("', '")
					i += 1
					j = i
				# elif item[i] == " ":
				# 	if (j != i):
				# 		conditionComponents.append(conditionSQL[j:i])
				# 		print(conditionSQL[j:i])
				# 	conditionComponents.append("')'")
				# 	print(')')
				# 	i += 1
				# 	j = i
				elif item[i:i+2].strip() in operators:
					op = item[i:i+2].strip()
					conditionComponents.append(" ' " + op + " ' ")
					i += 2
					j = i
				elif i == len(item)-1:
					if (j != i):
						conditionComponents.append(item[j:i+1])
					# conditionComponents.append(conditionSQL[i])
					i += 2
					j = i
				else:
					i+=1
		return " || ".join(conditionComponents)
	elif len(conditions) <= 0:
		# print("array length is zero")
		return ""

# Input: Tables for joining (e.g. ['C t0', 'C t1', 'C t2', 'B t3'])
# Output Example: t0.condition || t1.condition || t2.condition || t3.condition
@timeit
def getTablesAsConditions(tables = [], colmName = "condition"):
	tableRefs = []
	for table in tables:
		tableReference = table.split()[1]
		tableRefs.append(tableReference + "." + colmName)
	return " || ".join(tableRefs)


# Input: Condition
# Processing: Replace negative integers by c-vars
# Output: String in z3 format
@timeit
def replaceCVarsNegative(condition, mapping):
    replacedConditions = []
    for c in condition:
        for var in mapping:
            c = c.replace(str(var), str(mapping[var]))
        replacedConditions.append(c)
    return replacedConditions

# Input: Condition
# Processing: Replace cvariables by sql locations
# Output: Return processed condition
@timeit
def replaceCVars(condition, mapping, arrayVariables=[]):
    replacedConditions = []
    for c in condition:
        addCondition = True
        for var in mapping:
            if var in arrayVariables: # TODO: Hacky way to remove conditions over arrays from z3. Fix it
                addCondition = False
                continue
            c = c.replace(str(var)+" ", str(mapping[var][0]+" ")) # TODO: Hacky way to only replace variables
            c = c.replace(str(var)+")", str(mapping[var][0]+")")) # TODO: Hacky way to only replace variables
            c = c.replace(str(var)+",", str(mapping[var][0]+",")) # TODO: Hacky way to only replace variables
        if addCondition:
            replacedConditions.append(c)
    return replacedConditions

# When a bracket close is encountered, pop items from the stack until a logical operator is encountered
@timeit
def popUntilLogicalOP(stack):
	elem = stack.pop()
	listItems = []
	while elem != "^" and elem != "&":
		listItems.append(elem)
		elem = stack.pop()
	return listItems[::-1], logicalOpsConversion[elem] #Todo: Should work even without reversing array using ::-1

# Combines a list of items under a single logical operator into pairwise logical operations that are understandable by CUDD
@timeit
def combineItems(listItems, logicalOP, replacements):
	if logicalOP in replacements:
		logicalOP = replacements[logicalOP]
	if len(listItems) == 1:
		return listItems[0]
	elif len(listItems) == 2:
		return "("+listItems[0]+" "+logicalOP+" "+listItems[1]+")"
	currString = "("+listItems[0]+" "+logicalOP+" "+combineItems(listItems[1:], logicalOP, replacements)+")"
	return currString


# Extract conditions from a given position in the whole condition string. Note that i is the position of "=="
@timeit
def extractConditions(conditions, i):
	start = 0
	end = len(conditions)
	curr = i
	while(curr >= 0 and conditions[curr] != '(' and conditions[curr] != ','):
		curr -= 1
	start = curr + 1
	curr = i
	while(curr < len(conditions) and conditions[curr] != ')' and conditions[curr] != ',' and i < len(conditions)-1):
		curr += 1
	end = curr
	return conditions[start:end].strip(), start, end

@timeit
def processCon(var1, var2, op, replacements, cVarTypes={}):
	condition = ""
	if var1 in replacements:
		condition += replacements[var1]
	else:
		condition += var1
	if op in replacements:
		condition += " " + replacements[op] + " "
	else:
		condition += " " + op + " "
	if var2 in replacements:
		if replacements[var2][0] == "[" and op == "==":
			condition += "ANY("+replacements[var2][1:-1]+")"
		elif replacements[var2][0] == "[" and op == "!=":
			condition += "ALL("+replacements[var2][1:-1]+")"
		else:
			condition += replacements[var2]
	else:
		condition += var2

	finalCondition = condition
	# to support negative integers as c-variables
	if var1 in replacements:
		if var1 in cVarTypes and "inet_faure" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + replacements[var1] + " < " + "'0.0.255.0')"  
		elif var1 in cVarTypes and "integer_faure" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + replacements[var1] + " < " + "0)"  
	else:
		if var1 in cVarTypes and "inet" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + var1 + " < " + "'0.0.255.0')"  	
		elif var1 in cVarTypes and "integer_faure" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + var1 + " < " + "0)"  	

	return finalCondition

# Converts a z3 condition into a SQL where clause
@timeit
def z3ToSQL(condition, operators = ["==", "!=", ">", ">=", "<", "<="], replacements = {"==":"="}, cVarTypes={}):
	if (len(condition) <= 1): # Empty condition
		return TRUE, []
	stack = deque()
	i = 0
	while i < len(condition):
		if condition[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.
			if (len(listItems) > 1):
				stack.append(combineItems(listItems, logicalOP, replacements))
			else:
				stack.append(listItems[0])
			i+=1
		elif condition[i:i+4] == "And(":
			stack.append("&")
			i+=4
		elif condition[i:i+3] == "Or(":
			stack.append("^")
			i+=3
		elif condition[i:i+2].strip() in operators:
			op = condition[i:i+2].strip()
			currCondition, _,_ = extractConditions(condition, i)
			length = len(condition)
			splitConditionsPre = currCondition.split(op)
			splitConditions = [splitConditionsPre[0].strip(), splitConditionsPre[1].strip()]
			encodedCond = processCon(splitConditions[0], splitConditions[1], op, replacements, cVarTypes)
			stack.append(encodedCond)
			i+=len(splitConditionsPre[1])+len(op)-1
		else:
			i+=1

	if (len(stack) != 1):
		print(stack)
		print("Length of stack should be 1")
		exit()
	sqlFormCond = stack.pop()
	return sqlFormCond

@timeit
def split_atoms(bodystr):
	i = 0
	in_cond = False
	in_param = False
	atom_strs = []
	begin_pos = i
	while i < len(bodystr):
		if bodystr[i] == '(' and not in_cond:
			in_param = True
		elif bodystr[i] == '[' and not in_param:
			in_cond = True
		elif bodystr[i] == ')' and not in_cond:
			in_param = False
			atom_str = bodystr[begin_pos: i+1].strip(" ,")
			atom_strs.append(atom_str)
			begin_pos = i+1
		elif bodystr[i] == ']' and not in_param:
			# if len(in_parenth) < 1:
			in_cond = False
			in_param = False
			relation = atom_strs.pop(-1)
			atom_str_with_condition = relation + bodystr[begin_pos: i+1]
			atom_str_with_condition.strip(" ,")
			atom_strs.append(atom_str_with_condition)
			begin_pos = i + 1
		
		i += 1
	if begin_pos != len(bodystr):
		atom_strs.append(bodystr[begin_pos:].strip(" ,"))
	
	return atom_strs

@timeit
def datalog_condition2z3_condition(condition):
	# Assume support logical Or/And, excluding mixed uses
	logical_opr = None
	if '^' in condition:
		logical_opr = '^'
	elif '&' in condition:
		logical_opr = '&'
	
	conds = []
	processed_cond = None
	if logical_opr:
		for c in condition.split(logical_opr):
			c = c.strip()
			if c.split()[1].strip() == '=':
				c = c.replace('=', '==')
			conds.append(c)
	else:
		if len(condition.split()) > 1 and condition.split()[1].strip() == '=':
			condition = condition.replace('=', '==')
		processed_cond = condition
	
	if logical_opr == '^':
		processed_cond = "Or({})".format(", ".join(conds))
	elif logical_opr == '&':
		processed_cond = "And({})".format(", ".join(conds))
	
	if processed_cond is None:
		print("Illegal condition: {}!".format(condition))
		exit()
	return processed_cond

@timeit
# paramstring is anything in an atom after the table name and initial bracket
def getAtomParameters(paramString):
	parameters = []
	parameter_str = paramString.strip() # parameter_str = 'a1, xd, p'
	if parameter_str[-1] == ')':
		parameter_str = parameter_str[:-1] 
	# if '[' in parameter_str: # there is an array in parameters, e.g., R(a1, xd, [a1, e1]), then parameter_str = 'a1, xd, [a1, e1]'
	#     items = parameter_str.split('[')
	in_sqr_parenth = False
	vars_in_sqr_parenth = []
	for var in parameter_str.split(','):
		if '[' in var and ']' in var and '||' in var: # special case, parameter_str = 'a1, xd, a || [a1]'
			parameters.append(var.strip())
		elif '[' in var and ']' in var: # special case, parameter_str = 'a1, xd, [a1]'
			value_in_array = re.findall(r'\[(.*?)\]', var)
			parameters.append(copy(value_in_array))
		elif '[' in var:
			in_sqr_parenth = True
			vars_in_sqr_parenth.append(var.split('[')[1].strip())
		elif ']' in var:
			in_sqr_parenth = False
			vars_in_sqr_parenth.append(var.split(']')[0].strip())
			parameters.append(copy(vars_in_sqr_parenth))
			vars_in_sqr_parenth.clear()
		else:
			if in_sqr_parenth:
				vars_in_sqr_parenth.append(var.strip())
			else:
				parameters.append(var.strip())
	return parameters

def getAtomVariables(parameters, c_variables, operators):
	variables = []
	for i, var in enumerate(parameters):
		if type(var) == list:
			for v in var:
				isDigit = v[0].isdigit() or (v[0] == "'" and v[1].isdigit)
				if not isDigit and v not in variables and v not in c_variables: # hacky fix
					variables.append(v)
		else:
			hasOperator = False
			for op in operators:
				if (op in var):
					hasOperator = True
					concatinatingVars = var.split(op)
					for concatinatingVar in concatinatingVars:
						concatinatingVar = concatinatingVar.strip()
						if '[' in concatinatingVar and ']' in concatinatingVar:
							concatinatingVar = concatinatingVar.replace("[",'').replace("]",'').split(",")
							for v in concatinatingVar:
								if not v[0].isdigit() and v not in variables and v not in c_variables:
									variables.append(v)
						elif not concatinatingVar[0].isdigit() and concatinatingVar not in variables:
							variables.append(concatinatingVar)
			if not hasOperator and not var[0].isdigit():
				if var not in c_variables and var not in variables:
					variables.append(var)
	return variables