from collections import deque

logicalOpsConversion = {"^":"Or", "&":"And"}

# Input: Conditions as conjunctive array (e.g. ['t0.c0 == t1.c0', 't1.c0 == t2.c0', 't2.c0 == t3.c0', ['t0.c0 == 2', 'And(Or(t0.c0 == 1, t0.c0 == 2), t0.c0 == 5)']])
# Output Example: Array['And(' || t0.c0 || ' == ' || t1.c0 || ', ' || t1.c0 || ' == ' || t2.c0 || ', ' || t2.c0 || ' == ' || t3.c0 || ', ' || t0.c0 || ' == ' || 2 || ', ' || 'And(' || 'Or(' || t0.c0 || ' == ' || 1 || ', ' || t0.c0 || ' == ' || 2 || ')' || ', ' || t0.c0 || ' == ' || 5 || ')' || ')']
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
def getTablesAsConditions(tables = [], colmName = "condition"):
	tableRefs = []
	for table in tables:
		tableReference = table.split()[1]
		tableRefs.append(tableReference + "." + colmName)
	return " || ".join(tableRefs)


# Input: Condition
# Processing: Replace negative integers by c-vars
# Output: String in z3 format
def replaceCVarsNegative(condition, mapping):
    replacedConditions = []
    for c in condition:
        for var in mapping:
            c = c.replace(var, mapping[var])
        replacedConditions.append(c)
    return replacedConditions

# Input: Condition
# Processing: Replace cvariables by sql locations
# Output: Return processed condition
def replaceCVars(condition, mapping):
    replacedConditions = []
    for c in condition:
        for var in mapping:
            c = c.replace(var+" ", mapping[var][0]+" ")
        replacedConditions.append(c)
    return replacedConditions

# When a bracket close is encountered, pop items from the stack until a logical operator is encountered
def popUntilLogicalOP(stack):
	elem = stack.pop()
	listItems = []
	while elem != "^" and elem != "&":
		listItems.append(elem)
		elem = stack.pop()
	return listItems[::-1], logicalOpsConversion[elem] #Todo: Should work even without reversing array using ::-1

# Combines a list of items under a single logical operator into pairwise logical operations that are understandable by CUDD
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

# TODO: Remove is ip
# TODO: Need to have table c-var type so that conditions can be appropriately run
def processCon(var1, var2, op, replacements, cVarTypes={}, is_ip=False):
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
		condition += replacements[var2]
	else:
		condition += var2

	# to support negative integers as c-variables
	if var1 in replacements:
		if var1 in cVarTypes and "inet" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + replacements[var1] + " < " + "'0.0.255.0')"  
		else:
			finalCondition = "(" + condition + " or " + replacements[var1] + " < " + "0)"  
	else:
		if var1 in cVarTypes and "inet" in cVarTypes[var1]:
			finalCondition = "(" + condition + " or " + var1 + " < " + "'0.0.255.0')"  	
		else:
			finalCondition = "(" + condition + " or " + var1 + " < " + "0)"  	

	return finalCondition

# Converts a z3 condition into a SQL where clause
def z3ToSQL(condition, operators = ["==", "!=", ">", ">=", "<", "<="], replacements = {"==":"="}, cVarTypes={}, is_ip=False):
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
			splitConditions = currCondition.split(op)
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			encodedCond = processCon(splitConditions[0], splitConditions[1], op, replacements, cVarTypes, is_ip)
			stack.append(encodedCond)
			i+=len(splitConditions[1])+len(op)-1
		else:
			i+=1

	if (len(stack) != 1):
		print("Length of stack should be 1")
		exit()
	sqlFormCond = stack.pop()

	return sqlFormCond

print(z3ToSQL("And(y == 10, y < 20)"))
# print(z3ToSQL("And(Or(Or(Or(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))), x3 == 1, x2 == 1, x1 == 1), x3 == 1, x2 == 1, Or(And(x3 == 1, 1 == x1), And(x2 == 1, 1 == x1), 1 == x1, x1 == 1)), x2 == 1, x3 == 1, x1 == 1), 1 == x2, x2 == 2)"))