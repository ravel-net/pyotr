from collections import deque

logicalOpsConversion = {"^":"Or", "&":"And"}

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

def processCon(var1, var2, op, replacements, is_ip=False):
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
	return condition

# Converts a z3 condition into a SQL where clause
def z3ToSQL(condition, operators = ["==", "!=", ">", ">=", "<", "<="], replacements = {"==":"="}, is_ip=False):
	print(condition)
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
			encodedCond = processCon(splitConditions[0], splitConditions[1], op, replacements, is_ip)
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