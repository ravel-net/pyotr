#And(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(1 == x1, And(x2 == 1, x3 == 1, 1 == x1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, 1 == x1), And(x3 == 1, 1 == x1))), 1 == x3, x3 == 2)
from collections import deque
from os.path import dirname, abspath, join
import sys
root = dirname(dirname(abspath(__file__)))
filename = join(root, 'util', 'variable_closure_algo')
sys.path.append(filename)
import DFS

# When a bracket close is encountered, pop items from the stack until a logical operator is encountered
def popUntilLogicalOP(stack):
	elem = stack.pop()
	listItems = []
	while elem != "Or" and elem != "And":
		listItems.append(elem)
		elem = stack.pop()
	return listItems[::-1], elem #Todo: Should work even without reversing array using ::-1

# Combines a list of items under a single logical operator into pairwise logical operations that are understandable by CUDD
def combineItems(listItems, logicalOP):
	if len(listItems) == 1:
		return listItems[0]+")"
	elif len(listItems) == 2:
		return logicalOP+"("+listItems[0]+","+listItems[1]+")"
	currString = logicalOP+"("+listItems[0]+","+combineItems(listItems[1:], logicalOP)+")"
	return currString

# Extract conditions from a given position in the whole condition string. Note that i is the position of "=="
def extractConditions(conditions, i):
	start = 0
	end = len(conditions)
	curr = i
	while(conditions[curr] != '(' and conditions[curr] != ','):
		curr -= 1
	start = curr + 1
	curr = i
	while(conditions[curr] != ')' and conditions[curr] != ','):
		curr += 1
	end = curr
	return conditions[start:end].strip(), start, end

# checks if the condition is variable to variable equality. TODO: Support inequality operators
def isVarCondition(var1, var2):
	return var1[0].isalpha() and var2[0].isalpha()

# Get variable substitutions by tracking the assignments as a graph
def getSubstituitions(varConditions, variables):
    g = DFS.Graph(variables)
    variableConditionGraph = {}
    for varCond in varConditions:
    	splitCond = varCond.split("==")
    	var1 = splitCond[0].strip()
    	var2 = splitCond[1].strip()
    	g.add_edge(var1, var2)
    variableConnections = g.connectedComponents()
    varMapping = {}
    for connectedComponent in variableConnections:
    	for var in connectedComponent:
    		varMapping[var] = connectedComponent[0]
    return varMapping

# substitutes variable to variable assignments
def substituteVars(cuddFormCond, varMapping):
	substitutedConds = ""
	i = 0
	while i < len(cuddFormCond):
		substitutedConds += cuddFormCond[i]
		if cuddFormCond[i:i+2] == "==":
			condition, start, end = extractConditions(cuddFormCond, i)
			substitutedConds = substitutedConds[0:len(substitutedConds)-i+start-1]
			newCondition = condition.split("==")
			newCondition[0] = newCondition[0].strip()
			newCondition[1] = newCondition[1].strip()
			if (newCondition[0] in varMapping):
				newCondition[0] = varMapping[newCondition[0]]
			if (newCondition[1] in varMapping):
				newCondition[1] = varMapping[newCondition[1]]
			substitutedConds += newCondition[0] + " == " + newCondition[1]
			i=end-1
		i += 1
	return substitutedConds

# Updates the domain of variables given 
def findUpdatedDomains(domain, varMapping):
	updatedDomains = {}
	for var in domain:
		if var not in varMapping:
			if var not in updatedDomains:
				updatedDomains[var]  = []
			for val in domain[var]:
				if val not in updatedDomains[var]:
					updatedDomains[var].append(val)
		else:		
			mappedVar = varMapping[var]
			if mappedVar not in updatedDomains:
				updatedDomains[mappedVar] = []
			for val in domain[var]:
				if val not in updatedDomains[mappedVar]:
					updatedDomains[mappedVar].append(val)
	return updatedDomains

# Preprocessing constant == constant and constant == variables
def preprocessCond(var1, var2):
	if (var1.isdigit() and var2.isdigit()): # constant = constant e.g. 1 == 2
		if (var1 == var2):
			return ' 1 '
		else:
			return ' 0 '
	elif (var1.isdigit() and not var2.isdigit()): # constant = variable e.g. 1 == x
		return str(var2) + "==" + str(var1)
	else:
		return str(var1) + "==" + str(var2)

# at this point we are only left with constraints of the form var == constant. We perform a binary encoding of this
def encode(cuddFormCond, updatedDomains):
	stack = deque()
	for i in range(len(cuddFormCond)):
		if cuddFormCond[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.
			stack.append(combineItems(listItems, logicalOP))
		elif cuddFormCond[i:i+4] == "And(":
			stack.append("And")
			i+=4
		elif cuddFormCond[i:i+3] == "Or(":
			stack.append("Or")
			i+=3
		elif cuddFormCond[i:i+2] == "==":
			condition, _,_ = extractConditions(cuddFormCond, i)
			splitConditions = condition.split('==')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			newItems = []
			if (len(updatedDomains[splitConditions[0]]) == 1):
				stack.append(splitConditions[0]+"_0")
			else:
				for i in range(len(updatedDomains[splitConditions[0]])):
					if int(splitConditions[1]) == int(updatedDomains[splitConditions[0]][i]):
						newItems.append(splitConditions[0]+"_"+str(i))
					else:
						newItems.append("Not("+splitConditions[0]+"_"+str(i)+")")
				stack.append(combineItems(newItems, "And"))
			i+=length
		elif cuddFormCond[i].isdigit() and cuddFormCond[i-1] == ' ' and cuddFormCond[i+1] == ' ':
			stack.append(cuddFormCond[i])

	cuddFormCond = stack.pop()
	return(cuddFormCond)

def getUpdatedVariables(updatedDomains):
	variables = []
	for var in updatedDomains:
		i = 0
		for val in updatedDomains[var]:
			variables.append(var + "_" + str(i))
			i += 1
	return variables


def convertToCUDD(conditions):
	allConstraints = []
	varConditions = []
	variables = []
	domain = {}
	stack = deque()
	for i in range(len(conditions)):
		print(stack)
		if conditions[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.

			TODO: Revisit this
			if (len(listItems) > 1):
				stack.append(combineItems(listItems, logicalOP))
			else:
				stack.append(" 1 ")
		elif conditions[i:i+4] == "And(":
			stack.append("And")
			i+=4
		elif conditions[i:i+3] == "Or(":
			stack.append("Or")
			i+=3
		elif conditions[i:i+2] == "==":
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split('==')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			if isVarCondition(splitConditions[0],splitConditions[1]):
				varConditions.append(condition)
				if splitConditions[0] not in variables:
					variables.append(splitConditions[0])
				if splitConditions[1] not in variables:
					variables.append(splitConditions[1])
			else:
				condition = preprocessCond(splitConditions[0], splitConditions[1])
				if condition != " 0 " and condition != " 1 ":
					allConstraints.append(condition)
					splitConditionsProcessed = condition.split("==")
					if splitConditionsProcessed[0] not in domain:
						domain[splitConditionsProcessed[0]] = []
					domain[splitConditionsProcessed[0]].append(splitConditionsProcessed[1])
				stack.append(condition)
			i+=length
	cuddFormCond = stack.pop()
	varMapping = getSubstituitions(varConditions, variables)
	cuddFormCond = substituteVars(cuddFormCond, varMapping)
	updatedDomains = findUpdatedDomains(domain, varMapping)
	print(cuddFormCond)
	cuddFormCond = encode(cuddFormCond, updatedDomains)
	variables = getUpdatedVariables(updatedDomains)
	newStr = "DdNode "
	for var in variables:
		print(var + " = Cudd_bddNewVar(gbm);")
		newStr += "*" + var + ", "
	print(newStr)
	print(cuddFormCond)

# print(combineItems(["x1","x2", "x3", "x4"],"Or"))
# convertToCUDD("And(Or(Or(x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x3 == 1), x2 == 1, x3 == 1), x3 == 1, x2 == 1, Or(x1 == 1, And(x2 == 1, x3 == 1, x1 == 1), x1 == 1, And(x1 == 1, x2 == 1), And(x2 == 1, x1 == 1), And(x3 == 1, x1 == 1))), x3 == 1, x3 == 2)")
# convertToCUDD("And(x4 == 5, Or(x1 == 1,x2 == 2, x2 == x3, x2 == x3, 1 == 2),x3 == 3,x3 == x1, x4 == x5)")
convertToCUDD("Or(And(x1 == x2, x2 == x3), And(1 == x2, x2 == x3), x1 == x3, 1 == x3, And(x1 == 1, x2 == x3), And(x1 == 1, x2 == x3), And(x2 == 1, x3 == x2), x2 == 1, And(x2 == 1, x2 == x3), And(x2 == 1, x2 == x3), And(x3 == 1, x3 == x2), x3 == 1)")

# 8K hours
# Ask for feedback from Anduo

