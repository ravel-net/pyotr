from collections import deque
from os.path import dirname, abspath, join
import sys
import math

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
	while(curr >= 0 and conditions[curr] != '(' and conditions[curr] != ','):
		curr -= 1
	start = curr + 1
	curr = i
	while(curr < len(conditions) and conditions[curr] != ')' and conditions[curr] != ',' and i < len(conditions)-1):
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

# Updates the domain of variables given. Returns a dictionary e.g. {x1: [1,2,3], x2: [1]}
# TODO: Take actual domain and return the least 
def findUpdatedDomains(domain, varMapping):
	updatedDomains = {}
	for var in domain:
		if var not in varMapping:
			updatedDomains[var] = [1,2]
		else:		
			mappedVar = varMapping[var]
			updatedDomains[mappedVar] = [1,2]
	return updatedDomains
	# updatedDomains = {}
	# for var in domain:
	# 	if var not in varMapping:
	# 		if var not in updatedDomains:
	# 			updatedDomains[var]  = []
	# 		for val in domain[var]:
	# 			if val not in updatedDomains[var]:
	# 				updatedDomains[var].append(val)
	# 		if -1 not in updatedDomains[var]:
	# 			updatedDomains[var].append(-1)
	# 	else:		
	# 		mappedVar = varMapping[var]
	# 		if mappedVar not in updatedDomains:
	# 			updatedDomains[mappedVar] = []
	# 		for val in domain[var]:
	# 			if val not in updatedDomains[mappedVar]:
	# 				updatedDomains[mappedVar].append(val)
	# 		if -1 not in updatedDomains[mappedVar]:
	# 			updatedDomains[mappedVar].append(-1)
	# return updatedDomains

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

def processCon(var1, var2, updatedDomains):
	newItems = []
	if isVarCondition(var1,var2):	# TODO: Get the domain with the minimum range
		for i in range(math.ceil(math.log(len(updatedDomains[var1]),2))):
			newItems.append("Xnor("+var1+"_"+str(i)+","+var2+"_"+str(i)+")")
	else:
		iterator = 0
		binary_rep = bin(updatedDomains[var1].index(var2))[2:]
		diff_len = math.ceil(math.log(len(updatedDomains[var1]),2)) - len(binary_rep)
		for i in range(diff_len):
			binary_rep = '0'+binary_rep
		for val in binary_rep: # binary representation
			# print(splitConditions[0])
			# print(bin(updatedDomains[splitConditions[0]].index(splitConditions[1]))[2:])
			# print(val)
			# print(updatedDomains[var1].index(var2))
			if val == '1':
				newItems.append(var1+"_"+str(iterator))
			else:
				newItems.append("Not("+var1+"_"+str(iterator)+")")
			iterator += 1
	return newItems

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
		# TODO: Add not equal to
		elif cuddFormCond[i:i+2] == "==":
			condition, _,_ = extractConditions(cuddFormCond, i)
			splitConditions = condition.split('==')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			newItems = processCon(splitConditions[0],splitConditions[1], updatedDomains)
			if (len(newItems) > 1):
				stack.append(combineItems(newItems, "And"))
			elif (len(newItems) > 0):
				stack.append(newItems[0])
			else:
				print("Error")
				exit()
			i+=length
		elif cuddFormCond[i].isdigit() and cuddFormCond[i-1] == ' ' and cuddFormCond[i+1] == ' ':
			stack.append(cuddFormCond[i-1:i+2])

	cuddFormCond = stack.pop()
	return(cuddFormCond)

def getUpdatedVariables(updatedDomains):
	variables = []
	for var in updatedDomains:
		for i in range(math.ceil(math.log(len(updatedDomains[var]),2))):
			variables.append(var + "_" + str(i))
	return variables

def addDomain(variables, domain):
	updatedDomain = {}
	for variable in variables:
		updatedDomain[variable] = domain
	return updatedDomain

def domainConstraints(variables, updatedDomains):
	constraint = "And("
	for var in variables:
		currConstraint = "Or("
		for d in updatedDomains[var]:
			currConstraint += str(var)+"=="+str(d)+","
		currConstraint = currConstraint[0:-1]+")"
		constraint = constraint + (currConstraint) + ","
	constraint = constraint[0:-1] + ")"
	return constraint

def convertToCUDD(conditions, input_domain):
	allConstraints = []
	varConditions = []
	variables = []
	domain = {}
	
	stack = deque()
	for i in range(len(conditions)):
		# print(stack)
		if conditions[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.

			# TODO: Revisit this
			if (len(listItems) > 1):
				stack.append(combineItems(listItems, logicalOP))
			else:
				stack.append(listItems[0])

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
					if splitConditionsProcessed[0] not in variables:
						variables.append(splitConditionsProcessed[0])
			stack.append(condition)
			i+=length

	if (len(stack) != 1):
		print("Length of stack should be 1")
		exit()
	cuddFormCond = stack.pop()
	updatedDomains = addDomain(variables, input_domain)
	domainConstraint = domainConstraints(variables, updatedDomains)
	cuddFormCond = "And(" + domainConstraint + "," + cuddFormCond + ")"

	# varMapping = getSubstituitions(varConditions, variables)
	# cuddFormCond = substituteVars(cuddFormCond, varMapping)
	# updatedDomains = findUpdatedDomains(domain, varMapping)
	# print(updatedDomains)
	cuddFormCond = encode(cuddFormCond, updatedDomains)
	# print("bdd = " + cuddFormCond + ";")
	variables = getUpdatedVariables(updatedDomains)
	cuddFormCond = cuddFormCond.replace(" 1 ","1")
	cuddFormCond = cuddFormCond.replace(" 0 ","0")
	cuddFormCond = cuddFormCond.replace("Not(","~(")
	cuddFormCond = cuddFormCond.replace("And(","&(")
	cuddFormCond = cuddFormCond.replace("Xnor(","$(")
	cuddFormCond = cuddFormCond.replace("Or(","^(")
	return cuddFormCond, variables

# Returns the length of the biggest variable name in list
def maxLength(variablesArray):
	if (len(variablesArray) <= 0):
		print("The length of variable array must be non-zero")
		exit()
	maximum = len(variablesArray[0])
	for var in variablesArray:
		if len(var) > maximum:
			maximum = len(var)
	return maximum


if __name__ == "__main__":
	if len(sys.argv) < 3:
		print("Not enough arguments provided")
	else:
		input_fileName = sys.argv[1]
		output_fileName = sys.argv[2]
		f_output = open(output_fileName, "w")
		with open(input_fileName) as f_input:
			lines = f_input.readlines()
			for line in lines:
				condition, variablesArray = convertToCUDD(line, ['1','2','3','4','5'])
				numVars = len(variablesArray)
				maxVarNameLength = maxLength(variablesArray)
				conditionSize = len(condition)
				variablesString = " ".join(variablesArray)
				f_output.write(str(numVars) + " " + str(maxVarNameLength) + " " + str(conditionSize) + " " + variablesString + " " + condition + "\n")
				# print(numVars, maxVarNameLength, conditionSize, variablesString, condition)  
		f_input.close()
		f_output.close()
		# convertToCUDD(sys.argv[1])