from collections import deque
from os.path import dirname, abspath, join
import sys
import math
import time

# When a bracket close is encountered, pop items from the stack until a logical operator is encountered
def popUntilLogicalOP(stack):
	elem = stack.pop()
	listItems = []
	while elem != "^" and elem != "&":
		listItems.append(elem)
		elem = stack.pop()
	return listItems[::-1], elem #Todo: Should work even without reversing array using ::-1

# Combines a list of items under a single logical operator into pairwise logical operations that are understandable by CUDD
def combineItems(listItems, logicalOP):
	if len(listItems) == 1:
		return listItems[0]
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


# Preprocessing constant == constant and constant == variables
def preprocessCond(var1, var2):
	if (var1.isdigit() and var2.isdigit()): # constant = constant e.g. 1 == 2
		if (var1 == var2):
			return '1', '1'
		else:
			return '0', '0'
	elif (var1.isdigit() and not var2.isdigit()): # constant = variable e.g. 1 == x
		return str(var2), str(var1)
	else:
		return str(var1), str(var2)

def binaryRepresentation(var1, numBinDigits, binary_rep):
	newItems = []
	iterator = 0
	diff_len = numBinDigits - len(binary_rep)
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
			newItems.append("~("+var1+"_"+str(iterator)+")")
		iterator += 1
	return newItems

def processCon(var1, var2, updatedDomains, variables):
	newItems = []
	processedCond = ""
	numBinDigits = math.ceil(math.log(len(updatedDomains),2))
	if isVarCondition(var1,var2):	# TODO: Get the domain with the minimum range
		variables.add(var1)
		variables.add(var2)
		for i in range(numBinDigits):
			newItems.append("$("+var1+"_"+str(i)+","+var2+"_"+str(i)+")")
		processedCond = combineItems(newItems, "&")
	else:
		newVar1, newVar2 = preprocessCond(var1, var2)
		variables.add(newVar1)
		if (newVar1 != '1' and newVar1 != '0'): # case when it is constant = constant
			binary_rep = bin(updatedDomains.index(newVar2))[2:]
			newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep)
			processedCond = combineItems(newItems, "&")
			if updatedDomains.index(newVar2) == 0: # if domain is not an exponential of two, we need to fill in the missing elements. We do this by filling the left over elements with the first element i.e. domain = [1,2,3,4,5] becomes domain = [1,2,3,4,5,1,1,1]
				allConditions = [processedCond]
				for i in range(len(updatedDomains), int(math.pow(2,numBinDigits))):
					binary_rep = bin(i)[2:]
					newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep)
					allConditions.append(combineItems(newItems, "&"))
				processedCond = combineItems(allConditions, "^")
		else:
			processedCond = newVar1
	return processedCond

def getUpdatedVariables(variables, input_domain):
	newVariables = []
	for var in variables:
		for i in range(math.ceil(math.log(len(input_domain),2))):
			newVariables.append(var + "_" + str(i))
	return newVariables

def domainConstraints(variables, input_domain):
	constraint = "And("
	for var in variables:
		currConstraint = "Or("
		for d in input_domain:
			currConstraint += str(var)+"=="+str(d)+","
		currConstraint = currConstraint[0:-1]+")"
		constraint = constraint + (currConstraint) + ","
	constraint = constraint[0:-1] + ")"
	return constraint

def findVariables(conditions):
	variables = set()
	for i in range(len(conditions)):
		if conditions[i] == ')' or conditions[i] == ',' or conditions[i] == '(':
			i += 1
		elif conditions[i:i+4] == "And(":
			i+=4
		elif conditions[i:i+3] == "Or(":
			i+=3
		elif conditions[i:i+2] == "==" or conditions[i:i+2] == "!=":
			op = conditions[i:i+2]
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split(op)
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			if (not splitConditions[0].isdigit()):
				variables.add(splitConditions[0])			
			if (not splitConditions[1].isdigit()):
				variables.add(splitConditions[1])
			length = len(condition)
			i+=length
	return variables


def convertToCUDD(conditions, input_domain):
	variables = findVariables(conditions)
	stack = deque()
	for i in range(len(conditions)):
		if conditions[i] == ')':
			listItems, logicalOP = popUntilLogicalOP(stack) # pop until logical operator encountered.

			if (len(listItems) > 1):
				stack.append(combineItems(listItems, logicalOP))
			else:
				stack.append(listItems[0])

		elif conditions[i:i+4] == "And(":
			stack.append("&")
			i+=4
		elif conditions[i:i+3] == "Or(":
			stack.append("^")
			i+=3
		elif conditions[i:i+2] == "==" or conditions[i:i+2] == "!=":
			op = conditions[i:i+2]
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split(op)
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			encodedCond = processCon(splitConditions[0], splitConditions[1], input_domain, variables)
			stack.append(encodedCond)
			i+=length

	if (len(stack) != 1):
		print("Length of stack should be 1")
		exit()
	cuddFormCond = stack.pop()

	variables = getUpdatedVariables(variables, input_domain)

	count = 2 # starting from 2 since 0 and 1 are reserved for true and false
	for var in variables:
		cuddFormCond = cuddFormCond.replace(var,str(count)) 
		count += 1

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
	# print(a)
	if len(sys.argv) < 3:
		print("Not enough arguments provided")
	else:
		input_fileName = sys.argv[1]
		output_fileName = sys.argv[2]
		f_output = open(output_fileName, "w")
		with open(input_fileName) as f_input:
			lines = f_input.readlines()
			for line in lines:
				t0 = time.time()

				condition, variablesArray = convertToCUDD(line, ['1','2','3','4','5'])
				t1 = time.time()
				total = t1-t0
				numVars = len(variablesArray)
				maxVarNameLength = maxLength(variablesArray)
				conditionSize = len(condition)
				print(total)
				# print(numVars, maxVarNameLength, conditionSize, variablesString, condition)  
				f_output.write(str(numVars) + " " + str(conditionSize) + " " + condition + "\n")
		f_input.close()
		f_output.close()

# &(^(~(2),2),&(~(2),2))