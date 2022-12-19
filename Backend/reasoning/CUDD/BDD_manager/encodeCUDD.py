from collections import deque
from os.path import dirname, abspath, join
import sys
import math
import time
from ipaddress import IPv4Address

TRUE = "(1)"
FALSE = "(0)"

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
			return TRUE, TRUE
		else:
			return FALSE, FALSE
	elif (var1.isdigit() and not var2.isdigit()): # constant = variable e.g. 1 == x
		return str(var2), str(var1)
	else:
		return str(var1), str(var2)

def binaryRepresentation(var1, numBinDigits, binary_rep, expectedBinDigits):
	newItems = []
	iterator = 0
	diff_len = numBinDigits - len(binary_rep)
	for i in range(diff_len):
		binary_rep = '0'+binary_rep
	for val in binary_rep[:expectedBinDigits]: # binary representation
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

def processCon(var1, var2, updatedDomains, is_ip=False):
	# print("var1", var1, "var2", var2)
	newItems = []
	processedCond = ""
	numBinDigits = 32
	varDomain = [] # If varDomain is empty, that means the domain is the entire integer set
	newVar1, newVar2 = preprocessCond(var1, var2)
	if newVar1 in updatedDomains:
		varDomain = updatedDomains[newVar1]
	if not is_ip and varDomain: 
		numBinDigits = math.ceil(math.log(len(varDomain),2))
	if isVarCondition(newVar1,newVar2):	
		numBinDigits2 = 32
		if var2 in updatedDomains:
			numBinDigits2 = math.ceil(math.log(len(updatedDomains[var2]),2))
		if (numBinDigits != numBinDigits2):
			print("Error: {}={} is an incorrect condition since the domains do not match".format(newVar1,newVar2))
			exit()
		for i in range(numBinDigits):
			newItems.append("$("+var1+"_"+str(i)+","+var2+"_"+str(i)+")")
		processedCond = combineItems(newItems, "&")
	else:
		# newVar1, newVar2 = preprocessCond(var1, var2)
		if (newVar1 == TRUE or newVar1 == FALSE): # case when it is constant = constant
			processedCond = newVar1
		elif (is_ip): # For IP address. Only 32 bit ip addresses supported right now
			ip = newVar2
			subnet = 32
			if '/' in newVar2:
				varsplit = newVar2.split("/")
				ip = varsplit[0]
				subnet = int(varsplit[1])
			addr = IPv4Address(ip)
			binary_rep = bin(int(addr))[2:]
			newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep, subnet)
			processedCond = combineItems(newItems, "&")
		elif len(varDomain) > 0: # case when it is var = constant with a specified domain
			if newVar2 not in varDomain or str(newVar2) not in varDomain: #if constant is out of the domain, var = constant is a contraiction
				processedCond = FALSE 
			else:
				binary_rep = bin(varDomain.index(newVar2))[2:]
				newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep, numBinDigits)
				processedCond = combineItems(newItems, "&")
				if varDomain.index(newVar2) == 0: # if domain is not an exponential of two, we need to fill in the missing elements. We do this by filling the left over elements with the first element i.e. domain = [1,2,3,4,5] becomes domain = [1,2,3,4,5,1,1,1]
					allConditions = [processedCond]
					for i in range(len(varDomain), int(math.pow(2,numBinDigits))):
						binary_rep = bin(i)[2:]
						newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep, numBinDigits)
						allConditions.append(combineItems(newItems, "&"))
					processedCond = combineItems(allConditions, "^")
		else: # case when it is var = constant in the entire integer domain
			binary_rep = bin(int(newVar2))[2:]
			newItems = binaryRepresentation(newVar1, numBinDigits, binary_rep, numBinDigits)
			processedCond = combineItems(newItems, "&")
	# print("processedCond", processedCond)
	return processedCond

def getUpdatedVariables(variables, input_domain, is_ip=False):
	newVariables = []
	for var in variables:
		numVars = 32
		if not is_ip and var in input_domain and len(input_domain[var]) != 0:
			numVars = math.ceil(math.log(len(input_domain[var]),2))
		for i in range(numVars):
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
		elif conditions[i:i+2] == "==":
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split('==')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			if (not splitConditions[0][0].isdigit()):
				variables.add(splitConditions[0])			
			if (not splitConditions[1][0].isdigit()):
				variables.add(splitConditions[1])
			length = len(condition)
			i+=length
	return variables


def convertToCUDD(conditions, input_domain, variables, is_ip=False):
	if (len(conditions) <= 1): # Empty condition
		return TRUE, [] 
	# variables = findVariables(conditions)
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
		elif conditions[i:i+2] == "==":
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split('==')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			encodedCond = processCon(splitConditions[0], splitConditions[1], input_domain, is_ip)
			stack.append(encodedCond)
			i+=length		
		elif conditions[i:i+2] == "!=":
			condition, _,_ = extractConditions(conditions, i)
			splitConditions = condition.split('!=')
			splitConditions[0] = splitConditions[0].strip()
			splitConditions[1] = splitConditions[1].strip()
			length = len(condition)
			encodedCond = processCon(splitConditions[0], splitConditions[1], input_domain, is_ip)
			encodedCond = "~(" + encodedCond + ")"
			stack.append(encodedCond)
			i+=length

	if (len(stack) != 1):
		print("Length of stack should be 1")
		exit()
	cuddFormCond = stack.pop()

	variables = getUpdatedVariables(variables, input_domain, is_ip)
	count = 2 # starting from 2 since 0 and 1 are reserved for true and false
	for var in variables:
		replacingVar = f'{var})' 
		cuddFormCond = cuddFormCond.replace(replacingVar,str(count)+')') 

		replacingVar = f'{var},' 
		cuddFormCond = cuddFormCond.replace(replacingVar,str(count)+',') 
		count += 1

	return cuddFormCond, variables

# Returns the length of the biggest variable name in list
def maxLength(variablesArray):
	if (len(variablesArray) <= 0):
		# print("The length of variable array must be non-zero. This might be an error")
		return 0
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
				t0 = time.time()

				variables = findVariables(line)
				condition, variablesArray = convertToCUDD(line, [], variables, True)
				# condition, variablesArray = convertToCUDD(line, ['1','2'], variables, False)
				t1 = time.time()
				total = t1-t0
				numVars = len(variablesArray)
				maxVarNameLength = maxLength(variablesArray)
				conditionSize = len(condition)
				# print(total)
				# print(numVars, maxVarNameLength, conditionSize, variablesString, condition)  
				f_output.write(str(numVars) + " " + str(conditionSize) + " " + condition + "\n")
		f_input.close()
		f_output.close()
	# # condition, variablesArray = convertToCUDD("And(x == 2, y == 5, z == 10)", {'x':['1','2','3'],'y':['4','5','6'],'z':['1','10']},['x','y','z'], False)
	# condition, variablesArray = convertToCUDD("And(x == 2, y == 5, z == 10)", {'x':['1','2','3'],'y':['4','5','6']},['x','y','z'], False)
	# print(condition, variablesArray)