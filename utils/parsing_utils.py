import sys
import re
from copy import copy
from os.path import dirname, abspath
root = dirname(abspath(__file__))
sys.path.append(root)
from ipaddress import IPv4Network

from collections import deque
from utils.logging import timeit
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table


############################################ Condition Tree Parsing ##################################
# conditions end in either a comma or a bracket. A comma in array is not counted
@timeit 
def findCondEnd(condition, startPos):
	inSquareBrackets = False
	index = startPos
	while index < len(condition):
		char = condition[index]
		if (char == "," or char == ")") and not inSquareBrackets:
			return index
		if condition[index] == "{" or condition[index] == "[":
			inSquareBrackets = True
		elif condition[index] == "}" or condition[index] == "]":
			inSquareBrackets = False
		index += 1
	return index

# conditions end in either a comma or a bracket. A comma in array is not counted
@timeit 
def findOperator(condition, startPos, endPos, operators = ["==", "!=", ">", ">=", "<", "<="]):
	i = startPos
	while i+2 < endPos:
		if condition[i:i+2].strip() in operators:
			return condition[i:i+2].strip()
		i += 1
	print("Could not find any operator in condition {}".format(condition[startPos, endPos]))
	exit()

def condToStringDefault(var1, operator, var2):
	return var1 + " " + operator + " " + var2

def condToStringModes(var1, operator, var2, mode, replacementDict = {}, atomTables = [], reasoningType={}):
	if mode == "Z3": 
		newOp = operator
		if newOp == "=":
			newOp = "=="
		if newOp != "==" and newOp != "!=" and (_isIP(var1) or _isIP(var2)):
			print("Unsuported operator given for condition {}. Exiting.".format(condToStringDefault(var1, newOp, var2)))
			exit()
		if _isIP(var1) and _isIP(var2):
			if operator == "==" and str(var1) == str(var2):
				return "z3.Bool(True)"
			elif operator == "==" and str(var1) != str(var2):
				return "z3.Bool('False')"
			elif operator == "!=" and str(var1) != str(var2):
				return "z3.Bool('True')"
			elif operator == "!=" and str(var1) == str(var2):
				return "z3.Bool('False')"
		if _isIP(var1):
			return _convertIPCondition(var=var2, operator=operator, ip=var1)
		elif _isIP(var2):
			return _convertIPCondition(var=var1, operator=operator, ip=var2)
		else:
			newVar1 = _convertToZ3Var(var1, reasoningType)
			newVar2 = _convertToZ3Var(var2, reasoningType)
			return condToStringDefault(newVar1, newOp, newVar2)
	elif mode == "Replace String":
		newVar1 = var1
		newVar2 = var2
		if var1 in replacementDict:
			newVar1 = replacementDict[var1]
		elif str(var1) in replacementDict:
			newVar1 = replacementDict[str(var1)]
		if var2 in replacementDict:
			newVar2 = replacementDict[var2]
		elif str(var2) in replacementDict:
			newVar2 = replacementDict[str(var2)]
		return condToStringDefault(newVar1, operator, newVar2)
	elif mode == "SQL":
		newOp = operator
		newVar1 = var1
		newVar2 = var2        
		if operator == "==":
			newOp = "="
		if not _isConstant(var1):
			var1_table = var1.split(".")[0]
			var1_colm = var1.split(".")[1]
			var1_type = atomTables[var1_table].columns[var1_colm]
			if "[]" in var1_type and operator == "!=":
				newVar1 = "All(" + var1 + ")"
			elif "[]" in var1_type:
				newVar1 = "Any(" + var1 + ")"
		if not _isConstant(var2):
			var2_table = var2.split(".")[0]
			var2_colm = var2.split(".")[1]
			var2_type = atomTables[var2_table].columns[var2_colm]
			if "[]" in var2_type and operator == "!=":
				newVar2 = "All(" + var2 + ")"
			elif "[]" in var2_type:
				newVar2 = "Any(" + var2 + ")"
		return condToStringDefault(newVar1, newOp, newVar2)
	elif mode == "Array Integration":
		newOp = operator
		newVar1 = var1
		newVar2 = var2        
		if operator == "=":
			newOp = "=="
		if not _isConstant(var1):
			var1_table = var1.split(".")[0]
			var1_colm = var1.split(".")[1]
			var1_type = atomTables[var1_table].columns[var1_colm]
			if "[]" in var1_type:
				newVar1 = var1 + "::text"
		if not _isConstant(var2):
			var2_table = var2.split(".")[0]
			var2_colm = var2.split(".")[1]
			var2_type = atomTables[var2_table].columns[var2_colm]
			if "[]" in var2_type:
				newVar2 = var2 + "::text"
		return condToStringDefault(newVar1, newOp, newVar2)
	elif mode == "Negative Int":
		conditions = []
		conditions.append(condToStringDefault(var1, operator, var2)) # first condition is the default one
		if not _isConstant(var1):
			var1_table = var1.split(".")[0]
			var1_colm = var1.split(".")[1]
			var1_type = atomTables[var1_table].columns[var1_colm]
			if "faure" in var1_type: # c-table
				newCondition = _negativeIntCondition(var1, var1_type)
				conditions.append(newCondition)
		if not _isConstant(var2):
			var2_table = var2.split(".")[0]
			var2_colm = var2.split(".")[1]
			var2_type = atomTables[var2_table].columns[var2_colm]
			if "faure" in var2_type: # c-table
				newCondition = _negativeIntCondition(var2, var2_type)
				conditions.append(newCondition)
		return "Or(" + ", ".join(conditions) + ")"


############################################ Faure Parsing ##################################

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
				elif item[i:i+2].strip() in operators:
					op = item[i:i+2].strip()
					conditionComponents.append(" ' " + op + " ' ")
					i += 2
					j = i
				elif i == len(item)-1:
					# if (j != i):
					conditionComponents.append(item[j:i+1])
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

############################################ Helper Parsing ##################################
# given a variable and its type, returns the negative integer condition
# not adding any or all here. Need to keep track of this when doiing sql conversion. ALL only when != used.
@timeit
def _negativeIntCondition(var, var_type):
	if "inet_faure" in var_type: # inet list
		return "'0.0.255.0' > " + var
	elif "integer_faure" in var_type:# integer list
		return "0 > " + var
	
# Returns true if the var is a digit or an IP
@timeit
def _isConstant(var):
	if _isInt(var) or _isIP(var):
		return True
	else:
		return False

def _isIP(var):
	if var.count(".") == 3:
		return True
	else:
		return False
	
def _isInt(var):
	if type(var) == int or str(var)[0].isdigit():
		return True
	else:
		return False

############################################ Z3 Parsing ##################################
def _convertIPToBits(IP, bits):
	if "/" in IP:
		IP = IP.split("/")[0]
	IP_stripped = IP.split(".")
	bitValue = 0
	i = bits-8
	for rangeVals in IP_stripped:
		if "\\" in rangeVals:
			rangeVals = rangeVals.split("\\")[0]
		bitValue += (int(rangeVals) << i)
		i -= 8 
	return (bitValue)

# Breaks IP into a range if it is subnetted.
def _getRange(ip, bits = 32):
	net = IPv4Network(ip)
	if (net[0] != net[-1]): # subnet
		return [str(net[0]), str(net[-1])]
	else:
		return [ip]
	
def _convertIPCondition(var, operator, ip, bits=32):
	ip = ip.strip().strip("'").strip('"') # remove quotation marks
	ipRange = _getRange(ip, bits)
	var = "z3.BitVec('{}',{})".format(var, bits)
	if len(ipRange) == 0:
		return condToStringDefault(var1=var,operator=operator, var2=_convertToBitVec(ip, bits))
	lower = _convertToBitVec(ipRange[0], bits)
	upper = _convertToBitVec(ipRange[-1], bits)
	if operator == "!=":
		return "Or({var} < {lower}, {var} > {upper})".format(var=var,lower=lower,upper=upper)
	if operator == "==":
		return "And({var} >= {lower}, {var} <= {upper})".format(var=var,lower=lower,upper=upper)
	
def _convertToBitVec(ip, bits = 32):
	ipBits = _convertIPToBits(ip, bits)
	return "z3.BitVec('{ip}',{bits})".format(ip = ipBits, bits = bits)

def _convertToZ3Var(var, reasoningType, bits = 32):
	if var in reasoningType:
		datatype = reasoningType[var]
		if datatype == 'BitVec':
			return "z3.{}('{}',{})".format(reasoningType[var], var, bits)
		else:
			return "z3.{}('{}')".format(reasoningType[var], var)
	elif _isIP(var):
		return "z3.IntVal('{}')".format(var)
	else: # We assume that anything that is not an ip is an integer
		return "z3.IntVal('{}')".format(var)

############################################ Atom Parsing ##################################
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
						elif not concatinatingVar[0].isdigit() and concatinatingVar not in variables and concatinatingVar not in c_variables:
							variables.append(concatinatingVar)
			if not hasOperator and not var[0].isdigit():
				if var not in c_variables and var not in variables:
					variables.append(var)
	return variables