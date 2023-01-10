import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Core.Homomorphism.Datalog.atom import DT_Atom
from Core.Homomorphism.Datalog.rule import DT_Rule
from utils.logging import timeit
import psycopg2 
import databaseconfig as cfg
from itertools import permutations
from copy import deepcopy
# initializing size of new c-variable
N = 2


# Note: We do not take into account cases where a c-variable appears in the head but not in the body
@timeit
def unify(rule1, rule2, rule1Name, constantUnificationOn = True):
	rule3, C1_head, C1_body = getEquivalentRule(rule1, rule1Name, constantUnificationOn)
	rule2_without_Faure = rule2.getRuleWithoutFaure()
	equal_subs_r3_to_r2 = getEquivalentSubstitutions(rule3, rule2_without_Faure)
	if not equal_subs_r3_to_r2: # no equal substitutions found
		return None
	C2_head, C2_body = getConditions(equal_subs_r3_to_r2, rule3, rule2, rule2_without_Faure, rule1Name, constantUnificationOn)
	finalRule = getNewRule(C1_head, C1_body, C2_head, C2_body, rule3, constantUnificationOn)
	return finalRule

@timeit
# Performs simplification of conditions and returns a new rule
def getNewRule(C1_head, C1_body, C2_head, C2_body, rule3, constantUnificationOn):
	# Delete repeated conditions
	# for cond in C1_head:
	# 	if cond in C1_body:
	# 		C1_head.remove(cond)
	# for cond in C2_head:
	# 	if cond in C2_body:
	# 		C2_head.remove(cond)

	if constantUnificationOn:
		cVarReplacements = getCVarReplacements(C1_head, C2_head)
		cVarReplacements.update(getCVarReplacements(C1_body, C2_body))
	
	C1_head_str = getSimplifiedCondition("And", C1_head+C1_body)
	C2_head_str = getSimplifiedCondition("And", C2_head+C2_body)
	C1_body_str = getSimplifiedCondition("And", C1_body)
	C2_body_str = getSimplifiedCondition("And", C2_body)
	# The presence of () in a condition means an empty condition. We do not let empty conditions propogate
	newHeadCondition = getSimplifiedCondition("Or", [C1_head_str]+[C2_head_str])
	newBodyCondition = getSimplifiedCondition("Or", [C1_body_str]+[C2_body_str])
	if len(rule3._additional_constraints) > 0 and rule3._additional_constraints[0][:2] == "Or" and newBodyCondition != '': # TODO: Hacky way to combine additional conditions of rules. 
		newBodyCondition = "("+rule3._additional_constraints[0][:-1] + "," + newBodyCondition + ")"
		rule3.removeAdditionalCondition()
	rule3._head.replaceCondition([newHeadCondition])
	rule3Str = str(rule3)

	if constantUnificationOn:
		for cvar in cVarReplacements:
			rule3Str = rule3Str.replace(cvar, cVarReplacements[cvar])
	newRule = DT_Rule(rule3Str, databaseTypes=rule3._databaseTypes, operators=rule3._operators, domains=rule3._domains, c_variables=rule3._c_variables, reasoning_engine=rule3._reasoning_engine, reasoning_type=rule3._reasoning_type, datatype=rule3._datatype, simplification_on=rule3._simplication_on, c_tables = rule3._c_tables, headAtom="", bodyAtoms = [], additional_constraints=[newBodyCondition]) #todo: additional_constraints=rule3._additional_constraints+newCondition
	return newRule

@timeit
def getSimplifiedCondition(operator, condList):
	if "" in condList:
		condList.remove("")
	if len(condList) == 0:
		return ""
	elif len(condList) == 1:
		return condList[0]
	else:
		return operator + "("+",".join(condList)+")"


# Takes two list of conditions involving c-variables. If any condition is common in both lists, the c-variable is replaced by a constant. e.g. getCVarReplacements([a == 3, b == 2], [a == 3, b ==4]) results in {a: 3} 
@timeit
def getCVarReplacements(conditions1, conditions2):
	cVarReplacements = {}
	for cond1 in conditions1.copy():
		if "==" not in cond1:
			continue
		for cond2 in conditions2.copy():
			if "==" not in cond1 or cond2 != cond1:
				continue
			# cvars are constants and can be replaced at this point
			conditions1.remove(cond1) # performs removal inplace
			conditions2.remove(cond2) # performs removal inplace
			cvar = cond2.split(" == ")[0]
			constant = cond2.split(" == ")[1]
			cVarReplacements[cvar] = constant
	return cVarReplacements

# get conditions from substitutions of rule 
# Constants is equality
# C-variables is replacement of conditions from rule 2
# Variable is ignoring
@timeit
def getConditions(substitution, rule, rule2, r2_without_faure, ruleName, constantUnificationOn):
	conditions = []
	for atom in rule2._body:
		if atom.constraints:
			conditions += atom.constraints
	atomNum = 0
	replacements = {}
	for atom in rule._body: # note that the order of tuples in substitution should be the same as the order of atoms of rule
		currTuple = substitution[atomNum][1:-1].split(",")
		parameterNum = 0
		for val in currTuple: 
			c_var_param = atom.parameters[parameterNum]
			if isConstant(c_var_param):
				continue
			datatype = atom.db["column_types"][parameterNum]
			if val[0] == '{': # is a list
				listCurrTuple = val[1:-1].split("^")
				for i, listVal in enumerate(listCurrTuple):
					if isConstant(listVal):
						newCondition = c_var_param[i] + " == " + listVal
						if newCondition not in conditions:
							conditions.append(newCondition) 
					elif "inet" not in datatype and int(listVal) in r2_without_faure._reverseMapping:
						variable = r2_without_faure._reverseMapping[int(listVal)]
						replacements[variable] = c_var_param[i]
						if "True" not in conditions:
							conditions.append("True")
					elif "inet" in datatype and listVal in r2_without_faure._reverseMapping:
						variable = r2_without_faure._reverseMapping[listVal]
						replacements[variable] = c_var_param[i]
						if "True" not in conditions:
							conditions.append("True")
					elif listVal in r2_without_faure._c_variables: # if val is a c_variables, we have to make sure that it is the same as the one used in the generalize rule
						replacements[listVal] = c_var_param[i]
			elif isConstant(val):
				newCondition = c_var_param + " == " + val
				if newCondition not in conditions:
					conditions.append(newCondition) 
			elif "inet" not in datatype and int(val) in r2_without_faure._reverseMapping: # variables
				variable = r2_without_faure._reverseMapping[int(val)]
				replacements[variable] = c_var_param
				if "True" not in conditions:
					conditions.append("True")
			elif "inet" in datatype and val in r2_without_faure._reverseMapping: # variables
				variable = r2_without_faure._reverseMapping[val]
				replacements[variable] = c_var_param
				if "True" not in conditions:
					conditions.append("True")
			elif val in r2_without_faure._c_variables: # if val is a c_variables, we have to make sure that it is the same as the one used in the generalize rule
				replacements[val] = c_var_param
			parameterNum += 1
		atomNum += 1
	_, newHeadCondition, _ = getEquivalentAtom(rule2._head, rule2, ruleName+"-H-"+rule2._head.db["name"], constantUnificationOn)
	replacedBodyConditions = []
	replacedHeadConditions = []

	for cond in conditions:
		for replacement in replacements:
			c_var = replacements[replacement]
			cond = cond.replace(replacement, c_var)
		replacedBodyConditions.append(cond)
	for cond in newHeadCondition:
		for replacement in replacements:
			c_var = replacements[replacement]
			cond = cond.replace(replacement, c_var)
		replacedHeadConditions.append(cond)

	# newHeadCondition = "And(" + ",".join(newHeadCondition) + ")"
	return replacedHeadConditions, replacedBodyConditions

# takes in a tuple and removes the last column
@timeit
def removeCondition(strTuple):
	i = len(strTuple)-1
	inBracketCount = 0
	while strTuple[i] != "," or inBracketCount > 0:
		i -= 1
		if (strTuple[i] == ")"):
			inBracketCount += 1
		if (strTuple[i] == "("):
			inBracketCount -= 1

	return strTuple[:i]+")"

# takes a particular substitution and returns the corresponding atoms
# e.g. given getAtomSubstitutions((100,1,{})', '(2,100,3,{})', '(100,1,{})'), ["l t0", "k t1", "l t2"] 
# returns {l(100,1),l(2,100,3),l(100,1) 
@timeit
def getAtomSubstitutions(substitution, tables_r2):
	substitutedAtoms = []
	for i in range(len(substitution)):
		currTuple = substitution[i]
		currTable = tables_r2[i].strip()[0]
		# substitutedAtom = currTable+removeCondition(currTuple) #ignoring the final condition column
		substitutedAtom = currTable+currTuple #ignoring the final condition column
		substitutedAtoms.append(substitutedAtom)
	return substitutedAtoms

# Get substitutions for which there is equivalence between rule and rule2
# The intuition is that the correct substitutions should contain all constants and c-variables that the data instance rule (rule2) had
@timeit
def getEquivalentSubstitutionsDB(rule3, r2_without_faure):
	substitutions_r3_to_r2, tables_r2 = getSubstitutions(rule3, r2_without_faure) 
	if len(substitutions_r3_to_r2) == 0: # no substitutions found so no way to align atoms
		return None 
	# create a set with that contains all mapped atoms of rule2 as string
	mappedAtomsRule2 = []
	for atom in r2_without_faure._body:
		parameters = []
		atomString = atom.db["name"] + "("
		for parameter in atom.parameters:
			if isinstance(parameter, list):
				listParams = []
				for i, listParam in enumerate(parameter):
					if listParam in r2_without_faure._mapping:
						listParams.append(str(r2_without_faure._mapping[listParam]))
					else:
						listParams.append(str(listParam))
				parameters.append('{'+"^".join(listParams)+'}')
			elif parameter in r2_without_faure._mapping:
				parameters.append(str(r2_without_faure._mapping[parameter]))
			else:
				parameters.append(str(parameter))
		atomString += ",".join(parameters) + ")"
		mappedAtomsRule2.append(atomString)

	for substitution in substitutions_r3_to_r2:
		substitutedAtoms = getAtomSubstitutions(substitution, tables_r2) 
		found = True
		for mappedAtom in mappedAtomsRule2:
			if mappedAtom not in substitutedAtoms: # missing substitution
				found = False
				break
			else:
				substitutedAtoms.remove(mappedAtom)
		if found: #TODO: Need to check that the head mapping is also correct
			return tuple(substitution)
	return None # if we reach this point without returning substitutions, that means we didn't find the correct substitution and need to return

@timeit
# Checks if two parameters match given the mapping
def matchParams(param1, param2, mappings):
	if isinstance(param1, list):
		for subparamNum, subParam1 in enumerate(param1):
			sumParam2 = param2[subparamNum]
			if isConstant(subParam1) and subParam1 != sumParam2:
				return False
			if subParam1 in mappings:
				return (mappings[subParam1] == sumParam2)
			mappings[subParam1] = sumParam2
	else:
		if param1 in mappings:
			return (mappings[param1] == param2)
		mappings[param1] = param2
	return True

@timeit
# returns substitutions in the same format as the DB version: e.g. ('(1,2)', '(1,3)', '(1,4)', '(3,10000)')
def getSubstitutionsMapping(rule3, r2_without_faure, mappings):
	completeSubstitutions = []
	for atom in rule3._body:
		atomSubstitutions = []
		for param in atom.parameters:
			if isinstance(param, list):
				listSubs = []
				for listVal in param:
					val = mappings[listVal]
					if val in r2_without_faure._mapping:
						listSubs.append(str(r2_without_faure._mapping[val]))
					else:
						listSubs.append(str(val))					
				atomSubstitutions.append("{"+"^".join(listSubs)+"}")					
			else:		
				val = mappings[param]
				if val in r2_without_faure._mapping:
					atomSubstitutions.append(str(r2_without_faure._mapping[val]))
				else:
					atomSubstitutions.append(str(val))
		completeSubstitutions.append("(" + ",".join(atomSubstitutions).replace(" ","") + ")")
	return tuple(completeSubstitutions)


@timeit
# Attempts to try all possible cominations of pattern matching rule3 with r2_without_faure
def getEquivalentSubstitutionsBruteForce(rule3, r2_without_faure):
	all_combinations = list(permutations(rule3._body))
	found = True
	headMappings = {}
	atom1 = rule3._head
	atom2 = r2_without_faure._head
	if atom1.db["name"] != atom2.db["name"]:
		return None
	for paramNum, param1 in enumerate(atom1.parameters):
		param2 = atom2.parameters[paramNum]
		if not matchParams(param1, param2, headMappings):
			return None
	for combination_rule in all_combinations:
		mappings = deepcopy(headMappings)
		found = True
		for atomNum, atom1 in enumerate(combination_rule):
			atom2 = r2_without_faure._body[atomNum]
			if atom1.db["name"] != atom2.db["name"]:
				found = False
				break
			for paramNum, param1 in enumerate(atom1.parameters):
				param2 = atom2.parameters[paramNum]
				if isinstance(param1, list):
					if len(param1) != len(param2):
						found - False
						break
					for listValNum, listVal1 in enumerate(param1):
						listVal2 = param2[listValNum]
						if not matchParams(param1, param2, mappings):
							found = False
							break
				else:
					if not matchParams(param1, param2, mappings):
						found = False
						break
			if not found:
				break
		if found:
			return getSubstitutionsMapping(rule3, r2_without_faure, mappings)
			# loop over original body and substitute with mappings
	return None # if we reach this point then none of the combinations work

def getEquivalentSubstitutions(rule3, r2_without_faure):
	# if len(rule3._body) > 8:
	# 	return getEquivalentSubstitutionsDB(rule3, r2_without_faure)
	# else:
	# 	return getEquivalentSubstitutionsBruteForce(rule3, r2_without_faure)
	return getEquivalentSubstitutionsBruteForce(rule3, r2_without_faure)



# Treats rule as program and rule2 as data and finds substitutions that enable homomorphism between rule and rule2
@timeit
def getSubstitutions(rule, rule2_without_Faure):
	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	rule2_without_Faure.initiateDB(conn)
	rule2_without_Faure.addConstants(conn)
	_, tables, constraints = rule.convertRuleToSQLPartitioned()
	tuples = []
	for table in tables:
		tuples.append(table.split()[1])
	sql = "select " + ", ".join(tuples) + " from " + ", ".join(tables)
	if (constraints):
		sql += " where " + " and ".join(constraints)
	cursor = conn.cursor()

	cursor.execute(sql)
	conn.commit()
	result = cursor.fetchall()
	return result, tables

# Takes a rule as input and returns a new rule that has all parameters replaced with c-variables. 
@timeit
def getEquivalentRule(rule, ruleName, constantUnificationOn):
	newAtoms = []
	newConditions = []
	c_vars = []
	newHead, newHeadCondition, new_cvars = getEquivalentAtom(rule._head, rule, ruleName+"-H-"+rule._head.db["name"], constantUnificationOn)
	c_vars += new_cvars
	new_ctables = rule._c_tables
	for atomNum, atom in enumerate(rule._body):
		newAtom, newCondition, new_cvars = getEquivalentAtom(atom, rule, ruleName+"-"+str(atomNum)+"-"+rule._head.db["name"], constantUnificationOn)
		c_vars += new_cvars # to avoid reusing a c-variable
		newAtoms.append(newAtom)
		newConditions += newCondition
		if atom.db["name"] not in new_ctables:
			new_ctables.append(atom.db["name"])
	rule_str = str(newHead) + " :- "
	for atom in newAtoms:
		rule_str += str(atom) + ", "
	rule_str = rule_str[:-2]
	newBodyCondition = ""
	if len(newCondition) == 1:
		newBodyCondition = newConditions[0]
	elif len(newCondition) > 1:
		newBodyCondition = "And(" + ",".join(newConditions) + ")"

	newRule = DT_Rule("", databaseTypes=rule._databaseTypes, operators=rule._operators, domains=rule._domains, c_variables=c_vars+rule._c_variables, reasoning_engine=rule._reasoning_engine, reasoning_type=rule._reasoning_type, datatype=rule._datatype, simplification_on=rule._simplication_on, c_tables = new_ctables, headAtom=newHead, bodyAtoms = newAtoms, additional_constraints=rule._additional_constraints)
	return newRule, newHeadCondition, newConditions

# TODO: the param < 10000 is a hardcoded condition. Need to fix 
def isConstant(param):
	if "." in param and param[:5] == '0.0.0':
		return False
	elif "." in param:
		return True
	elif param[0].isdigit() and int(param) < 100000:
		return True
	else:
		return False

# def generateNewCvar(c_vars):
# 	# using random.choices()
# 	# generating random strings
# 	randomString = ''.join(random.choices(string.ascii_lowercase, k=N))
# 	while randomString in c_vars:
# 		randomString = ''.join(random.choices(string.ascii_lowercase, k=N))
# 	return randomString


# Function assumes that atom1 and atom2 can be combined together
# Takes two atoms and returns a combined atom
# Atom number means atomName 
@timeit
def getEquivalentAtom(atom, rule, atomName, constantUnificationOn):
		table = atom.db["name"]
		conditions = []
		parameters = []
		c_tables = [table]
		c_variables = atom.c_variables
		new_cvariables = []
		for paramNum, param in enumerate(atom.parameters):
			if isinstance(param, list):
				listParams = []
				for i, listParam in enumerate(param):
					if isConstant(listParam):
						if constantUnificationOn:
							new_cvar = atomName+"_l"+str(paramNum+i)
							new_cvariables.append(new_cvar)
							listParams.append(new_cvar)
							if (new_cvar + " == " + listParam) not in conditions:
								conditions.append(new_cvar + " == " + listParam)
						else:
							listParams.append(listParam)
					elif listParam in c_variables or listParam in new_cvariables:
						listParams.append(listParam)
						if atom.constraints and atom.constraints[0] not in conditions:
							conditions += atom.constraints
					else: # variables:
						new_cvar = listParam + "`"
						new_cvariables.append(new_cvar)
						listParams.append(new_cvar)
				parameters.append('['+",".join(listParams)+']')

			elif isConstant(param):
				if constantUnificationOn:
					new_cvar = atomName+"_"+str(paramNum)
					new_cvariables.append(new_cvar)
					parameters.append(new_cvar)
					if (new_cvar + " == " + param) not in conditions:
						conditions.append(new_cvar + " == " + param)
				else:
					parameters.append(param)
			elif param in c_variables or param in new_cvariables:
				parameters.append(param)
				if atom.constraints and atom.constraints[0] not in conditions:
					conditions += atom.constraints
			else: # variables:
				new_cvar = param + "`"
				new_cvariables.append(new_cvar)
				parameters.append(new_cvar)
		atom_str = table+"("+",".join(parameters)+")"
		newAtom = DT_Atom(atom_str, rule._databaseTypes, rule._operators, c_variables+new_cvariables, table)
		return newAtom, conditions, new_cvariables

if __name__ == "__main__":
    p1 = "l(3,4) :- l(w,1), k(2,w,3), l(1,5)\nl(3,4) :- l(1,3), k(2,1,3), l(1,5)"
    # p1 = "l(3,4) :- l(1,3), l(1,5), k(2,1,3)\nl(3,4) :- k(2,w,3), l(w,1), l(1,5)"
    # p1 = "l(3,4) :- m(1,x), l(x,3), m(x,x), m(a,y), l(y,a), m(y,y)\nl(3,4) :- m(5,y), l(y,5), m(y,y), m(1,7), l(7,3), m(7,7)"

    # p1 = "m(1,x)[x == 1] :- l(1,2),l(1,3),l(1,4),m(2,x)[x == 1]\nm(1,x)[x == 2] :- l(1,2),l(1,3),l(1,4),m(3,x)[x == 2]"

    program1 = DT_Program(p1, {"l":["int4_faure", "int4_faure"],"m":["int4_faure", "int4_faure"], "k":["int4_faure", "int4_faure", "int4_faure"]}, domains={}, c_variables=['a','b','c','d','e','f','g'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["l","k","m"])

    newRule1 = program1._rules[0]
    newRule2 = program1._rules[1]
    print(unify(newRule1, newRule2, "r1"))
    # equivRule, equivConditions = getEquivalentRule(newRule1)
    # substitutions_r3_to_r2, tables_r2 = getSubstitutions(equivRule, newRule2) 
    # equal_subs_r3_to_r2 = getEquivalentSubstitutions(substitutions_r3_to_r2, equivRule, newRule2, tables_r2)
    # getConditions(equal_subs_r3_to_r2, equivRule, newRule2)