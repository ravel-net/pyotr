import string
import random
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from Core.Homomorphism.Datalog.atom import DT_Atom
from Core.Homomorphism.Datalog.rule import DT_Rule
from Core.Homomorphism.Datalog.program import DT_Program
import psycopg2 
import databaseconfig as cfg
 
# initializing size of new c-variable
N = 2


# Note: We do not take into account cases where a c-variable appears in the head but not in the body
def unify(rule1, rule2, rule1Name):
	if not sameTables(rule1, rule2):
		return False
	if not headConstantsSame(rule1, rule2):
		return False
	rule3, C1_head, C1_body = getEquivalentRule(rule1, rule1Name)
	substitutions_r3_to_r2, tables_r2 = getSubstitutions(rule3, rule2) 
	if len(substitutions_r3_to_r2) == 0: # no substitutions found so no way to align atoms
		return None 
	equal_subs_r3_to_r2 = getEquivalentSubstitutions(substitutions_r3_to_r2, rule3, rule2, tables_r2)
	if not equal_subs_r3_to_r2: # no equal substitutions found
		return None
	C2_head, C2_body = getConditions(equal_subs_r3_to_r2, rule3, rule2, rule1Name)
	cVarReplacements = getCVarReplacements(C1_head, C2_head)
	cVarReplacements.update(getCVarReplacements(C1_body, C2_body))
	C1_head_str = "And("+",".join(C1_head+C1_body)+")"
	C2_head_str = "And("+",".join(C2_head+C2_body)+")"
	C1_body_str = "And("+",".join(C1_body)+")"
	C2_body_str = "And("+",".join(C2_body)+")"
	newHeadCondition = "Or("+C1_head_str+","+C2_head_str+")"
	newBodyCondition = "Or("+C1_body_str+","+C2_body_str+")"
	rule3._head.replaceCondition([newHeadCondition])
	rule3Str = str(rule3)
	for cvar in cVarReplacements:
		rule3Str = rule3Str.replace(cvar, cVarReplacements[cvar])
	newRule = DT_Rule(rule3Str, databaseTypes=rule3._databaseTypes, operators=rule3._operators, domains=rule3._domains, c_variables=rule3._c_variables, reasoning_engine=rule3._reasoning_engine, reasoning_type=rule3._reasoning_type, datatype=rule3._datatype, simplification_on=rule3._simplication_on, c_tables = rule3._c_tables, headAtom="", bodyAtoms = [], additional_constraints=[newBodyCondition]) #todo: additional_constraints=rule3._additional_constraints+newCondition
	return newRule

def sameTables(r1, r2):
	if r1._head.db["name"] != r2._head.db["name"]:
		return False
	r1_tables = {} # contains count of each table
	r2_tables = {} # contains count of each table
	for atom in r1._body:
		table = atom.db["name"]
		if table not in r1_tables:
			r1_tables[table] = 1
		else:
			r1_tables[table] += 1
	for atom in r2._body:
		table = atom.db["name"]
		if table not in r2_tables:
			r2_tables[table] = 1
		else:
			r2_tables[table] += 1
	for table in r1_tables:
		if table not in r2_tables or r2_tables[table] != r1_tables[table]:
			return False
	return True

def headConstantsSame(r1, r2):
	for paramNum in range(len(r1._head.parameters)):
		param1 = r1._head.parameters[paramNum]
		param2 = r2._head.parameters[paramNum]
		if isConstant(param1) and isConstant(param2) and param1 != param2:
			return False
	return True

# Takes two list of conditions involving c-variables. If any condition is common in both lists, the c-variable is replaced by a constant. e.g. getCVarReplacements([a == 3, b == 2], [a == 3, b ==4]) results in {a: 3} 
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
def getConditions(substitution, rule, rule2, ruleName):
	conditions = []
	for atom in rule._body:
		if atom.constraints:
			conditions += atom.constraints
	atomNum = 0

	replacements = {}
	for atom in rule._body: # note that the order of tuples in substitution should be the same as the order of atoms of rule
		currTuple = substitution[atomNum][1:-1].split(",")
		parameterNum = 0
		for val in currTuple[:-1]: # assuming last element is condition
			c_var_param = atom.parameters[parameterNum]
			if isConstant(val):
				newCondition = c_var_param + " == " + val
				if newCondition not in conditions:
					conditions.append(newCondition) 
			elif int(val) in rule2._reverseMapping:
				replaceVar = rule2._reverseMapping[int(val)]
				replacements[replaceVar] = c_var_param
			parameterNum += 1
		atomNum += 1
	replacedConditions = conditions
	for replacement in replacements:
		c_var = replacements[replacement]
		for cond in condition:
			replacedConditions.append(cond.replace(replacement, c_var))
	_, newHeadCondition, _ = getEquivalentAtom(rule2._head, rule2, ruleName+"-H-"+rule2._head.db["name"])
	# newHeadCondition = "And(" + ",".join(newHeadCondition) + ")"
	return newHeadCondition, replacedConditions,

# takes in a tuple and removes the last column
def removeCondition(strTuple):
	i = len(strTuple)-1
	while strTuple[i] != ",":
		i -= 1
	return strTuple[:i]+")"

# takes a particular substitution and returns the corresponding atoms
# e.g. given getAtomSubstitutions((100,1,{})', '(2,100,3,{})', '(100,1,{})'), ["l t0", "k t1", "l t2"] 
# returns {l(100,1),l(2,100,3),l(100,1) 
def getAtomSubstitutions(substitution, tables_r2):
	substitutedAtoms = []
	for i in range(len(substitution)):
		currTuple = substitution[i]
		currTable = tables_r2[i].strip()[0]
		substitutedAtom = currTable+removeCondition(currTuple) #ignoring the final condition column
		substitutedAtoms.append(substitutedAtom)
	return substitutedAtoms

# Get substitutions for which there is equivalence between rule and rule2
# The intuition is that the correct substitutions should contain all constants and c-variables that the data instance rule (rule2) had
def getEquivalentSubstitutions(substitutions, rule, rule2, tables_r2):
	# create a set with that contains all mapped atoms of rule2 as string
	mappedAtomsRule2 = []
	for atom in rule2._body:
		parameters = []
		atomString = atom.db["name"] + "("
		for parameter in atom.parameters:
			if parameter in rule2._mapping:
				parameters.append(str(rule2._mapping[parameter]))
			else:
				parameters.append(str(parameter))
		atomString += ",".join(parameters) + ")"
		mappedAtomsRule2.append(atomString)
	for substitution in substitutions:
		substitutedAtoms = getAtomSubstitutions(substitution, tables_r2) 
		found = True
		for mappedAtom in mappedAtomsRule2:
			if mappedAtom not in substitutedAtoms: # missing substitution
				found = False
				break
			else:
				substitutedAtoms.remove(mappedAtom)
		if found:
			return tuple(substitution)
	return None # if we reach this point without returning substitutions, that means we didn't find the correct substitution and need to return


# Treats rule as program and rule2 as data and finds substitutions that enable homomorphism between rule and rule2
def getSubstitutions(rule, rule2):
	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	rule2.initiateDB(conn)
	rule2.addConstants(conn)
	summary_nodes, tables, constraints = rule.convertRuleToSQLPartitioned()
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
def getEquivalentRule(rule, ruleName):
	newAtoms = []
	newConditions = []
	c_vars = []
	newHead, newHeadCondition, new_cvars = getEquivalentAtom(rule._head, rule, ruleName+"-H-"+rule._head.db["name"])
	c_vars += new_cvars
	new_ctables = rule._c_tables
	for atomNum, atom in enumerate(rule._body):
		newAtom, newCondition, new_cvars = getEquivalentAtom(atom, rule, ruleName+"-"+str(atomNum)+"-"+rule._head.db["name"])
		c_vars += new_cvars # to avoid reusing a c-variable
		newAtoms.append(newAtom)
		newConditions += newCondition
		if atom.db["name"] not in new_ctables:
			new_ctables.append(atom.db["name"])
	rule_str = str(newHead) + " :- "
	for atom in newAtoms:
		rule_str += str(atom) + ", "
	rule_str = rule_str[:-2]
	newBodyCondition = "And(" + ",".join(newConditions) + ")"
	newRule = DT_Rule("", databaseTypes=rule._databaseTypes, operators=rule._operators, domains=rule._domains, c_variables=c_vars+rule._c_variables, reasoning_engine=rule._reasoning_engine, reasoning_type=rule._reasoning_type, datatype=rule._datatype, simplification_on=rule._simplication_on, c_tables = new_ctables, headAtom=newHead, bodyAtoms = newAtoms, additional_constraints=rule._additional_constraints)
	# newHeadCondition = "And(" + ",".join(newHeadCondition) + ")"
	return newRule, newHeadCondition, newConditions

# TODO: the param < 100 is a hardcoded condition. Need to fix 
def isConstant(param):
	if param[0].isdigit() and int(param) < 100:
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
def getEquivalentAtom(atom, rule, atomName):
		table = atom.db["name"]
		conditions = []
		parameters = []
		c_tables = [table]
		c_variables = atom.c_variables
		new_cvariables = []
		for paramNum, param in enumerate(atom.parameters):
			if isConstant(param):
				new_cvar = atomName+"_"+str(paramNum)
				new_cvariables.append(new_cvar)
				parameters.append(new_cvar)
				conditions.append(new_cvar + " == " + param)
			elif param in c_variables:
				parameters.append(param)
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