# We need to store the pattern independent of the symbols
# def combine(rule1, rule2):
# 	if (not headerSame(rule1, rule2)): # Compatible (might have different symbol for variables but have same pattern)
# 		return ""
# 	elif (not bodyTablesSame(rule1, rule2)):
# 		return ""
# 	elif (not variableLocSame(rule1, rule2)): # Get location of all variables in rule1 and compare against location in rule2. Should consider both c-variables and variables
# 		return ""
# 	else:
# 		tables = getTables(rule1)
# 		# We will compress each rule so that there is only one rule per 
# 		for table in tables:
# 			# assign a c-variable to each column
# 				# If a c-variable already exists in the column, use that c-variable for the entire column. The c-variable conditions are retained.
# 			# All assignments to the new c-variable should be added as a conjunction of conditions


# # =============== Example 1 ===============
# r1: .... :- .... R(2, 20), R(5, 50) -> R(x, y)[((x == 2 and y == 20) OR (x == 5 and y == 50))]
# r2: .... :- .... R(3, 10) -> R(x,y)[(x == 3 and y == 10)]

# => .... :- .... R(x,y)[(((x == 2 and y == 20) OR (x == 5 and y == 50)) OR (x == 3 and y == 10))]

# =============== Example 2 ===============
# .... :- .... R(2, 20), R(x, 50)[x < 3] -> R(x, y)[((x == 2 and y == 20) OR (x < 3 and y == 50))]
# .... :- .... R(3, 10) -> R(x,y)[(x == 3 and y == 10)]

# => .... :- .... R(x,y)[(((x == 2 and y == 20) OR (x < 5 and y == 50)) OR (x == 3 and y == 10))]

# Function assumes that atom1 and atom2 can be combined together
# Takes two atoms and returns a combined atom
def combineAtoms(atom1, atom2, oldDomain):
		table = atom1.table
		condition1 = ""
		condition2 = ""
		newAtomParams = []
		replacements = {}
		for paramNum in range(len(atom1.parameters)):
			param1 = atom1.parameters[paramNum]
			param2 = atom2.parameters[paramNum]
			if isVar(param1) and isCVar(param2):
				newAtomParams.append(param2) 
				condition1 = ""
				condition2 = atom2.condition			
			elif isVar(param2) and isCVar(param1):
				newAtomParams.append(param1) 
				condition1 = atom1.condition
				condition2 = ""
			elif isVar(param1) and isConstant(param2):
				newCVar = create new c-variable with ` after param1 with newDomain of column. Check from old domain to make sure c-var not used earlier
				newAtomParams.append(newCVar) 
				condition1 = ""
				condition2 = newCVar + " == " + param2			
			elif isVar(param2) and isConstant(param1):
				newCVar = create new c-variable with ` after param2 with newDomain of column. Check from old domain to make sure c-var not used earlier
				newAtomParams.append(newCVar) 
				condition1 = newCVar + " == " + param1
				condition2 = ""
			elif isVar(param1) and isVar(param2):
				newAtomParams.append(param1) # replace c-var, constant or var with var. Always use param1's var/cvar by default. Can use param2 but just need to be consistent
			elif isCVar(param1) and isCVar(param2): # both c-var
				newAtomParams.append(param1) # replace another c-var with c-var
				condition1 = atom1.condition
				condition2 = atom2.condition
				replacements[param2] = param1
			elif isCVar(param1): # param1 is cvar but param2 is a constant
				newAtomParams.append(param1) # replace constant with c-var
				condition1 = atom1.condition
				condition2 = param1 + " == " + param2
				#TODO: Extend domain
			elif isCVar(param2): # param2 is cvar but param1 is a constant
				newAtomParams.append(param2) # replace constant with c-var
				condition1 = param2 + " == " + param1
				condition2 = atom2.condition
				#TODO: Extend domain
			else: # both constants
				if param1 == param2:
					newAtomParams.append(param1) 
				else:
					newCVar = create new c-variable with newDomain of column. Check from old domain to make sure c-var not used earlier
					newAtomParams.append(newCVar) # replace constant by a c-variable
					condition1 = newCVar + " == " + param1
					condition2 = newCVar + " == " + param2
		return table, newAtomParams, condition1, condition2, newDomain, replacements

def addReplacements(condition, replacements):
	for replacingCvar in replacements:
		condition = condition.replace(replacingCvar, replacements[replacingCvar])
	return condition

def combine(rule1, rule2):
	alignPossible, atomMapping = mapAtoms(rule1, rule2) 
	if not alignPossible:
		return ""
	newDomains = {}
	headtable, newHeadAtomParams, headcondition1, headcondition2, headDomain, headReplacements = combineAtoms(rule1._head, rule2._head)
	newDomains.update(headDomain)
	newHeadCondition = addReplacements("Or("+headcondition1+", "+headcondition2+")",headReplacements)
	create newHeadAtom with headTable and newHeadAtomParams and newHeadCondition
	newRuleAtoms = []
	bodyConditions1 = []
	bodyConditions2 = []
	bodyReplacements = {}
	for atom in atomMapping:
		atom1 = atom
		atom2 = atomMapping[atom]
		bodytable, newBodyAtomParams, c1, c2, bodyDomain, replacements = combineAtoms(atom1, atom2)
		bodyConditions1.append(c1)
		bodyConditions2.append(c2)
		bodyReplacements.update(replacements)
		newDomains.update(bodyDomain)
		create newBodyAtom with bodytable and newBodyAtomParams
		newRuleAtoms.append(newBodyAtom)
	bodyJoinedCondition1 = "And("+",".join(bodyConditions1)+")"
	bodyJoinedCondition2 = "And("+",".join(bodyConditions2)+")"
	bodyConditionFinal = addReplacements("Or("+bodyJoinedCondition1+","+bodyJoinedCondition2+")", bodyReplacements)
	update condition of last atom as bodyConditionFinal
	make new rule from newRuleAtoms and new domain + domain of rule1 + domain of rule2 (choose the most liberal one) and return

# Returns {param: "atoms":[], "fingerPrint":[], "number":[], "type":""}
def addParamMapping(atom, parametersMapping, atomtype):
	currTable = atom.table
	i = 0
	for param in atom:
		if param not in parametersMapping:
			parametersMapping[param] = ["atoms":[], "fingerPrint":[], "number":[]]
		parametersMapping[param]["atom"].append(atom)
		parametersMapping[param]["number"].append(i)
		if param in currParams:
			parametersMapping[param]["fingerPrint"][-1] = parametersMapping[param]["fingerPrint"][-1] + "-" i # If a parameter appears more than once in the same atom, we add a dash. This is necessary to separate it from occurences in the same position at different atoms
		else:
			if atomtype == "Head":
				parametersMapping[param]["fingerPrint"].append("H_"+atom.table + "_" + i)
			elif atomtype == "Body":
				parametersMapping[param]["fingerPrint"].append("B_"+atom.table + "_" + i)
			else:
				print("Illegal atom type. Exiting")
				exit()
		i += 1

# Returns a dictionary with the fingerprint of an atom as the key and the 
# l(y,1), k(2,y,3), m(2,4)
# l(1,3), k(2,1,3), m(1,5)
# => 
# table mapping
# l
# Atom       fingerprint_1       fingerprint_2
# l(y,1)       l_1,k_2             l_2,m_1

# l
# Atom       fingerprint_1       fingerprint_2
# l(1,3)       l_1,m_1,k_2          l_2,k_3
def findFingerprints(rule):
	parametersMapping = {}
	for atom in rule:
		addParamMapping(atom, parametersMapping, "Body")
	addParamMapping(rule._head, parametersMapping, "Head")
	tableMapping = {}
	for param in parametersMapping:
		atoms = parametersMapping[param]["atoms"]
		paramNums = parametersMapping[param]["number"]
		if len(paramNums) != len(atoms):
			print("Length of atoms and parameter number is not the same. Something is wrong. Exiting")
			exit()
		for atomNum in range(len(atoms)):
			atom = atoms[atomNum]
			parameterNum = paramNums[atomNum]
			table = atom.table
			if table not in tableMapping:
				tableMapping[table] = {}
			if atom not in tableMapping[table]:
				tableMapping[table][atom] = {}
			tableMapping[table][atom][parameterNum] = parametersMapping[param]["fingerPrint"]

		# sort fingerprint and join with "," to get unique fingerprint

def fingerprintsMatch(atom1, atom2, fingerPrint1, fingerPrints2):
	for paramNum in range(len(atom1.parameters)):
		param1 = atom1.parameters[paramNum]
		param2 = atom2.parameters[paramNum]
		fingerPrintParam1 = fingerPrint1[paramNum]
		fingerPrintParam2 = fingerPrint2[paramNum]
		if isConstant(param1) and isConstant(param2):
			continue
		elif isConstant(param1): # the fingerprint should at least be a superset of the fingerprint of a variable/cvar
			if set(fingerPrintParam2) <= set(fingerPrintParam1): # subset checking
				continue
			else:
				return False
		elif isConstant(param2): # the fingerprint should at least be a superset of the fingerprint of a variable/cvar
			if set(fingerPrintParam1) <= set(fingerPrintParam2): # subset checking
				continue
			else:
				return False
		else: # not constant, just c-var or variables. Need to only check for the equivalence of fingerprints
			if set(fingerPrintParam1) <= set(fingerPrintParam2) and set(fingerPrintParam2) <= set(fingerPrintParam1): # check for equivalence
				continue
			else:
				return False
	return True


# atom belongs to fingerprints1
# find a matching atom from fingerprints2
def getMappingAtom(atom, fingerprintsTable1, fingerprintsTable2):
	parameters = atom.parameters
	fingerprintsOfAtom1 = fingerprintsTable1[atom.table][atom]
	for atom2 in fingerprintsTable2[atom.table]:
		if fingerprintsMatch(atom, atom2, fingerprintsOfAtom1, fingerprintsTable2[atom.table][atom2]):
			return atom2
	return "" # denotes that matching atom was not found


# Returns:
# 1. alignPossible: Is it possible to align the two rules?
# 2. atomMapping: List of atoms of rule1 mapped to corresponding list of atoms in rule2
def mapAtoms(rule1, rule2):
	if (not self.headerSame(rule1, rule2)): # Compatible (might have different symbol for variables but have same pattern)
		return False,{}
	elif (not self.bodyTablesSame(rule1, rule2)): # number of each table should be the same
		return False,{}
	else:
		fingerprintsAtoms1 = findFingerprints(sortedRule1) # loops over rules, returns any var, c-var, constant that occurs more than once in the body. Format of return would be a dictionary whereby Key is Atom plus column of all the repeats. Thus, for ... :- R(1,x), L(x,3), R(x,x) we get R_2,R_1-R_2,L_1 in sorted order. Sorting is necessary to make sure that the tables work as keys. Value is ["cvar/var/const", Tables/atoms involved]. This must also take into account the head (haven't thought this part through)
		fingerprintsAtoms2 = findFingerprints(sortedRule2)
		atomMapping = {}
		for atom in rule1:
			mappingAtom = getMappingAtom(atom, fingerprintsAtoms1, fingerprintsAtoms2)
			if not mappingAtom:
				return False,{}
			else:
				atomMapping[atom] = mappingAtom
		return True, atomMapping