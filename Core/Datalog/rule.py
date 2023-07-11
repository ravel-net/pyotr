import sys
from os.path import dirname, abspath
from Backend.reasoning.Z3.z3smt import z3SMTTools
from ipaddress import IPv4Address
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)

import re
from copy import deepcopy
from psycopg2.extras import execute_values
from Core.Datalog.atom import DT_Atom
from Core.Faure.faure_evaluation import FaureEvaluation
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples as merge_tuples
from utils import parsing_utils
# from Backend.reasoning.CUDD.BDDTools import BDDTools
from utils.logging import timeit
import logging
import time 

# TODO: Update documentation
class DT_Rule:
    """
    A class used to represent a datalog rule.
    rule format: head :- body
            head: atom
            body: atom1, atom2, ... [, constraint1, constraint2, ...]
            atom: table(param1, param2, ...)[condition1, condition2, ...]

    Attributes
    ----------
    _head : DT_Atom
        the head of the rule
    _body : DT_Atom[]
        the body of the rule, represented by an array of datalog rules
    _DBs : dictionary{"name", "column_names", "column_types"}[]
        list of databases referenced in the rule along with the column names and column types. The default column type is integer and the default column names is c1, c2, ..., cn
    _variables : string[]
        list of variables in rule (not including c-variables)
    _c_variables : string[]
        list of c-variables in rule
    _domains: {}
        domain of c-variables, with c-variable as key and the domain as a list. e.g. {'x':[1,2], 'y':[40,5]}
    _mapping : dictionary{variable : integer}
        mapping of variables to integers (used in containment). The only important part here is to map distinct variables to distinct constants. TODO: Should this mapping take into account the domain of c-variables?
    _operators : string[]
        operators supported in queries. Currently, only array concatination operator "||" is supported
    
    Faure related attributes: 
    _reasoning_engine, _reasoning_type, _datatype, _simplication_on

    Methods
    -------
    execute(conn)
        run this datalog rule on database pointed by psycopg2 connection "conn". Conversion to sql and execution of sql occurs here
    isHeadContained(conn)
        run sql query to check if the head of the rule is contained or not in the output. This is useful to terminate program execution when checking for containment. Conversion to sql and execution of sql occurs here
    """
    @timeit
    def __init__(self, rule_str, operators=[], reasoning_tool=None, headAtom="", bodyAtoms=[], additional_constraints=[], database=None, optimizations={}):
        self._additional_constraints = []
        self.db = database
        if (len(additional_constraints) > 0 and additional_constraints[0] != ''):
            self._additional_constraints = deepcopy(additional_constraints) 
        self.reasoning_tool = reasoning_tool
        if self.db:
            self._cVarMappingReverse = self.db.cVarMappingReverse
        self.optimizations = optimizations
        if headAtom and bodyAtoms:
            self.generateRule(head=headAtom, body=bodyAtoms, operators=operators, optimizations=self.optimizations, database=self.db)
        else:
            head_str = rule_str.split(":-")[0].strip()
            additional_constraint_split = rule_str.split(":-")[1].strip().split(",(")
            body_str = additional_constraint_split[0]
            if len(additional_constraint_split) > 1:
                additional_constraint_split[1] = additional_constraint_split[1][:-1]
                self._additional_constraints += additional_constraint_split[1:]
            head = DT_Atom(head_str, database=self.db, operators=operators)
            body = []
            # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
            atom_strs = parsing_utils.split_atoms(body_str)
            for atom_str in atom_strs:
                atom_str = atom_str.strip()
                # if atom_str[0] == '(': # additional constraint
                #     self._additional_constraints.append(atom_str[1:-1])
                #     continue
                currAtom = DT_Atom(atom_str, database=self.db, operators=operators)
                body.append(currAtom)
            self.generateRule(head=head, body=body, operators=operators, optimizations=self.optimizations, database=self.db)

    def safe(self):
        headVars = self._head.variables
        for var in headVars:
            if var not in self._variables:
                return False        
        return True

    @timeit
    def generateRule(self, head, body, operators=[], optimizations={}, database=None):
        self._variables = [] 
        self._c_variables = [] 
        self._head = head
        self._body = body
        self._mapping = {}
        self._operators = operators
        self._reasoning_engine = "z3" # TODO: Change this to have a member of reasoning tool that identifies the engine
        self._simplication_on = self.optimizations["simplification_on"]
        if self.db:
            self._c_tables = self.db.c_tables
        self._reverseMapping = {}
        self._recursive_rules = self.optimizations["recursive_rules"]
        
        #TODO: Function to add c-vars and vars 
        for currAtom in self._body:
            atomVars = currAtom.variables
            for var in atomVars:
                if var not in self._variables:
                    self._variables.append(var)
            
            atomCVars = currAtom.c_variables
            for var in atomCVars:
                if var not in self._c_variables:
                    self._c_variables.append(var)
                            
        # corner case, relation of atom in head does not appear in the body, e.g.,  R(n1, n2): link(n1, n2)
        # if self._head.table.name not in db_names:
        #     self._DBs.append(self._head.db)
        #     db_names.append(self._head.table.name)

        # TODO: Make sure that the mapping does not overlap with any other constant in the body
        # TODO: Add a Function to create mapping
        i = 0
        for atom in self._body:
            for paramNum, var in enumerate(atom.parameters):
                if isinstance(var, list):
                    for listVar in var:
                        if listVar not in self._variables:
                            continue
                        paramDatatype = paramDatatype[:-2]
                        if "inet" in paramDatatype:
                            #TODO: Document that IPs from 0.0.0.1 to 0.0.255.0 are reserved for c-variables. IPs from 0.1.0.0 to 0.1.0.255 are reserved for variables. Need a check on rules to ensure that there is no overlapping constant
                            IPaddr = str(IPv4Address(int(IPv4Address('0.1.0.0')) + i))
                            self._mapping[listVar] = IPaddr
                            self._reverseMapping[IPaddr] = listVar
                            i += 1
                        else: # Int data type
                            # TODO: Document that integers above 100000 are reserved for variables and negative integers are reserved for c-variables. Include a check that no integers should overlap
                            self._mapping[listVar] = 100000+i
                            self._reverseMapping[100000+i] = listVar
                            i += 1
                    continue    
                if var not in self._variables:
                    continue
                paramDatatype = atom.table.getColmType(paramNum)
                if "inet" in paramDatatype:
                    IPaddr = str(IPv4Address(int(IPv4Address('0.1.0.0')) + i))
                    self._mapping[var] = IPaddr
                    self._reverseMapping[IPaddr] = var
                    i += 1
                else: # Int data type
                    self._mapping[var] = 100000+i
                    self._reverseMapping[100000+i] = var
                    i += 1

        # in case of unsafe rule
        if self.safe():
            self._summary_nodes, self._tables, self._constraints, self._constraintsZ3Format = self.convertRuleToSQLPartitioned()
            self.sql = self.convertRuleToSQL()
        else:
            print("\n------------------------")
            print("Unsafe rule: {}!".format(self)) 
            print("------------------------\n")

        self.selectColumns = self.calculateSelect() 

    @timeit
    # Includes the select part of query including datatype
    def calculateSelect(self):
        selectColumns = []
        for i, colName in enumerate(self._head.table.columns):
            selectColumns.append("CAST({} as {})".format(colName, self._head.table.getColmType(i)))
        return selectColumns

    @property
    def numBodyAtoms(self):
        return len(self._body)

    @property
    def getDBs(self):
        return self._DBs

    def removeAdditionalCondition(self):
        self._additional_constraints = []

    def deleteAtom(self, atomNum):
        del self._body[atomNum]

    @timeit
    def copyWithDeletedAtom(self, atomNum):
        newRule_head = self._head
        newRule_body = []
        i = 0
        for atom in self._body:
            i += 1
            if i == atomNum+1:
                continue
            else:
                newRule_body.append(atom)

        newRule = DT_Rule(rule_str="", database=self.db, operators=self._operators, reasoning_tool=self.reasoning_tool, headAtom=newRule_head, bodyAtoms = newRule_body, additional_constraints=self._additional_constraints, optimizations=self.optimizations)
        return newRule

    @timeit
    def addConstants(self, conn, cVarMappingReverse):
        self.initiateDB(conn)
        for atom in self._body:
            atom.addConstants(conn, self._mapping, cVarMappingReverse)

        # if using bdd engine, convert text[]-type condition to integer-type condition
        if len(self._c_tables) > 0 and self._reasoning_engine == 'bdd': 
            for ctablename in self._c_tables:
                self.reasoning_tool.process_condition_on_ctable(conn, ctablename)

    @timeit
    def convertRuleToSQL(self):
        sql = "select " + ", ".join(self._summary_nodes) + " from " + ", ".join(self._tables)
        if (self._constraints):
            sql += " where " + " and ".join(self._constraints)
        return sql

    # initiates database of rule
    @timeit
    def initiateDB(self, conn):
        for atom in self._body:
            atom.table.initiateTable(conn)

    @timeit
    def getRuleWithoutFaure(self): # returns the same rule but without any c-variables and conditions
        newRuleStr = self._head.strAtomWithoutConditions() + " :- "
        for bodyAtom in self._body:
            newRuleStr += bodyAtom.strAtomWithoutConditions() + ", "
        newRuleStr = newRuleStr[:-2]
        newRule = DT_Rule(newRuleStr, database=self.db, operators=self.operators, reasoning_tool=self.reasoning_tool, optimizations=self.optimizations) # assuming that the default is without faure
        return newRule

    @timeit
    def convertRuleToSQLPartitioned(self):
        tables = []
        constraints = []
        variableList = {} # stores variable to table.column mapping. etc: {'x': ['t0.c0'], 'w': ['t0.c1', 't1.c0'], 'z': ['t0.c2', 't1.c1', 't2.c0'], 'y': ['t2.c1']}
        summary = set()
        summary_nodes = []
        arrayVariables = [] # stores all variables that are involved with array operations. This is necessary to replace the condition of the operation with All[variable]
        constraintsZ3Format = []
        constraints_for_array = {} # format: {'location': list[variables]}, e.g., {'t1.n3':['a1', 'e2']}
        variables_idx_in_array = {} # format {'var': list[location], e.g., {'a1':['t1.n3','t4.n1']}}
        for i, atom in enumerate(self._body):
            tables.append("{} t{}".format(atom.table.name, i))
            # currentTableName = atom.table.name
            columns = {}
            if self.db:
                currentTable = self.db.getTable(atom.table.name)
                columns = currentTable.columns
            for col, val in enumerate(atom.parameters):
                if type(val) == list:
                    loc = "t{}.{}".format(i, atom.table.getColmName(col))
                    constraints_for_array[loc] = val
                    for idx, var in enumerate(val):
                        if var not in variableList and var not in variables_idx_in_array:
                            variables_idx_in_array[var] = {'location': loc}
                            variables_idx_in_array[var]['idx'] = idx+1 # postgres array uses one-based numbering convention
                elif val[0].isdigit():
                    if len(columns) > 0 and "inet_faure" in columns[atom.table.getColmName(col)]:
                        constraints.append("(t{}.{} = {} or t{}.{} < '0.0.255.0')".format(i, atom.table.getColmName(col), val, i, atom.table.getColmName(col)))
                    elif len(columns) > 0 and "inet" in columns[atom.table.getColmName(col)]:
                        constraints.append("t{}.{} = {}".format(i, atom.table.getColmName(col), val))
                    elif len(columns) > 0 and "integer_faure" in columns[atom.table.getColmName(col)]:
                        constraints.append("(t{}.{} = {} or t{}.{} < 0)".format(i, atom.table.getColmName(col), val, i, atom.table.getColmName(col)))
                    else:
                        constraints.append("t{}.{} = {}".format(i, atom.table.getColmName(col), val))
                    constraintsZ3Format.append("t{}.{} == {}".format(i, atom.table.getColmName(col), val))
                else: # variable or c_variable
                    if val not in variableList:
                        variableList[val] = []
                    if "[]" in atom.table.getColmType(col):
                        arrayVariables.append(val)
                    variableList[val].append("t{}.{}".format(i, atom.table.getColmName(col)))
        for idx, param in enumerate(self._head.parameters):
            if type(param) == list:
                replace_var2attr = []
                for p in param:
                    if p in variableList:
                        replace_var2attr.append(str(variableList[p][0]))
                    elif p in variables_idx_in_array:
                        replace_var2attr.append("{}[{}]".format(variables_idx_in_array[p]['location'], variables_idx_in_array[p]['idx']))
                    elif p[0].isdigit: # could be a constant that is not found in the body
                        replace_var2attr.append("{}".format(str(p)))
                    else: # could be a c-variable that is not found in the body
                        replace_var2attr.append("'{}'".format(self._cVarMappingReverse[p]))

                summary = "ARRAY[" + ", ".join(replace_var2attr) + "]"
                summary_nodes.append("{} as {}".format(summary, self._head.table.getColmName(idx)))
            else:
                hasOperator = False
                for op in self._operators:
                    concatinatingValues = []
                    if (op in param):
                        hasOperator = True
                        concatinatingVars = param.split(op)
                        for concatinatingVar in concatinatingVars:
                            concatinatingVar = concatinatingVar.strip()
                            if '[' in concatinatingVar and ']' in concatinatingVar:
                                concatList = []
                                concatinatingVar = concatinatingVar.replace("[",'').replace("]",'').split(",")
                                for v in concatinatingVar:
                                    concatList.append(variableList[v][0])
                                concatinatingValues.append("ARRAY[" + ", ".join(concatList) + "]")
                            elif not concatinatingVar[0].isdigit():
                                concatinatingValues.append(variableList[concatinatingVar][0])
                        opString = " " + op + " "
                        summary = opString.join(concatinatingValues)
                        if summary:
                            summary_nodes.append("{} as {}".format(summary, self._head.table.getColmName(idx)))
                if not hasOperator:
                    if param[0].isdigit(): # constant parameter
                        summary_nodes.append("{} as {}".format(param, self._head.table.getColmName(idx)))
                    else:
                        if param not in variableList.keys() and param not in self._cVarMappingReverse:
                            summary_nodes.append("'{}' as {}".format(param, self._head.table.getColmName(idx)))
                        elif param not in variableList.keys() and param in self._cVarMappingReverse:
                            summary_nodes.append("'{}' as {}".format(self._cVarMappingReverse[param], self._head.table.getColmName(idx)))
                        else: # variable or c-var that also appears in body
                            summary_nodes.append("{} as {}".format(variableList[param][0], self._head.table.getColmName(idx)))
        for var in variableList:
            for i in range(len(variableList[var])-1):
                colmName = variableList[var][i].split(".")[1]
                tableNameSQL = variableList[var][i].split(".")[0]
                for table in tables:
                    tableName = table.split()[0]
                    tableNameS = table.split()[1]
                    if tableNameSQL == tableNameS:
                        break
                columns = {}
                if self.db:
                    currentTable = self.db.getTable(tableName)
                    columns = currentTable.columns

                if len(columns) > 0 and "inet_faure" in columns[colmName]:
                    constraints.append("(" + variableList[var][i] + " = " + variableList[var][i+1] + " or " + variableList[var][i] + " < '0.0.255.0')")
                elif len(columns) > 0 and "integer_faure" in columns[colmName]:
                    constraints.append("(" + variableList[var][i] + " = " + variableList[var][i+1] + " or " + variableList[var][i] + "< 0)")
                else:
                    constraints.append(variableList[var][i] + " = " + variableList[var][i+1])
                constraintsZ3Format.append(variableList[var][i] + " == " + variableList[var][i+1])

        # adding variables in arrays in variableList
        # TODO: Possibly inefficient
        varListWithArray = deepcopy(variableList)
        for var in variables_idx_in_array:
            varListWithArray[var] = [variables_idx_in_array[var]["location"]+'['+str(variables_idx_in_array[var]["idx"]) + ']']

        # Additional constraints are faure constraints.
        constraints_faure = []
        for atom in self._body:
            for constraint in atom.conditions:
                constraints_faure.append(constraint)

        if len(constraints_faure) > 0:
            faure_constraints = self.addtional_constraints2where_clause(constraints_faure, varListWithArray, arrayVariables)
            constraintsZ3Format += parsing_utils.replaceCVars(constraints_faure, varListWithArray, arrayVariables)
            constraints.append(faure_constraints)

        # TODO: Check for appropriate z3 format conversion for arrays
        # constraints for array
        for attr in constraints_for_array:
            for var in constraints_for_array[attr]:
                if var in variableList:
                    constraints.append("{} = ANY({})".format(variableList[var][0], attr))
                # else:
                #     constraints.append("{}[{}] = ANY({})".format(variables_idx_in_array[var]['location'], variables_idx_in_array[var]['idx'], attr))

        return summary_nodes, tables, constraints, constraintsZ3Format

    @timeit
    def execute(self, conn, faure_evaluation_mode="contradiction"):
        if len(self._c_variables) == 0:
            cursor = conn.cursor()
            except_sql = "insert into {header_table} ({sql} except select {attrs} from {header_table})".format(header_table=self._head.table.name, sql = self.sql, attrs= ", ".join(self.selectColumns))
            if (not self._recursive_rules):
                except_sql = "insert into {header_table} {sql}".format(header_table=self._head.table.name, sql = self.sql)
            start = time.time()
            cursor.execute(except_sql)
            affectedRows = 0
            if (self._recursive_rules):
                affectedRows = cursor.rowcount
            end = time.time()
            total_time = end-start
            logging.info(f'Time: execute_except_sql took {total_time:.4f}')
            changed = (affectedRows > 0)
            if (not self._recursive_rules):
                changed = False
        else:
            return self.run_with_faure(conn, self.sql, faure_evaluation_mode)
        return changed

    @timeit
    def isHeadContained(self, conn):
        if len(self._c_variables) != 0:
            return self.is_head_contained_faure(conn)
        
        constraints = []
        for col, param in enumerate(self._head.parameters):
            if type(param) == list:
                mapping_constants = []
                for p in param:
                    mapping_constants.append(str(self._mapping[p]))
                # check if two arrays are equal
                constraints.append("ARRAY[{}] @> {}".format(", ".join(mapping_constants), self._head.table.getColmName(col)))
                constraints.append("ARRAY[{}] <@ {}".format(", ".join(mapping_constants), self._head.table.getColmName(col)))
            else:
                hasOperator = False
                for op in self._operators:
                    concatinatingValues = []
                    if (op in param):
                        hasOperator = True
                        concatinatingVars = param.split(op)
                        for concatinatingVar in concatinatingVars:
                            concatinatingVar = concatinatingVar.strip()
                            if not concatinatingVar[0].isdigit():
                                concatinatingValues.append(str(self._mapping[concatinatingVar]))
                        if op == "||":
                            finalString = "{" + ",".join(concatinatingValues) +"}"
                            constraints.append("{} = '{}'".format(self._head.table.getColmName(col), finalString))
                        else:
                            print("Error. Unsupported OP encountered")
                            exit()
                if not hasOperator:
                    if param[0].isdigit():
                        constraints.append("{} = {}".format(self._head.table.getColmName(col), param))
                    else:
                        constraints.append("{} = {}".format(self._head.table.getColmName(col), str(self._mapping[param])))
        sql = "select * from " + self._head.table.name
        if (constraints):
            sql += " where " + " and ".join(constraints)
        cursor = conn.cursor()
        cursor.execute(sql)
        result = cursor.fetchall()
        conn.commit()
        contained = (len(result) > 0)
        return contained
    
    # Check if two variables/constants/c_variables are the same
    @timeit
    def _equal_faure(self, elem1, elem2):
        elem1 = elem1.strip().replace("'","")
        elem2 = elem2.strip().replace("'","")
        if elem1 in self._c_variables or elem2 in self._c_variables:
            return True
        else:
            return (str(elem1) == str(elem2))

    # Check if two lists have the same data portion
    @timeit
    def _sameDataPortion(self, list1, list2):
        for i, elem in enumerate(list1):
            elem2 = list2[i]
            if type(elem) == list: # Assuming that the format of column type is the same
                if ("}" in elem2):
                    elem2 = elem2.strip('}{')
                    elem2 = elem2.split(',')
                if len(elem) != len(elem2):
                    return False
                for j,p in enumerate(elem):
                    p2 = elem2[j]
                    if not self._equal_faure(str(p), str(p2)):
                        return False
            elif not self._equal_faure(str(elem), str(elem2)):
                return False
        return True

    # 1. Selects all tuples in table
    # 2. Finds out the target head tuple (by mapping the variables to assigned constants)
    # 3. Loops over all tuples to see if target tuple is found
    # 4. Checks if the condition of the head implies the condition in the found tuple 
    @timeit
    def is_head_contained_faure(self, conn):
        cursor = conn.cursor()
        contains = False

        # delete redundants
        # if self._reasoning_engine == 'z3':
        #     merge_tuples.merge_tuples_z3(self._head.table.name, # tablename of header
        #                                 information_on=False) 
        # else:
        #     merge_tuples.merge_tuples_bdd(self._head.table.name, self.reasoning_tool, information_on=False)

        '''
        check whether Q_summary is in resulting table
        '''
        sql = "select {} from {}".format(", ".join(self.selectColumns), self._head.table.name)
        if self._reasoning_engine == 'bdd':
            sql = sql.replace('text[]', 'integer')
        cursor.execute(sql)
        resulting_tuples = cursor.fetchall()
        conn.commit()
        
        # add constants to header data portion
        header_data_portion = []
        for i, p  in enumerate(self._head.parameters):
            col_type = self._head.table.getColmType(i)
            if type(p) == list:
                newP = []
                for elem in p:
                    if elem in self._c_variables:
                        newP.append(self._cVarMappingReverse[elem])
                    elif elem.isdigit() and "integer" in col_type:
                        newP.append(int(elem))
                    elif elem.isdigit() and "integer" not in col_type:
                        newP.append(str(elem))
                    elif len(elem.split('.')) == 4: # it is an IP constant
                        # newP.append("'{}'".format(elem))
                        newP.append(str(elem))
                    elif "integer" in col_type:
                        newP.append(self._mapping[elem])                    
                    else:
                        newP.append(str(self._mapping[elem]))
                header_data_portion.append(newP)
            else:
                if p in self._c_variables or type(p) == int:
                    header_data_portion.append(self._cVarMappingReverse[p])
                elif p.isdigit() and "integer" in col_type:
                    header_data_portion.append(int(p))
                elif p.isdigit() and "integer" not in col_type:
                    header_data_portion.append(str(p))
                elif len(p.split('.')) == 4: # it is an IP constant
                    # header_data_portion.append("'{}'".format(p))
                    header_data_portion.append(str(p))
                elif "integer" in col_type:
                    header_data_portion.append(self._mapping[p])
                else:
                    header_data_portion.append(str(self._mapping[p]))

        # set header condition
        header_condition = None
        if self._head.conditions:
            if len(self._head.conditions) == 0:
                header_condition = ""
            elif len(self._head.conditions) == 1:
                header_condition = self._head.conditions[0]
            else:
                header_condition = "And({})".format(", ".join(self._head.conditions))
        for tup in resulting_tuples:
            tup_cond = tup[-1] # assume condition locates the last position
            data_portion = list(tup[:-1])
            if self._sameDataPortion(header_data_portion, data_portion): 
                # Adding extra c-conditions
                extra_conditions = []
                for i, dat in enumerate(header_data_portion):
                    if type(dat) == list:
                        data_portion_list = str(data_portion[i])[1:-1].split(",") # Removes curly parts 
                        for j, listdat in enumerate(dat):
                            extra_conditions.append("{} == {}".format(listdat, data_portion_list[j]))
                    else:        
                        if isinstance(dat,str):
                            dat = dat.replace("'","")
                        extra_conditions.append("{} == {}".format(dat, data_portion[i]))
                if self._reasoning_engine == 'z3':
                    # convert list of conditions to a string of condition
                    extra_conditions = "And({})".format(", ".join(extra_conditions))
                    str_tup_cond = "And({})".format(", ".join(tup_cond))
                    if len(tup_cond) == 0:
                        str_tup_cond = ""
                    elif len(tup_cond) == 1:
                        str_tup_cond = tup_cond[0]

                    # Does the condition in the header imply the condition in the tuple?
                    # We are not checking for equivalence because we are merging tuples
                    # if not self.reasoning_tool.iscontradiction([str_tup_cond]) and self.reasoning_tool.is_implication(str_tup_cond, extra_conditions) and self.reasoning_tool.is_implication(header_condition, str_tup_cond):
                    if not self.reasoning_tool.iscontradiction([str_tup_cond]) and self.reasoning_tool.is_implication(str_tup_cond, extra_conditions):
                        contains = True
                        return contains                    
                elif self._reasoning_engine == 'bdd':
                    # convert list of conditions to a string of condition
                    extra_conditions = "And({})".format(", ".join(extra_conditions))
                    extra_condition_idx = self.reasoning_tool.str_to_BDD(extra_conditions)
                    if header_condition is None:
                        header_condition=""
                    header_condition_idx = self.reasoning_tool.str_to_BDD(header_condition)

                    if self.reasoning_tool.evaluate(tup_cond) != 0 and \
                        self.reasoning_tool.is_implication(tup_cond, extra_condition_idx) and \
                        (self.reasoning_tool.is_implication(tup_cond, header_condition_idx) and self.reasoning_tool.is_implication(header_condition_idx, tup_cond)):
                        contains = True
                        return contains
                else:
                    print("We do not support {} engine!".format(self._reasoning_engine))
                    exit()
        return contains


    # The argument tuple1 and tuple2 are single tuples. 
    # Functions checks if the tuples are equivalent
    @timeit
    def tuplesEquivalent(self, tuple1, tuple2):
        if str(tuple1[:-1]) != str(tuple2[:-1]): # data portion must be the same
            return False
        elif len(tuple1) == 1 and len(tuple2) == 1:
            return True
        conditions1 = tuple1[-1]
        conditions2 = tuple2[-1]
        if self._reasoning_engine == 'z3':
            if len(conditions1) != len(conditions2): # for Z3, we can just check the strings since they would be equal if the conditions are equal. This is only true when inserting head
                return False
            for i, cond in enumerate(conditions1):
                if str(cond) != str(conditions2[i]):
                    return False
        else:
            if not (self.reasoning_tool.is_implication(conditions1, conditions2) and self.reasoning_tool.is_implication(conditions2, conditions1)):
                return False
        return True
    
    # Adds the result of the table "output" to head. Only adds distinct variables
    @timeit
    def insertTuplesToHead(self, conn, fromTable="output"):
        cursor = conn.cursor()
        header_table = self._head.table.name

        if (not self._recursive_rules):
            sql = "insert into {header_table} select * from {fromTable}".format(header_table=header_table, fromTable=fromTable)
            cursor.execute(sql)
            conn.commit()
            return False
        else:
            select_gen_sql = "select distinct {} from {}".format(", ".join(self.selectColumns), fromTable)
            if self._reasoning_engine == 'bdd': # replace condition datatype from text[] to integer 
                select_gen_sql = select_gen_sql.replace('text[]', 'integer')  
            cursor.execute(select_gen_sql)
            generatedHead = cursor.fetchall()
            if not generatedHead:
                return False

            select_head_table_sql = "select * from {}".format(header_table)

            cursor.execute(select_head_table_sql)
            head_table = cursor.fetchall()

            # Check if any of the generated head is new
            newTuples = []
            for generatedTuple in generatedHead:
                alreadExists = False
                for tuple in head_table:
                    if self.tuplesEquivalent(generatedTuple, tuple): # only add tuples that are not equivalent
                        alreadExists = True
                if not alreadExists:
                    newTuples.append(generatedTuple)
            if len(newTuples) > 0:
                execute_values(cursor, "insert into {} values %s".format(header_table), newTuples)
                conn.commit()
                return True
            else:
                conn.commit()
                return False

    @timeit
    def run_with_faure(self, conn, program_sql, faure_evaluation_mode="contradiction"):
        header_table = self._head.table.name
        changed = False
        '''
        generate new facts
        '''
        FaureEvaluation(conn, program_sql, reasoning_tool=self.reasoning_tool, additional_condition=",".join(self._additional_constraints), output_table="output", domains=self.db.cvar_domain, reasoning_engine=self._reasoning_engine, reasoning_sort=self.db.reasoning_types, simplication_on=self._simplication_on, information_on=True, faure_evaluation_mode=faure_evaluation_mode, sqlPartitioned = {"summary_nodes": self._summary_nodes, "tables":self._tables, "constraints":self._constraints, "constraintsZ3Format":self._constraintsZ3Format})
        changed = self.insertTuplesToHead(conn)
        return changed

    @timeit
    def addtional_constraints2where_clause(self, constraints, variableList, arrayVariables):
        newConstraints = []
        singleLocVarList = {}
        for var in variableList: # Variable list contains location for every occurrence of the variable. Need to fix
            if var in arrayVariables:
                singleLocVarList[var] = "[" + variableList[var][0] + "]"
            else:
                singleLocVarList[var] = variableList[var][0]
        for constraint in constraints:
            newConstraints.append(parsing_utils.z3ToSQL(condition = constraint, replacements = singleLocVarList, cVarTypes=self.db.cVarTypes))
        newConstraint = newConstraints[0] # note that this function should only be called when there are positive number of constraints
        if len(newConstraints) > 1:
            newConstraint = " and ".join(newConstraints)
        return newConstraint.replace("==","=")

    def __str__(self):
        string = str(self._head) + " :- "
        for atom in self._body:
            string += str(atom) + ","
        if self._additional_constraints:
            string += "({})".format(",".join(self._additional_constraints))
            return string
        return string[:-1]

if __name__ == "__main__":
    a = "Asd"
    rule = DT_Rule("A(x,y,z) :- Gasd(x,1,y)[],B(z,x),C(y,z,2)")
    # rule.isHeadContained(a)
    # print(atom.db)