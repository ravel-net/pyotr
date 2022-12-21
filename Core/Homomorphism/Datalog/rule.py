# Constructor: string to array of atoms (head and list of body)
# each atom has a database and arguments (string)

# Iterate over atoms
# Delete atom
# Make new rule with a deleted atom
# Rule to sql
# Populate with constants in database (return the expected head). Give connection
# Expected head to sql
import sys
from os.path import dirname, abspath
import time

from Backend.reasoning.Z3.z3smt import z3SMTTools
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)

import re
from copy import deepcopy
from psycopg2.extras import execute_values
from Core.Homomorphism.Datalog.atom import DT_Atom
from Core.Homomorphism.faure_translator.faure_evaluation import FaureEvaluation
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples as merge_tuples
from utils.parsing_utils import z3ToSQL
from Backend.reasoning.CUDD.BDDTools import BDDTools

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

    def __init__(self, rule_str, databaseTypes={}, operators=[], domains={}, c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Int', simplification_on=True, c_tables=[], reasoning_tool=None, headAtom="", bodyAtoms=[], additional_constraints=[]):
        self._additional_constraints = deepcopy(additional_constraints) 
        self.reasoning_tool = reasoning_tool
        if headAtom and bodyAtoms:
            self.generateRule(headAtom, bodyAtoms, databaseTypes, operators, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables)
        else:
            head_str = rule_str.split(":-")[0].strip()
            additional_constraint_split = rule_str.split(":-")[1].strip().split(",(")
            body_str = additional_constraint_split[0]
            if len(additional_constraint_split) > 1:
                self._additional_constraints += additional_constraint_split[1:]
            head = DT_Atom(head_str, databaseTypes, operators, c_variables, c_tables)
            body = []
            # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
            atom_strs = self.split_atoms(body_str)
            for atom_str in atom_strs:
                atom_str = atom_str.strip()
                # if atom_str[0] == '(': # additional constraint
                #     self._additional_constraints.append(atom_str[1:-1])
                #     continue
                currAtom = DT_Atom(atom_str, databaseTypes, operators, c_variables, c_tables)
                body.append(currAtom)
            self.generateRule(head, body, databaseTypes, operators, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables)

    def safe(self):
        headVars = self._head.variables
        for var in headVars:
            if var not in self._variables:
                return False        
        return True

    def generateRule(self, head, body, databaseTypes={}, operators=[], domains={}, c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Int', simplification_on=True, c_tables=[]):
        self._variables = [] 
        self._c_variables = [] 
        self._head = head
        self._body = body
        self._DBs = []
        self._mapping = {}
        self._operators = operators
        self._domains = domains
        self._reasoning_engine = reasoning_engine
        self._reasoning_type = reasoning_type
        self._datatype = datatype
        self._simplication_on = simplification_on
        self._databaseTypes = databaseTypes
        self._c_tables = c_tables
        self._reverseMapping = {}
        db_names = []
        # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
        for currAtom in self._body:
            if currAtom.db["name"] not in db_names:
                self._DBs.append(currAtom.db)
                db_names.append(currAtom.db["name"])
            atomVars = currAtom.variables
            for var in atomVars:
                if var not in self._variables:
                    self._variables.append(var)
            
            atomCVars = currAtom.c_variables
            for var in atomCVars:
                if var not in self._c_variables:
                    self._c_variables.append(var)
                            
        # corner case, relation of atom in head does not appear in the body, e.g.,  R(n1, n2): link(n1, n2)
        if self._head.db['name'] not in db_names:
            self._DBs.append(self._head.db)
            db_names.append(self._head.db["name"])

        # TODO: Make sure that the mapping does not overlap with any other constant in the body
        # for i, var in enumerate(self._variables+self._c_variables):
        for i, var in enumerate(self._variables):
            self._mapping[var] = 100+i
            self._reverseMapping[100+i] = var

        # in case of unsafe rule
        if self.safe():
            self.sql = self.convertRuleToSQL()
        else:
            print("\n------------------------")
            print("Unsafe rule: {}!".format(self)) 
            print("------------------------\n")

        self.selectColumns = self.calculateSelect() 

        # if len(c_tables) > 0:
        #     if self._reasoning_engine == 'z3':
        #         self.reasoning_tool = z3SMTTools(variables=self._c_variables,domains=self._domains, reasoning_type=self._reasoning_type)
        #     else:
        #         self.reasoning_tool = BDDTools(variables=self._c_variables,domains=self._domains, reasoning_type=self._reasoning_type)

    # Includes the select part of query including datatype
    # e.g. 
    def calculateSelect(self):
        selectColumns = []
        for i, col in enumerate(self._head.db["column_names"]):
            selectColumns.append("CAST({} as {})".format(col, self._head.db["column_types"][i]))
        return selectColumns

    @property
    def numBodyAtoms(self):
        return len(self._body)

    @property
    def getDBs(self):
        return self._DBs

    # returns the signature of a rule
    def getSignature(self):
        signature = self._head.db["name"]+":-"
        bodyTables = []

        for atom in self._body:
            table = atom.db["name"]
            bodyTables.append(table)
        bodyTables.sort()
        signature += ",".join(bodyTables)
        return signature

    def deleteAtom(self, atomNum):
        del self._body[atomNum]

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

        newRule = DT_Rule(rule_str="", databaseTypes=self._databaseTypes, operators=self._operators, domains=self._domains, c_variables=self._c_variables, reasoning_engine=self._reasoning_engine, reasoning_type=self._reasoning_type, datatype=self._datatype, simplification_on=self._simplication_on, c_tables = self._c_tables, reasoning_tool=self.reasoning_tool, headAtom=newRule_head, bodyAtoms = newRule_body, additional_constraints=self._additional_constraints)
        return newRule

    def addConstants(self, conn):
        for atom in self._body:
            atom.addConstants(conn, self._mapping)

        # if using bdd engine, convert text[]-type condition to integer-type condition
        if len(self._c_tables) > 0 and self._reasoning_engine == 'bdd': 
            for ctablename in self._c_tables:
                self.reasoning_tool.process_condition_on_ctable(conn, ctablename)

    def convertRuleToSQL(self):
        summary_nodes, tables, constraints = self.convertRuleToSQLPartitioned()
        sql = "select " + ", ".join(summary_nodes) + " from " + ", ".join(tables)
        if (constraints):
            sql += " where " + " and ".join(constraints)
        return sql

    # initiates database of rule
    def initiateDB(self, conn):
        databases = []
        db_names = []
        for db in self.getDBs:
            if db["name"] not in db_names:
                db_names.append(db["name"])
                databases.append(db)

        for db in databases:
            cursor = conn.cursor()
            cursor.execute("DROP TABLE IF EXISTS {};".format(db["name"]))
            table_creation_query = "CREATE TABLE {}(".format(db["name"])
            num_cols = len(db["column_names"]) # assuming that last column is always condition
            for col in range(num_cols): 
                table_creation_query += '{} {},'.format(db["column_names"][col], db["column_types"][col])
            table_creation_query = table_creation_query[:-1]
            table_creation_query += ");"
            # print(table_creation_query)
            cursor.execute(table_creation_query)
        conn.commit()

    def getRuleWithoutFaure(self): # returns the same rule but without any c-variables and conditions
        newRuleStr = self._head.strAtomWithoutConditions() + " :- "
        for bodyAtom in self._body:
            newRuleStr += bodyAtom.strAtomWithoutConditions() + ", "
        newRuleStr = newRuleStr[:-2]
        newRule = DT_Rule(newRuleStr) # assuming that the default is without faure
        return newRule

    def convertRuleToSQLPartitioned(self):
        tables = []
        constraints = []
        variableList = {} # stores variable to table.column mapping. etc: {'x': ['t0.c0'], 'w': ['t0.c1', 't1.c0'], 'z': ['t0.c2', 't1.c1', 't2.c0'], 'y': ['t2.c1']}
        summary = set()
        summary_nodes = []
        constraints_for_array = {} # format: {'location': list[variables]}, e.g., {'t1.n3':['a1', 'e2']}
        variables_idx_in_array = {} # format {'var': list[location], e.g., {'a1':['t1.n3','t4.n1']}}
        for i, atom in enumerate(self._body):
            tables.append("{} t{}".format(atom.db["name"], i))
            for col, val in enumerate(atom.parameters):
                if type(val) == list:
                    loc = "t{}.{}".format(i, atom.db["column_names"][col])
                    constraints_for_array[loc] = val
                    for idx, var in enumerate(val):
                        if var not in variableList and var not in variables_idx_in_array:
                            variables_idx_in_array[var] = {'location': loc}
                            variables_idx_in_array[var]['idx'] = idx+1 # postgres array uses one-based numbering convention
                elif val[0].isdigit():
                    constraints.append("t{}.{} = {}".format(i, atom.db["column_names"][col], val))
                else: # variable or c_variable
                    if val not in variableList:
                        variableList[val] = []
                    variableList[val].append("t{}.{}".format(i, atom.db["column_names"][col]))
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
                        replace_var2attr.append("'{}'".format(str(p)))

                summary = "ARRAY[" + ", ".join(replace_var2attr) + "]"
                summary_nodes.append("{} as {}".format(summary, self._head.db['column_names'][idx]))
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
                                concatinatingValues.append(variableList[concatinatingVar][0])
                    opString = " " + op + " "
                    summary = opString.join(concatinatingValues)
                    if summary:
                        summary_nodes.append("{} as {}".format(summary, self._head.db['column_names'][idx]))
                if not hasOperator:
                    if param[0].isdigit(): # constant parameter
                        summary_nodes.append("{} as {}".format(param, self._head.db['column_names'][idx]))
                    else:
                        if param not in variableList.keys():
                            summary_nodes.append("'{}' as {}".format(param, self._head.db['column_names'][idx]))
                        else:
                            summary_nodes.append("{} as {}".format(variableList[param][0], self._head.db['column_names'][idx]))
        for var in variableList:
            for i in range(len(variableList[var])-1):
                constraints.append(variableList[var][i] + " = " + variableList[var][i+1])

        # adding variables in arrays in variableList
        # TODO: Possibly inefficient
        varListWithArray = deepcopy(variableList)
        for var in variables_idx_in_array:
            varListWithArray[var] = [variables_idx_in_array[var]["location"]+'['+str(variables_idx_in_array[var]["idx"]) + ']']
        # if (self._additional_constraints):
        #     additional_constraints = self.addtional_constraints2where_clause(self._additional_constraints, varListWithArray)
        #     constraints += additional_constraints

        # Additional constraints are faure constraints.
        constraints_faure = []
        for atom in self._body:
            for constraint in atom.constraints:
                constraints_faure.append(constraint)

        if len(constraints_faure) > 0:
            faure_constraints = self.addtional_constraints2where_clause(constraints_faure, varListWithArray)
            constraints.append(faure_constraints)
        # constraints for array
        for attr in constraints_for_array:
            for var in constraints_for_array[attr]:
                if var in variableList:
                    constraints.append("{} = ANY({})".format(variableList[var][0], attr))
                # else:
                #     constraints.append("{}[{}] = ANY({})".format(variables_idx_in_array[var]['location'], variables_idx_in_array[var]['idx'], attr))
        return summary_nodes, tables, constraints

    def execute(self, conn):
        if len(self._c_variables) == 0:
            cursor = conn.cursor()
            except_sql = "insert into {header_table} ({sql} except select {attrs} from {header_table})".format(header_table=self._head.db["name"], sql = self.sql, attrs= ", ".join(self.selectColumns))
            print(except_sql)
            cursor.execute(except_sql)
            affectedRows = cursor.rowcount
            conn.commit()
            changed = (affectedRows > 0)
        else:
            return self.run_with_faure(conn, self.sql)
        return changed

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
                constraints.append("ARRAY[{}] @> {}".format(", ".join(mapping_constants), self._head.db["column_names"][col]))
                constraints.append("ARRAY[{}] <@ {}".format(", ".join(mapping_constants), self._head.db["column_names"][col]))
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
                            constraints.append("{} = '{}'".format(self._head.db["column_names"][col], finalString))
                        else:
                            print("Error. Unsupported OP encountered")
                            exit()
                if not hasOperator:
                    if param[0].isdigit():
                        constraints.append("{} = {}".format(self._head.db["column_names"][col], param))
                    else:
                        constraints.append("{} = {}".format(self._head.db["column_names"][col], str(self._mapping[param])))
        sql = "select * from " + self._head.db["name"]
        if (constraints):
            sql += " where " + " and ".join(constraints)
        # print(sql)
        cursor = conn.cursor()
        cursor.execute(sql)
        result = cursor.fetchall()
        conn.commit()
        contained = (len(result) > 0)
        # print("contained", contained)
        return contained
    
    # Check if two variables/constants/c_variables are the same
    def _equal_faure(self, elem1, elem2):
        elem1 = elem1.strip()
        elem2 = elem2.strip()
        if elem1 in self._c_variables or elem2 in self._c_variables:
            return True
        else:
            return (str(elem1) == str(elem2))

    # Check if two lists have the same data portion
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
                    if not self._equal_faure(p, p2):
                        return False
            elif not self._equal_faure(str(elem), str(elem2)):
                return False
        return True

    # 1. Selects all tuples in table
    # 2. Finds out the target head tuple (by mapping the variables to assigned constants)
    # 3. Loops over all tuples to see if target tuple is found
    # 4. Checks if the condition of the head implies the condition in the found tuple 
    def is_head_contained_faure(self, conn):
        cursor = conn.cursor()
        contains = False

        # delete redundants
        merge_begin = time.time()
        if self._reasoning_engine == 'z3':
            merge_tuples.merge_tuples_z3(self._head.db["name"], # tablename of header
                                        information_on=False) 
        else:
            merge_tuples.merge_tuples_bdd(self._head.db["name"], self.reasoning_tool, information_on=False)
        merge_end = time.time()

        '''
        check whether Q_summary is in resulting table
        '''
        sql = "select {} from {}".format(", ".join(self.selectColumns), self._head.db["name"])
        if self._reasoning_engine == 'bdd':
            sql = sql.replace('text[]', 'integer')
        cursor.execute(sql)
        resulting_tuples = cursor.fetchall()
        conn.commit()

        # add constants to header data portion
        header_data_portion = []
        for i, p  in enumerate(self._head.parameters):
            col_type = self._head.db["column_types"][i]
            if type(p) == list:
                newP = []
                for elem in p:
                    if elem in self._c_variables:
                        newP.append(elem)
                    elif elem.isdigit() and "integer" in col_type:
                        newP.append(int(elem))
                    elif elem.isdigit() and "integer" not in col_type:
                        newP.append(str(elem))
                    elif "integer" in col_type:
                        newP.append(self._mapping[elem])                    
                    else:
                        newP.append(str(self._mapping[elem]))
                header_data_portion.append(newP)
            else:
                if p in self._c_variables or type(p) == int:
                    header_data_portion.append(p)
                elif p.isdigit() and "integer" in col_type:
                    header_data_portion.append(int(p))
                elif p.isdigit() and "integer" not in col_type:
                    header_data_portion.append(str(p))
                elif "integer" in col_type:
                    header_data_portion.append(self._mapping[p])
                else:
                    header_data_portion.append(str(self._mapping[p]))

        # set header condition
        header_condition = None
        if self._head.constraints:
            if len(self._head.constraints) == 0:
                header_condition = ""
            elif len(self._head.constraints) == 1:
                header_condition = self._head.constraints[0]
            else:
                header_condition = "And({})".format(", ".join(self._head.constraints))
        for tup in resulting_tuples:
            tup_cond = tup[-1] # assume condition locates the last position
            data_portion = list(tup[:-1])
            if self._sameDataPortion(header_data_portion, data_portion): #TODO: Need to add conditions for c-variable equivalence
                # Adding extra c-conditions
                extra_conditions = []
                for i, dat in enumerate(header_data_portion):
                    if type(dat) == list:
                        data_portion_list = data_portion[i][1:-1].split(",") # Removes curly parts 
                        for j, listdat in enumerate(dat):
                            extra_conditions.append("{} == {}".format(listdat, data_portion_list[j]))
                    else:        
                        extra_conditions.append("{} == {}".format(dat, data_portion[i]))

                if self._reasoning_engine == 'z3':
                    # convert list of conditions to a string of condition
                    extra_conditions = "And({})".format(", ".join(extra_conditions))
                    str_tup_cond = "And({})".format(", ".join(tup_cond))
                    if len(tup_cond) == 0:
                        str_tup_cond = ""
                    elif len(tup_cond) == 1:
                        str_tup_cond = tup_cond[0]

                    # Does the condition in the tuple imply the condition in the header?
                    if not self.reasoning_tool.iscontradiction([str_tup_cond]) and self.reasoning_tool.is_implication(str_tup_cond, extra_conditions) and self.reasoning_tool.check_equivalence_for_two_string_conditions(str_tup_cond, header_condition):
                        contains = True

                elif self._reasoning_engine == 'bdd':
                    # convert list of conditions to a string of condition
                    extra_conditions = "And({})".format(", ".join(extra_conditions))
                    print("extra_conditions", extra_conditions)
                    extra_condition_idx = self.reasoning_tool.str_to_BDD(extra_conditions)
                    # str_tup_cond_idx = reasoning_tool.str_to_BDD(str_tup_cond)
                    if header_condition is None:
                        header_condition=""
                    header_condition_idx = self.reasoning_tool.str_to_BDD(header_condition)

                    if self.reasoning_tool.evaluate(tup_cond) != 0 and \
                        self.reasoning_tool.is_implication(tup_cond, extra_condition_idx) and \
                        (self.reasoning_tool.is_implication(tup_cond, header_condition_idx) and self.reasoning_tool.is_implication(header_condition_idx, tup_cond)):
                        contains = True
                else:
                    print("We do not support {} engine!".format(self._reasoning_engine))
                    exit()
        return contains


    # The argument tuple1 and tuple2 are single tuples. 
    # Functions checks if the tuples are equivalent
    def tuplesEquivalent(self, tuple1, tuple2):
        if str(tuple1[:-1]) != str(tuple2[:-1]): # data portion must be the same
            return False
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
    def insertTuplesToHead(self, conn, fromTable="output"):
        cursor = conn.cursor()
        header_table = self._head.db["name"]

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

    
    def run_with_faure(self, conn, program_sql):
        print("program_sql", program_sql)
        header_table = self._head.db["name"]
        changed = False
        '''
        generate new facts
        '''
        query_begin = time.time()
        FaureEvaluation(conn, program_sql, reasoning_tool=self.reasoning_tool, additional_condition=",".join(self._additional_constraints), output_table="output", domains=self._domains, reasoning_engine=self._reasoning_engine, reasoning_sort=self._reasoning_type, simplication_on=False, information_on=True)
        query_end = time.time()
        print("query_time:", query_end-query_begin, "\n*******************************\n")
        
        # input()
        
        changed = self.insertTuplesToHead(conn)
        # input()
        return changed

    def addtional_constraints2where_clause(self, constraints, variableList):
        newConstraints = []
        singleLocVarList = {}
        for var in variableList: # Variable list contains location for every occurrence of the variable. Need to fix
            singleLocVarList[var] = variableList[var][0]
        for constraint in constraints:
            newConstraints.append(z3ToSQL(condition = constraint, replacements = singleLocVarList))
        newConstraint = newConstraints[0] # note that this function should only be called when there are positive number of constraints
        if len(newConstraints) > 1:
            newConstraint = " and ".join(newConstraints)
        return newConstraint.replace("==","=")

    def split_atoms(self, bodystr):
        i = 0
        in_parenth = False
        atom_strs = []
        begin_pos = i
        while i < len(bodystr):
            if bodystr[i] == '(':
                in_parenth = True
            elif bodystr[i] == ')':
                in_parenth = False
                atom_str = bodystr[begin_pos: i+1].strip(" ,")
                atom_strs.append(atom_str)
                begin_pos = i+1
            elif bodystr[i] == ']':
                if not in_parenth:
                    relation = atom_strs.pop(-1)
                    atom_str_with_condition = relation + bodystr[begin_pos: i+1]
                    atom_str_with_condition.strip(" ,")
                    atom_strs.append(atom_str_with_condition)
                    begin_pos = i + 1
            
            i += 1
        if begin_pos != len(bodystr):
            atom_strs.append(bodystr[begin_pos:].strip(" ,"))
        
        return atom_strs

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