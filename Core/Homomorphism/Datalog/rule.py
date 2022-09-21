# Constructor: string to array of atoms (head and list of body)
# each atom has a database and arguments (string)

# Iterate over atoms
# Delete atom
# Make new rule with a deleted atom
# Rule to sql
# Populate with constants in database (return the expected head). Give connection
# Expected head to sql
from operator import add
import sys
from os.path import dirname, abspath
from unicodedata import name
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)

import re
from copy import deepcopy
from psycopg2.extras import execute_values
from Core.Homomorphism.Datalog.atom import DT_Atom
from Core.Homomorphism.faure_translator.faure_evaluation import FaureEvaluation
import Core.Homomorphism.translator_pyotr as translator_z3
import Core.Homomorphism.translator_pyotr_BDD as translator_bdd
import BDD_managerModule as bddmm
import Backend.reasoning.CUDD.BDD_manager.encodeCUDD as encodeCUDD
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_tautology as merge_tuples_z3
import Core.Homomorphism.Optimizations.merge_tuples.merge_tuples_BDD as merge_tuples_bdd
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology

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
    _domains: int[]
        domain of c-variables
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

    def __init__(self, rule_str, databaseTypes={}, operators=[], domains=[], c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Int', simplification_on=True, c_tables=[], headAtom="", bodyAtoms=[], additional_constraints=[]):

        self._additional_constraints = deepcopy(additional_constraints)
        if headAtom and bodyAtoms:
            self.generateRule(headAtom, bodyAtoms, databaseTypes, operators, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables)
        else:
            head_str = rule_str.split(":-")[0].strip()
            body_str = rule_str.split(":-")[1].strip()
            head = DT_Atom(head_str, databaseTypes, operators, c_variables, c_tables)
            body = []
            # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
            atom_strs = self.split_atoms(body_str)
            for atom_str in atom_strs:
                atom_str = atom_str.strip()
                # if "[" in atom_str:  # atom with conditions for c-variables
                #     pass
                # elif "(" in atom_str: # atom without c-variables
                #     pass
                if atom_str[0] == '(': # additional constraint
                    self._additional_constraints.append(atom_str[1:-1])
                    continue
                currAtom = DT_Atom(atom_str, databaseTypes, operators, c_variables, c_tables)
                body.append(currAtom)
            self.generateRule(head, body, databaseTypes, operators, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables)

    def safe(self):
        headVars = self._head.variables
        if len(headVars) != len(self._variables):   
            return False
        for var in headVars:
            if var not in self._variables:
                return False        

        headCVars = self._head.c_variables        
        if len(headCVars) != len(self._c_variables):   
            return False
        for cvar in headCVars:
            if cvar not in self._c_variables:
                return False
        return True

    def generateRule(self, head, body, databaseTypes={}, operators=[], domains=[], c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Int', simplification_on=True, c_tables=[]):
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

        for i, var in enumerate(self._variables+self._c_variables):
            self._mapping[var] = i


        # in case of unsafe rule
        # if not self.safe():
        #     print("\n------------------------")
        #     print("Unsafe rule: {}!".format(self)) 
        #     print("------------------------\n")

        # headVars = self._head.variables        
        # for var in headVars:
        #     if var not in self._variables:
        #         self._variables.append(var)
        #         self._mapping[var] = len(self._mapping.keys())
                
        #         print("\n------------------------")
        #         print("Unsafe rule: {}!".format(self)) 
        #         print("variable '{var}' does not appear in body! Initiate '{var}' to constants {con} when executing".format(var=var, con=self._mapping[var]))
        #         print("------------------------\n")

    @property
    def numBodyAtoms(self):
        return len(self._body)

    @property
    def getDBs(self):
        return self._DBs

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

        newRule = DT_Rule(rule_str="", databaseTypes=self._databaseTypes, operators=self._operators, domains=self._domains, c_variables=self._c_variables, reasoning_engine=self._reasoning_engine, reasoning_type=self._reasoning_type, datatype=self._datatype, simplification_on=self._simplication_on, c_tables = self._c_tables, headAtom=newRule_head, bodyAtoms = newRule_body, additional_constraints=self._additional_constraints)
        return newRule

    def addConstants(self, conn):
        for atom in self._body:
            atom.addConstants(conn, self._mapping)

    def execute(self, conn):
        tables = []
        constraints = []
        variableList = {}
        summary = set()
        summary_nodes = []
        constraints_for_array = {} # format: {'location': list[variables]}, e.g., {'t1.n3':['a1', 'e2']}
        variables_idx_in_array = {} # format {'var': list[location]}
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
                    constraints.append("t{}.{} = '{}'".format(i, atom.db["column_names"][col], val))
                else: # variable
                    if val not in variableList:
                        variableList[val] = []
                    variableList[val].append("t{}.{}".format(i, atom.db["column_names"][col]))
        for idx, param in enumerate(self._head.parameters):
            if type(param) == list:
                # print("param", param)
                replace_var2attr = []
                for p in param:
                    if p in variableList:
                        replace_var2attr.append(str(variableList[p][0]))
                    else:
                        replace_var2attr.append("{}[{}]".format(variables_idx_in_array[p]['location'], variables_idx_in_array[p]['idx']))

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
                        # print("variableList", variableList)
                        if param not in variableList.keys():
                            summary_nodes.append("{} as {}".format(self._mapping[param], self._head.db['column_names'][idx]))
                        else:
                            summary_nodes.append("{} as {}".format(variableList[param][0], self._head.db['column_names'][idx]))
        for var in variableList:
            for i in range(len(variableList[var])-1):
                constraints.append(variableList[var][i] + " = " + variableList[var][i+1])

        # adding variables in arrays in variableList
        varListWithArray = deepcopy(variableList)
        for var in variables_idx_in_array:
            varListWithArray[var] = [variables_idx_in_array[var]["location"]+'['+str(variables_idx_in_array[var]["idx"]) + ']']
        if (self._additional_constraints):
            additional_constraints = self.addtional_constraints2where_clause(self._additional_constraints, varListWithArray)
            constraints += additional_constraints

        # Additional constraints are faure constraints. Assuming that head atom constains all constraints
        constraints_faure = []
        for atom in self._body:
            for constraint in atom.constraints:
                constraints_faure.append(constraint)
        faure_constraints = self.addtional_constraints2where_clause(constraints_faure, variableList)
        constraints += faure_constraints

        # constraints for array
        for attr in constraints_for_array:
            for var in constraints_for_array[attr]:
                if var in variableList:
                    constraints.append("{} = ANY({})".format(variableList[var][0], attr))
                # else:
                #     constraints.append("{}[{}] = ANY({})".format(variables_idx_in_array[var]['location'], variables_idx_in_array[var]['idx'], attr))

        if len(self._c_variables) == 0:

            sql = "select " + ", ".join(summary_nodes) + " from " + ", ".join(tables)
            if (constraints):
                sql += " where " + " and ".join(constraints)
            cursor = conn.cursor()
            print("sql", sql)
            # remove the duplicates
            except_sql = "insert into {header_table} ({sql} except select {attrs} from {header_table})".format(header_table=self._head.db["name"], sql = sql, attrs= ", ".join(self._head.db["column_names"]))
            # print("except_sql", except_sql)
            cursor.execute(except_sql)
            affectedRows = cursor.rowcount
            # print("insert", cursor.query)
            # print("affectedRows", affectedRows)
            conn.commit()
            changed = (affectedRows > 0)
        else:
            # attrs = []
            # for i in range(len(summary_nodes)):
            #     attrs.append('{} {}'.format(summary_nodes[i], self._head.db["column_names"][i]))
            sql = " select " + ", ".join(summary_nodes) + " from " + ", ".join(tables)
            if (constraints):
                sql += " where " + " and ".join(constraints)
            return self.run_with_faure(conn, sql)

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
        '''
        check whether Q_summary is in resulting table
        '''
        cursor.execute("select {} from {}".format(", ".join(self._head.db["column_names"]), self._head.db["name"]))
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
        # print(resulting_tuples)
        # print(header_data_portion)
        # print(self._head)
        # exit()
        for tup in resulting_tuples:
            tup_cond = tup[-1] # assume condition locates the last position
            if self._sameDataPortion(header_data_portion, list(tup[:-1])):
                if self._reasoning_engine == 'z3':
                    # convert list of conditions to a string of condition
                    str_tup_cond = None
                    if len(tup_cond) == 0:
                        str_tup_cond = ""
                    elif len(tup_cond) == 1:
                        str_tup_cond = tup_cond[0]
                    else:
                        str_tup_cond = "And({})".format(", ".join(tup_cond))


                    if check_tautology.check_equivalence_for_two_string_conditions(header_condition, str_tup_cond, self._reasoning_type):
                        contains = True
                        return contains

                elif self._reasoning_engine == 'bdd':
                    if bddmm.is_implication(header_condition, tup_cond) and bddmm.is_implication(tup_cond, header_condition):
                        contains = True
                        return contains
                else:
                    print("We do not support {} engine!".format(self._reasoning_engine))
                    exit()

        return contains

    # def exists_new_tuple(self, conn):
    #     cursor = conn.cursor()
    #     header_table = self._head.db["name"]

    #     cursor.execute("select {} from output".format(", ".join(self._head.db["column_names"])))
    #     output_results = cursor.fetchall()

    #     cursor.execute("select {} from {}".format(", ".join(self._head.db["column_names"]), header_table))
    #     existing_tuples = cursor.fetchall()
    #     conn.commit()

    #     inserting_tuples = []
    #     for res_tup in output_results:
    #         for existing_tup in existing_tuples:
    #             res_cond = res_tup[-1]
    #             existing_cond = existing_tup[-1]
    #             if str(res_tup[:-1]) == str(existing_tup[:-1]):
    #                 if self._reasoning_engine == 'z3':
    #                     condition1 = None
    #                     if len(existing_cond) == 0:
    #                         condition1 = ""
    #                     elif len(existing_cond) == 1:
    #                         condition1 = existing_cond[0]
    #                     else:
    #                         condition1 = "And({})".format(", ".join(existing_cond))

    #                     condition2 = None
    #                     if len(res_cond) == 0:
    #                         condition2 = ""
    #                     elif len(res_cond) == 1:
    #                         condition2 = res_cond[0]
    #                     else:
    #                         condition2 = "And({})".format(", ".join(res_cond))
    #                     if check_tautology.check_is_implication(condition1, condition2, self._reasoning_type):
    #                         continue
    #                     else: 
    #                         inserting_tuples.append(res_tup)
    #                 elif self._reasoning_engine == 'bdd':
    #                     if bddmm.is_implication(existing_cond, res_cond):
    #                         continue
    #                     else:
    #                         inserting_tuples.append(res_tup)
    #                 else:
    #                     print("We do not support {} engine!".format(self._reasoning_engine))
    #                     exit()
    #             else:
    #                 inserting_tuples.append(res_tup)
    #     if len(inserting_tuples) == 0:
    #         changes = False
    #     else:
    #         changes = True
    #         insert_sql = "insert into {} values %s".format(header_table)
    #         execute_values(cursor, insert_sql, inserting_tuples)
    #     conn.commit()
    #     return changes  

    # Adds the result of the table "output" to head. Only adds distinct variables
    def insertTuplesToHead(self, conn, fromTable="output"):
        cursor = conn.cursor()
        changed = False
        header_table = self._head.db["name"]

        # if self._reasoning_engine == "z3":
        #     translator_z3.normalization(self._reasoning_type, header_table)
        # elif self._reasoning_engine == "bdd": # TODO: Add table name to BDD
        #     translator_bdd.normalization(self._reasoning_type, header_table)

        # '''
        # Merge tuples
        # '''
        # merge_tuples_z3.merge_tuples(header_table, # tablename of header
        #                             "{}_out".format(header_table), # output tablename
        #                             [], # domain
        #                             self._reasoning_type) # reasoning type of engine
        # cursor = conn.cursor()
        # cursor.execute("drop table if exists {}".format(header_table))
        # cursor.execute("alter table {}_out rename to {}".format(header_table, header_table))

        # counting non-redundant rows in header after simplification
        cursor.execute("select distinct count(*) from {}".format(header_table))
        headerCountAfterSimp = int(cursor.fetchall()[0][0])

        # Adding result of output to header
        cursor.execute("insert into {} select {} from {}".format(header_table, ", ".join(self._head.db["column_names"]), fromTable))

        conn.commit()
        # delete redundants
        merge_tuples_z3.merge_tuples(header_table, # tablename of header
                                    "{}_out".format(header_table), # output tablename
                                    [], # domain
                                    self._reasoning_type) # reasoning type of engine
        cursor = conn.cursor()
        cursor.execute("drop table if exists {}".format(header_table))
        cursor.execute("alter table {}_out rename to {}".format(header_table, header_table))

        # counting non-redundant rows in header after inserting output tables
        cursor.execute("select distinct count(*) from {}".format(header_table))
        headerCountAfterInsert = int(cursor.fetchall()[0][0])
        conn.commit()
        
        if headerCountAfterInsert > headerCountAfterSimp:
            changed = True
        conn.commit()

        return changed
    
    def run_with_faure(self, conn, program_sql):
        header_table = self._head.db["name"]
        changed = False
        print(program_sql)
        '''
        generate new facts
        '''
        if self._reasoning_engine == 'z3':
            # tree = translator_z3.generate_tree(program_sql)
            # translator_z3.data(tree)
            # translator_z3.upd_condition(tree, self._datatype)

            # if self._simplication_on == 'On':
            #     translator_z3.normalization(self._reasoning_type)
            # conn.commit()
            faure_domains = {}
            for cvar in self._c_variables:
                faure_domains[cvar] = self._domains
            #TODO: Explicitly give output table name instead of relying on defaults
            FaureEvaluation(conn, program_sql, domains=faure_domains, reasoning_engine=self._reasoning_engine, reasoning_sort=self._reasoning_type, simplication_on=self._simplication_on, information_on=False)

            '''
            compare generating IDB and existing DB if there are new IDB generated
            if yes, the DB changes, continue run the program on DB
            if no, the DB does not change, stop running 
            '''
            changed = self.insertTuplesToHead(conn)
            # changed = self.exists_new_tuple(conn)

        elif self._reasoning_engine == 'bdd':
            if self._reasoning_type == 'BitVec':
                print("BDD engine does not support BitVec now! ")
                exit()

            bddmm.initialize(len(self._c_variables), len(self._domains))
            translator_bdd.set_domain(self._domains)
            translator_bdd.set_variables(self._c_variables)

            cursor = conn.cursor()
            for db in self._DBs:
                bdd_tablename = translator_bdd.process_condition_on_ctable(db)
                sql = "drop table if exists {db}".format(db=db)
                cursor.execute(sql)

                sql = "create table {db} as select * from {bdd_tablename} with NO DATA".format(db=db, bdd_tablename=bdd_tablename)
                cursor.execute(sql)
            conn.commit()
            
            tree = translator_bdd.generate_tree(program_sql)
            translator_bdd.data(tree)
            translator_bdd.upd_condition(tree, self._datatype)

            changed = self.exists_new_tuple(conn, self._reasoning_engine, self._reasoning_type)

            '''
            Merge tuples
            '''
            merge_tuples_bdd.merge_tuples(header_table, # tablename of header
                                    "{}_out".format(header_table)) # output tablename
            cursor = conn.cursor()                        
            cursor.execute("drop table if exists {}".format(header_table))
            cursor.execute("alter table {}_out rename to {}".format(header_table, header_table))
            conn.commit()
        else:
            print("We do not support {} engine!".format(self._reasoning_engine))
            exit()

        return changed

    def addtional_constraints2where_clause(self, constraints, variableList):
        # print("constraints", constraints)
        additional_conditions = []
        safe_constraints = []
        for constraint in constraints:
            # only support logical or/and exculding mixed use)
            constraint = constraint.replace("==", "=") #TODO: Hacky method to convert back to sql format
            conditions = []
            logical_opr = None
            logical_sym = None
            if '&' in constraint:
                conditions = constraint.split('&')
                logical_opr = 'and'
                logical_sym = '&'
            elif '^' in constraint:
                conditions = constraint.split('^')
                logical_opr = 'or'
                logical_sym = '^'
            else:
                conditions.append(constraint)

            safe_conditions = []
            temp_processed_conditions = []
            for cond in conditions:
                cond = cond.strip()
                processed_cond = self.condition2where_caluse(cond, variableList)
                if processed_cond is not None:
                    temp_processed_conditions.append(processed_cond)
                    safe_conditions.append(cond)
            
            # update additional constraints
            if len(safe_conditions) == 0:
                continue
            if len(safe_conditions) == 1:
                constraint = safe_conditions[0]
                safe_constraints.append(constraint)
            else:
                constraint = logical_sym.join(safe_conditions)
                safe_constraints.append(constraint)
            
            if logical_opr == 'and':
                additional_conditions.append(" and ".join(temp_processed_conditions))
            elif logical_opr == 'or':
                additional_conditions.append("({})".format(" or ".join(temp_processed_conditions)))
            else:
                additional_conditions += temp_processed_conditions

        return additional_conditions

    def condition2where_caluse(self, condition, variableList):
        # assume there are spaces between operands and operator
        items = condition.split()
        if len(items) != 3:
            print("Wrong condition format! The format of condition is {left_opd}{whitespace}{operator}{whitespace}{right_opd}!")
            exit()
        left_opd = items[0]
        opr = items[1]
        right_opd = items[2]
        elementsRight = []

        # Note: We do not support arrays as the left hand opd
        if not left_opd[0].isdigit(): # it is a var or c-var
            if left_opd not in variableList.keys():
                print("No '{}' in variables! Unsafe condition!".format(left_opd))
                return None
            left_opd = variableList[left_opd][0]

        if right_opd[0] == '[': # an array
            elements = right_opd[1:-1].split(",")
            for elem in elements:
                if not elem[0].isdigit():
                    elementsRight.append(variableList[elem][0])
                else:
                    elementsRight.append(elem)
        elif not right_opd[0].isdigit(): # it is a var or c-var
            if right_opd not in variableList.keys():
                print("No '{}' in variables! Unsafe condition!".format(right_opd))
                return None
            right_opd = variableList[right_opd][0]

        
        if 'in' in opr and not elementsRight:
            print("Wrong condition. Operator '{}' requires an array at the right side! Exiting".format(opr))
            exit()

        processed_condition = None
        if '\\not_in' in opr:
            processed_condition = "Not {} = Any(ARRAY[{}])".format(left_opd, ",".join(elementsRight))


        elif '\\in' in opr:
            processed_condition = "{} = Any(ARRAY[{}])".format(left_opd, ",".join(elementsRight))
        # elif opr == '=':
        #     processed_condition = " {} == {}".format(left_opd, right_opd)
        else:
            processed_condition = "{} {} {}".format(left_opd, opr, right_opd)

        return processed_condition

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
            




    # # Uniform containment. self rule C rule2 (self rule contains rule2). Treat self rule as constant and apply the rule in the argument as program
    # # Returns (containment result, any changes to database)
    # def contains(self, rule2):
    #     # get variables
    #     # get mappings
    #     # loop over atoms
    #         # add items to database (in atoms)
    #     conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    #     conn.set_session()
    #     for atom in self._body:
    #         atom.addConstantDB(conn, self._mapping)
    #     headConstants = self._head.constants(self._mapping)
    #     sql = rule2.sql() # select 
    #     # Map rule2 body to sql
    #     cur = conn.cursor()
    #     cur.execute(sql)
    #     results = cur.fetchall()
    #     conn.commit()
    #     if len(results) == 0:
    #         conn.close()
    #         return False, False
    #     elif (headConstants in results):
    #         conn.close()
    #         return True, True
    #     else:
    #         addToDatabase(conn, results)
    #     conn.close()
    #     print("Max iterations reached")
    #     return False, True

    def __str__(self):
        string = str(self._head) + " :- "
        for atom in self._body:
            string += str(atom) + ","
        if self._additional_constraints:
            string += " ({})".format(", ".join(self._additional_constraints))
            return string
        return string[:-1]

if __name__ == "__main__":
    a = "Asd"
    rule = DT_Rule("A(x,y,z) :- Gasd(x,1,y)[],B(z,x),C(y,z,2)")
    # rule.isHeadContained(a)
    # print(atom.db)