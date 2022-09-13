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
        list of variables in rule
    _mapping : dictionary{variable : integer}
        mapping of variables to integers (used in containment). The only important part here is to map distinct variables to distinct constants
    _operators : string[]
        operators supported in queries. Currently, only array concatination operator "||" is supported


    Methods
    -------
    execute(conn)
        run this datalog rule on database pointed by psycopg2 connection "conn". Conversion to sql and execution of sql occurs here
    isHeadContained(conn)
        run sql query to check if the head of the rule is contained or not in the output. This is useful to terminate program execution when checking for containment. Conversion to sql and execution of sql occurs here
    """

    def __init__(self, rule_str, databaseTypes={}, operators=[], domains=[], c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Int', simplification_on=True, c_tables=[]):
        head_str = rule_str.split(":-")[0].strip()
        body_str = rule_str.split(":-")[1].strip()
        self._variables = [] 
        self._c_variables = c_variables 
        self._head = DT_Atom(head_str, databaseTypes, operators, c_variables, c_tables)
        self._body = []
        self._DBs = []
        self._mapping = {}
        self._constraints = [] # additional constraints
        self._operators = operators
        self._domains = domains
        self._reasoning_engine = reasoning_engine
        self._reasoning_type = reasoning_type
        self._datatype = datatype
        self._simplication_on = simplification_on
        db_names = []
        # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
        atom_strs = self.split_atoms(body_str)
        for atom_str in atom_strs:
            atom_str = atom_str.strip()
            if "[" in atom_str:  # atom with conditions for c-variables
                pass
            elif "(" in atom_str: # atom without c-variables
                pass
            else: # it's not an atom, instead additional conditions
                constraints = atom_str.split(',')
                for constraint in constraints:
                    self._constraints.append(constraint.strip())
                continue

            currAtom = DT_Atom(atom_str, databaseTypes, operators, c_variables, c_tables)
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
                    
            self._body.append(currAtom)
        
        # corner case, relation of atom in head does not appear in the body, e.g.,  R(n1, n2): link(n1, n2)
        if self._head.db['name'] not in db_names:
            self._DBs.append(self._head.db)
            db_names.append(self._head.db["name"])

        for i, var in enumerate(self._variables):
            self._mapping[var] = i

        # in case of unsafe rule
        headVars = self._head.variables
        for var in headVars:
            if var not in self._variables:
                self._variables.append(var)
                self._mapping[var] = len(self._mapping.keys())
                
                print("\n------------------------")
                print("Unsafe rule: {}!".format(self)) 
                print("variable '{var}' does not appear in body! Initiate '{var}' to constants {con} when executing".format(var=var, con=self._mapping[var]))
                print("------------------------\n")
    
    @property
    def numBodyAtoms(self):
        return len(self._body)

    @property
    def getDBs(self):
        return self._DBs

    def deleteAtom(self, atomNum):
        del self._body[atomNum]

    def copyWithDeletedAtom(self, atomNum):
        newRule = deepcopy(self)
        newRule.deleteAtom(atomNum)
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
        print("Running atom:")
        for i, atom in enumerate(self._body):
            print(atom)
        print("Head atom:", self._head)
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
                c_var = False
                for p in param:
                    if p in self._c_variables:
                        c_var = True
                        replace_var2attr.append('"{}"'.format(p))
                    else:
                        if p in variableList:
                            replace_var2attr.append(str(variableList[p][0]))
                        else:
                            replace_var2attr.append("{}[{}]".format(variables_idx_in_array[p]['location'], variables_idx_in_array[p]['idx']))

                summary = "ARRAY[" + ", ".join(replace_var2attr) + "]"
                if c_var:
                    summary = "'{" + ", ".join(replace_var2attr) + "}'"
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
        additional_constraints = self.addtional_constraints2where_clause(self._constraints, variableList)
        constraints += additional_constraints
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
            # print("sql", sql)
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
            # print("sql", sql)
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
        for p in self._head.parameters:
            if type(p) == list:
                newP = []
                for elem in p:
                    if elem in self._c_variables or elem.isdigit():
                        newP.append(elem)
                    else:
                        newP.append(str(self._mapping[elem]))
                header_data_portion.append(newP)
            else:
                if p in self._c_variables or type(p) == int or p.isdigit():
                    header_data_portion.append(p)
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
            if str(header_data_portion) == str(list(tup[:-1])):
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

    def exists_new_tuple(self, conn):
        cursor = conn.cursor()
        header_table = self._head.db["name"]

        cursor.execute("select {} from output".format(", ".join(self._head.db["column_names"])))
        output_results = cursor.fetchall()

        cursor.execute("select {} from {}".format(", ".join(self._head.db["column_names"]), header_table))
        existing_tuples = cursor.fetchall()
        conn.commit()

        inserting_tuples = []
        for res_tup in output_results:
            for existing_tup in existing_tuples:
                res_cond = res_tup[-1]
                existing_cond = existing_tup[-1]
                if str(res_tup[:-1]) == str(existing_tup[:-1]):
                    if self._reasoning_engine == 'z3':
                        condition1 = None
                        if len(existing_cond) == 0:
                            condition1 = ""
                        elif len(existing_cond) == 1:
                            condition1 = existing_cond[0]
                        else:
                            condition1 = "And({})".format(", ".join(existing_cond))

                        condition2 = None
                        if len(res_cond) == 0:
                            condition2 = ""
                        elif len(res_cond) == 1:
                            condition2 = res_cond[0]
                        else:
                            condition2 = "And({})".format(", ".join(res_cond))
                        if check_tautology.check_is_implication(condition1, condition2, self._reasoning_type):
                            continue
                        else: 
                            inserting_tuples.append(res_tup)
                    elif self._reasoning_engine == 'bdd':
                        if bddmm.is_implication(existing_cond, res_cond):
                            continue
                        else:
                            inserting_tuples.append(res_tup)
                    else:
                        print("We do not support {} engine!".format(self._reasoning_engine))
                        exit()
                else:
                    inserting_tuples.append(res_tup)

        if len(inserting_tuples) == 0:
            changes = False
        else:
            changes = True
            insert_sql = "insert into {} values %s".format(header_table)
            execute_values(cursor, insert_sql, inserting_tuples)
        conn.commit()
        return changes
    
    def run_with_faure(self, conn, program_sql):
        header_table = self._head.db["name"]
        changed = False
        '''
        generate new facts
        '''
        print(program_sql)
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
            FaureEvaluation(conn, program_sql, domains=faure_domains, reasoning_engine=self._reasoning_engine, reasoning_sort=self._reasoning_type, simplication_on=self._simplication_on, information_on=False)
            '''
            compare generating IDB and existing DB if there are new IDB generated
            if yes, the DB changes, continue run the program on DB
            if no, the DB does not change, stop running 
            '''
            changed = self.exists_new_tuple(conn)

            '''
            Merge tuples
            '''
            merge_tuples_z3.merge_tuples(header_table, # tablename of header
                                    "{}_out".format(header_table), # output tablename
                                    [], # domain
                                    self._reasoning_type) # reasoning type of engine
            cursor = conn.cursor()
            cursor.execute("drop table if exists {}".format(header_table))
            cursor.execute("alter table {}_out rename to {}".format(header_table, header_table))
            conn.commit()
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
        
        
        # update additional constraints
        self._constraints = safe_constraints

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
        
        if not left_opd[0].isdigit(): # it is a var or c-var
            if left_opd not in variableList.keys():
                print("No '{}' in variables! Unsafe condition!".format(left_opd))
                return None
            left_opd = variableList[left_opd][0]
        if not right_opd[0].isdigit(): # it is a var or c-var
            if right_opd not in variableList.keys():
                print("No '{}' in variables! Unsafe condition!".format(right_opd))
                return None
            right_opd = variableList[right_opd][0]

        processed_condition = None
        if '\\not_in' in opr:
            if right_opd[0].isalpha():
                processed_condition = "Not {} = Any({})".format(left_opd, right_opd)
            else:
                processed_condition = "{} not in {}".format(left_opd, right_opd)

        elif '\\in' in opr:
            if right_opd[0].isalpha():
                processed_condition = "{} = Any({})".format(left_opd, right_opd)
            else:
                processed_condition = "{} in {}".format(left_opd, right_opd)
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
        if self._constraints:
            string += "{}".format(", ".join(self._constraints))
            return string
        return string[:-1]

if __name__ == "__main__":
    a = "Asd"
    rule = DT_Rule("A(x,y,z) :- Gasd(x,1,y)[],B(z,x),C(y,z,2)")
    # rule.isHeadContained(a)
    # print(atom.db)