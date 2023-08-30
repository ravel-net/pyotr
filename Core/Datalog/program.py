import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2 
from copy import deepcopy
from Core.Datalog.rule import DT_Rule
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
from Backend.reasoning.Z3.z3smt import z3SMTTools
# from Backend.reasoning.CUDD.BDDTools import BDDTools
from utils import parsing_utils
from utils import sql_operations
from utils.converter.recursion_converter import RecursiveConverter
import databaseconfig as cfg
from utils.logging import timeit
from Backend.reasoning.CUDD.BDDTools import BDDTools

class DT_Program:
    """
    A class used to represent a datalog program.

    Attributes
    ----------
    __MAX_ITERATIONS : int
        the maximum number of times a datalog program should be run (in case fixed point isn't reached)
    __OPERATORS : string[]
        operators supported in queries. Currently, only array concatination operator "||" is supported
    rules : DT_Rule[]
        array of datalog rules
    db : DT_Database
        Database over which this program is run
    reasoning_tool : z3SMTTools or BDDTools
        Reasoning tool (z3 or BDD) used for processing conditions (checking implication, contradiction etc.)

    Methods
    -------
    contains(program2)
        does this program uniformly contain program2?
    minimize()
        minimize this datalog program
    execute(conn, faure_evaluation_mode="contradiction")
        run this datalog program on database pointed by psycopg2 connection "conn" until fixed point is reached. If we are dealing with an incomplete database, the faure_evaluation_mode is used to determine if the semantics of the required evaluation (exact answer vs certain answer)
    executeonce(conn, faure_evaluation_mode="contradiction")
        run this datalog program once on database pointed by psycopg2 connection "conn". If we are dealing with an incomplete database, the faure_evaluation_mode is used to determine if the semantics of the required evaluation (exact answer vs certain answer)
    executeonce_and_check_containment(conn, rule2)
        run this datalog program once on database pointed by psycopg2 connection "conn" and return true if rule2 is uniformly contained by this program
    initiateDB(conn)
        initiate tables in this datalog program on database pointed by psycopg2 connection "conn"
    contains_rule(rule2)
        does this program uniformly contain rule2?
    stats()
        returns the number of rules and the number of total atoms in the program
    """
    
    __MAX_ITERATIONS = 10
    __OPERATORS = ["||"]
    
    # Default values: "simplification_on"=False, "pg_native_recursion"=False, "recursive_rules"=True
    def __init__(self, program_str, database=None, reasoning_engine='z3', optimizations={}, bits = 32):
        self.rules = []
        # TODO IMPORTANT: The assignment of variables cannot be random. They have to be assigned based on the domain of any c variable involved
        self._program_str = program_str
        self.db = database
        if not self.db:
            self.db = self.__createDB(program_str)
        self._isFaureEval = False
        self._optimizations = optimizations
        self.reasoning_tool = None
        self._reasoning_engine = reasoning_engine

        if len(self.db.c_tables) > 0: # when faureeval is required
            self._isFaureEval = True
            if self._reasoning_engine == 'z3':
                self.reasoning_tool = z3SMTTools(variables=self.db.c_variables, domains=self.db.cvar_domain, reasoning_type=self.db.reasoning_types, mapping=self.db.cVarMapping, bits=bits)
            else:
                # self.reasoning_tool = BDDTools(variables=self.db.c_variables, domains=self.db.cvar_domain, reasoning_types=self.db.reasoning_types, mapping=self.db.cVarMapping, bits=bits)
                self.reasoning_tool = BDDTools(variables=self.db.c_variables, domains=self.db.cvar_domain, reasoning_types=self.db.reasoning_types, mapping=self.db.cVarMapping, bits=bits)

        if "simplification_on" not in self._optimizations:
            self._optimizations["simplification_on"] = False # default value
        if "pg_native_recursion" not in self._optimizations:
            self._optimizations["pg_native_recursion"] = False # default value
        if "recursive_rules" not in self._optimizations:
            self._optimizations["recursive_rules"] = True # default value

        if isinstance(program_str, DT_Rule):
            self.rules.append(program_str)
        else:
            rules_str = program_str.split("\n")
            i = 0
            for rule in rules_str:
                    i += 1
                    self.rules.append(DT_Rule(rule_str=rule, operators=self.__OPERATORS, reasoning_tool=self.reasoning_tool, optimizations=self._optimizations, database=self.db, ruleNo=i))
        self.idb_predicates = []
        idb_predicate_names = []
        for rule in self.rules:
            if rule._head.table.name not in idb_predicate_names:
                self.idb_predicates.append(rule._head.table)
                idb_predicate_names.append(rule._head.table.name)

    def __str__(self):
        DT_Program_str = ""
        for rule in self.rules:
            DT_Program_str += str(rule) + "\n"
        return DT_Program_str[:-1] # removing the last \n
    
    # Uniform containment. self C dt_program2 (i.e. self program uniformly contains dt_program2)
    @timeit
    def contains(self, dt_program2):
        # consider rules in dt_program2 one by one, i.e., self contains rule1 of dt_program2, self contains rule2 of dt_program2, ...
        for rule in dt_program2.rules:
            if not self.contains_rule(rule, dt_program2.db.cVarMappingReverse):
                return False
        return True

    # Execute this program
    @timeit
    def executeonce(self, conn, faure_evaluation_mode="contradiction"):
        if self._optimizations["pg_native_recursion"] and self._isFaureEval: # pg_recursion is only used to Datalog
            program_sqls = RecursiveConverter(self).recursion_converter()
            cursor = conn.cursor()
            for sql in program_sqls:
                cursor.execute(sql)
            # conn.commit()
            return False
        else:
            changed = False
            for rule in self.rules:
                DB_changes = rule.execute(conn, faure_evaluation_mode)
                changed = changed or DB_changes
            # conn.commit()
            return changed    

    @timeit
    def execute(self, conn, faure_evaluation_mode="contradiction", violationTables=[]):
        iterations = 0
        changed = True
        while (changed and iterations < self.__MAX_ITERATIONS): # run until a fixed point reached or MAX_ITERATION reached
            iterations += 1
            changed = self.executeonce(conn, faure_evaluation_mode=faure_evaluation_mode)
            # for table in violationTables:
            #     if self._optimizations["simplification_on"] == False: # we always simplify the violation tables since we are early exiting
            #         self.reasoning_tool.simplification(table.name, conn)
            #     if not table.isEmpty(conn):
            #         conn.commit()
            #         return
        if iterations >= self.__MAX_ITERATIONS:
            print("Execution ending since max iterations of {} reached".format(str(iterations)))
            exit()
        conn.commit()

    # returns a program in which there are only non-recursive rules
    @timeit
    def getNonRecursiveRules(self):
        non_recursive_program = deepcopy(self)
        for i, rule in enumerate(non_recursive_program.rules):
            if rule.isRecursive:
                non_recursive_program.__deleteRule(ruleNum=i)
        return non_recursive_program

    # Given a mapping from old table names to new table names, changes the names of headers in the program
    @timeit 
    def changeIDBNames(self, IDBNamesChanges):
        for rule in self.rules:
            rule.changeHeaderTable(IDBNamesChanges[rule._head.table.name])

    @timeit
    def execute_semi_naive(self, conn, faure_evaluation_mode="contradiction"):
        if self._reasoning_engine.lower() == "bdd":
            for table in self.db.tables:
                if not table.isEmpty(conn):
                    self.reasoning_tool.process_condition_on_ctable(conn, tablename=table.name)
        P_prime = self.getNonRecursiveRules()
        IDBNamesChanges = {}
        for idb_predicate in self.idb_predicates: # idb_predicate is of type DT_Table
            idb_predicate_0_name = idb_predicate.name+"_0"
            idb_predicate_delta_1_name = idb_predicate.name+"_delta_1"
            idb_predicate.initiateNewTable(conn=conn, newName=idb_predicate_0_name)
            idb_predicate_delta = idb_predicate.initiateNewTable(conn=conn, newName=idb_predicate_delta_1_name)
            IDBNamesChanges[idb_predicate.name] = idb_predicate_delta
        P_prime.changeIDBNames(IDBNamesChanges)
        P_prime.executeonce(conn)
        if self._reasoning_engine.lower() == "bdd":
            print("before",self.reasoning_tool.variables_mapping)
            self.reasoning_tool.variables_mapping = deepcopy(P_prime.reasoning_tool.variables_mapping) #TODO: Fix hacky method
            print("after",self.reasoning_tool.variables_mapping)
        i = 1
        changed = True
        iterationEndMapping = {} # stores the last iteration of each idb_predicate. The last iteration contains the final result
        while changed:
            changed = False
            for idb_predicate in self.idb_predicates: # idb_predicate is of type DT_Table
                if idb_predicate.name in iterationEndMapping:
                    continue
                pred_name = idb_predicate.name
                output_pred = idb_predicate.initiateNewTable(conn=conn, newName=pred_name+"_"+str(i))
                output_pred_previous_name =  pred_name+"_"+str(i-1)
                pred_delta_i = idb_predicate.duplicateWithNewName("{}_delta_{}".format(pred_name,str(i)))
                if pred_delta_i.isEmpty(conn):
                    iterationEndMapping[idb_predicate.name] = idb_predicate.name+"_"+str(i-1)
                    continue
                output_pred.unionDifference(conn, tableNames=[output_pred_previous_name, pred_delta_i.name]) # Computes S_i := S_(i-1) U S_delta_i and returns S_i
                P_temp, P_temp_name = self.getTempRules(IDB_name = idb_predicate.name, i = i) # for each rule with idb_predicate, for each idb, create temp rules
                idb_predicate.initiateNewTable(conn=conn, newName=P_temp_name)
                P_temp.executeonce(conn)
                if self._reasoning_engine.lower() == "bdd":
                    self.reasoning_tool.variables_mapping = deepcopy(P_temp.reasoning_tool.variables_mapping) #TODO: Fix hacky method
                conn.commit()
                pred_delta_next = idb_predicate.initiateNewTable(conn=conn, newName="{}_delta_{}".format(pred_name,str(i+1)))
                tuplesAdded = pred_delta_next.setDifference(conn=conn, table1Name = P_temp_name, table2Name = output_pred.name) # tuples added is a boolean which is true when new tuples are generated
                if tuplesAdded != 0:
                    changed = True
                else:
                    iterationEndMapping[idb_predicate.name] = idb_predicate.name+"_"+str(i)
                    print(iterationEndMapping)
            i += 1
        conn.commit()
        for idb_predicate in self.idb_predicates: # idb_predicate is of type DT_Table
            if idb_predicate.name in iterationEndMapping:
                idb_predicate.delete(conn)
                idb_predicate.rename(conn, iterationEndMapping[idb_predicate.name])

    # given an idb predicate with name=name on iteration number i, return rules that compute the temporary IDBs for iteration i+1
    # TODO: Change the iteration variable 'i' to something else, since i is confusing
    def getTempRules(self, IDB_name, i):
        tempProgram = deepcopy(self)
        idb_predicate_names = []
        newHeadName = ""
        allTempRules = []
        for predicate in self.idb_predicates:
            idb_predicate_names.append(predicate.name)
        for rule in tempProgram.rules:
            if not rule.isRecursive:
                continue
            if rule._head.table.name == IDB_name:
                tempRules, newHeadName = rule.getTempRules(i=i, idb_predicates_names=idb_predicate_names) # return list of temp rules generated from that one rule
                allTempRules += tempRules
        numRules = len(tempProgram.rules)
        for j in range(numRules):
            tempProgram.__deleteRule(0)
        for tempRule in allTempRules:
            tempProgram.rules.append(tempRule)
        return tempProgram, newHeadName


    @timeit
    def executeonce_and_check_containment(self, conn, rule2):
        changedLocal = False
        for rule in self.rules:
            DB_changes = rule.execute(conn, faure_evaluation_mode="implication")
            changedLocal = changedLocal or DB_changes
            if rule2.isHeadContained(conn):
                return False
        return changedLocal
        # conn.commit()
        # return changed

    @timeit
    def stats(self):
        numAtoms = 0
        for rule in self.rules:
            numAtoms += len(rule._body)
        return len(self.rules), numAtoms


    # Uniform containment. 
    # self contains one rule of dt_program2
    def contains_rule(self, rule2, cVarMappingReverse2):
        conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
        # conn.set_session()
        conn.set_session(isolation_level=psycopg2.extensions.ISOLATION_LEVEL_READ_UNCOMMITTED)
        changed = True
        self.db.initiateDB(conn)
        rule2.addConstants(conn, cVarMappingReverse2)
        iterations = 0
        # conn.commit()
        while (changed and iterations < self.__MAX_ITERATIONS): # run until a fixed point reached or MAX_ITERATION reached
            iterations += 1
            if self._optimizations["recursive_rules"]:
                changed = self.executeonce(conn, faure_evaluation_mode="implication")
            else:
                changed = self.executeonce_and_check_containment(conn, rule2)

            if self._optimizations["simplification_on"] and self._reasoning_engine == 'z3':
                self.reasoning_tool.simplification(rule2._head.table.name, conn)
        conn.commit()
        if rule2.isHeadContained(conn):
            return True
        return False
            
    # minimize. Does minimization in place. Make sure to make a copy if you want the original program
    #TODO IMPORTANT: Program only rule should be entire program. Method: Delete contained rule and then add a rule without atom
    def minimize(self, minimizeAtomsOn = True, minimizeRulesOn = True, enhancedMinimizationOn = "Off", informationOn = False):
        if minimizeAtomsOn:
            self.__minimizeAtoms()
        if minimizeRulesOn:
            self.__minimizeRules(informationOn)
        if enhancedMinimizationOn != "Off": # enhancedMinimizationOn can either be "Off", "Const", or "No-Const". "No-Const" disables constant unification
            if enhancedMinimizationOn == "No-Const":
                self.__enhancedMinimization(False)
            else:
                self.__enhancedMinimization(True)
        

    # ======================== Private Methods ============================
    def __replaceRule(self, ruleNum, newRule):
        self.rules[ruleNum] = newRule

    def __deleteRule(self, ruleNum):
        if ruleNum < len(self.rules):
            self.rules.pop(ruleNum)

    def __copyWithDeletedRule(self, ruleNum):
        newProgram = deepcopy(self)
        newProgram.__deleteRule(ruleNum)
        return newProgram

    # Creates a database if the database is not explictly specified. Default db has only integers
    def __createDB(self, program_str):
        tables = []
        tableNames = []
        for rule_str in program_str.split("\n"):
            head_str = rule_str.split(":-")[0].strip()
            body_str = rule_str.split(":-")[1].strip().split(",(")[0]

            head_table = self.__createTable(head_str)
            if head_table.name not in tableNames:
                tableNames.append(head_table.name)
                tables.append(head_table)
            body = []
            # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
            atom_strs = parsing_utils.split_atoms(body_str)
            for atom_str in atom_strs:
                atom_str = atom_str.strip()
                # if atom_str[0] == '(': # additional constraint
                #     self._additional_constraints.append(atom_str[1:-1])
                #     continue
                body_atom_table = self.__createTable(atom_str)
                if body_atom_table.name not in tableNames:
                    tableNames.append(body_atom_table.name)
                    tables.append(body_atom_table)
        return DT_Database(tables)

    # given an atom string, creates a table
    def __createTable(self, atom_str):
        tableName = atom_str.split("(")[0].strip()
        numParameters = atom_str.count(",")+1 # hacky method to know the number of parameters. This will not work when there are arrays. TODO: Fix when there are arrays
        columns = {}
        for param in range(numParameters):
            columns['c'+str(param)] = "integer"
        return DT_Table(name=tableName, columns=columns)


    @property
    def __numRules(self):
        return len(self.rules)

    def __getRule(self, ruleNum):
        return self.rules[ruleNum]

    @timeit
    def __minimizeAtoms(self):        
        for ruleNum in range(self.__numRules):
            rule = self.__getRule(ruleNum)
            atomNum = 0
            while atomNum < rule.numBodyAtoms:
                if rule.numBodyAtoms == 1: # if only one atom left in program, stop minimizing redundant atoms
                    break

                rule_with_deleted_atom = rule.copyWithDeletedAtom(atomNum)
                if not rule_with_deleted_atom.safe():
                    atomNum += 1 
                    continue
                contained = self.contains_rule(rule_with_deleted_atom, self.db.cVarMappingReverse)
                if contained:
                    self.__replaceRule(ruleNum, rule_with_deleted_atom) 
                    rule = rule_with_deleted_atom
                else:
                    atomNum += 1   

    @timeit
    def __minimizeRules(self, informationOn = False):
        ruleNum = 0
        while ruleNum < self.__numRules: # replace for loop to while loop to avoid ruleNum out of list after deleting a rule
            if self.__numRules == 1: # if only one rule left in program, stop minimizing
                return
            rule = self.__getRule(ruleNum)
            newProgram = self.__copyWithDeletedRule(ruleNum)
            if informationOn:
                print("\n\nChecking rule: ", rule)
                print("Program:\n" + str(newProgram))
            if newProgram.contains_rule(rule, self.db.cVarMappingReverse):
                if informationOn:
                    print("The minimized program contains rule {}. Removing rule.".format(rule.ruleNo))
                    input()
                self.__deleteRule(ruleNum)
            else:
                if informationOn:
                    print("Rule is not redundant")
                    input()
                ruleNum += 1   


    # @timeit
    # def __enhancedMinimization(self, constantUnificationOn = True):
    #     signatureBuckets = {}
    #     ruleName = {}
    #     P_unified = []
    #     for ruleNum, rule in enumerate(Prules):
    #         signature = rule.getSignature()
    #         if not signature in signatureBuckets:
    #             signatureBuckets[signature] = ([],[]) # (rule, ruleNum)
    #         signatureBuckets[signature][0].append(rule)
    #         signatureBuckets[signature][1].append("r"+str(ruleNum))
    #     for signature in signatureBuckets:
    #         bucket = signatureBuckets[signature][0]
    #         ruleNums = signatureBuckets[signature][1]
    #         # for i in range(len(bucket)-1):
    #         i = 0
    #         while i < len(bucket):
    #             j = i+1
    #             # for j in range(i+1, len(bucket)-1):
    #             while j < len(bucket):
    #                 r1 = bucket[i]
    #                 r2 = bucket[j]
    #                 r_tmp = unify(r1, r2, ruleNums[i], constantUnificationOn)
    #                 if (r_tmp != None): # unification was successful
    #                     bucket[i] = r_tmp
    #                     del bucket[j]
    #                     del ruleNums[j]
    #                 else:
    #                     j += 1
    #             i += 1
    #         for rule in bucket: # add all unified rules to p_unified
    #             P_unified.append(str(rule))
    #     self.__replaceProgram(P_unified)