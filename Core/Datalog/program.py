import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2 
from copy import deepcopy
from Core.Datalog.rule import DT_Rule
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table
from Core.Datalog.DL_minimization import minimizeAtoms, minimizeRules, enhancedMinimization
from Backend.reasoning.Z3.z3smt import z3SMTTools
from Backend.reasoning.CUDD.BDDTools import BDDTools
from utils.parsing_utils import split_atoms
from utils.converter.recursion_converter import RecursiveConverter
import databaseconfig as cfg
from utils.logging import timeit

class DT_Program:
    """
    A class used to represent a datalog program.

    Attributes
    ----------
    __MAX_ITERATIONS : int
        the maximum number of times a datalog program should be run (in case fixed point isn't reached)
    __OPERATORS : string[]
        operators supported in queries. Currently, only array concatination operator "||" is supported
    _rules : DT_Rule[]
        array of datalog rules


    Methods
    -------
    contains(program2)
        does this program uniformly contain program2?
    minimize()
        minimize this datalog program
    execute(conn)
        run this datalog program on database pointed by psycopg2 connection "conn"
    initiateDB(conn)
        initiate tables in this datalog program on database pointed by psycopg2 connection "conn"
    contained_by_rule(rule2)
        does rule2 uniformly contain this program?
    """
    
    __MAX_ITERATIONS = 10
    __OPERATORS = ["||"]
    
    # Default values: "simplification_on"=False, "pg_native_recursion"=False, "recursive_rules"=True
    def __init__(self, program_str, database=None, reasoning_engine='z3', optimizations={}):
        self.rules = []
        # IMPORTANT: The assignment of variables cannot be random. They have to be assigned based on the domain of any c variable involved
        self._program_str = program_str
        self.db = database #TODO: When tables not specified, have a function to extract tables and databases.
        if not self.db:
            self.db = self.createDB(program_str)
        self._isFaureEval = False
        self._optimizations = optimizations
        self.reasoning_tool = None
        self._reasoning_engine = reasoning_engine
        if len(self.db.c_tables) > 0: # when faureeval is required
            self._isFaureEval = True
            if self._reasoning_engine == 'z3':
                self.reasoning_tool = z3SMTTools(variables=self.db.c_variables, domains=self.db.cvar_domain, reasoning_type=self.db.reasoning_types, mapping=self.db.cVarMapping)
            else:
                self.reasoning_tool = BDDTools(variables=self.db.c_variables, domains=self.db.cvar_domain, reasoning_type=self.db.reasoning_types)

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
            for rule in rules_str:
                    self.rules.append(DT_Rule(rule_str=rule, operators=self.__OPERATORS, reasoning_tool=self.reasoning_tool, optimizations=self._optimizations, database=self.db))
    
    def __str__(self):
        DT_Program_str = ""
        for rule in self.rules:
            DT_Program_str += str(rule) + "\n"
        return DT_Program_str[:-1] # removing the last \n
    
    # Uniform containment. self C dt_program2 (self program contains dt_program2)
    def contains(self, dt_program2):
        # consider rules in dt_program2 one by one, i.e., self contains rule1 of dt_program2, self contains rule2 of dt_program2, ...
        for rule in dt_program2.rules:
            if not self.contains_rule(rule, dt_program2.db.cVarMappingReverse):
                return False
        return True


    # @timeit
    def execute(self, conn, faure_evaluation_mode="contradiction"):
        if self._optimizations["pg_native_recursion"] and self._isFaureEval: # pg_recursion is only used to Datalog
            program_sqls = RecursiveConverter(self).recursion_converter()
            cursor = conn.cursor()
            for sql in program_sqls:
                cursor.execute(sql)
            conn.commit()
            return False
        else:
            changed = False
            for rule in self.rules:
                DB_changes = rule.execute(conn, faure_evaluation_mode)
                changed = changed or DB_changes
            conn.commit()
            return changed    

    # @timeit
    def execute_and_check_containment(self, conn, rule2):
        changedLocal = False
        for rule in self.rules:
            DB_changes = rule.execute(conn, faure_evaluation_mode="implication")
            changedLocal = changedLocal or DB_changes
            if rule2.isHeadContained(conn):
                return False
        return changedLocal
        # conn.commit()
        # return changed

    def stats(self):
        print("Number of rules: ", len(self.rules))
        numAtoms = 0
        for rule in self.rules:
            numAtoms += len(rule._body)
        print("Number of atoms: ", numAtoms)
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
                changed = self.execute(conn, faure_evaluation_mode="implication")
            else:
                changed = self.execute_and_check_containment(conn, rule2)

            if self._optimizations["simplification_on"] and self._reasoning_engine == 'z3':
                self.reasoning_tool.simplification(rule2._head.table.name, conn)
        if rule2.isHeadContained(conn):
            return True
        conn.commit()
        return False

    # Takes a newRules (a list of rules as strings) as input, and replaces the current program with the new rules
    def replaceProgram(self, newRules):
        newProgram = DT_Program(program_str="\n".join(newRules), database=self.db, reasoning_engine=self._reasoning_engine, optimizations=self._optimizations)
        # newObj = func(newProgram)
        self.__dict__.update(newProgram.__dict__)

    def replaceRule(self, ruleNum, newRule):
        self.rules[ruleNum] = newRule

    def deleteRule(self, ruleNum):
        if ruleNum < len(self.rules):
            self.rules.pop(ruleNum)

    def copyWithDeletedRule(self, ruleNum):
        newProgram = deepcopy(self)
        newProgram.deleteRule(ruleNum)
        return newProgram
        

    # minimize. Does minimization in place. Make sure to make a copy if you want the original program
    #TODO IMPORTANT: Program only rule should be entire program. Method: Delete contained rule and then add a rule without atom
    def minimize(self, minimizeAtomsOn = True, minimizeRulesOn = True, enhancedMinimizationOn = "Off"):
        if minimizeAtomsOn:
            minimizeAtoms(self)
        if minimizeRulesOn:
            minimizeRules(self)
        if enhancedMinimizationOn != "Off": # enhancedMinimizationOn can either be "Off", "Const", or "No-Const". "No-Const" disables constant unification
            if enhancedMinimizationOn == "No-Const":
                enhancedMinimization(self, False)
            else:
                enhancedMinimization(self, True)

    # Creates a database if the database is not explictly specified. Default db has only integers
    def createDB(self, program_str):
        tables = []
        tableNames = []
        for rule_str in program_str.split("\n"):
            head_str = rule_str.split(":-")[0].strip()
            body_str = rule_str.split(":-")[1].strip().split(",(")[0]

            head_table = self.createTable(head_str)
            if head_table.name not in tableNames:
                tableNames.append(head_table.name)
                tables.append(head_table)
            body = []
            # atom_strs = re.split(r'\),|\],', body_str) # split by ], or ),
            atom_strs = split_atoms(body_str)
            for atom_str in atom_strs:
                atom_str = atom_str.strip()
                # if atom_str[0] == '(': # additional constraint
                #     self._additional_constraints.append(atom_str[1:-1])
                #     continue
                body_atom_table = self.createTable(atom_str)
                if body_atom_table.name not in tableNames:
                    tableNames.append(body_atom_table.name)
                    tables.append(body_atom_table)
        return DT_Database(tables)

    # given an atom string, creates a table
    def createTable(self, atom_str):
        tableName = atom_str[0]
        numParameters = atom_str.count(",")+1 # hacky method to know the number of parameters. This will not work when there are arrays. TODO: Fix when there are arrays
        columns = {}
        for param in range(numParameters):
            columns['c'+str(param)] = "integer"
        return DT_Table(name=tableName, columns=columns)


    @property
    def numRules(self):
        return len(self.rules)

    def getRule(self, ruleNum):
        return self.rules[ruleNum]