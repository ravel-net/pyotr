import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2 
from copy import deepcopy
from Core.Homomorphism.Datalog.rule import DT_Rule
import databaseconfig as cfg

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
    
    # databaseTypes is a dictionary {"database name":[ordered list of column types]}. By default, all column types are integers. If we need some other datatype, we need to specify using this parameter
    def __init__(self, program_str, databaseTypes={}):
        rules_str = program_str.split("\n")
        print("rules_str", rules_str)
        self._rules = []
        for rule in rules_str:
            self._rules.append(DT_Rule(rule, databaseTypes, self.__OPERATORS))
        
    # def __eq__(self, other):
    #     return True if self._account_number == other._account_number else False
    
    def __str__(self):
        DT_Program_str = ""
        for rule in self._rules:
            DT_Program_str += str(rule) + "\n"
        return DT_Program_str[:-1] # removing the last \n
    
    # Uniform containment. self C dt_program2 (self program contains dt_program2)
    def contains(self, dt_program2):
        for rule in self._rules:
            if not dt_program2.contained_by_rule(rule):
                return False
        return True

    def execute(self, conn):
        changed = False
        for rule in self._rules:
            DB_changes = rule.execute(conn)
            changed = changed or DB_changes
        return changed

    def initiateDB(self, conn):
        databases = []
        db_names = []
        for rule in self._rules:
            for db in rule.getDBs:
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


    # Uniform containment. rule2 C self (rule contains self program)
    def contained_by_rule(self, rule2):
        conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
        conn.set_session()
        changed = True
        self.initiateDB(conn)
        rule2.addConstants(conn)
        iterations = 0
        while (changed and iterations < self.__MAX_ITERATIONS):
            iterations += 1
            changed = self.execute(conn)
            if rule2.isHeadContained(conn):
                return True
        return False


    def replaceRule(self, ruleNum, newRule):
        self._rules[ruleNum] = newRule

    def deleteRule(self, ruleNum):
        self._rules.pop(ruleNum)

    def copyWithDeletedRule(self, ruleNum):
        newProgram = deepcopy(self)
        newProgram.deleteRule(ruleNum)
        return newProgram

    # minimize. Does minimization in place. Make sure to make a copy if you want the original program
    def minimize(self):
        numRules = self.numRules
        for ruleNum in range(numRules):
            rule = self.getRule(ruleNum)
            numAtoms = rule.numBodyAtoms
            for atomNum in range(numAtoms):
                rule_with_deleted_atom = rule.copyWithDeletedAtom(atomNum)
                if self.contained_by_rule(rule_with_deleted_atom):
                    self.replaceRule(ruleNum, rule_with_deleted_atom)                
        for ruleNum in range(numRules):
            rule = self.getRule(ruleNum)
            newProgram = self.copyWithDeletedRule(ruleNum)
            if newProgram.contained_by_rule(rule):
                self.deleteRule(ruleNum)
    
    @property
    def numRules(self):
        return len(self._rules)

    def getRule(self, ruleNum):
        return self._rules[ruleNum]

    # @classmethod
    # def from_csv(cls, filepath):
    #     with open(filepath, "r") as f:
    #         row = csv.reader(f).__next__()
    #         owner, account_number = row
    #     return cls(owner, account_number)
    
    # @staticmethod
    # def _to_dash_date(date):
    #     # utility to replace "/" with "-" in a date
    #     return date.replace("/", "-") 
    
if __name__ == "__main__":
    # Example 6 - Containment
    p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
    p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
    print(p1)
    print(p2)
    # program1 = DT_Program(p1)
    # program2 = DT_Program(p2)
    # print(program1.contains(program2))
    # print(program2.contains(program1))    

    # # Example 7 - Minimization
    p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
    p2 = "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"
    print(p1)
    print(p2)
    # program1 = DT_Program(p1)
    # program2 = DT_Program(p2)
    # print(program1.contains(program2))
    # print(program2.contains(program1))    
    # program1.minimize()
    # print(program1)

    # # Control Plane Toy Example
    p1 = "R(x2,xd,x2 || xp) :- link(x2,x3), link(x2,x4), R(x3,xd,xp)\nR(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), link(x2,x4), R(x2,xd,xp)"
    p2 = "R(x2,xd,x2 || xp) :- link(x2,x3), R(x3,xd,xp)\nR(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), R(x2,xd,xp)"
    print(p1)
    print(p2)
    # program1 = DT_Program(p1, {"R":["integer", "integer","integer[]"]}) # We need to provide the second argument, the list of column types for a database only when the default column type is not integer
    # program2 = DT_Program(p2, {"R":["integer", "integer","integer[]"]})
    # print(program2.contains(program1))
    # print(program1.contains(program2))
