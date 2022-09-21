import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
import psycopg2 
from copy import deepcopy
from Core.Homomorphism.Datalog.rule import DT_Rule
import databaseconfig as cfg
import time

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
    def __init__(self, program_str, databaseTypes={}, domains=[], c_variables=[], reasoning_engine='z3', reasoning_type='Int', datatype='Integer', simplification_on=True, c_tables=[]):
        self._rules = []
        # IMPORTANT: The assignment of variables cannot be random. They have to be assigned based on the domain of any c variable involved
        if isinstance(program_str, DT_Rule):
            self._rules.append(program_str)
        else:
            rules_str = program_str.split("\n")
            for rule in rules_str:
                self._rules.append(DT_Rule(rule, databaseTypes, self.__OPERATORS, domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on, c_tables))
    # def __eq__(self, other):
    #     return True if self._account_number == other._account_number else False
    
    def __str__(self):
        DT_Program_str = ""
        for rule in self._rules:
            DT_Program_str += str(rule) + "\n"
        return DT_Program_str[:-1] # removing the last \n
    
    # Uniform containment. self C dt_program2 (self program contains dt_program2)
    def contains(self, dt_program2):
        # consider rules in dt_program2 one by one, i.e., self contains rule1 of dt_program2, self contains rule2 of dt_program2, ...
        for rule in dt_program2._rules:
            if not self.contains_rule(rule):
                return False
        return True

    def execute(self, conn):
        changed = False
        for rule in self._rules:
            # print("\n------------------------")
            print("executing rule:", rule)
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


    # Uniform containment. 
    # self contains one rule of dt_program2
    def contains_rule(self, rule2):
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
    #TODO IMPORTANT: Program only rule should be entire program. Method: Delete contained rule and then add a rule without atom
    def minimize(self):
        numRules = self.numRules
        
        for ruleNum in range(numRules):
            rule = self.getRule(ruleNum)
            atomNum = 0
            while atomNum < rule.numBodyAtoms:
                if rule.numBodyAtoms == 1: # if only one atom left in program, stop minimizing redundant atoms
                    break

                rule_with_deleted_atom = rule.copyWithDeletedAtom(atomNum)
                
                if not rule_with_deleted_atom.safe():
                    atomNum += 1 
                    continue

                contained = self.contains_rule(rule_with_deleted_atom)
                if contained:
                    self.replaceRule(ruleNum, rule_with_deleted_atom) 
                    rule = rule_with_deleted_atom
                else:
                    atomNum += 1   

        ruleNum = 0
        while ruleNum < self.numRules: # replace for loop to while loop to avoid ruleNum out of list after deleting a rule
            if self.numRules == 1: # if only one rule left in program, stop minimizing
                return
            rule = self.getRule(ruleNum)
            newProgram = self.copyWithDeletedRule(ruleNum)
            if newProgram.contains_rule(rule):
                self.deleteRule(ruleNum)
            else:
                ruleNum += 1   
              
        # for ruleNum in range(numRules):
        #     rule = self.getRule(ruleNum)
        #     newProgram = self.copyWithDeletedRule(ruleNum)
        #     if newProgram.contains_rule(rule):
        #         print("pop rule:", rule)
        #         self.deleteRule(ruleNum)
    
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
    ################################## Example 6 - Containment ##################################
    # p1 = "G(x,z) :- A(x,z)\nG(x,z) :- G(x,y),G(y,z)"
    # p2 = "G(x,z) :- A(x,z)\nG(x,z) :- A(x,y),G(y,z)"
    # print(p1)
    # print(p2)
    # program1 = DT_Program(p1)
    # program2 = DT_Program(p2)
    # print(program1.contains(program2))
    # print(program2.contains(program1))    

    ################################# Example 7 - Minimization################################
    # p1 = "G(x,y,z) :- G(x,w,z),A(w,y),A(w,z),A(z,z),A(z,y)"
    # # p2 = "G(x,y,z) :- G(x,w,z),A(w,z),A(z,z),A(z,y)"
    # program1 = DT_Program(p1)
    # # program2 = DT_Program(p2)
    # # print(program1.contains(program2))
    # # print(program2.contains(program1))    
    # print(program1)
    # program1.minimize()
    # print(program1)

    ################################# Control Plane Toy Example #################################
    # p1 = "R(h,xd,h || xp) :- l(h,x1), l(h,x2), R(x2,xd,xp)\nR(h,xd,h || xp) :- l(h,x1), l(h,x2), R(x1,xd,xp), (h \\not_in [xp])\nR(x1,xd,[xd]) :- l(h,x1), l(x1,xd), (x1 \\not_in [xd])\nR(x2,xd,[xd]) :- l(h,x2), l(x2, xd)"
    p1 = "R(h,xd,h || xp) :- l(h,x2), R(x2,xd,xp)\nR(h,xd,h || xp) :- l(h,x1), R(x1,xd,xp), (h \\not_in [xp])\nR(x1,xd,[xd]) :- l(x1,xd), (x1 \\not_in [xd])\nR(x2,xd,[xd]) :- l(x2, xd)"
    # p2 = "R(x2,xd,x2 || xp) :- link(x2,x3), R(x3,xd,xp)\nR(x1,xd,x1 || xp) :- link(x1,x2), link(x2,x3), R(x2,xd,xp)"
    program1 = DT_Program(p1, {"R":["integer", "integer","integer[]"]}) # We need to provide the second argument, the list of column types for a database only when the default column type is not integer
    print()
    print(program1)
    print()
    # program2 = DT_Program(p2, {"R":["integer", "integer","integer[]"]})
    # print(program2.contains(program1))
    # print(program1.contains(program2))
    program1.minimize()
    print("After Minimize")
    print(program1)

    ################################ toy example of route aggregation#########################
    # P = "R(z, d1, [z])[d1 = 1] :- R(x, d1, [z])[d1 = 1], R(y, d2, [z]), L(z, x), L(z, y)\nR(z, d2, [z])[d2 = 2] :- R(x, d1, [z]), R(y, d2, [z])[d2 = 2], L(z, x), L(z, y)"
    # Q = "R(v, d, [u])[d = 1 ^ d = 2] :- R(u, d, [u])[d = 1 ^ d = 2], L(v, u)"     

    # # P = "R(z, d1)[d1 = 1] :- R(x, d1)[d1 = 1], R(y, d2), L(z, x), L(z, y)\nR(z, d2)[d2 = 2] :- R(x, d1), R(y, d2)[d2 = 2], L(z, x), L(z, y)"
    # # Q = "R(v, d)[d = 1 ^ d = 2] :- R(u, d)[d = 1 ^ d = 2], L(v, u)" 
    # # P_program = DT_Program(P, {"R":["int4_faure", "int4_faure"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d1', 'd2'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R"])
    # # Q_program = DT_Program(Q, {"R":["int4_faure", "int4_faure"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R"])


    # ''' 
    # # we need to provide databaseTypes, the list of column types for a database only when the default column type is not integer
    # # we need to provide domains, c_variables, reasoning_engine, reasoning_type, datatype, simplification_on when using faure_log.
    # '''
    # P_program = DT_Program(P, {"R":["int4_faure", "int4_faure", "Integer[]"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d1', 'd2'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R"])
    # Q_program = DT_Program(Q, {"R":["int4_faure", "int4_faure", "Integer[]"], "L":["int4_faure", "int4_faure"]}, domains=['1', '2'], c_variables=['d'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R"])
    # print(P_program)
    # res1 = P_program.contains(Q_program)
    # print("P contains Q:", res1)
    # res2 = Q_program.contains(P_program)
    # print("Q contains P:", res2)
    # print("P equivalent Q:", res1 and res2)

    # print("brefore minimizing", P_program)
    # P_program.minimize()
    # print("after minimizing", P_program)

    ########################################## ACL Example:  ######################################
    # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, h4), l(a2, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a1, e1), l(a3, e1)\nR(a1, h3, [e1, x, y], 3)[h3 = 10] :- R(e1, h3, [x, y], 2)[h3 = 10], l(a1, h1), l(a1, e1), l(a1, h2)\nR(h1, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h1)\nR(h2, h3, [a1, x, y, z], 4) :- R(a1, h3, [x, y, z], 3), l(a1, h2)"

    # # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, e1)\nR(e1, h3, [a3, x], 2) :- R(a3, h3, [x], 1), l(a2, e1), l(a3, e1)\nR(e1, h3, [a2, x], 2) :- R(a2, h3, [x], 1), l(a2, e1), l(a3, e1)"    

    # # p1 = "R(a3, h3, [h3], 1)[h3 = 10] :- l(a3,h3)[h3 = 10], l(a3,e1)\nR(a2, h3, [h3], 1) :- l(a2,h3), l(a2, e1)"

    # program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains=['10', '20'], c_variables=['h3'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])
    # # program1 = DT_Program(p1, {"R":["integer", "integer","integer[]", "integer"], "l":["integer", "integer"]})

    # start = time.time()
    # print(program1)
    # program1.minimize()
    # print(program1)
    # print("After Minimization")
    # end = time.time()
    # print(program1)
    # print (end-start)


    ####################################### Fattree 16: ######################################
    # num_exp = 5
    # time_16 = []
    # for i in range(num_exp):
    #     fattree16 = "R(a1, h16, [e2], 1) :- l(a1,e2)\nR(a2, h16, [e2], 1) :- l(a2,e2)\nR(a3, h16, [e2], 1) :- l(a3,e2)\nR(a4, h16, [e2], 1) :- l(a4,e2)\nR(a5, h16, [e2], 1) :- l(a5,e2)\nR(a6, h16, [e2], 1) :- l(a6,e2)\nR(a7, h16, [e2], 1) :- l(a7,e2)\nR(a8, h16, [e2], 1) :- l(a8,e2)\nR(e1, h16, [a1,x], 2) :- R(a1, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a2,x], 2) :- R(a2, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a3,x], 2) :- R(a3, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a4,x], 2) :- R(a4, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a5,x], 2) :- R(a5, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a6,x], 2) :- R(a6, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a7,x], 2) :- R(a7, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)\nR(e1, h16, [a8,x], 2) :- R(a8, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4), l(e1, a5), l(e1, a6), l(e1, a7), l(e1, a8)"
    #     fattree16_program = DT_Program(fattree16, {"R":["integer", "integer","integer[]", "integer"]})
    #     start = time.time()
    #     fattree16_program.minimize()
    #     end = time.time()
    #     print(fattree16_program)
    #     time_16.append(end-start)


    ######################################## Fattree 8: ######################################
    # time_8 = []
    # for i in range(num_exp):
    #     fattree8 = "R(a1, h8, [e2], 1) :- l(a1,e2)\nR(a2, h8, [e2], 1) :- l(a2,e2)\nR(a3, h8, [e2], 1) :- l(a3,e2)\nR(a4, h8, [e2], 1) :- l(a4,e2)\nR(e1, h8, [a1,x], 2) :- R(a1, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4)\nR(e1, h8, [a2,x], 2) :- R(a2, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4)\nR(e1, h8, [a3,x], 2) :- R(a3, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4)\nR(e1, h8, [a4,x], 2) :- R(a4, h8, [x], 1), l(e1, a1), l(e1, a2), l(e1, a3), l(e1, a4)"
    #     fattree8_program = DT_Program(fattree8, {"R":["integer", "integer","integer[]", "integer"]})
    #     start = time.time()
    #     fattree8_program.minimize()
    #     print(fattree8_program)
    #     end = time.time()
    #     time_8.append(end-start)
    # print("16 fattree:", time_16)
    # print("8 fattree:", time_8)

    ######################################## Loops Example ######################################
    # p1 = "R(x1, d, [d]) :- l(d,x1), l(h,x1), (x1 \\not_in [d])\nR(x2, d, [d]) :- l(d,x2), l(h,x2), (x2 \\not_in [d])\nR(h, d, [x1, y]) :- R(x1, d, [y]), l(h, x1), l(h, x2), (h \\not_in [x1,y])\nR(h, d, [x2, y]) :- R(x2, d, [y]), l(h, x1), l(h, x2), (h \\not_in [x2,y])"

    # # program1 = DT_Program(p1, {"R":["int4_faure", "int4_faure","int4_faure[]", "integer"], "l":["int4_faure", "int4_faure"]}, domains=['10', '20'], c_variables=['x1','x2'], reasoning_engine='z3', reasoning_type='Int', datatype='int4_faure', simplification_on=True, c_tables=["R", "l"])

    # program1 = DT_Program(p1, {"R":["integer", "integer","integer[]"], "l":["integer", "integer"]})

    # start = time.time()
    # print(program1)
    # program1.minimize()
    # print("Before Minimization")
    # print("R(x1, d, [d]) :- l(d,x1), l(h,x1), (x1 \\not_in [d])\nR(x2, d, [d]) :- l(d,x2), l(h,x2), (x2 \\not_in [d])\nR(h, d, [x1, y]) :- R(x1, d, [y]), l(h, x1), l(h, x2), (h \\not_in [x1,y])\nR(h, d, [x2, y]) :- R(x2, d, [y]), l(h, x1), l(h, x2), (h \\not_in [x2,y])")
    # print()
    # print("After Minimization")
    # print(program1)
    # end = time.time()
    # print (end-start)