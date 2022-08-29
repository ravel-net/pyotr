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
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)

from Core.Homomorphism.Datalog.atom import DT_Atom

class DT_Rule:
    """
    A class used to represent a datalog rule.

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

    def __init__(self, rule_str, databaseTypes={},operators=[]):
        head_str = rule_str.split(":-")[0].strip()
        body_str = rule_str.split(":-")[1].strip()
        self._variables = []
        self._head = DT_Atom(head_str, databaseTypes, operators)
        self._body = []
        self._DBs = []
        self._mapping = {}
        self._operators = operators
        db_names = []
        for atom_str in body_str.split("),"):
            atom_str = atom_str.strip()
            if atom_str[-1] != ")":
                atom_str += ")"
            currAtom = DT_Atom(atom_str, databaseTypes, operators)
            if currAtom.db["name"] not in db_names:
                self._DBs.append(currAtom.db)
                db_names.append(currAtom.db["name"])
            atomVars = currAtom.variables
            for var in atomVars:
                if var not in self._variables:
                    self._variables.append(var)
            self._body.append(currAtom)
        for i, var in enumerate(self._variables):
            self._mapping[var] = i
    
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
        query_summary = self._head.parameters
        for i, atom in enumerate(self._body):
            tables.append("{} t{}".format(atom.db["name"], i))
            for col, val in enumerate(atom.parameters):
                if val[0].isdigit():
                    constraints.append("t{}.{} = '{}'".format(i, atom.db["column_names"][col], val))
                else: # variable
                    if val not in variableList:
                        variableList[val] = []
                    variableList[val].append("t{}.{}".format(i, atom.db["column_names"][col]))
        for param in self._head.parameters:
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
                    summary_nodes.append(summary)
            if not hasOperator:
                if param[0].isdigit():
                    summary_nodes.append(param)
                else:
                    summary_nodes.append(variableList[param][0])
        for var in variableList:
            for i in range(len(variableList[var])-1):
                constraints.append(variableList[var][i] + " = " + variableList[var][i+1])

        sql = "insert into " + self._head.db["name"] + " select " + ", ".join(summary_nodes) + " from " + ", ".join(tables)
        if (constraints):
            sql += " where " + " and ".join(constraints)
        cursor = conn.cursor()
        # print(sql)
        cursor.execute(sql)
        affectedRows = cursor.rowcount
        conn.commit()
        changed = (affectedRows > 0)
        return changed

    def isHeadContained(self, conn):
        constraints = []
        for col, param in enumerate(self._head.parameters):
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
        changed = (len(result) > 0)
        return changed

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
        return string[:-1]

if __name__ == "__main__":
    a = "Asd"
    rule = DT_Rule("A(x,y,z) :- Gasd(x,1,y),B(z,x),C(y,z,2)")
    rule.isHeadContained(a)
    # print(atom.db)