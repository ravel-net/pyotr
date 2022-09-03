import re
from ipaddress import IPv4Address

class DT_Atom:
    """
    A class used to represent a Datalog Atom
    
    Attributes
    ----------
    parameters : string[]
        ordered list of parameters in the atom
    db : dictionary{"name", "column_names", "column_types"}
        databases referenced in the atom along with the column names and column types. The default column type is integer and the default column names is c1, c2, ..., cn
    variables : string[]
        list of variables in the atom

    Methods
    -------
    addConstants(conn)
        Add constants in place of variables referenced in this atom on database pointed by psycopg2 connection "conn". Conversion to sql and execution of sql occurs here
    """
    
    def __init__(self, atom_str, databaseTypes={}, operators=[], c_variables=[]):
        split_str = re.split(r'\(|\)\[', atom_str[:-1])
        # split_str = atom_str[:-1].split("(")
        self.db = {}
        self.variables = []
        self.c_variables = c_variables
        self.constraints = [] # conditions for c-variables
        if len(split_str) == 3: # conditions for c-variables
            for c in split_str[2].split(","):
                processed_c = self.datalog_condition2z3_condition(c)
                self.constraints.append(processed_c)
        self.parameters = [p.strip() for p in split_str[1].split(",")]
        self.db["name"] = split_str[0]
        self.db["column_names"] = []
        self.db["column_types"] = []
        for i, var in enumerate(self.parameters):
            self.db["column_names"].append("c"+str(i))
            if self.db["name"] in databaseTypes:
                self.db["column_types"].append(databaseTypes[self.db["name"]][i])
            else:
                self.db["column_types"].append("integer")
            hasOperator = False
            for op in operators:
                if (op in var):
                    hasOperator = True
                    concatinatingVars = var.split(op)
                    for concatinatingVar in concatinatingVars:
                        concatinatingVar = concatinatingVar.strip()
                        if not concatinatingVar[0].isdigit() and concatinatingVar not in self.variables:
                            self.variables.append(concatinatingVar)
            if not hasOperator and not var[0].isdigit():
                if var not in self.c_variables and var not in self.variables:
                    self.variables.append(var)
        # column for condition attribute
        if self.constraints:
            self.db["column_names"].append("condition")
            self.db["column_types"].append("text[]")
        
    def __str__(self):
        atom_str = self.db["name"]+"("+",".join(self.parameters)+")"
        if self.constraints:
            atom_str += "[{}]".format(", ".join(self.constraints))
        return atom_str


    def addConstants(self, conn, mapping):
        variableConstants = []
        for i, var in enumerate(self.parameters):
            if var in self.c_variables:
                variableConstants.append("'{}'".format(var))
                continue
            if self.db["column_types"][i] == "integer":
                variableConstants.append(str(mapping[var]))
            elif "[]" in self.db["column_types"][i]: # Only supports single dimensional array
                variableConstants.append("ARRAY [" + str(mapping[var]) + "]")
            elif self.db["column_types"][i] == "inet_faure":
                IPaddr = int(IPv4Address('10.0.0.1')) + mapping[var]
                variableConstants.append("'{}'".format(str(IPv4Address(IPaddr))))
            elif self.db["column_types"][i] == "int4_faure":
                variableConstants.append("'{}'".format(mapping[var]))

        if self.c_variables:
            variableConstants.append("'{" + ", ".join(['"{}"'.format(c) for c in self.constraints]) + "}'") 
        sql = "insert into " + self.db["name"] + " values(" +  ",".join(variableConstants) + ")"
        cursor = conn.cursor()
        # print(sql)
        cursor.execute(sql)
        conn.commit()
    
    def datalog_condition2z3_condition(self, condition):
        # Assume support logical Or/And, excluding mixed uses
        logical_opr = None
        if '^' in condition:
            logical_opr = '^'
        elif '&' in condition:
            logical_opr = '&'
        
        conds = []
        processed_cond = None
        if logical_opr:
            for c in condition.split(logical_opr):
                c = c.strip()
                if c.split()[1].strip() == '=':
                    c = c.replace('=', '==')
                conds.append(c)
        else:
            if condition.split()[1].strip() == '=':
                condition = condition.replace('=', '==')
            processed_cond = condition
        
        if logical_opr == '^':
            processed_cond = "Or({})".format(", ".join(conds))
        elif logical_opr == '&':
            processed_cond = "And({})".format(", ".join(conds))
        
        if processed_cond is None:
            print("Illegal condition: {}!".format(condition))
            exit()
        return processed_cond
        



if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
