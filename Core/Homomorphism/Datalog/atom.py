
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
    
    def __init__(self, atom_str, databaseTypes={}, operators=[]):
        split_str = atom_str[:-1].split("(")
        self.db = {}
        self.variables = []
        self.parameters = split_str[1].split(",")
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
            if not hasOperator and not var[0].isdigit() and var not in self.variables:
                self.variables.append(var)
        
    def __str__(self):
        return self.db["name"]+"("+",".join(self.parameters)+")"


    def addConstants(self, conn, mapping):
        variableConstants = []
        for i, var in enumerate(self.parameters):
            if self.db["column_types"][i] == "integer":
                variableConstants.append(str(mapping[var]))
            elif "[]" in self.db["column_types"][i]: # Only supports single dimensional array
                variableConstants.append("ARRAY [" + str(mapping[var]) + "]")
        sql = "insert into " + self.db["name"] + " values(" +  ",".join(variableConstants) + ")"
        cursor = conn.cursor()
        # print(sql)
        cursor.execute(sql)
        conn.commit()


if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
