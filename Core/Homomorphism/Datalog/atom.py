
class DT_Atom:
    """
    A class used to represent a Datalog Atom
    """
    
    def __init__(self, atom_str):
        split_str = atom_str[:-1].split("(")
        self.db = {}
        self.variables = []
        self.parameters = split_str[1].split(",")
        self.db["name"] = split_str[0]
        self.db["column_names"] = []
        for i, var in enumerate(self.parameters):
            self.db["column_names"].append("c"+str(i))
            if not var[0].isdigit() and var not in self.variables:
                self.variables.append(var)
        
    def __str__(self):
        return self.db["name"]+"("+",".join(self.parameters)+")"


    def addConstants(self, conn, mapping):
        variableConstants = []
        for var in self.parameters:
            variableConstants.append(str(mapping[var]))
        sql = "insert into " + self.db["name"] + " values(" +  ",".join(variableConstants) + ")"
        cursor = conn.cursor()
        print(sql)
        cursor.execute(sql)
        conn.commit()


if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
