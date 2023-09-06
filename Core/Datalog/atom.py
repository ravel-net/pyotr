from ipaddress import IPv4Address
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from utils import parsing_utils
from Core.Datalog.conditionTree import ConditionTree
from copy import deepcopy
from utils.logging import timeit

class DT_Atom:
    """
    A class used to represent a Datalog Atom
    
    Attributes
    ----------
    parameters : string[]
        ordered list of parameters in the atom
    db : DT_Database
        databases referenced in the rule of which this atom is a part of
    variables : string[]
        list of variables in the atom
    c_variables : string[]
        list of c_variables in the atom
    conditions : string[]
        list of conditions in the atom
    table : DT_Table
        the table referenced by this atom

    Methods
    -------
    addConstants(conn, variableMapping, cVarMappingReverse)
        Add constants in place of variables referenced in this atom on database pointed by psycopg2 connection "conn". Conversion to sql and execution of sql occurs here
    strAtomWithoutConditions()
        returns the atom string without any conditions
    replaceCondition(new_condition)
        replaces the condition of the atom with the new_condition
    """
    
    def __init__(self, atom_str, database=None, operators=[]):
        relation = None
        condition = ""
        if ')[' in atom_str: # contains conditions for atom, e.g., R(a1, xd, p)[a1 = 1]
            items = atom_str.strip().split(')[')
            relation = items[0] + ')'
            if items[1][-1] == ']':
                condition = items[1][:-1] # condition = 'a1 = 1'
            else:
                condition = items[1]
        else: # without conditions for atom, e.g., R(a1, xd, p)
            relation = atom_str.strip()
        split_str = relation.split("(")
        self.db = database
        self.variables = []
        
        self.condition = ConditionTree(list(condition))

        self.parameters =  []

        self.parameters = parsing_utils.getAtomParameters(split_str[1])

        tableName = split_str[0].strip()
        self.table = self.db.getTable(tableName)
        if self.table == None:
            print("Table {} not found. Exiting".format(tableName)) #TODO: Log it
            exit()
        self._isCTable = self.table.isCTable

        self.c_variables = [] # this shouldnt be the case. It should be computed for each atom (e.g. any non-digit that is in self.table.cvars)
        for param in self.parameters:
            if type(param) == list: #todo: we loop over list
                continue
            if param in self.table.cvars: 
                self.c_variables.append(param)
        self.variables = parsing_utils.getAtomVariables(self.parameters, self.c_variables, operators)
        
    def __str__(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.table.name+"("+",".join(parameter_strs)+")"
        if not self.condition.isEmpty:
            atom_str += "[{}]".format(str(self.condition))
        return atom_str

    # duplicates the current table but changes the name
    def getChangedName(self, newName):
        newAtom = deepcopy(self)
        newAtom.table = newAtom.table.duplicateWithNewName(newName)
        return newAtom


    # variableMapping is a dictionary with variables as keys and their mapping to distinct constants as value
    # cVarMappingReverse is a dictionary with c_variables as keys and their mapping to negative integers/defined IPs as value
    def addConstants(self, conn, variableMapping, cVarMappingReverse):
        variableConstants = []
        for i, var in enumerate(self.parameters):
            if type(var) == list:
                mapping_constants = []
                for v in var:
                    if v in cVarMappingReverse: # it is a c-variable
                        mapping_constants.append(cVarMappingReverse[v])
                    else:
                        mapping_constants.append(str(variableMapping[v]))
                variableConstants.append("'{" + ", ".join( mapping_constants) + "}'")
                continue
            if len(var.split('.')) == 4: # it is IP constant
                variableConstants.append("'{}'".format(var))
                continue
            elif var[0].isdigit(): #TODO: Can ip in the if before this be merged with this one? Also, why if and not elif?
                variableConstants.append(str(var))
                continue
            elif var in cVarMappingReverse: # it is a cvariable
                variableConstants.append("{}".format(cVarMappingReverse[var]))
                continue
            # if self.db["column_types"][i] == "integer":
            #     variableConstants.append(str(mapping[var]))
            if "[]" in self.table.getColmType(i): # TODO: Add documentation that this only supports single dimensional array
                variableConstants.append("'{" + str(variableMapping[var]).replace("'","") + "}'")
            elif "int" in self.table.getColmType(i):
                variableConstants.append(str(variableMapping[var]))
            elif len(variableMapping[var].split('.')) == 4:
                variableConstants.append("'{}'".format(variableMapping[var]))
            else:
                variableConstants.append(str(variableMapping[var]))

        # if self.c_variables:
        if self._isCTable:
            if self.condition.isEmpty:
                variableConstants.append("'{}'") 
            else:
                variableConstants.append("'{" + '"{}"'.format(str(self.condition).replace("'","")) + "}'") 
            # variableConstants.append("'{}'") 

        sql = "insert into " + self.table.name + " values(" +  ",".join(variableConstants) + ") ON CONFLICT DO NOTHING"
        cursor = conn.cursor()
        cursor.execute(sql)
        conn.commit()

    def replaceCondition(self, new_condition):
        self.conditions = new_condition

    # return the column names as an array of where the variable appears. i.e. if table F has columns (c1,c2,c3,c4) and has value (a,200,a,c4[800,a]) then this atom.getVarColmNames("a") will return [F.c1,F.c3,F.c4[2]]. Thus array is also returned
    def getVarColmNames(self, var, tableReference):
        i = 0
        varColms = []
        for param in self.parameters:
            colmName = self.table.getColmName(i)
            reference = "{}.{}".format(tableReference, colmName)
            if type(param) == list:
                index = 1 # postgres indexing starts from 1
                for symbol in param:
                    if symbol == var:
                        varColms.append("{}[{}]".format(reference, index))
                    index += 1
            elif param == var:
                varColms.append(reference)
            i += 1
        return varColms
    
    def sqlConstraints(self, varListMapping, tableReference):
        i = 0
        constraints = []
        for param in self.parameters:
            colmName = self.table.getColmName(i)
            reference = "{}.{}".format(tableReference, colmName)
            if type(param) == list:
                index = 1 # postgres indexing starts from 1
                for symbol in param:
                    if symbol[0].isdigit():
                        constraints.append("{}[{}] == {}".format(reference, index, symbol))
                    index += 1
            elif param[0].isdigit():
                constraints.append("{} == {}".format(reference, param))
            i += 1


        if not self.condition.isEmpty:
            constraints.append(self.condition.toString(mode="Replace String", replacementDict=varListMapping))
        return constraints


if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
