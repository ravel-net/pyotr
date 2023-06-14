from copy import copy
import re
from ipaddress import IPv4Address
import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
from utils import parsing_utils


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
        condition = None
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
        self.c_variables = self.db.c_variables

        self.conditions = [] # conditions for c-variables
        if condition is not None: # conditions for c-variables
            processed_c = parsing_utils.datalog_condition2z3_condition(condition)
            self.conditions.append(processed_c)

        self.parameters =  []

        self.parameters = parsing_utils.getAtomParameters(split_str[1])

        tableName = split_str[0].strip()
        self.table = self.db.getTable(tableName)
        if self.table == None:
            print("Table {} not found. Exiting".format(tableName)) #TODO: Log it
            exit()
        self._isCTable = self.table.isCTable

        self.variables = parsing_utils.getAtomVariables(self.parameters, self.c_variables, operators)
        
    def __str__(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.table.name+"("+",".join(parameter_strs)+")"
        if self.conditions:
            atom_str += "[{}]".format(", ".join(self.conditions))
        return atom_str

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
            variableConstants.append("'{" + ", ".join(['"{}"'.format(c.replace("'","")) for c in self.conditions]) + "}'") 
            # variableConstants.append("'{}'") 

        sql = "insert into " + self.table.name + " values(" +  ",".join(variableConstants) + ")"
        cursor = conn.cursor()
        cursor.execute(sql)
        conn.commit()

    def strAtomWithoutConditions(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.table.name+"("+",".join(parameter_strs)+")"
        return atom_str

    def replaceCondition(self, new_condition):
        self.conditions = new_condition

if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
