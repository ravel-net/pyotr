from copy import copy
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

        self.constraints = [] # conditions for c-variables
        if condition is not None: # conditions for c-variables
            processed_c = self.datalog_condition2z3_condition(condition)
            self.constraints.append(processed_c)

        self.parameters =  []
        #TODO: Move to parsing utils
        parameter_str = split_str[1].strip() # parameter_str = 'a1, xd, p'
        if parameter_str[-1] == ')':
            parameter_str = parameter_str[:-1] 
        # if '[' in parameter_str: # there is an array in parameters, e.g., R(a1, xd, [a1, e1]), then parameter_str = 'a1, xd, [a1, e1]'
        #     items = parameter_str.split('[')
        in_sqr_parenth = False
        vars_in_sqr_parenth = []
        for var in parameter_str.split(','):
            if '[' in var and ']' in var and '||' in var: # special case, parameter_str = 'a1, xd, a || [a1]'
                self.parameters.append(var.strip())
            elif '[' in var and ']' in var: # special case, parameter_str = 'a1, xd, [a1]'
                value_in_array = re.findall(r'\[(.*?)\]', var)
                self.parameters.append(copy(value_in_array))
            elif '[' in var:
                in_sqr_parenth = True
                vars_in_sqr_parenth.append(var.split('[')[1].strip())
            elif ']' in var:
                in_sqr_parenth = False
                vars_in_sqr_parenth.append(var.split(']')[0].strip())
                self.parameters.append(copy(vars_in_sqr_parenth))
                vars_in_sqr_parenth.clear()
            else:
                if in_sqr_parenth:
                    vars_in_sqr_parenth.append(var.strip())
                else:
                    self.parameters.append(var.strip())

        tableName = split_str[0].strip()
        self.table = self.db.getTable(tableName)
        if self.table == None:
            print("Table {} not found. Exiting".format(tableName)) #TODO: Log it
            exit()
        self._isCTable = self.table.isCTable

        # TODO: Move to parsing utils as getAtomVariables
        for i, var in enumerate(self.parameters):
            if type(var) == list:
                for v in var:
                    isDigit = v[0].isdigit() or (v[0] == "'" and v[1].isdigit)
                    if not isDigit and v not in self.variables and v not in c_variables: # hacky fix
                        self.variables.append(v)
            else:
                hasOperator = False
                for op in operators:
                    if (op in var):
                        hasOperator = True
                        concatinatingVars = var.split(op)
                        for concatinatingVar in concatinatingVars:
                            concatinatingVar = concatinatingVar.strip()
                            if '[' in concatinatingVar and ']' in concatinatingVar:
                                concatinatingVar = concatinatingVar.replace("[",'').replace("]",'').split(",")
                                for v in concatinatingVar:
                                    if not v[0].isdigit() and v not in self.variables and v not in c_variables:
                                        self.variables.append(v)
                            elif not concatinatingVar[0].isdigit() and concatinatingVar not in self.variables:
                                self.variables.append(concatinatingVar)
                if not hasOperator and not var[0].isdigit():
                    if var not in self.c_variables and var not in self.variables:
                        self.variables.append(var)
        
    def __str__(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.table.name+"("+",".join(parameter_strs)+")"
        if self.constraints:
            atom_str += "[{}]".format(", ".join(self.constraints))
        return atom_str

    def strAtomWithoutConditions(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.table.name+"("+",".join(parameter_strs)+")"
        return atom_str

    def replaceCondition(self, condition):
        self.constraints = condition

    def addConstants(self, conn, mapping, cVarMappingReverse):
        variableConstants = []
        for i, var in enumerate(self.parameters):
            if type(var) == list:
                mapping_constants = []
                for v in var:
                    if v in cVarMappingReverse: # it is a c-variable
                        mapping_constants.append(cVarMappingReverse[v])
                    else:
                        mapping_constants.append(str(mapping[v]))
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
                variableConstants.append("'{" + str(mapping[var]).replace("'","") + "}'")
            elif "int" in self.table.getColmType(i):
                variableConstants.append(str(mapping[var]))
            elif len(mapping[var].split('.')) == 4:
                variableConstants.append("'{}'".format(mapping[var]))
            else:
                variableConstants.append(str(mapping[var]))

        # if self.c_variables:
        if self._isCTable:
            variableConstants.append("'{" + ", ".join(['"{}"'.format(c.replace("'","")) for c in self.constraints]) + "}'") 
            # variableConstants.append("'{}'") 

        sql = "insert into " + self.table.name + " values(" +  ",".join(variableConstants) + ")"
        cursor = conn.cursor()
        cursor.execute(sql)
        conn.commit()
    
    #TODO: Check if still relevant. If it is, move to parsingUtils
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
            if len(condition.split()) > 1 and condition.split()[1].strip() == '=':
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
