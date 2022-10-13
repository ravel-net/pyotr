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
    
    def __init__(self, atom_str, databaseTypes={}, operators=[], c_variables=[], c_tables=[]):
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
        self.db = {}
        self.variables = []
        self.c_variables = c_variables
        self._isCTable = False

        self.constraints = [] # conditions for c-variables
        if condition is not None: # conditions for c-variables
            for c in condition.split(","):
                processed_c = self.datalog_condition2z3_condition(c)
                self.constraints.append(processed_c)

        self.parameters =  []
        parameter_str = split_str[1].strip() # parameter_str = 'a1, xd, p'
        if parameter_str[-1] == ')':
            parameter_str = parameter_str[:-1] 
        # if '[' in parameter_str: # there is an array in parameters, e.g., R(a1, xd, [a1, e1]), then parameter_str = 'a1, xd, [a1, e1]'
        #     items = parameter_str.split('[')
        in_sqr_parenth = False
        vars_in_sqr_parenth = []
        for var in parameter_str.split(','):
            if '[' in var and ']' in var: # special case, parameter_str = 'a1, xd, [a1]'
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

        self.db["name"] = split_str[0].strip()
        if self.db["name"] in c_tables:
            self._isCTable = True
        self.db["column_names"] = []
        self.db["column_types"] = []
        for i, var in enumerate(self.parameters):
            self.db["column_names"].append("c"+str(i))
            if self.db["name"] in databaseTypes:
                self.db["column_types"].append(databaseTypes[self.db["name"]][i])
            else:
                self.db["column_types"].append("integer")

            if type(var) == list:
                for v in var:
                    if not v[0].isdigit() and v not in self.variables and v not in c_variables:
                        self.variables.append(v)
            else:
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

        # # cleaning up parameters so that integers are represented as integers and variables/c-vars as text
        # cleaned_params = []
        # for param in self.parameters:
        #     if type(param) == list:
        #         newSubParam = []
        #         for subparam in param:
        #             if subparam.isdigit():
        #                 newSubParam.append(int(subparam))
        #             else:
        #                 newSubParam.append(subparam)
        #         cleaned_params.append(newSubParam)
        #     else:
        #         if param.isdigit():
        #             cleaned_params.append(int(param))
        #         else:
        #             cleaned_params.append(param)
        # self.parameters = cleaned_params

        # column for condition attribute
        if self._isCTable:
            self.db["column_names"].append("condition")
            self.db["column_types"].append("text[]")
        
    def __str__(self):
        parameter_strs = []
        for p in self.parameters:
            if type(p) == list:
                parameter_strs.append("[{}]".format(", ".join(p)))
            else:
                parameter_strs.append(p)
        atom_str = self.db["name"]+"("+",".join(parameter_strs)+")"
        if self.constraints:
            atom_str += "[{}]".format(", ".join(self.constraints))
        return atom_str


    def addConstants(self, conn, mapping):
        variableConstants = []
        for i, var in enumerate(self.parameters):
            if type(var) == list:
                mapping_constants = []
                for v in var:
                    if self.db["column_types"][i] == "int4_faure[]":
                        mapping_constants.append('"' + str(mapping[v]) + '"')
                    else:
                        mapping_constants.append(str(mapping[v]))
                variableConstants.append("'{" + ", ".join( mapping_constants) + "}'")
                continue
            if var[0].isdigit():
                variableConstants.append(str(var))
                continue
            if var in self.c_variables:
                variableConstants.append("'{}'".format(var))
                continue
            if self.db["column_types"][i] == "integer":
                variableConstants.append(str(mapping[var]))
            elif "[]" in self.db["column_types"][i]: # Only supports single dimensional array
                # # For supporting array[]
                # if "[" in var:
                #     if var[0] == '[': 
                #         var = var[1:]
                #     if var[-1] == ']':
                #         var = var[:-1]
                #     listing_vars = var.split(',')
                #     temp_variable_constants = []
                #     for listing_var in listing_vars:
                #         if var in self.c_variables:
                #             temp_variable_constants.append("'{}'".format(listing_var))
                #         else:
                #             temp_variable_constants.append(str(mapping[var]))
                #     variableConstants.append("ARRAY[{}]".format(", ".join(temp_variable_constants)))
                #     continue

                # For supporting ||
                variableConstants.append("'{" + str(mapping[var]) + "}'")
            elif self.db["column_types"][i] == "inet_faure":
                IPaddr = int(IPv4Address('10.0.0.1')) + mapping[var]
                variableConstants.append("'{}'".format(str(IPv4Address(IPaddr))))
            elif self.db["column_types"][i] == "int4_faure":
                variableConstants.append("'{}'".format(mapping[var]))

        # if self.c_variables:
        if self._isCTable:
            variableConstants.append("'{" + ", ".join(['"{}"'.format(c) for c in self.constraints]) + "}'") 
            # variableConstants.append("'{}'") 

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

        processed_cond = processed_cond.replace("{","(")
        processed_cond = processed_cond.replace("}",")")
        return processed_cond
        



if __name__ == "__main__":
    atom = DT_Atom("Gasd(x,y,z)")
    mapping = {"x":1, "y":2, "z":3}
    atom.addConstants("ads",mapping)
