from ast import operator
import z3
from z3 import * 
from ipaddress import IPv4Network
import re

class z3SMTTools:
    def __init__(self, variables, domains={}, reasoning_type='Int') -> None:
        self._variables = variables
        self._domains = domains # {variable: []}
        self._reasoning_type = reasoning_type
        self.solver = z3.Solver()

        domain_str = self._get_domain_str()
        if len((domain_str)) != 0:
            self.solver.add(eval(domain_str))


    def iscontradiction(self, conditions):
        self.solver.push()

        if len(conditions) == 0:
            return 

        for c in conditions:
            prcd_cond = self.condition_parser(c)
            self.solver.add(eval(prcd_cond))

        result = self.solver.check()

        if result == z3.unsat:
            self._olver.pop()
            return True
        else:
            self.solver.pop()
            return False
    
    def istauto(self, conditions):
        if len(conditions) == 0:
            return True
        for c in conditions:
            prcd_cond = self.condition_parser(c)
            self.solver.push()
            self.solver.add(eval("Not({prcd_cond})".format(prcd_cond)))
            re = self.solver.check()
            self.solver.pop()

            if str(re) == 'sat':
                pass
            else:
                return False
        return True
    
    def has_redundancy(self, conditions):
        has_redundant = False
        is_tauto = True
        result = conditions[:]
        
        drop_idx = {}
        dp_arr = []
        for i in range(len(conditions)):
            drop_idx[i] = []
        
        if len(conditions) == 0:
            return has_redundant, result
        
        processed_conditions = {}
        if len(conditions) == 1:
            expr = self.condition_parser(conditions[0])

            # check tautology
            c = "Not({})".format(expr)
            self.solver.push()
            self.solver.add(eval(c))
            if self.solver.check() == z3.sat:
                is_tauto = False
            self.solver.pop()

            if is_tauto:
                return is_tauto, '{}'
            else:
                return has_redundant, result
        else:        
            for idx1 in range(len(conditions) - 1):
                expr1 = ""
                if idx1 not in processed_conditions.keys():
                    expr1 = self.condition_parser(conditions[idx1])
                    processed_conditions[idx1] = expr1
                else:
                    expr1 = processed_conditions[idx1]

                for idx2 in range(idx1+1,len(conditions)):
                    expr2 = ""
                    if idx2 not in processed_conditions.keys():
                        expr2 = self.condition_parser(conditions[idx2])
                        processed_conditions[idx2] = expr2  
                    else:
                        expr2 = processed_conditions[idx2]
                    
                    G = Implies(eval(expr1), eval(expr2))
                    self.solver.push()
                    self.solver.add(Not(G))
                    re = str(self.solver.check())
                    self.solver.pop()
                    if str(re) == 'unsat':
                        drop_idx[idx1].append(idx2)
                        if not has_redundant:
                            has_redundant = True

                    G = Implies(eval(expr2), eval(expr1))
                    self.solver.push()
                    self.solver.add(Not(G))
                    re = str(self.solver.check())
                    self.solver.pop()
                    if str(re) == 'unsat':
                        drop_idx[idx2].append(idx1)
                        if not has_redundant:
                            has_redundant = True

        if has_redundant:
            drop_result = {}
            for i in range(len(conditions)):
                drop_result[i] = []

            for c1 in list(drop_idx):
                for c2 in drop_idx[c1]:
                    if c2 == c1:
                        continue
                    drop_idx[c1]+=(drop_idx[c2])
                    drop_idx[c1] = list(set(drop_idx[c1]))
                    drop_idx[c2] = []
                    if c1 in drop_idx[c1]:
                        drop_idx[c1].remove(c1)

            for c1 in list(drop_idx):
                for c2 in drop_idx[c1]:        
                    dp_arr.append(c2)

            is_tauto = True
            final_result = []
            subset_prcd_conditions = []
            for i in range(0, len(result), 1):
                if i not in dp_arr:
                    final_result.append(result[i])
                    subset_prcd_conditions.append(processed_conditions[i])

            c = "Not(And({}))".format(", ".join(subset_prcd_conditions))

            self.solver.push()
            self.solver.add(eval(c))
            if self.solver.check() == z3.sat:
                is_tauto = False
            self.solver.pop()
            
            # result = [result[i] for i in range(0, len(result), 1) if i not in dp_arr]
            if is_tauto:
                return is_tauto, '{}'
            return has_redundant, final_result

        else:
            return has_redundant, result

    def condition_parser(self, condition):
        if condition is None or len(condition) == 0:
            return "True"
        cond_str = condition
        prcd_cond = ""
        if 'And' in cond_str or 'Or' in cond_str:
            stack_last_post = []
            i = 0
            stack_last_post.insert(0, i)
            condition_positions = []
            in_square_parenthese = False
            while i < len(cond_str):
                if cond_str[i] == '[':
                    in_square_parenthese = True
                elif cond_str[i] == ']':
                    in_square_parenthese = False
                elif cond_str[i] == '(':
                    if len(stack_last_post) != 0:
                        stack_last_post.pop()
                    stack_last_post.insert(0, i+1)
                elif cond_str[i] == ')' or cond_str[i] == ',':
                    if cond_str[i] == ',' and in_square_parenthese:
                        continue
                    begin_idx = stack_last_post.pop()
                    if i != begin_idx:
                        condition_positions.append((begin_idx, i))
                    stack_last_post.insert(0, i+1)      
                i += 1
                
            if len(stack_last_post) != 0:
                begin_idx = stack_last_post.pop()
                if begin_idx !=  len(cond_str):
                    condition_positions.append((begin_idx, len(cond_str)))
            # print(cond_str[51:])
            # print(stack_last_post)
            # print(condition_positions)
            for idx, pair in enumerate(condition_positions):
                if idx == 0:
                    prcd_cond += cond_str[0:pair[0]]
                else:
                    prcd_cond += cond_str[condition_positions[idx-1][1]:pair[0]]
                
                c = cond_str[pair[0]: pair[1]].strip()
                prcd_cond += self._convert_z3_variable(c, self._reasoning_type)
                # for num in range(len(op1)):# TODO: assert that length of op1, operator and op2 is the same
                #     prcd_cond += "{} {} {}".format(op1[num], operator[num], op2[num])
                #     if num < len(op1)-1:
                #         prcd_cond += ","
            prcd_cond += cond_str[condition_positions[-1][1]:]
            # print(prcd_cond)
        else:
            prcd_cond += self._convert_z3_variable(condition, self._reasoning_type)
            # for num in range(len(op1)):# TODO: assert that length of op1, operator and op2 is the same
            #     prcd_cond += "{} {} {}".format(op1[num], operator[num], op2[num])
            #     if num < len(op1)-1:
            #         prcd_cond += ","
        return prcd_cond
    
    def _get_domain_str(self):
        domain_conditions = []
        if self._reasoning_type == 'Int':
            
            for var in self._domains:
                var_conditions = []
                for val in self._domains[var]:
                    var_conditions.append("z3.{sort}('{var}') == z3.{sort}Val({val})".format(sort=self._reasoning_type, var=var, val=val))
                domain_conditions.append("Or({})".format(", ".join(var_conditions)))
        else:
            for var in self._domains:
                var_conditions = []
                for val in self._domains[var]:

                    net = IPv4Network(val)
                    # if net[0] != net[-1]: # subnet
                        

        domain_str = ", ".join(domain_conditions)
        return domain_str
    
    def _convert_z3_variable(self, condition, datatype):
        if datatype == "BitVec":
            return self.convert_z3_variable_bit(condition, datatype, 32)

        # TODO: BitVec datatype of value in array
        if "\\not_in" in condition or "\\in" in condition:
            return self._convert_array_condition2z3_variable(condition)

        c_list = condition.split()
        operator = c_list[1]

        if c_list[0][0].isalpha():
            op1 = f"z3.{datatype}('{c_list[0]}')"
        else: 
            op1 = f"z3.{datatype}Val('{c_list[0]}')"

        if c_list[2][0].isalpha():
            op2 = f"z3.{datatype}('{c_list[2]}')"
        else:
            op2 = f"z3.{datatype}Val('{c_list[2]}')"
        
        return "{} {} {}".format(op1, operator, op2)

    def _convert_array_condition2z3_variable(self, condition):
        # array must be at right operand
        c_list = condition.split()
        operator = c_list[1]

        if c_list[0][0].isalpha():
            op1 = "z3.{}('{}')".format(self._reasoning_type, c_list[0])
        else: 
            op1 = "z3.{}Val('{}')".format(self._reasoning_type, c_list[0])

        array_condition = "EmptySet({}Sort()".format(self._reasoning_type)
        array_items_str = re.findall(r'\[(.*?)\]', c_list[2])
        for item in array_items_str.split(','):
            item = item.strip()

            if item.isalpha():
                array_condition = "SetAdd({}, {}('{}'))".format(array_condition, self._reasoning_type, item)
            else:
                array_condition = "SetAdd({}, {}Val('{}'))".format(array_condition, self._reasoning_type, item)
        if operator == '\\not_in':
            return "isMember({}, {})".format(op1, array_condition)
        else:
            return "Not(isMember({}, {}))".format(op1, array_condition)

    def _convertIPToBits(self, IP, bits):
        IP_stripped = IP.split(".")
        bitValue = 0
        i = bits-8
        for rangeVals in IP_stripped:
            bitValue += (int(rangeVals) << i)
            i -= 8 
        return (bitValue)

    # Breaks IP into a range if it is subnetted. sep is a separator. For z3, it must be empty. For sql, it must be a single quotation mark
    def _getRange(self, var, op, IP, sep): 
        net = IPv4Network(IP)
        if (net[0] != net[-1]): # subnet
            if op == "==" or op == "=":
                return [var + " >= " + sep + str(net[0]) + sep, var + " <= " + sep + str(net[-1]) + sep]
            elif op == "!=":
                return [var + " <= " + sep + str(net[0]) + sep, var + " >= " + sep + str(net[-1]) + sep]
            else:
                print("Error, illegal operation", op)
                exit()
        else:
            return ["{} {} {}{}{}".format(var,op,sep,IP,sep)]

    def _convert_z3_variable_bit(self, condition, datatype, bits):
        conditionSplit = condition.split()
        constraints = [condition]
        if not conditionSplit[2][0].isalpha():
            constraints = self._getRange(conditionSplit[0], conditionSplit[1], conditionSplit[2], "")
        elif not conditionSplit[0][0].isalpha():
            constraints = self._getRange(conditionSplit[2], conditionSplit[1], conditionSplit[0], "")
        conditionFinal = "And("
        for i, constraint in enumerate(constraints):
            c_list = constraint.split()
            if c_list[0][0].isalpha():
                op1 = f"z3.{datatype}('{c_list[0]}',{bits})"
            else: 
                val = self._convertIPToBits(c_list[0], 32)
                op1 = f"z3.{datatype}Val('{val}',{bits})"
            
            if c_list[2][0].isalpha():
                op2 = f"z3.{datatype}('{c_list[2]}',{bits})"
            else:
                val = self._convertIPToBits(c_list[2], 32)
                op2 = f"z3.{datatype}Val('{val}',{bits})"
            operator = c_list[1]
            conditionFinal += "{} {} {}".format(op1, operator, op2)
            if i < len(constraints)-1:
                conditionFinal += ","
        conditionFinal += ')'
        return conditionFinal


