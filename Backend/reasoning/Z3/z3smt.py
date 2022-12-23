import z3
from z3 import * 
from ipaddress import IPv4Network
import re
import time
from tqdm import tqdm
from utils.logging import timeit


class z3SMTTools:
    """
    Z3 SMT Tools. Collect all necessary function for Z3.
    It has set domain for variables at __init__

    Functions:
    ----------
    iscontradiction(conditions)
        Determine if 'conditions' is contradictory
    
    istauto(conditions)
        Determine if 'conditions' is a tautology. 
    
    has_redundancy(conditions)
        Determine if 'conditions' has redundancy and return a simplized "redundancy"
    
    condition_parser(condition):
        Parse text condition to condition with z3 datatype. E.g., And(x == 1, y == 1) to And(z3.Int('x') == z3.IntVal(1), z3.Int('y') == z3.IntVal(1))
    
    check_equivalence_for_two_string_conditions(condition1, condition2)
        Check if two conditions are equivalent
    
    _get_domain_str()
        get the domain condition with z3 datatype
    
    _convert_z3_variable(condition, datatype)
        A tool for converting text atom condition to atom condition with z3 datatype. E.g., x == 1 to z3.Int('x') == z3.IntVal(1)
    
    _convert_array_condition2z3_variable(condition)
        A tool for converting text array conditin to array condition with z3 datatype. E.g., 1 \in [1, 2] to IsMember(2,SetAdd(SetAdd(EmptySet(IntSort()), 1), 2))

    _convertIPToBits(IP, bits)
        A tool for converting IP to bit value.
    
    _getRange(var, op, IP, sep)
        A tool to get the range of bit values for an aggregate IP address
    
    _convert_z3_variable_bit(condition, datatype, bits)
        A tool to get IP data with z3 BitVec
    """
    @timeit
    def __init__(self, variables, domains={}, reasoning_type='Int') -> None:
        """
        Parameters:
        -----------
        variables: list
            the list of variables
        
        domains: dict
            {var:[]}, set domain for each variable

        reasoning_type: string
            Currently only support "Int" and "BitVec"
        
        solver: z3.Solver()
            The instance of z3.Solver()
        """
        self._variables = variables
        self._domains = domains # {variable: []}
        self._reasoning_type = reasoning_type
        self.solver = z3.Solver()
        self.simplication_time = {}

        domain_str = self._get_domain_str()
        if len((domain_str)) != 0:
            self.solver.add(eval(domain_str))

    @timeit
    def iscontradiction(self, conditions):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        True or False
        """

        if len(conditions) == 0:
            return 

        self.solver.push()
        for c in conditions:
            prcd_cond = self.condition_parser(c)
            self.solver.add(eval(prcd_cond))

        result = self.solver.check()

        if result == z3.unsat:
            self.solver.pop()
            return True
        else:
            self.solver.pop()
            return False
    
    @timeit
    def istauto(self, conditions):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        True or False
        """
        and_condition = None
        if len(conditions) == 0:
            return True
        elif len(conditions) == 1:
            and_condition = conditions[0]
        else:
            and_condition = "And({})".format(", ".join(conditions))
        # print("and_condition", and_condition)
        prcd_cond = self.condition_parser(and_condition)
        self.solver.push()
        self.solver.add(eval("Not({})".format(prcd_cond)))
        re = self.solver.check()
        self.solver.pop()

        if str(re) == 'unsat':
            return True
        else:
            return False
    
    @timeit
    def has_redundancy(self, conditions):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        has_redundant: Boolean
            If it has redundant condition
        
        result: list
            simplified 'conditions'
        """
        has_redundant = False
        is_tauto = True

        result = []
        simplified_conditions = []
        # print("redundant conditions", conditions)
        for c in conditions:
            # print("c", c)
            expr_c = self.condition_parser(c)
            if expr_c == 'True':
                expr_c = "z3.Bool('True')"
            # print("expr_c", expr_c)
            simplified_c = z3.simplify(eval(expr_c))
            result.append(str(simplified_c))
            simplified_conditions.append(simplified_c)
        
        drop_idx = {}
        dp_arr = []
        for i in range(len(simplified_conditions)):
            drop_idx[i] = []
        
        if len(simplified_conditions) == 0:
            return has_redundant, result
        
        # processed_conditions = {}
        if len(simplified_conditions) == 1:
            expr = simplified_conditions[0]
            # simplified_expr = z3.simplify(eval(expr)) # simplify condition

            # check tautology
            self.solver.push()
            self.solver.add(Not(expr))
            if self.solver.check() == z3.sat:
                is_tauto = False
            self.solver.pop()

            if is_tauto:
                return is_tauto, '{}'
            else:
                return has_redundant, expr
        else:        
            for idx1 in range(len(simplified_conditions) - 1):
                expr1 = simplified_conditions[idx1]
                # if idx1 not in processed_conditions.keys():
                #     expr1 = self.condition_parser(conditions[idx1])
                #     processed_conditions[idx1] = expr1
                # else:
                #     expr1 = processed_conditions[idx1]

                for idx2 in range(idx1+1,len(conditions)):
                    expr2 = simplified_conditions[idx2]
                    # if idx2 not in processed_conditions.keys():
                    #     expr2 = self.condition_parser(conditions[idx2])
                    #     processed_conditions[idx2] = expr2  
                    # else:
                    #     expr2 = processed_conditions[idx2]
                    
                    G = Implies(expr1, expr2)
                    self.solver.push()
                    self.solver.add(Not(G))
                    re = str(self.solver.check())
                    self.solver.pop()
                    if str(re) == 'unsat':
                        drop_idx[idx1].append(idx2)
                        if not has_redundant:
                            has_redundant = True

                    G = Implies(expr2, expr1)
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
                    final_result.append(str(result[i]))
                    subset_prcd_conditions.append(simplified_conditions[i])

            # c = "Not(And({}))".format(", ".join(subset_prcd_conditions))
            c = Not(And([cond for cond in subset_prcd_conditions]))

            self.solver.push()
            self.solver.add(c)
            if self.solver.check() == z3.sat:
                is_tauto = False
            self.solver.pop()
            
            # result = [result[i] for i in range(0, len(result), 1) if i not in dp_arr]
            if is_tauto:
                return is_tauto, '{}'
            return has_redundant, final_result

        else:
            return has_redundant, result

    @timeit
    def condition_parser(self, condition):
        """
        Parameters:
        -----------
        condition: string

        Returns:
        --------
        encoded 'condition' which adds z3 datatype

        #TODO: convert True to z3.Bool('True')
        """
        if condition is None or len(condition) == 0 or condition == 'True' or condition == True:
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
    
    @timeit
    def check_equivalence_for_two_string_conditions(self, condition1, condition2):
        # print("condition1", condition1)
        # print("condition2", condition2)

        prcd_condition1 = self.condition_parser(condition1)
        prcd_condition2 = self.condition_parser(condition2)
        # print("prcd_condition2", prcd_condition2)
        
        C1 = eval(prcd_condition1)
        C2 = eval(prcd_condition2)

        # result = prove(C1 == C2)
        self.solver.push()
        # s.add(eval("Or(z3.BitVec('d',32) >= z3.BitVecVal('167772160',32),z3.BitVec('d',32) <= z3.BitVecVal('167772161',32))"))
        self.solver.add(Not(C1 == C2))
        result = self.solver.check()
        if result == z3.unsat:
            # print("proved")
            self.solver.pop()
            return True
        else:
            # print("unproved")
            # print(self.solver.model())
            self.solver.pop()
            return False

    @timeit
    def is_implication(self, condition1, condition2):
        """
        Check if condition1 implies condition2
        """
        prcd_condition1 = self.condition_parser(condition1)
        prcd_condition2 = self.condition_parser(condition2)

        P = eval(prcd_condition1)
        Q = eval(prcd_condition2)

        self.solver.push()

        self.solver.add(Not(Or(Not(P), Q)))
        result = self.solver.check()

        if result == z3.unsat:
            # print("implies")
            self.solver.pop()
            return True
        else:
            # print("Does not imply")
            # print(self.solver.model())
            self.solver.pop()
            return False

    @timeit
    def simplify_condition(self, condition):
        """
        Simplify a single condition

        Parameters:
        -----------
        condition: string
            string condition
        
        Returns:
        --------
        simplified_condition: string
        """
        prcd_condition = self.condition_parser(condition)
        simplified_condition = str(z3.simplify(eval(prcd_condition)))

        if simplified_condition == 'True':
            return ""
        else:
            simplified_condition
        
        return simplified_condition

    @timeit
    def simplification(self, target_table, conn):
        cursor = conn.cursor()

        column_datatype_mapping = self._get_column_datatype_mapping(target_table, conn)
            
        if 'id' not in column_datatype_mapping:
            column_datatype_mapping['id'] = 'integer' # add id column
            cursor.execute("ALTER TABLE {} ADD COLUMN id SERIAL PRIMARY KEY;".format(target_table))
        conn.commit()

        '''
        delete contradiction
        '''
        contrd_begin = time.time()
        cursor.execute("select id, condition from {}".format(target_table))
        contrad_count = cursor.rowcount
        # logging.info("size of input(delete contradiction): %s" % str(count))
        del_tuple = []
        for i in tqdm(range(contrad_count)):
            row = cursor.fetchone()
            # print("check contrad")
            # if len(row[1]) == 0:
            #     print(len(row[1]))
            # else:
            #     print(len(row[1][0]))

            is_contrad = self.iscontradiction(row[1])

            if is_contrad:
                del_tuple.append(row[0])
        
        if len(del_tuple) == 0:
            pass
        elif len(del_tuple) == 1:
            cursor.execute("delete from {} where id = {}".format(target_table, del_tuple[0]))
        else:
            cursor.execute("delete from {} where id in {}".format(target_table, tuple(del_tuple)))

        contrd_end = time.time()
        self.simplication_time['contradiction'] = contrd_end - contrd_begin
        conn.commit()

        '''
        set tautology and remove redundant
        '''
        # print("remove redundant")
        redun_begin = time.time()
        cursor.execute("select id, condition from {}".format(target_table))
        redun_count = cursor.rowcount
        # logging.info("size of input(remove redundancy and tautology): %s" % str(count))
        upd_cur = conn.cursor()

        for i in tqdm(range(redun_count)):
            row = cursor.fetchone()
            # print("check redun")
            has_redun, result = self.has_redundancy(row[1])
            if has_redun:
                if result != '{}':
                    result = ['"{}"'.format(r) for r in result]
                    upd_cur.execute("UPDATE {} SET condition = '{}' WHERE id = {}".format(target_table, "{" + ", ".join(result) + "}", row[0]))
                else:
                    upd_cur.execute("UPDATE {} SET condition = '{{}}' WHERE id = {}".format(target_table, row[0]))
        redun_end = time.time()
        self.simplication_time["redundancy"] = redun_end - redun_begin
        conn.commit()

        # if self._information_on:
        for k, v in self.solver.statistics():
            if (k == "max memory"):
                print ("Solver Max Memory: %s : %s" % (k, v))

    @timeit
    def _get_domain_str(self):
        domain_conditions = []
        if self._reasoning_type == 'Int':
            
            for var in self._domains:
                var_conditions = []
                for val in self._domains[var]:
                    var_conditions.append("z3.{sort}('{var}') == z3.{sort}Val({val})".format(sort=self._reasoning_type, var=var, val=val))
                
                if len(var_conditions) != 0:
                    domain_conditions.append("Or({})".format(", ".join(var_conditions)))
        else:
            for var in self._domains:
                var_conditions = []
                for val in self._domains[var]:
                    condition = self._convert_z3_variable_bit("{} == {}".format(var, val), self._reasoning_type, 32)
                    var_conditions.append(condition)

                domain_conditions.append("Or({})".format(", ".join(var_conditions)))
                # var_z3 = "z3.{sort}('{var}', {bits})".format(sort=self._reasoning_type, var=var, bits=32)
                # lower_bound = self._convertIPToBits('0.0.0.0', 32)
                # lower_bound_z3 = "z3.{sort}Val('{lower_bound}', {bits})".format(sort=self._reasoning_type, lower_bound=lower_bound, bits=32)

                # upper_bound = self._convertIPToBits('255.255.255.255', 32)
                # upper_bound_z3 = "z3.{sort}Val('{upper_bound}', {bits})".format(sort=self._reasoning_type, upper_bound=upper_bound, bits=32)
                
                # domain_conditions.append("And({var_z3} >= {lower_bound_z3}, {var_z3} <= {upper_bound_z3})".format(var_z3=var_z3, lower_bound_z3=lower_bound_z3, upper_bound_z3=upper_bound_z3))

        domain_str = ", ".join(domain_conditions)
        return domain_str
    
    @timeit
    def _convert_z3_variable(self, condition, datatype):
        if datatype == "BitVec":
            return self._convert_z3_variable_bit(condition, datatype, 32)

        # TODO: BitVec datatype of value in array
        if "\\not_in" in condition or "\\in" in condition:
            return self._convert_array_condition2z3_variable(condition)
        # print("condition", condition)
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

    @timeit
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
        if operator == '\\in':
            return "isMember({}, {})".format(op1, array_condition)
        else:
            return "Not(isMember({}, {}))".format(op1, array_condition)

    @timeit
    def _convertIPToBits(self, IP, bits):
        IP_stripped = IP.split(".")
        bitValue = 0
        i = bits-8
        for rangeVals in IP_stripped:
            bitValue += (int(rangeVals) << i)
            i -= 8 
        return (bitValue)

    # Breaks IP into a range if it is subnetted. sep is a separator. For z3, it must be empty. For sql, it must be a single quotation mark
    @timeit
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

    @timeit
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

    @timeit
    def _get_column_datatype_mapping(self, target_table, conn):
        """
        Because the datatypes are read from database, the 'int4_faure' and 'inet_faure' are faure datatype that return 'USER-DEFINE' from database; 
        the array datatype returns 'ARRAY' from datatype. We cannot make the accurate datatype for ARRAY. #TODO: specify the accurate datatype for array
        """
        column_datatype_mapping = {}
        cursor = conn.cursor()
        cursor.execute("SELECT column_name, data_type FROM information_schema.columns WHERE table_name = '{}';".format(target_table.lower()))
        for column_name, data_type in cursor.fetchall():
            column_datatype_mapping[column_name] = data_type
            if data_type.lower() == 'user-defined':
                if self._reasoning_type.lower() == 'int':
                    column_datatype_mapping[column_name] = 'int4_faure'
                elif self._reasoning_type.lower() == 'bitvec':
                    column_datatype_mapping[column_name] = 'inet_faure'
                else:
                    print("Unsupported reasoning sort:", self._reasoning_sort)
                    exit()
            else:
                column_datatype_mapping[column_name] = data_type
        conn.commit()
        return column_datatype_mapping

if __name__ == '__main__':
    condition1 = "Or(x == 1, x == 2)"
    condition2 = "x == 1"

    z3tool = z3SMTTools(variables=['x'], domains={})
    z3tool.is_implication(condition1, condition2)
    z3tool.is_implication(condition2, condition1)

