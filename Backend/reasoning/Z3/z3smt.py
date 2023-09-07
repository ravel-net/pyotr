import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
print(root)
sys.path.append(root)

import z3
from z3 import * 
from ipaddress import IPv4Network
import re
import time
from tqdm import tqdm
from utils.logging import timeit
from utils import parsing_utils
from Core.Datalog.conditionTree import ConditionTree
import logging

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
    """
    ########@timeit
    def __init__(self, variables, domains={}, reasoning_type={}, mapping={}, bits = 32) -> None:
        """
        Parameters:
        -----------
        variables: list
            the list of variables
        
        domains: dict
            {var:[]}, set domain for each variable

        reasoning_type: dict
            Currently only support "Int" and "BitVec"
            format: {var1: "Int", var2: "BitVec", ...}
        
        solver: z3.Solver()
            The instance of z3.Solver()
        """
        self._variables = variables
        self._domains = domains # {variable: []}
        self._reasoning_type = reasoning_type
        self._mapping = mapping
        self.solver = z3.Solver()
        self.simplication_time = {}
        self.bits = bits
        self.name = "z3"

        domain_str = self._get_domain_str()
        if len((domain_str)) != 0:
            self.solver.add(eval(domain_str))

    ########@timeit
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
        all_cond = []
        for c in conditions:
            prcd_cond = self.condition_parser(c)
            all_cond.append(prcd_cond)

        start = time.time()
        for cond in all_cond:
            self.solver.add(eval(cond))
        result = self.solver.check()
        end = time.time()
        total_time = end-start
        logging.info(f'Time: z3smt_contracheck took {total_time:.4f}')

        if result == z3.unsat:
            self.solver.pop()
            return True
        else:
            self.solver.pop()
            return False
    
    ########@timeit
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
        # print("prcd_cond", prcd_cond)
        prcd_cond = self.condition_parser(and_condition)
        self.solver.push()
        self.solver.add(eval("Not({})".format(prcd_cond)))
        re = self.solver.check()
        self.solver.pop()

        if str(re) == 'unsat':
            return True
        else:
            return False
    
    ########@timeit
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
            expr_c = self.condition_parser(c)
            
            simplified_c = eval(expr_c)  # TODO:simpliy a string condition
            result.append(c)
            simplified_conditions.append(simplified_c)
        
        drop_idx = {}
        for i in range(len(simplified_conditions)):
            drop_idx[i] = []
        
        if len(simplified_conditions) == 0:
            return has_redundant, result
        
        drops = []
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
            for idx1 in range(len(simplified_conditions)):
                # print("drops", drops)
                # print("idx1", idx1,"-----------")
                if idx1 in drops:
                    continue

                expr1 = simplified_conditions[idx1]

                for idx2 in range(len(simplified_conditions)):
                    if idx1 == idx2 or idx2 in drops:
                        continue
                    # print('idx2', idx2)
                    expr2 = simplified_conditions[idx2]
                    
                    G = Implies(expr1, expr2)
                    self.solver.push()
                    self.solver.add(Not(G))
                    re = str(self.solver.check())
                    self.solver.pop()
                    if str(re) == 'unsat': # expr1 implies expr2, that is expr1 is subset of expr2
                        drops.append(idx2)
                        if not has_redundant:
                            has_redundant = True


        final_result = []
        if has_redundant:
            temp_result = []
            for i in range(len(simplified_conditions)):
                if i not in drops:
                    final_result.append(result[i])
                    temp_result.append(simplified_conditions[i])

            is_tauto = True

            c = Not(And([cond for cond in temp_result]))

            self.solver.push()
            self.solver.add(c)
            if self.solver.check() == z3.sat:
                is_tauto = False
            self.solver.pop()
            
            if is_tauto:
                return is_tauto, '{}'
            # else:
            #     final_result = [str(cond) for cond in final_result]
            # return has_redundant, final_result

        else:
            final_result = result
        
        return has_redundant, final_result

    ########@timeit
    def condition_parser(self, condition):
        conditionTree = ConditionTree(condition).toString(mode = "Replace String", replacementDict=self._mapping)
        conditionTreeNegative = ConditionTree(conditionTree)
        if conditionTreeNegative.getIsTrue():
            return "z3.Bool('True')"
        else:
            return conditionTreeNegative.toString(mode = "Z3", reasoningType=self._reasoning_type, bits = self.bits)
    
    ########@timeit
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
            self.solver.pop()
            return False

    ########@timeit
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

    ########@timeit
    def _get_domain_str(self):
        domain_conditions = []
        
        for var in self._domains:
            if var not in self._reasoning_type.keys() or self._reasoning_type[var] == 'Int':
                var_conditions = []
                if type(self._domains[var]) == tuple: # this allows ranges
                    minVal = self._domains[var][0]
                    maxVal = self._domains[var][1]
                    var_conditions.append("And(z3.{sort}('{var}') >= z3.{sort}Val({minVal}), z3.{sort}('{var}') <= z3.{sort}Val({maxVal}))".format(sort='Int', var=var, minVal=minVal, maxVal=maxVal))
                else:
                    for val in self._domains[var]:
                        var_conditions.append("z3.{sort}('{var}') == z3.{sort}Val({val})".format(sort='Int', var=var, val=val))
                if len(var_conditions) != 0:
                    domain_conditions.append("Or({})".format(", ".join(var_conditions)))
            else:
                var_conditions = []
                for val in self._domains[var]:
                    condition = self._convert_z3_variable_bit("{} == {}".format(var, val), 'BitVec', self.bits) # TODO: Fix this. Nedd the correct version of convertz3variablebit
                    var_conditions.append(condition)
                domain_conditions.append("Or({})".format(", ".join(var_conditions)))

        domain_str = ", ".join(domain_conditions)
        return domain_str

    
if __name__ == '__main__':
    condition1 = "Or(And(x == 1, y == '10.0.0.1'), And(x == 2, y == '10.0.0.2'))"
    condition2 = "And(x == 1, y == '10.0.0.1')"

    z3tool = z3SMTTools(variables=['x'], domains={}, reasoning_type={'x':'Int', 'y':'BitVec'})
    z3tool.is_implication(condition1, condition2)
    z3tool.is_implication(condition2, condition1)

