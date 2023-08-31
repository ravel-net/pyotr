import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
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
from Backend.reasoning.DoC.DoC import DoC

import logging

class DoCSolver:
    """
    Implements methods over difference of cube

    Functions:
    ----------
    iscontradiction(conditions)
        Determine if 'conditions' are contradictory
    """
    @timeit
    def __init__(self, variables, mapping={}, bits = 32) -> None:
        """
        Parameters:
        -----------
        variables: list
            the list of variables
        
        mapping: dict
            {number:var}, maps integers to variables

        bits: integer
            number of bits in the DoC
        """
        self._variables = variables
        self._mapping = mapping
        self.bits = bits
        self.name = "DoCSolver"

    # takes a list of conditions as and returns the positive and negative conditions for each variable
    # Retruns dictionary variableConditions which has variableConditions[var] = {"pos":#..., "neg":[]}
    def _getVariableConditions(self, leaves):
        variableConditions = {}
        variables = []
        for leaf in leaves:
            var1 = leaf.var1
            var2 = leaf.var2
            if var1 in self._mapping:
                var1 = self._mapping[var1]
            elif str(var1) in self._mapping:
                var1 = self._mapping[str(var1)]
            if var2 in self._mapping:
                var2 = self._mapping[var2]
            elif str(var2) in self._mapping:
                var2 = self._mapping[str(var2)]
            if var1 not in variables: # assumes var1 is always a var
                variables.append(var1)
            if not parsing_utils._isConstant(var2):
                continue
            if var1 not in variableConditions:
                variableConditions[var1] = {}
            if leaf.operator == "==":
                if "pos" not in variableConditions[var1]:
                    variableConditions[var1]["pos"] = []
                variableConditions[var1]["pos"].append(var2)
            elif leaf.operator == "!=":
                if "neg" not in variableConditions[var1]:
                    variableConditions[var1]["neg"] = []
                variableConditions[var1]["neg"].append(var2)
        return variableConditions, variables

    # Given a condition with three variables: o_j, i_k, and o_k, returns None if it is a contradiction
    # Returns a simplified version in terms of o_j if it's not a contradiction
    # Need to be careful about wildcard entries and 
    @timeit
    def simplifyCondition(self, conditions):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        True or False
        """
        # print(conditions)
        start = time.time()
        condition = conditions[0]
        if len(conditions) > 1:
            condition = "And("+", ".join(conditions)+")"
        
        start = time.time()
        conditionParsed = ConditionTree(condition)
        end = time.time()
        total_time = end-start
        logging.info(f'Time: simplifyCondition_parsing took {total_time:.4f}')
        leaves = conditionParsed.getLeaves()
        variableConditions, variables = self._getVariableConditions(leaves)
        DoCs = {}
        input_doc = None
        output_doc = None
        output_prev_doc = None
        for var in variableConditions:
            if "neg" in variableConditions[var]:
                DoCs[var] = DoC(name=var, posStrings=variableConditions[var]["pos"], negStrings=variableConditions[var]["neg"], bits=self.bits)
            else:
                DoCs[var] = DoC(name=var, posStrings=variableConditions[var]["pos"], negStrings=[], bits=self.bits)
            if "i" in var:
                input_doc = DoCs[var]
                if input_doc.hasContradiction():
                    return None
        if input_doc == None: # no changes made
            return condition
        for var in DoCs:
            if "o" in var and var.split("_")[1] == input_doc.name.split("_")[1]:
                output_doc = DoCs[var]
            elif "o" in var:
                output_prev_doc = DoCs[var]

        # note that when output_doc is none, we assume that there is no rewriting
        if output_prev_doc == None: # case when there are only two variables (e.g. condition directly from the forwarding table)
            if output_doc == None: # no rewriting
                input_doc.name = input_doc.name.replace("i","o")
                if input_doc.hasContradiction():
                    return None
                return str(input_doc)
            else:
                output_doc.mergeWildcards(input_doc) # merges wildcard of input and output and makes sure that there are no contradictions. Done in place
                output_doc.removeContradictions() # this is done in place
                return str(output_doc)
        elif len(variables) == 3: # case when there are three variables (e.g. condition of the form: [output_prev_doc = ..., output_prev_doc = input_doc, output_doc = ... / output_doc = input_doc, input_doc = ...])
            and_doc = input_doc.intersect(output_prev_doc)
            if and_doc.hasContradiction():
                return None
            if output_doc == None: # no rewriting
                and_doc.name = and_doc.name.replace("i","o")
                return str(and_doc)
            else:
                output_doc.mergeWildcards(and_doc)
                output_doc.removeContradictions() # this is done in place
                return str(output_doc)
        return None
    
    
if __name__ == '__main__':
    condition1 = "Or(And(x == 1, y == '10.0.0.1'), And(x == 2, y == '10.0.0.2'))"
    condition2 = "And(x == 1, y == '10.0.0.1')"

    z3tool = z3SMTTools(variables=['x'], domains={}, reasoning_type={'x':'Int', 'y':'BitVec'})
    z3tool.is_implication(condition1, condition2)
    z3tool.is_implication(condition2, condition1)

