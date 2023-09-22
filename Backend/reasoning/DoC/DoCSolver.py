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
    ########@timeit
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
        self.conditionTrees = []
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
    # Need to be careful about wildcard entries 
    # If the condition is in terms of just o_j and i_j, then converts it into o_j
    ###@timeit
    def simplifyCondition(self, index):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        None or simplified condition
        """
        # start = time.time()
        conditionParsed = self.conditionTrees[int(index)]
        leaves = conditionParsed.getLeaves()
        variableConditions, variables = self._getVariableConditions(leaves)
        # end = time.time()
        # parsing_time = end-start
        # logging.info(f'Time: simplifyCondition_parsing took {parsing_time:.6f}')

        
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
                # result = input_doc.hasContradiction()
                # if result:
                #     return None        
        
        if input_doc == None: # no changes made
            return index
        for var in DoCs:
            if "o" in var and var.split("_")[1] == input_doc.name.split("_")[1]:
                output_doc = DoCs[var]
            elif "o" in var:
                output_prev_doc = DoCs[var]

        return_string = None
        # note that when output_doc is none, we assume that there is no rewriting
        if output_prev_doc == None: # case when there are only two variables (e.g. condition directly from the forwarding table)
            if output_doc == None: # no rewriting
                input_doc.name = input_doc.name.replace("i","o")
                if input_doc.hasContradiction():
                    return None
                return_string = str(input_doc)
            else:
                if input_doc.hasContradiction():
                    return None
                rewritingTBV = output_doc.mergeWildcards(input_doc) # merges wildcard of input and output and makes sure that there are no contradictions. Done in place
                output_doc.removeContradictions(rewritingTBV) # this is done in place
                return_string = str(output_doc)
        elif len(variables) == 3: # case when there are three variables (e.g. condition of the form: [output_prev_doc = ..., output_prev_doc = input_doc, output_doc = ... / output_doc = input_doc, input_doc = ...])
            and_doc = input_doc.intersect(output_prev_doc)
            if and_doc.hasContradiction():
                return None
            if output_doc == None: # no rewriting
                and_doc.name = and_doc.name.replace("i","o")
                return_string = str(and_doc)
            else:
                rewritingTBV = output_doc.mergeWildcards(and_doc)
                output_doc.removeContradictions(rewritingTBV) # this is done in place
                return_string = str(output_doc)
        if return_string == None:
            return None
        else:
            return self.str_to_BDD(return_string)
    
    @timeit
    def process_condition_on_ctable(self, conn, tablename):
        cursor = conn.cursor()
        cursor.execute("ALTER TABLE {} ADD COLUMN IF NOT EXISTS id SERIAL PRIMARY KEY;".format(tablename))
        '''
        delete contradiction
        '''
        cursor.execute("select id, condition from {}".format(tablename))
        contrad_count = cursor.rowcount
        del_tuple = []
        update_tuple = {}
        simplification_time = 0
        start = time.time()
        for i in tqdm(range(contrad_count)):
            row = cursor.fetchone()
            simplifiedCond = self.simplifyConditionInitial(row[1])
            if simplifiedCond == None:
                del_tuple.append(row[0])
            else:
                index = self.str_to_BDD(simplifiedCond)
                update_tuple[row[0]] = index
        end = time.time()
        simplification_time += (end-start)
        logging.info(f'Time: process_condition_on_ctable_simplification took {simplification_time:.4f}')
       
                
        if len(del_tuple) == 0:
            pass
        elif len(del_tuple) == 1:
            cursor.execute("delete from {} where id = {}".format(tablename, del_tuple[0]))
        else:
            cursor.execute("delete from {} where id in {}".format(tablename, tuple(del_tuple)))
                  
        #TODO: Update columns, possibly in bulk?
        for id in update_tuple:
            cursor.execute("UPDATE {} SET condition = Array['{}'] WHERE id = {}".format(tablename, update_tuple[id], id))
        cursor.execute("ALTER TABLE {} DROP COLUMN IF EXISTS id".format(tablename))
    
    ########@timeit
    def restoreStringConditions(self, conn, tablename):
        cursor = conn.cursor()
        cursor.execute("ALTER TABLE {} ADD COLUMN IF NOT EXISTS id SERIAL PRIMARY KEY;".format(tablename))
        '''
        delete contradiction
        '''
        cursor.execute("select id, condition from {}".format(tablename))
        contrad_count = cursor.rowcount
        del_tuple = []
        update_tuple = {}

        for i in tqdm(range(contrad_count)):
            row = cursor.fetchone()
            if len(row[1]) != 1:
                print("{} conditions encountered. Only 1 expected in {}.".format(str(len(row[1])), row[1]))
                exit()
            simplifiedCond = self.conditionTrees[int(row[1][0])] # todo check
            update_tuple[row[0]] = simplifiedCond
                
        if len(del_tuple) == 0:
            pass
        elif len(del_tuple) == 1:
            cursor.execute("delete from {} where id = {}".format(tablename, del_tuple[0]))
        else:
            cursor.execute("delete from {} where id in {}".format(tablename, tuple(del_tuple)))
                  
        #TODO: Update columns, possibly in bulk?
        for id in update_tuple:
            cursor.execute("UPDATE {} SET condition = Array['{}'] WHERE id = {}".format(tablename, update_tuple[id], id))
        cursor.execute("ALTER TABLE {} DROP COLUMN IF EXISTS id".format(tablename))

    ########@timeit
    # simplifies conditions with only two variables (input and output)
    # returns index of the simplified conditions
    def simplifyConditionInitial(self, conditions):
        """
        Parameters:
        -----------
        conditions: list
            A list of conditions

        Returns:
        --------
        None or modified conditions
        """
        # print(conditions)
        condition = conditions[0]
        if len(conditions) > 1:
            condition = "And("+", ".join(conditions)+")"
        
        conditionParsed = ConditionTree(list(condition))
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
                # if input_doc.hasContradiction():
                #     return None
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
                output_name = input_doc.name.replace("i","o")
                if input_doc.hasContradiction():
                    return None
                return "And(" + str(input_doc) + ", " + "{} == {})".format(output_name, input_doc.name)
            else:
                if input_doc.hasContradiction():
                    return None
                # if output_doc.hasContradiction():
                #     return None
                return "And(" + str(input_doc) + ", " + str(output_doc) + ")"
        return None
    
    ###@timeit
    def str_to_BDD(self, condition):
        newTree = ConditionTree(condition=condition)
        self.conditionTrees.append(newTree)
        return len(self.conditionTrees)-1
    
    ###@timeit
    def operate_BDDs(self, conditionTreeIndex1, conditionTreeIndex2, logicalOP):
        newCT = ConditionTree("")
        newCT.getCombinedConditionTree(self.conditionTrees[int(conditionTreeIndex1)], self.conditionTrees[int(conditionTreeIndex2)], logicalOp=logicalOP)
        self.conditionTrees.append(newCT)
        return len(self.conditionTrees)-1
    
if __name__ == '__main__':
    condition1 = "Or(And(x == 1, y == '10.0.0.1'), And(x == 2, y == '10.0.0.2'))"
    condition2 = "And(x == 1, y == '10.0.0.1')"

    z3tool = z3SMTTools(variables=['x'], domains={}, reasoning_type={'x':'Int', 'y':'BitVec'})
    z3tool.is_implication(condition1, condition2)
    z3tool.is_implication(condition2, condition1)

