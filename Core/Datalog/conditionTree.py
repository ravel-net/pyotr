import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
from utils.logging import timeit
from utils import parsing_utils
from copy import deepcopy
from Core.Datalog.database import DT_Database
from Core.Datalog.table import DT_Table

class ConditionLeaf:
    """
    A class used to represent a single condition of the form 'var1 op var2'
    """
    # Leafs are conditions of the form var1 op var2
    @timeit
    def __init__(self, condition, pos):
        self.endPos = parsing_utils.findCondEnd(condition, pos)
        self.operator = parsing_utils.findOperator(condition, pos, self.endPos)
        currCond = deepcopy(condition[pos:self.endPos])
        conditionSplit = currCond.split(self.operator)
        self.var1 = conditionSplit[0].strip()
        self.var2 = conditionSplit[1].strip()
        if self.endPos < len(condition) and condition[self.endPos] == ",":
            self.endPos += 1
    
    # @property
    def getLeafEndPos(self):
        return self.endPos
    
    def __str__(self):
        return self.var1 + " " + self.operator + " " + self.var2

    def replacedString(self, replacementDict):
        newVar1 = self.var1
        newVar2 = self.var2
        if self.var1 in replacementDict:
            newVar1 = replacementDict[self.var1]
        if self.var2 in replacementDict:
            newVar2 = replacementDict[self.var2]
        return newVar1 + " " + self.operator + " " + newVar2
    
    def sqlString(self, atomTables):
        newOp = self.operator
        newVar1 = self.var1
        newVar2 = self.var2        
        if self.operator == "==":
            newOp = "="

        if not self.var1[0].isdigit():
            var1_table = self.var1.split(".")[0]
            var1_colm = self.var1.split(".")[1]
            var1_type = atomTables[var1_table].columns[var1_colm]
            if "[]" in var1_type and self.operator == "!=":
                newVar1 = "All(" + self.var1 + ")"
            elif "[]" in var1_type:
                newVar1 = "Any(" + self.var1 + ")"
        if not self.var2[0].isdigit():
            var2_table = self.var2.split(".")[0]
            var2_colm = self.var2.split(".")[1]
            var2_type = atomTables[var2_table].columns[var2_colm]
            if "[]" in var2_type and self.operator == "!=":
                newVar2 = "All(" + self.var2 + ")"
            elif "[]" in var2_type:
                newVar2 = "Any(" + self.var2 + ")"

        return newVar1 + " " + newOp + " " + newVar2
    
    def arrayIntegrationString(self, atomTables):
        newOp = self.operator
        newVar1 = self.var1
        newVar2 = self.var2        
        if self.operator == "=":
            newOp = "=="
        if not self.var1[0].isdigit():
            var1_table = self.var1.split(".")[0]
            var1_colm = self.var1.split(".")[1]
            var1_type = atomTables[var1_table].columns[var1_colm]
            if "[]" in var1_type:
                newVar1 = self.var1 + "::text"
        if not self.var2[0].isdigit():
            var2_table = self.var2.split(".")[0]
            var2_colm = self.var2.split(".")[1]
            var2_type = atomTables[var2_table].columns[var2_colm]
            if "[]" in var2_type:
                newVar2 = self.var2 + "::text"
        return newVar1 + " " + newOp + " " + newVar2

    def negativeIntString(self, atomTables):
        conditions = []
        conditions.append(str(self)) # first condition is the default one
        if not self.var1[0].isdigit():
            var1_table = self.var1.split(".")[0]
            var1_colm = self.var1.split(".")[1]
            var1_type = atomTables[var1_table].columns[var1_colm]
            if "faure" in var1_type: # c-table
                newCondition = parsing_utils.negativeIntCondition(self.var1, var1_type)
                conditions.append(newCondition)
        if not self.var2[0].isdigit():
            var2_table = self.var2.split(".")[0]
            var2_colm = self.var2.split(".")[1]
            var2_type = atomTables[var2_table].columns[var2_colm]
            if "faure" in var2_type: # c-table
                newCondition = parsing_utils.negativeIntCondition(self.var2, var2_type)
                conditions.append(newCondition)
        return "Or(" + ", ".join(conditions) + ")"

# make sure to check if the conditionTree isTrue or not. If it is, then it is trivially true and can be skipped altogether
# ConditionTree is either a single condition or a logical operator with conditionTrees as children
class ConditionTree:
    """
    A class used to represent a condition using a tree. Each node is either a logical operator or a leaf node (that represents a single condition)
    """
    @timeit
    def __init__(self, condition, pos = 0):
        self.condition_string = condition
        self.children = []
        self.isLeaf = False
        self.isEmpty = False
        
        # skip over spaces:
        while pos < len(condition) and (condition[pos] == " " or condition[pos] == ","):
            pos += 1
        
        isLogicalOP = True
        if len(condition) == 0:
            self.isEmpty = True
            isLogicalOP = False
        elif len(condition)-pos < 4: # must be a leaf
            self.value = ConditionLeaf(condition, pos)
            self.endPos = self.value.getLeafEndPos()
            self.isLeaf = True
            isLogicalOP = False
        elif condition[pos:pos+2] == "Or":
            while pos < len(condition) and condition[pos] != "(":
                pos += 1
            pos += 1
            self.value = "Or"
        elif condition[pos:pos+3] == "And":
            while pos < len(condition) and condition[pos] != "(":
                pos += 1
            pos += 1
            self.value = "And"
        else: # must be a leaf
            self.value = ConditionLeaf(condition, pos)
            self.endPos = self.value.getLeafEndPos()
            self.isLeaf = True
            isLogicalOP = False

        # skip over spaces:
        while pos < len(condition) and condition[pos] == " ":
            pos += 1

        # The bottom part only run if it's a logical operator
        if isLogicalOP:
            while pos < len(condition) and condition[pos] != ")":
                child = ConditionTree(condition, pos)
                # if not child.getIsTrue(): # when the condition is trivially true. #TODO: Also think about doing something when the condition is trivially False.
                self.children.append(child)
                pos = child.getEndPos()
                while pos < len(condition) and condition[pos] == " ":
                    pos += 1
                        # skip over spaces:
                # else:
                    # del child

            pos += 1 # skipping over last bracket
            self.endPos = pos

    # @property
    def getEndPos(self):
        return self.endPos
    
    def __str__(self):
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return str(self.value)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(str(child))
            if len(childrenStr) > 0:
                return self.value + "(" + ", ".join(childrenStr) + ")" 
            else:
                return ""
    
    # returns another condition tree but this time with added constraints for negative integers
    def getNegativeIntegerTree(self, atomTables):
        negativeIntString = self.negativeIntString(atomTables)
        return ConditionTree(negativeIntString)

    # returns current condition string but this time with added constraints for negative integers
    def negativeIntString(self, atomTables):
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return self.value.negativeIntString(atomTables)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(child.negativeIntString(atomTables))
            if len(childrenStr) > 0:
                return self.value + "(" + ", ".join(childrenStr) + ")" 
            else:
                return ""   

    # prints the condition but with variables replaced from replacementDictionary
    def replacedString(self, replacementDict):
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return self.value.replacedString(replacementDict)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(child.replacedString(replacementDict))
            if len(childrenStr) > 0:
                return self.value + "(" + ", ".join(childrenStr) + ")" 
            else:
                return ""     

    # returns current condition string but this time in array integration format (::text with array variables and == instead of =)
    def arrayIntegrationString(self, atomTables):
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return self.value.arrayIntegrationString(atomTables)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(child.arrayIntegrationString(atomTables))
            if len(childrenStr) > 0:
                return self.value + "(" + ", ".join(childrenStr) + ")" 
            else:
                return ""

    # prints an sql version of the conditionTree
    def sqlString(self, atomTables):
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return self.value.sqlString(atomTables)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(child.sqlString(atomTables))
            # return "(" + " {} ".format(self.value).join(childrenStr) + ")"
            if len(childrenStr) > 0:
                return "(" + " {} ".format(self.value).join(childrenStr) + ")"   
            else:
                return ""

if __name__ == '__main__':
    condition1 = "Or(  And  ( x == 1, y ==          '10.0.0.1'), And(  x==     2   , y ==    '10.0.0.2' )    )"
    condition1 = ""
    # condition1 = "x == 1"
    # condition1 = "And( x ==1   , y    == '10.0.0.1'   )"
    # condition2 = "And( x == 1, y == '10.0.0.1')"

    cond1Obj = ConditionTree(condition1, 0)
    print(cond1Obj)