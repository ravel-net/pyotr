import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
from utils.logging import timeit
from utils import parsing_utils
from copy import deepcopy

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
            return self.value + "(" + ", ".join(childrenStr) + ")"
        
if __name__ == '__main__':
    condition1 = "Or(  And  ( x == 1, y ==          '10.0.0.1'), And(  x==     2   , y ==    '10.0.0.2' )    )"
    condition1 = ""
    # condition1 = "x == 1"
    # condition1 = "And( x ==1   , y    == '10.0.0.1'   )"
    # condition2 = "And( x == 1, y == '10.0.0.1')"

    cond1Obj = ConditionTree(condition1, 0)
    print(cond1Obj)