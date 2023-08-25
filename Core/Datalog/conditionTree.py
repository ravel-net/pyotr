import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
from utils import parsing_utils
from copy import deepcopy

class ConditionLeaf:
    """
    A class used to represent a single condition of the form 'var1 op var2'
    """
    # Leafs are conditions of the form var1 op var2
    def __init__(self, currCond, operator):
        self.operator = operator
        conditionSplit = currCond.split(self.operator)
        self.var1 = conditionSplit[0].strip()
        self.var2 = conditionSplit[1].strip()
        self.isTrue = False
        if "==" in operator and str(self.var1) == str(self.var2):
            self.isTrue = True
        if "!=" in operator and str(self.var1) != str(self.var2):
            self.isTrue = True

    def __str__(self):
        return parsing_utils.condToStringDefault(self.var1, self.operator, self.var2)
    
    def getIsTrue(self):
        return self.isTrue

    def toString(self, mode, replacementDict = {}, atomTables = [], reasoningType={}, bits = 32):
        return parsing_utils.condToStringModes(var1=self.var1, operator=self.operator, var2=self.var2, mode=mode, replacementDict=replacementDict, atomTables=atomTables, reasoningType=reasoningType, bits = bits)

# make sure to check if the conditionTree isTrue or not. If it is, then it is trivially true and can be skipped altogether
# ConditionTree is either a single condition or a logical operator with conditionTrees as children
# Note that we break down arrays into elements e.g 'v != [1,2,3]' becomes 'And(v != 1, v != 2, v != 3)'
class ConditionTree:
    """
    A class used to represent a condition using a tree. Each node is either a logical operator or a leaf node (that represents a single condition)
    """
    def __init__(self, condition, pos = 0):
        self.condition_string = condition
        self.children = []
        self.isLeaf = False
        self.isEmpty = False
        isProcessed = False
        self.isTrue = False
        
        # skip over spaces:
        while pos < len(condition) and (condition[pos] == " " or condition[pos] == ","):
            pos += 1
        
        if len(condition) == 0:
            self.isEmpty = True
        elif len(condition)-pos < 4: # must be a leaf
            self.processLeaf(condition=condition, pos=pos)
            isProcessed = True
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
        elif condition[pos:pos+3] == "Not":
            while pos < len(condition) and condition[pos] != "(":
                pos += 1
            pos += 1
            self.value = "Not"
        else: # must be a leaf
            self.processLeaf(condition=condition, pos=pos)
            isProcessed = True

        # skip over spaces:
        while pos < len(condition) and condition[pos] == " ":
            pos += 1

        # The bottom part only run if it's a logical operator
        if not self.isEmpty and not isProcessed:
            while pos < len(condition) and condition[pos] != ")":
                child = ConditionTree(condition, pos)
                # if not child.getIsTrue(): # when the condition is trivially true. #TODO: Also think about doing something when the condition is trivially False.
                pos = child.getEndPos()
                if not child.getIsTrue() or self.value == "Or":
                    self.children.append(child)
                else:
                    del child
                while pos < len(condition) and condition[pos] == " ": # skip over spaces:
                    pos += 1

            pos += 1 # skipping over last bracket
            self.endPos = pos

        if not self.isLeaf and len(self.children) == 0:
            self.isEmpty = True
            self.isTrue = True

    def getIsTrue(self):
        return self.isTrue

    def processLeaf(self, condition, pos):
        endPos = parsing_utils.findCondEnd(condition, pos)
        operator = parsing_utils.findOperator(condition, pos, endPos)
        currCond = deepcopy(condition[pos:endPos])
        self.endPos = endPos
        if "{" in currCond: # it is an array
            self.isLeaf = False
            if operator == "!=": # not in
                self.value = "And"
            else:
                self.value = "Or"
            conditionSplit = currCond.split(operator)
            var1Arr = []
            var1 = conditionSplit[0].strip()
            if "{" in var1: # var1 also an array!
                var1Arr = conditionSplit[0].strip()[1:-1].split(",") # var1 could also be an array
            else:
                var1Arr.append(var1)
            var2Arr = conditionSplit[1].strip()[1:-1].split(",") # we assume that var2 is an array always when there is any array involved
            if len(var1Arr) == 1 and len(var2Arr) == 1:
                self.isLeaf = True
                currCond = "{} {} {}".format(var1Arr[0], operator, var2Arr[0])
                self.value = ConditionLeaf(currCond, operator)
                if self.value.getIsTrue():
                    self.isTrue = True
            else:
                for var1 in var1Arr:
                    var1 = var1.strip()
                    for var2 in var2Arr:
                        var2 = var2.strip()
                        conditionLeaf = "{} {} {}".format(var1, operator, var2)
                        self.children.append(ConditionLeaf(currCond=conditionLeaf, operator=operator))
        else:
            self.isLeaf = True
            self.value = ConditionLeaf(currCond, operator)
            if self.value.getIsTrue():
                # self.isEmpty = True
                self.isTrue = True

        if self.endPos < len(condition) and condition[self.endPos] == ",":
            self.endPos += 1

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
    
    def toString(self, mode, replacementDict={}, atomTables=[], reasoningType={}, bits = 32):
        bddMapping = {"And":"&","Or":"^","Not":"~"}
        if self.isEmpty:
            return ""
        if self.isLeaf:
            return self.value.toString(mode = mode, atomTables=atomTables, replacementDict=replacementDict, reasoningType=reasoningType, bits = bits)
        else:
            childrenStr = []
            for child in self.children:
                childrenStr.append(child.toString(mode = mode, atomTables=atomTables, replacementDict=replacementDict, reasoningType=reasoningType, bits = bits))
            if len(childrenStr) > 0:
                if mode == "SQL":
                    return "(" + " {} ".format(self.value).join(childrenStr) + ")"   
                elif mode == "BDD":
                    return parsing_utils._combineItems(childrenStr, bddMapping[self.value])
                else:
                    return self.value + "(" + ", ".join(childrenStr) + ")" 
            else:
                return ""

if __name__ == '__main__':
    condition1 = "And(And(1500007 == 1500007, -1 != {" + "1500000}, -10000036 == -20, 1500000 == 1500000))"
    print("asd")
    # condition1 = "x == 1"
    # condition1 = "And( x ==1   , y    == '10.0.0.1'   )"
    # condition2 = "And( x == 1, y == '10.0.0.1')"

    cond1Obj = ConditionTree(condition1, 0)
    print(cond1Obj)