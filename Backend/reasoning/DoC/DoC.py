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
from Backend.reasoning.DoC.tbv import tbv
import logging

class DoC:
    """
    Implements difference of cube

    Functions:
    ----------
    """
    def __init__(self, name, posStrings, negStrings=[], bits = 32) -> None:
        """
        Parameters:
        -----------
        bits: integer
            number of bits in the DoC
        """
        self.name = name
        self.bits = bits

        if type(posStrings) == list:
            self.pos = self.getPositiveDoC(posStrings)
            self.neg = []
            for negString in negStrings:
                self.neg.append(tbv(tbvString=negString, bits=self.bits))
        else: # directly providng correct pos and neg strings
            self.pos = posStrings
            self.neg = negStrings

    # takes as input a list of positive strings and outputs the result of anding them
    def getPositiveDoC(self, posStrings):
        if len(posStrings) == 0:
            print("Must have at least one positive string.")
            exit()
        pos = tbv(tbvString=posStrings[0], bits=self.bits)
        for tbvString in posStrings:
            currTbv = tbv(tbvString=tbvString, bits=self.bits)
            pos = pos.intersect(currTbv)
            # if pos.isUndefined:
                # print("Issue in intersection between {} and {}".format(str(pos), tbvString))
                # print(pos)
                # exit()
        return pos

    # Contradiction if positive is undefined or if any negative value contains the positive value
    # TODO: We do not check if collectively the negative conditions lead to a contradiction
    # For example, i = 1**, i != 1*0, i != 1*1 will not show up as a contradiction here
    def hasContradiction(self):
        if self.pos.isUndefined:
            return True
        newNeg = []
        i = 0
        while i < len(self.neg):
            tbv = self.neg[i]
            if tbv.contains(self.pos):
                return True
            count, index = self.pos.diff_by_012(tbv2=tbv)
            if count != 2:
                if count == 0:
                    return True
                elif count == 3:
                    i += 1
                else: # count == 1
                    newPos = self.pos.value[:index]+tbv.value[index]+self.pos.value[index+1:]
                    self.pos.value = newPos
                    currNeg = tbv.intersect(self.pos)
                    newNeg.append(currNeg)
                    newNeg += self.neg[i+1:]
                    self.neg = newNeg
                    i = 0
            else:
                newNeg.append(tbv)
                i += 1
        self.neg = newNeg
        return False
    
    def removeContradictions(self):
        newNeg = []
        for tbv in self.neg:
            if not tbv.contains(self.pos):
                newNeg.append(tbv)
        self.neg = newNeg

    # if at any position self has a wildcard but doc2 doesnt, make that bit a non-wildcard
    # done in place
    def mergeWildcards(self, doc2):
        self.pos.mergeWildCards(doc2.pos) 
        self.neg += doc2.neg

    # calculates the intersection between two docs
    # this is not done in place
    def intersect(self, doc2):
        newPos = None
        newNeg = []
        newPos = self.pos.intersect(doc2.pos)
        newNeg = self.neg + doc2.neg
        return DoC(name=self.name, posStrings=newPos, negStrings=newNeg, bits=self.bits)

    def __str__(self):
        pos_str = self.name + " == " + str(self.pos)
        if len(self.neg) == 0:
            return pos_str
        else:
            negativeStrs = []
            for tbv in self.neg:
                negativeStrs.append("{} != {}".format(self.name, str(tbv)))
        return "And(" + pos_str + ", " + ", ".join(negativeStrs) + ")"