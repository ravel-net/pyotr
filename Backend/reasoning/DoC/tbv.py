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
import logging

class tbv:
    """
    Implements ternary bit vector

    Functions:
    ----------
    """
    ########@timeit
    def __init__(self, tbvString="", bits = 32) -> None:
        """
        Parameters:
        -----------
        bits: integer
            number of bits in the DoC
        """
        if tbvString[0] == "#":
            self.value = tbvString[1:]
        else:
            self.value = tbvString
        self.bits = bits
        self.isUndefined = False
    
    # calculates the intersection between two tbvs. If the intersection is not possible, makes the current tbv undefined
    def intersect(self, tbv2):
        if len(self.value) != self.bits or len(tbv2.value) != self.bits:
            print("Number of bits do not match. Cannot calculate intersection")
            exit()
        outputstring = ""
        undefined = False
        for bit in range(self.bits):
            if self.value[bit] == "x":
                outputstring += tbv2.value[bit]
            elif tbv2.value[bit] == "x":
                outputstring += self.value[bit]
            elif tbv2.value[bit] != self.value[bit]:
                outputstring += "z" # denotes undefined
                undefined = True
            else:
                outputstring += self.value[bit]
        newTBV = tbv(outputstring, self.bits)
        newTBV.isUndefined = undefined
        return newTBV
            
    # checks if this tbv contains tbv2
    def contains(self, tbv2):
        if len(self.value) != self.bits or len(tbv2.value) != self.bits:
            print("Number of bits do not match. Cannot calculate containment")
            exit()
        for bit in range(self.bits):
            if self.value[bit] == "x":
                continue
            elif tbv2.value[bit] != self.value[bit]: # containment is false
                return False
        return True

    # if at any position self has a wildcard but doc2 doesnt, make that bit a non-wildcard
    # done in place
    def mergeWildCards(self, tbv2):
        if len(self.value) != self.bits or len(tbv2.value) != self.bits:
            print("Number of bits do not match. Cannot mergeWildcards")
            exit()
        newBit = ""
        for bit in range(self.bits):
            if self.value[bit] == "x" and tbv2.value[bit] != "x":
                newBit += tbv2.value[bit]
            else:
                newBit += self.value[bit]
        self.value = newBit

    # run on pos
    def diff_by_012(self, tbv2):
        if len(self.value) != self.bits or len(tbv2.value) != self.bits:
            print("Number of bits do not match. Cannot diff_by_012")
            exit()
        index = 0
        count = 0
        for i in range(self.bits):
            b1 = self.value[i]
            b2 = tbv2.value[i]
            if (b1 != b2): 
                if (count == 1): 
                    return 2, index
                if (b1 == "x"):
                    index = i
                    count = 1
                elif (b2 != "x"): 
                    return 3, index
        return count, index

    def __str__(self):
        return "#"+str(self.value)