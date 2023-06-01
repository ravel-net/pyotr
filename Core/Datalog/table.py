import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
# import psycopg2 
# from copy import deepcopy
import databaseconfig as cfg
from utils.logging import timeit

class DT_Table:
    """
    A class used to represent a table over which datalog programs are run.

    Attributes
    ----------
    __MAX_ITERATIONS : int
        the maximum number of times a datalog program should be run (in case fixed point isn't reached)

    Methods
    -------
    contains(program2)
        does this program uniformly contain program2?
    """
    
    # columns: {column_name : column_type}
    # domain: {column_name : []}
    # cvars: {cvar : column_name}
    def __init__(self, name, columns, cvars, domain={}):
        self.name = name
        self.columns = columns
        self.cvars = cvars
        self.domain = domain
        self.cvars_domain = self.getCvarsDomain()
        self.reasoning_type = self.getReasoningType()
        self.isCTable = self.isCTable()

    def isCTable(self):
        for colm in self.columns:
            if "faure" in self.columns[colm] or True: #TODO: Remove or true
                return True
        return False
        
    def getCvarsDomain(self):
        cvars_domain = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar]
            if colm in self.domain: # if domain for a column is not defined, we assume default domain
                cvars_domain[cvar] = self.domain[colm]
        return cvars_domain
    
    def getReasoningType(self):
        reasoningTypeMapping = {"integer":"Int", "inet":"BitVec"}
        reasoning_types = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar] 
            colm_type = reasoningTypeMapping[self.columns[colm]]
            if cvar in reasoning_types and reasoning_types[cvar] != colm_type: # When a cvariable has different column types
                    print("Error while getting reasoning types for table {}. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(self.name, cvar, colm_type, reasoning_types[cvar]))
                    exit()
            elif cvar not in reasoning_types:
                reasoning_types[cvar] = colm_type
        print("reasoning_types",reasoning_types)
        return reasoning_types


    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n