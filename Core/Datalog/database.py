import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
# import psycopg2 
# from copy import deepcopy
import databaseconfig as cfg
from utils.logging import timeit
from Core.Datalog.table import DT_Table

class DT_Database:
    """
    A class used to represent a database over which datalog programs are run.

    Attributes
    ----------
    __MAX_ITERATIONS : int
        the maximum number of times a datalog program should be run (in case fixed point isn't reached)

    Methods
    -------
    contains(program2)
        does this program uniformly contain program2?
    """

    # list of tables 
    def __init__(self, tables = [], cVarMapping={}):
        self.tables = tables
        self.cVarMapping = cVarMapping
        self.cVarMappingReverse = {}
        for negInt in self.cVarMapping:
            self.cVarMappingReverse[self.cVarMapping[negInt]] = negInt
        self.cvar_domain = self.getDomains()
        self.c_variables = self.getCVars()
        self.reasoning_types = self.getReasoningType()
        self.databaseTypes = self.getDatabaseTypes()
        self.c_tables = self.getCTables()
        self.cVarTypes = self.getCVarType()

    # creates an empty DB
    def initiateDB(self, conn):
        for table in self.tables:
            table.initiateTable(conn)

    def getTable(self, name):
        for table in self.tables:
            if table.name == name:
                return table
        return None

    def getCTables(self):
        c_tables = []
        for table in self.tables:
            if table.isCTable:
                c_tables.append(table.name)
        return c_tables

    def getDatabaseTypes(self):
        databaseTypes = {}
        for table in self.tables:
            table_types = []
            for colm in table.columns:
                table_types.append(table.columns[colm])
            databaseTypes[table.name] = table_types
        return databaseTypes
    
    def getCVars(self):
        return list(self.cVarMappingReverse.keys())

    def getDomains(self):
        cvar_domain = {}
        for table in self.tables:
            for cvar in table.cvars_domain:
                domain = table.cvars_domain[cvar]
                if cvar in cvar_domain and domain != cvar_domain[cvar]: # When two tables assing different domain to the same c-var
                    print("Error while getting domain for database. Two different domains defined for cvar {}: {} and {}. Exiting".format(cvar, domain, cvar_domain[cvar]))
                    exit()
                elif cvar not in cvar_domain:
                    cvar_domain[cvar] = domain
        return cvar_domain

    def getReasoningType(self):
        reasoning_types = {}
        for table in self.tables:
            for cvar in self.c_variables:
                if cvar not in table.reasoning_type:
                    continue
                colm_type = table.reasoning_type[cvar]
                if cvar in reasoning_types and reasoning_types[cvar] != colm_type: # When a cvariable has different column types
                        print("Error while getting reasoning types for database. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(cvar, colm_type, reasoning_types[cvar]))
                        exit()
                elif cvar not in reasoning_types:
                    reasoning_types[cvar] = colm_type
        return reasoning_types

    def getCVarType(self):
        cVarTypes = {}
        for table in self.tables:
            for cvar in self.c_variables:
                if cvar not in table.cVarTypes:
                    continue
                colm_type = table.cVarTypes[cvar]
                if cvar in cVarTypes and cVarTypes[cvar] != colm_type: # When a cvariable has different column types
                        print("Error while getting reasoning types for database. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(cvar, colm_type, reasoning_types[cvar]))
                        exit()
                elif cvar not in cVarTypes:
                    cVarTypes[cvar] = colm_type
        return cVarTypes


    
    
    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n