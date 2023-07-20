import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
# import psycopg2 
# from copy import deepcopy
import databaseconfig as cfg
from utils.logging import timeit
from Core.Datalog.table import DT_Table
from ipaddress import IPv4Address

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
    # cVarMapping must have string as key (not int)
    def __init__(self, tables = [], cVarMapping={}):
        self.tables = tables
        self.cvar_domain = self.getDomains()
        self.c_variables = self.getCVars()
        self.reasoning_types = self.getReasoningType()
        self.databaseTypes = self.getDatabaseTypes()
        self.c_tables = self.getCTables()
        self.cVarTypes = self.getCVarType()
        self.cVarMapping = cVarMapping
        if (len(cVarMapping) == 0):
            self.cVarMapping = self.getCVarMapping()
        self.cVarMappingReverse = {}
        for negInt in self.cVarMapping:
            currCvar = self.cVarMapping[negInt]
            if currCvar not in self.cVarMappingReverse:
                self.cVarMappingReverse[self.cVarMapping[negInt]] = negInt
            elif currCvar in self.cVarMappingReverse and "'" in negInt: # This is done because reverseMapping is used by sql and it requires quotation marks for ip addresses
                self.cVarMappingReverse[self.cVarMapping[negInt]] = negInt


    # Maps cvariable integers to negative integers and maps cvariable inets to 0.0.0.1 to 0.0.255.0
    def getCVarMapping(self):
        cvarMapping = {}
        i = 1
        for cvar in self.c_variables:
            if 'BitVec' in self.reasoning_types[cvar]:
                net = IPv4Address('0.1.0.0') + i # TODO: Doing /32 because postgresql interprets /32 as a host and doesn't print it. This is hacky and we need a better solution
                cvarMapping[str(net)+"/31"] = cvar
                cvarMapping["'"+str(net)+"/31"+"'"] = cvar
            else:
                cvarMapping[str(0-i)] = cvar
            i += 1 
        return cvarMapping

    def delete(self, conn): # destructor - drop tables
        for table in self.tables:
            table.delete(conn)
        conn.commit()

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
        cvars = []
        for table in self.tables:
            for cvar in table.cvars:
                if cvar not in cvars:
                    cvars.append(cvar)
        return cvars

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
                        print("Error while getting reasoning types for database. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(cvar, colm_type, table.reasoning_types[cvar]))
                        exit()
                elif cvar not in cVarTypes:
                    cVarTypes[cvar] = colm_type
        return cVarTypes