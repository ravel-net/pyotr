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
    # TODO: Add column order (by default dictionaries are insertion ordered so skipping this should be fine)
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
        self.cVarTypes = self.getCVarType()
        if self.isCTable:
            self.addConditionColumn()
    
    # TODO: Think about a better way than this
    def getColmTypeWithoutFaure(self, colmType):
        return colmType.replace("_faure","")
    
    # Initiates an empty table
    def initiateTable(self, conn):
        cursor = conn.cursor()
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))
        table_creation_query = "CREATE TABLE {}(".format(self.name)
        for colmName in self.columns: 
            colmType = self.columns[colmName]
            table_creation_query += '{} {},'.format(colmName, self.getColmTypeWithoutFaure(colmType))
        table_creation_query = table_creation_query[:-1]
        table_creation_query += ");"
        cursor.execute(table_creation_query)

    # Given a colm index, return the colm type
    def getColmType(self, i):
        j = 0
        for colmName in self.columns:
            if j == i:
                return self.getColmTypeWithoutFaure(self.columns[colmName])
            j += 1
        # If we have reached this point then incorrect colm index given
        print("Error (getColmType in Table): {} index given but there are only {} colms in table {}".format(i,j,self.name))
        exit()

    # Given a colm index, return the colm name
    def getColmName(self, i):
        j = 0
        for colmName in self.columns:
            if j == i:
                return colmName
            j += 1
        # If we have reached this point then incorrect colm index given
        print("Error (getColmName in Table): {} index given but there are only {} colms in table {}".format(i,j,self.name))
        exit()


    # Adds condition column of type text[] and name condition (if it already does not exist)
    def addConditionColumn(self):
        if "condition" not in self.columns:
            self.columns["condition"] = "text[]"

    def isCTable(self):
        for colm in self.columns:
            if "faure" in self.columns[colm]:
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
        reasoningTypeMapping = {"integer":"Int", "inet":"BitVec", "integer_faure":"Int", "inet_faure":"BitVec"}
        reasoning_types = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar] 
            colm_type = reasoningTypeMapping[self.columns[colm]]
            if cvar in reasoning_types and reasoning_types[cvar] != colm_type: # When a cvariable has different column types
                    print("Error while getting reasoning types for table {}. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(self.name, cvar, colm_type, reasoning_types[cvar]))
                    exit()
            elif cvar not in reasoning_types:
                reasoning_types[cvar] = colm_type
        return reasoning_types

    def getCVarType(self):
        cVar_types = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar] 
            colm_type = self.columns[colm]
            if cvar in cVar_types and cVar_types[cvar] != colm_type: # When a cvariable has different column types
                    print("Error while getting reasoning types for table {}. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(self.name, cvar, colm_type, reasoning_types[cvar]))
                    exit()
            elif cvar not in cVar_types:
                cVar_types[cvar] = colm_type
        return cVar_types


    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n