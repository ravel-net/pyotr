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
    @timeit
    def __init__(self, name, columns={}, cvars={}, domain={}):
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
    
    @timeit 
    def delete(self, conn): # drops table from db
        cursor = conn.cursor()
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))

    # TODO: Think about a better way than this
    @timeit
    def getColmTypeWithoutFaure(self, colmType):
        colmType = colmType.replace("integer","bigint") # for ip addresses
        return colmType.replace("_faure","")


    @timeit
    def getRandomTuple(self, conn, colmName):
        if self.isEmpty(conn):
            print("Table {} is empty. Exiting.".format(self.name))
            exit()
        cursor = conn.cursor()
        cursor.execute("select {} from {} order by random() limit 1;".format(colmName, self.name))
        return cursor.fetchall()[0][0]
    
    @timeit
    def enableIndexing(self, conn, colmName, using="btree"):
        if colmName not in self.columns:
            print("Column {} is not a valid column in table {}".format(colmName, self.name))
            return
        cursor = conn.cursor()
        cursor.execute("SELECT indexdef FROM pg_indexes WHERE tablename = '{}' and indexname = '{}_{}';".format(self.name.lower(), self.name.lower(), colmName))
        result = cursor.fetchall()
        if len(result) > 0 and using in result[0][0]: # index already exists
            return
        else:
            cursor.execute("CREATE INDEX {}_{} ON {} using {}({})".format(self.name, colmName, self.name, using, colmName))

    @timeit
    def deleteAllIndexes(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT indexname FROM pg_indexes WHERE tablename = '{}';".format(self.name.lower()))
        result = cursor.fetchall()
        for tuple in result:
            cursor.execute("DROP INDEX {}".format(tuple[0]))

    @timeit
    def deleteAllTuples(self, conn):
        self.delete(conn)
        self.initiateTable(conn)

    # returns true if table is empty
    @timeit
    def isEmpty(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT count(*) from {}".format(self.name)) # check if empty
        if cursor.fetchall()[0][0] == 0:
            return True
        else:
            return False

    # Initiates an empty table
    @timeit
    def initiateTable(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT count(to_regclass('{}'))".format(self.name)) # checking if table already exists
        if cursor.fetchall()[0][0] > 0 and self.isEmpty(conn): # if table exists and is already empty
            return # no need to create a new table
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))
        table_creation_query = "CREATE TABLE {}(".format(self.name)
        for colmName in self.columns: 
            colmType = self.columns[colmName]
            table_creation_query += '{} {},'.format(colmName, self.getColmTypeWithoutFaure(colmType))
        table_creation_query = table_creation_query[:-1]
        table_creation_query += ");"
        cursor.execute(table_creation_query)

    # Given a colm index, return the colm type
    @timeit
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
    @timeit
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
    @timeit
    def addConditionColumn(self):
        if "condition" not in self.columns:
            self.columns["condition"] = "text[]"

    @timeit
    def isCTable(self):
        for colm in self.columns:
            if "faure" in self.columns[colm]:
                return True
        return False
    
    @timeit
    def getCvarsDomain(self):
        cvars_domain = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar]
            if colm in self.domain: # if domain for a column is not defined, we assume default domain
                cvars_domain[cvar] = self.domain[colm]
        return cvars_domain
    
    @timeit
    def getReasoningType(self):
        reasoningTypeMapping = {"integer":"Int", "inet":"BitVec", "integer_faure":"Int", "inet_faure":"BitVec", "text[]":"Int", "integer_faure[]":"Int[]", "inet_faure[]":"BitVec[]"}
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

    @timeit
    def getCVarType(self):
        cVar_types = {}
        for cvar in self.cvars:
            colm = self.cvars[cvar] 
            colm_type = self.columns[colm]
            if cvar in cVar_types and cVar_types[cvar] != colm_type: # When a cvariable has different column types
                    print("Error while getting reasoning types for table {}. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(self.name, cvar, colm_type, self.reasoning_types[cvar]))
                    exit()
            elif cvar not in cVar_types:
                cVar_types[cvar] = colm_type
        return cVar_types


    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n