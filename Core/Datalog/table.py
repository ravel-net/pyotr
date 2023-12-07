import sys
from os.path import dirname, abspath
root = dirname(dirname(dirname(dirname(abspath(__file__)))))
sys.path.append(root)
# import psycopg2 
# from copy import deepcopy
import databaseconfig as cfg
from utils.logging import timeit
from Core.Datalog.conditionTree import ConditionTree
from tabulate import tabulate
from copy import deepcopy
from utils import sql_operations

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
    
    def delete(self, conn): # drops table from db
        cursor = conn.cursor()
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))

    # TODO: Think about a better way than this
    def getColmTypeWithoutFaure(self, colmType):
        # colmType = colmType.replace("integer","bigint") # for ip addresses
        if colmType == "bit_faure":
            return "integer"
        else:
            return colmType.replace("_faure","")

    # renames the current table to to the new table pointed out by newName
    def rename(self, conn, newName):
        cursor = conn.cursor()
        cursor.execute("ALTER TABLE {table_name} RENAME TO {new_table_name}".format(table_name=newName, new_table_name=self.name))

    def unionDifference(self, conn, tableNames):
        sql_operations.unionDifference(conn=conn, outputTableName=self.name, tableNames=tableNames)

    # calculates the set difference and returns the row count of inserted tuples
    def setDifference(self, conn, table1Name, table2Name):
        return sql_operations.setDifference(conn=conn, outputTableName=self.name, table1Name=table1Name, table2Name=table2Name)

    def getRandomTuple(self, conn, colmName, conditions=[]):
        if self.isEmpty(conn):
            print("Table {} is empty. Exiting.".format(self.name))
            exit()
        cursor = conn.cursor()
        sql = "select {} from {}" .format(colmName, self.name)
        if len(conditions) > 0:
            sql += " where " + " and ".join(conditions)
        sql += " order by random() limit 1;"
        cursor.execute(sql)
        result = cursor.fetchall()[0][0]
        return result
        # if type(result) == int:
        #     return result
        # else:
        #     return "'" + result + "'"

    def getNumberEntries(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT COUNT(*) FROM {}".format(self.name))
        return cursor.fetchall()[0][0]
    
    def enableIndexing(self, conn, colmName, using="btree"):
        if colmName not in self.columns:
            print("Column {} is not a valid column in table {}".format(colmName, self.name))
            return
        cursor = conn.cursor()
        cursor.execute("SELECT indexdef FROM pg_indexes WHERE tablename = '{}' and indexname = '{}_{}';".format(self.name.lower(), self.name.lower(), colmName))
        result = cursor.fetchall()
        if len(result) > 0 and using in result[0][0]: # index already exists
            return
        elif "gist" in using:
            cursor.execute("CREATE INDEX {}_{} ON {} using {}({} inet_ops)".format(self.name, colmName, self.name, using, colmName))
        else:
            cursor.execute("CREATE INDEX {}_{} ON {} using {}({})".format(self.name, colmName, self.name, using, colmName))

    def deleteAllIndexes(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT indexname FROM pg_indexes WHERE tablename = '{}';".format(self.name.lower()))
        result = cursor.fetchall()
        for tuple in result:
            cursor.execute("DROP INDEX {}".format(tuple[0]))

    def deleteAllTuples(self, conn):
        self.delete(conn)
        self.initiateTable(conn)

    # returns true if table is empty
    def isEmpty(self, conn):
        return sql_operations.isEmpty(conn, self.name)

    def deleteAllCVarRows(self, conn):
        cursor = conn.cursor()
        for colm in self.columns:
            if self.columns[colm] == "integer_faure":
                cursor.execute("DELETE FROM {} WHERE 0 > {}".format(self.name, colm))
            elif self.columns[colm] == "inet_faure":
                cursor.execute("DELETE FROM {} WHERE '0.255.0.0' > {}".format(self.name, colm))
            elif self.columns[colm] == "inet_faure[]":
                cursor.execute("DELETE FROM {} WHERE '0.255.0.0' > Any({})".format(self.name, colm))
            elif self.columns[colm] == "integer_faure[]":
                cursor.execute("DELETE FROM {} WHERE 0 > Any({})".format(self.name, colm))
        # conn.commit()

    def exists(self, conn):
        cursor = conn.cursor()
        cursor.execute("SELECT EXISTS ( SELECT FROM information_schema.tables WHERE table_name   = '{}' );".format(self.name.lower()))
        result = cursor.fetchall()[0][0]
        # conn.commit()
        return result

    # initiates an exact table but with the name changed
    def initiateNewTable(self, conn, newName):
        newTable = self.duplicateWithNewName(newName)
        cursor = conn.cursor()
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))
        newTable.initiateTable(conn)
        return newTable

    def duplicateWithNewName(self, newName):
        return DT_Table(name=newName, columns=self.columns, cvars=self.cvars, domain=self.domain)

    # Initiates an empty table
    def initiateTable(self, conn):
        cursor = conn.cursor()
        # cursor.execute("SELECT count(to_regclass('{}'))".format(self.name)) # checking if table already exists
        # if cursor.fetchall()[0][0] > 0 and self.isEmpty(conn): # if table exists and is already empty
        #     return # no need to create a new table
        cursor.execute("DROP TABLE IF EXISTS {};".format(self.name))
        table_creation_query = "CREATE TABLE {}(".format(self.name)
        for colmName in self.columns: 
            colmType = self.columns[colmName]
            table_creation_query += '{} {},'.format(colmName, self.getColmTypeWithoutFaure(colmType))
        table_creation_query = table_creation_query[:-1]
        all_unique_colms = []
        for colm in self.columns:
            if "condition" not in colm: # we ignore the condition column for a unique index. TODO: Might not be correct
                all_unique_colms.append(colm)
        # table_creation_query += ", UNIQUE (" + ",".join(all_unique_colms) + ")"
        table_creation_query += ");"
        cursor.execute(table_creation_query)

    # Given a colm index, return the colm type
    ########@timeit
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
        reasoningTypeMapping = {"integer":"Int", "inet":"BitVec", "integer_faure":"Int", "inet_faure":"BitVec", "text[]":"Int", "integer_faure[]":"Int[]", "inet_faure[]":"BitVec[]", "bit_faure":"BitVec", "bit_faure[]":"BitVec[]"}
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
                    print("Error while getting reasoning types for table {}. Two different reasoning types defined for cvar {}: {} and {}. Exiting".format(self.name, cvar, colm_type, self.reasoning_types[cvar]))
                    exit()
            elif cvar not in cVar_types:
                cVar_types[cvar] = colm_type
        return cVar_types

    def _replaceVal(self, val, mapping):
        if val in mapping:
            return mapping[val]
        elif str(val) in mapping:
            return mapping[str(val)]
        elif type(val) == str:
            conditions = ConditionTree(val)
            return conditions.toString(mode = "Replace String", replacementDict = mapping)
        else:
            return val
    
    # move this to table class
    def printTable(self, conn, mapping = {}, cVarMapping = {}, condition = None):
        cursor = conn.cursor()
        if condition:
            cursor.execute("SELECT * from {} where {}".format(self.name, condition))
        else:
            cursor.execute("SELECT * from {}".format(self.name))

        table = cursor.fetchall()
        newTable = []
        mapping.update(cVarMapping)
        for row in table:
            newRow = []
            for colm in row:
                if type(colm) == list:
                    colmArray = []
                    for item in colm:
                        colmArray.append(self._replaceVal(item, mapping))
                    newRow.append(colmArray)
                else:
                    newRow.append(self._replaceVal(colm, mapping))
            newTable.append(newRow)
        cursor.execute("SELECT column_name FROM information_schema.columns WHERE table_schema = 'public' AND table_name = '{}'".format(self.name.lower()))
        headers = cursor.fetchall()
        headerInArray = []
        for colm in headers:
            headerInArray.append(colm[0])
        print("\nPrinting Table: {}".format(self.name))
        print(tabulate(newTable, headers=headerInArray))

    # def __str__(self):
    #     DT_Program_str = ""
    #     for rule in self._rules:
    #         DT_Program_str += str(rule) + "\n"
    #     return DT_Program_str[:-1] # removing the last \n