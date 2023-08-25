import sys
import re
from copy import copy
from os.path import dirname, abspath
root = dirname(abspath(__file__))
sys.path.append(root)
from utils.logging import timeit
import psycopg2 

# check if the table given is empty or not
@timeit 
def isEmpty(conn, name):
	cursor = conn.cursor()
	cursor.execute("SELECT count(*) from {}".format(name)) # check if empty
	if cursor.fetchall()[0][0] == 0:
		return True
	else:
		return False

# returns the union of the resulting table
@timeit 
def unionDifference(conn, outputTableName, tableNames):
	cursor = conn.cursor()
	queries = []
	for tableName in tableNames:
		queries.append("SELECT * FROM {}".format(tableName))
	cursor.execute("INSERT INTO {} ".format(outputTableName) + " UNION ".join(queries))

# Returns the setdifference between table1 and table2 and inserts the result into the outputTable
@timeit
def setDifference(conn, outputTableName, table1Name, table2Name):
	cursor = conn.cursor()
	cursor.execute("INSERT INTO {outputTableName} SELECT * FROM {table1Name} EXCEPT SELECT * FROM {table2Name}".format(outputTableName=outputTableName, table1Name=table1Name, table2Name=table2Name))
	return cursor.rowcount
