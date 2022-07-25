import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import psycopg2 
import copy
import time
from tqdm import tqdm
import z3
from z3 import And, Not, Or, Implies
import databaseconfig as cfg
import Core.Homomorphism.tableau as tableau
import Core.Homomorphism.translator_pyotr as translator_pyotr
import Core.Homomorphism.Optimizations.closure_group.closure_group as closure_group
import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology
import Core.Homomorphism.Optimizations.split_merge.split_merge as split_merge

# This name is hard coded from translator_pyotr. This should ideally be taken dynamically
OUTPUT_TABLE_NAME = "output" 

def faure_valuation(sql, domain, storage_types, reasoning_type, output_table_name, simplification_on, column_names):
	# For constant tables
	if "condition" not in column_names:
		begin = time.time()
		conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
		conn.set_session()
		cur = conn.cursor()
		cur.execute(sql)
		result = cur.fetchall()
		conn.commit()
		sat = (len(result) > 0)
		conn.close()
		end = time.time()
		return sat, "", end-begin, 0, 0, 0

	tree = translator_pyotr.generate_tree(sql)
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree, storage_types[0]) # TODO: Need to update upd_condition to take into account different storage types for different columns
	simplification_time = 0
	if (simplification_on):
		simplification_time = translator_pyotr.normalization(reasoning_type)
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=reasoning_type)
	domain_conditions, domain_time = check_tautology.get_domain_conditions_general(domain=domain,datatype=reasoning_type)
	checktime = 0
	if union_conditions != "Or()": # i.e. Empty table
		ans, checktime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time
	else:
		model = ""
		ans = False
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time

def homomorphism(query=[("1","1",""),("1","2","")], query_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", data_summary=["1","2"], column_names=["n1","n2", "condition"], split_merge_on=False, simplification_on=True, variable_clousre_on=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int"):
	"""
	Performs homomorphism between two given tableaux. The data instance must be stored in the database

	Parameters:
	------------
	query : Array of tuples 
	    Tableau query. The position of columns in tuples must match that of the data instance tableau 
	query_summary : Array of integers/variables/IPs
		Summary of tableau query
	domain : Dictionary i.e. {string : [int]}
	    The domain of variables that are used in the data instance. The domain represents the values that the variables are allowed to have. Usually, the domain is all constants in the data instance
	data_instance_table : string
	    The name of the data instance that is stored in postgres
	column_names : [string]
		Column names of the data instance. This does not directly affect the working of the function but "condition" is a special column and must be the last column if the data instance has variables. See example in main function
	split_merge_on : bool
		Whether or not to use split merge optimization
	simplification_on : bool
		Whether or not to simplify conditions during faure valuation
	variable_clousre_on : bool
		Whether or not to use variable closure optimization
	storage_types : [string]
		The storage types of all columns of the data instance table except the condition column (which is text by default). This is usually int4_faure, which allows c-variables in integers
	reasoning_type : string
		The reasoning type (e.g. Int, String) of Z3 for variables.

	Returns:
	------------
	ans : bool
	    Whether or not homomorphism exists between the given tableaux
	model : string
		The counter example if homomorphism doesn't exist (i.e. unsatisfiable condition encountered)
	total_runtime : double
		Total runtime of the process
	data_time : double
		Time taken to apply the query
	upd_time : double
		Time taken to update the conditions
	simplification_time : dictionary
		simplification_time["contradiction"] contains the time taken to remove contradictions while simplification_time["redundancy"] contains the time taken to remove redundancies
	"""

	ans, total_runtime, total_data_time, total_upd_time, total_simplification_time, total_checktime = False, 0, 0, 0, {'contradiction': [0, 0], 'redundancy': [0, 0]}, 0
	groups = [query]

	if (variable_clousre_on):
		groups = closure_group.getAllClosureGroups(query)
	for group in groups:
		if (split_merge_on): # Not working. Need Fangping's input
			variables = closure_group.find_variables(group)
			data_time, upd_time, simplification_time, checktime, output_table = split_merge.split_merge(group, data_instance_table, variables, query_summary, storage_types, reasoning_type) #TODO: Split merge doesn't return individual runnin times

			total_data_time += data_time
			total_upd_time += upd_time
			total_simplification_time["contradiction"][0] += simplification_time["contradiction"][0]
			total_simplification_time["contradiction"][1] += simplification_time["contradiction"][1]
			total_simplification_time["redundancy"][0] += simplification_time["redundancy"][0]
			total_simplification_time["redundancy"][1] += simplification_time["redundancy"][1]
			total_checktime += total_checktime
			total_runtime += data_time+upd_time+checktime+simplification_time["contradiction"][1]+simplification_time["redundancy"][1]
		else:
			substituted_tableau = tableau.summary_substitutions(query, query_summary, data_summary)
			sql = tableau.general_convert_tableau_to_sql(substituted_tableau, data_instance_table, data_summary, column_names)
			ans, model, data_time, upd_time, simplification_time, checktime = faure_valuation(sql, domain, storage_types, reasoning_type, OUTPUT_TABLE_NAME, simplification_on, column_names)

			total_data_time += data_time
			total_upd_time += upd_time
			if simplification_time:
				total_simplification_time["contradiction"][0] += simplification_time["contradiction"][0]
				total_simplification_time["contradiction"][1] += simplification_time["contradiction"][1]
				total_simplification_time["redundancy"][0] += simplification_time["redundancy"][0]
				total_simplification_time["redundancy"][1] += simplification_time["redundancy"][1]
			total_checktime += total_checktime
			if simplification_time:
				total_runtime += data_time+upd_time+checktime+simplification_time["contradiction"][1]+simplification_time["redundancy"][1]
			else:
				total_runtime += data_time+upd_time+checktime+simplification_time

			if (ans == False):
				return ans, model, total_runtime, total_data_time, total_upd_time, total_simplification_time, total_checktime
				
	return ans, "", total_runtime, total_data_time, total_upd_time, total_simplification_time, total_checktime
	
# Loads a given table into postgres
# TODO: The condition column is a bit hardcoded here. Need to generalize
def load_table(data_instance_table, data_instance, column_names, storage_types, cursor):
	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	cursor = conn.cursor()
	cursor.execute("DROP TABLE IF EXISTS {};".format(data_instance_table))
	table_creation_query = "CREATE TABLE {}(".format(data_instance_table)
	num_cols = len(column_names)-1 # assuming that last column is always condition
	if (column_names[-1] != "condition"):
		num_cols += 1
	for col in range(num_cols): 
		table_creation_query += '{} {},'.format(column_names[col], storage_types[col])
	if (column_names[-1] == "condition"):
		table_creation_query += "condition TEXT[]);"
	else:
		table_creation_query = table_creation_query[:-1]
		table_creation_query += ");"
	cursor.execute(table_creation_query)  
	encodedRules = []
	for row in data_instance:
		table_insertion_query = "INSERT INTO {} VALUES (".format(data_instance_table)
		for i in range(num_cols): 
			table_insertion_query += "'{}',".format(row[i])

		if (column_names[-1] == "condition"):
			if (row[-1] == ""):
				table_insertion_query += "array[]::text[]);"
			else:
				table_insertion_query += "{});".format(row[-1])
		else:
			table_insertion_query = table_insertion_query[:-1]
			table_insertion_query += ");"

		cursor.execute(table_insertion_query)  
	conn.commit()
	conn.close()

def homomorphism_test(query=[("1","1",""),("1","2","")], query_summary=["1","2"], data_instance=[("1","u",""),("u","v",""),("v","2",""), ("1","1",""), ("u","u",""), ("v","v","")], data_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", column_names=["n1","n2", "condition"], split_merge_on=False, simplification_on=True, variable_clousre_on=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int"):
	"""
	Performs homomorphism between two given tableaux. This is a test function, which means that the data instance is given as raw input and stored into database first before applying the query. This function calls the function homomorphism.

	Parameters:
	------------
	query : Array of tuples 
	    Tableau query. The position of columns in tuples must match that of the data instance tableau 
	query_summary : Array of integers/variables/IPs
		Summary of tableau query
	data_instance:
		Tableau data instance. The position of columns in tuples must match that of the query tableau. If the data instance contains variables, then there must be an extra condition column for faure valuation.
	domain : Dictionary i.e. {string : [int]}
	    The domain of variables that are used in the data instance. The domain represents the values that the variables are allowed to have. Usually, the domain is all constants in the data instance
	data_instance_table : string
	    What the data instance table should be called in the database. This is optional and has no effect on the working of the function
	column_names : [string]
		Column names of the data instance. This does not directly affect the working of the function but "condition" is a special column and must be the last column if the data instance has variables. See example in main function
	split_merge_on : bool
		Whether or not to use split merge optimization
	simplification_on : bool
		Whether or not to simplify conditions during faure valuation
	variable_clousre_on : bool
		Whether or not to use variable closure optimization
	storage_types : [string]
		The storage types of all columns of the data instance table except the condition column (which is text by default). This is usually int4_faure, which allows c-variables in integers
	reasoning_type : string
		The reasoning type (e.g. Int, String) of Z3 for variables.

	Returns:
	------------
	ans : bool
	    Whether or not homomorphism exists between the given tableaux
	model : string
		The counter example if homomorphism doesn't exist (i.e. unsatisfiable condition encountered)
	total_runtime : double
		Total runtime of the process
	data_time : double
		Time taken to apply the query
	upd_time : double
		Time taken to update the conditions
	simplification_time : dictionary
		simplification_time["contradiction"] contains the time taken to remove contradictions while simplification_time["redundancy"] contains the time taken to remove redundancies
	"""

	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	cursor = conn.cursor()
	load_table(data_instance_table, data_instance, column_names, storage_types, cursor)
	ans, model, total_runtime, data_time, upd_time, simplification_time, checktime = homomorphism(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge_on, simplification_on, variable_clousre_on, storage_types, reasoning_type)
	cursor.execute("DROP TABLE IF EXISTS {};".format(data_instance_table))
	conn.commit()
	return ans, model, total_runtime, data_time, upd_time, simplification_time, checktime

# make
# load

# The database is loaded from file database.cfg in the root folder. The default username and passowrd is usually 'postgres' and 'postgres'. You need to specify a database to load. To do so, create a database in postgres. 
# i.e. sudo -u postgres -i, where postgres is a the user associated with postgres
# psql
# CREATE DATABASE [DB_NAME], 

# 
if __name__ == "__main__":
	# MINIMIZATION EXAMPLE
	# =====================================================================================
	query_summary=["1","4"] 
	domain={"x":["1","2","3","4"], "y":["1","2","3","4"], "z":["1","2","3","4"]} #only relevant if the data instance has these variables
	data_summary=["1","4"]

	# ===================================
	# minimization example with variables
	# ===================================
	column_names=["n1","n2", "condition"]
	T_data = [
		("1", "2", ""),
		("2", "x", ""),
		("x", "y", ""), # Homomorphism exists even after commenting this out (removing this tuple)
		("y", "x", ""), # Homomorphism exists even after commenting this out (removing this tuple)
		("x", "3", ""),
		("3", "z", ""), 
		("z", "4", ""),

		# self loops
		("x", "x", ""),
		("y", "y", ""),
		("z", "z", ""),
	]	

	# ===================================
	# minimization example with constants
	# ===================================
	# column_names=["n1","n2"]
	# T_data = [
	# 	("1", "2"),
	# 	("2", "5"),
	# 	("5", "6"), # Homomorphism exists even after commenting this out (removing this tuple)
	# 	("6", "5"), # Homomorphism exists even after commenting this out (removing this tuple)
	# 	("5", "3"),
	# 	("3", "7"),
	# 	("7", "4"),

	# 	# self loops
	# 	("5", "5"),
	# 	("6", "6"),
	# 	("7", "7"),
	# ]	

	T_query = [
		("1", "2"),
		("2", "x"),
		("x", "y"),
		("y", "x"),
		("x", "3"),
		("3", "z"),
		("z", "4"),
	]

	results = homomorphism_test(query=T_query, query_summary=query_summary, data_instance=T_data, data_summary=data_summary, domain=domain, data_instance_table="T_data", column_names=column_names, storage_types=["int4_faure", "int4_faure"])

	ans = results[0]
	model = results[1]
	print()
	print("Homomorphism Exists?: ", ans)
	if model:
		print("Counter Example: ", model)
	elif not ans and not model:
		print("The applied query did not yield any tuples")


	# LINK FAILURE EXAMPLE
	# =====================================================================================
	# query_summary=["a","c","e"] 
	# domain={"x":["0","1"], "y":["0","1"]}
	# data_summary=["1","3","5"]
	# column_names=["n1","n2", "x_link", "y_link", "condition"]
	# split_merge_on=False
	# simplification_on=True
	# variable_clousre_on=False
	# storage_types=["int4_faure", "int4_faure", "int4_faure", "int4_faure"]
	# reasoning_type="Int"

	# ==========================================
	# T_data_1 example (correct backup links)
	# ==========================================
	# T_data = [
	# 	("1","2","1","y", ""),
	# 	("2","3","x","y",""),
	# 	("1","3","0","y",""),
	# 	("3","4","x","1",""),
	# 	("4","5","x","y",""),
	# 	("3","5","x","0",""),

	# 	("1","1","x","y",""),
	# 	("2","2","x","y",""),
	# 	("3","3","x","y",""),
	# 	("4","4","x","y",""),
	# 	("5","5","x","y",""),
	# ]	

	# ==========================================
	# T_data_2 example (incorrect backup links)
	# ==========================================
	# T_data = [
	# 	("1","2","1","y", ""),
	# 	("2","3","x","y",""),
	# 	("1","4","0","y",""),
	# 	("3","4","x","1",""),
	# 	("4","5","x","y",""),
	# 	("3","5","x","0",""),

	# 	("1","1","x","y",""),
	# 	("2","2","x","y",""),
	# 	("3","3","x","y",""),
	# 	("4","4","x","y",""),
	# 	("5","5","x","y",""),
	# ]

	# T_query = [
	# 	("a","b","x","y",""),
	# 	("b","c","x","y",""),
	# 	("c","d","x","y",""),
	# 	("d","e","x","y",""),
	# ]

	# results = homomorphism_test(query=T_query, query_summary=query_summary, data_instance=T_data, data_summary=data_summary, domain=domain, data_instance_table="T_data", column_names=column_names)

	# ans = results[0]
	# model = results[1]
	# print()
	# print("Homomorphism Exists?: ", ans)
	# if model:
	# 	print("Counter Example: ", model)
	# elif not ans and not model:
	# 	print("The applied query did not yield any tuples")
