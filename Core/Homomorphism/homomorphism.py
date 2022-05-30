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

def faure_valuation(sql, domain, storage_types, reasoning_type, output_table_name, simplification_on):
	tree = translator_pyotr.generate_tree(sql)
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree, storage_types[0]) # TODO: Need to update upd_condition to take into account different storage types for different columns
	simplification_time = 0
	if (simplification_on):
		simplification_time = translator_pyotr.normalization(reasoning_type)
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=reasoning_type)
	domain_conditions, domain_time = check_tautology.get_domain_conditions_general(domain=domain,datatype=reasoning_type)
	checktime = 0
	print(domain_conditions)
	if union_conditions != "Or()": # i.e. Empty table
		ans, checktime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
		print(model)
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time
	else:
		model = ""
		ans = False
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time

def homomorphism(query=[("1","1",""),("1","2","")], query_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", data_summary=["1","2"], column_names=["n1","n2", "condition"], split_merge_on=False, simplification_on=True, variable_clousre_on=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int"):
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
			print(sql)
			ans, model, data_time, upd_time, simplification_time, checktime = faure_valuation(sql, domain, storage_types, reasoning_type, OUTPUT_TABLE_NAME, simplification_on)

			total_data_time += data_time
			total_upd_time += upd_time
			total_simplification_time["contradiction"][0] += simplification_time["contradiction"][0]
			total_simplification_time["contradiction"][1] += simplification_time["contradiction"][1]
			total_simplification_time["redundancy"][0] += simplification_time["redundancy"][0]
			total_simplification_time["redundancy"][1] += simplification_time["redundancy"][1]
			total_checktime += total_checktime
			total_runtime += data_time+upd_time+checktime+simplification_time["contradiction"][1]+simplification_time["redundancy"][1]

			if (ans == False):
				return ans, model, total_runtime, total_data_time, total_upd_time, total_simplification_time, total_checktime
	return ans, "", total_runtime, total_data_time, total_upd_time, total_simplification_time, total_checktime
	
def load_table(data_instance_table, data_instance, column_names, storage_types, cursor):
	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	cursor = conn.cursor()
	cursor.execute("DROP TABLE IF EXISTS {};".format(data_instance_table))
	table_creation_query = "CREATE TABLE {}(".format(data_instance_table)
	for col in range(len(column_names)-1): # assuming that last column is always condition
		table_creation_query += '{} {},'.format(column_names[col], storage_types[col])
	table_creation_query += "condition TEXT[]);"
	cursor.execute(table_creation_query)  
	encodedRules = []
	for row in data_instance:
		table_insertion_query = "INSERT INTO {} VALUES (".format(data_instance_table)
		for i in range(len(row)-1): # assuming that last column is always condition
			table_insertion_query += "'{}',".format(row[i])
		if (row[-1] == ""):
			table_insertion_query += "array[]::text[]);"
		else:
			table_insertion_query += "{});".format(row[-1])
		cursor.execute(table_insertion_query)  
	conn.commit()

def homomorphism_test(query=[("1","1",""),("1","2","")], query_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", data_summary=["1","2"], column_names=["n1","n2", "condition"], split_merge_on=False, simplification_on=True, variable_clousre_on=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int", data_instance=[("1","u",""),("u","v",""),("v","2",""), ("1","1",""), ("u","u",""), ("v","v","")]):

	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	cursor = conn.cursor()
	load_table(data_instance_table, data_instance, column_names, storage_types, cursor)
	ans, model, total_runtime, data_time, upd_time, simplification_time, checktime = homomorphism(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge_on, simplification_on, variable_clousre_on, storage_types, reasoning_type)
	cursor.execute("DROP TABLE IF EXISTS {};".format(data_instance_table))
	conn.commit()
	return ans, model, total_runtime, data_time, upd_time, simplification_time, checktime


# if __name__ == "__main__":
# 	query_summary=["1","2"] 
# 	domain={"u":["1","2"], "v":["1","2"]}
# 	data_summary=["1","2"]
# 	column_names=["n1","n2", "condition"]
# 	split_merge_on=False
# 	simplification_on=True
# 	variable_clousre_on=False
# 	storage_types=["int4_faure","int4_faure"]
# 	reasoning_type="Int"
# 	T_v = [
# 		("1","1",""),
# 		("1","2","")
# 	]

# 	T_p = [
# 		("1","u",""),
# 		("u","v",""),
# 		("v","2",""), 
# 		("1","1",""), 
# 		("u","u",""), 
# 		("v","v","")
# 	]
# 	T_v_prime = [
# 		("1","2","")
# 	]

# 	T_p_prime = [
# 		("1","u",""),
# 		("u","v",""),
# 		("v","2",""), 
# 	]

# 	query = T_p_prime
# 	data_instance_table="T_v_prime"
# 	data_instance=T_v_prime


# 	print(homomorphism_test(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge_on, simplification_on, variable_clousre_on, storage_types, reasoning_type, data_instance))

# if __name__ == "__main__":
# 	query_summary=["1","2","3"] 
# 	domain={"u":["2"], "v":["3"]}
# 	data_summary=["1","2","3"]
# 	column_names=["n1","n2", "condition"]
# 	split_merge_on=False
# 	simplification_on=True
# 	variable_clousre_on=False
# 	storage_types=["int4_faure", "int4_faure"]
# 	reasoning_type="Int"

# 	T_2 = [
# 		("1","u","1","y", ""),
# 		("u","2","x","y",""),
# 		("1","v","0","y",""),
# 		("2","v","x","1",""),
# 		("2","3","x","0",""),
# 		("v","3","x","y",""),
# 	]

# 	T_3 = [
# 		("1","2","1","y", ""),
# 		("1","v","0","y",""),
# 		("2","v","x","1",""),
# 		("2","3","x","0",""),
# 		("v","3","x","y",""),
# 	]	

# 	T_1 = [
# 		("1","u","1","y", ""),
# 		("u","2","x","y",""),
# 		("1","2","0","y",""),
# 		("2","v","x","1",""),
# 		("v","3","x","y",""),
# 		("2","3","x","0",""),
# 	]

# 	for x in ["0","1"]:
# 		for y in ["0","1"]:
# 			T_2_mod = []
# 			T_1_mod = []
# 			for tup in T_2:
# 				if (tup[2] == "x" or tup[2] == x) and (tup[3] == "y" or tup[3] == y):
# 					T_2_mod.append((tup[0],tup[1],tup[4]))
# 			for tup in T_1:
# 				if (tup[2] == "x" or tup[2] == x) and (tup[3] == "y" or tup[3] == y):
# 					T_1_mod.append((tup[0],tup[1],tup[4]))

# 			query = T_2_mod
# 			data_instance_table="T_1_mod"
# 			data_instance=T_1_mod
# 			print(x,y)
# 			print(T_1_mod)
# 			print(T_2_mod)
# 			print(homomorphism_test(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge_on, simplification_on, variable_clousre_on, storage_types, reasoning_type, data_instance))


if __name__ == "__main__":
	query_summary=["a","c","e"] 
	domain={"x":["0","1"], "y":["0","1"]}
	# domain={"u":["1","2"], "v":["2","3"], "x":["0","1"], "y":["0","1"]}
	data_summary=["1","3","5"]
	column_names=["n1","n2", "x_link", "y_link", "condition"]
	split_merge_on=False
	simplification_on=True
	variable_clousre_on=False
	storage_types=["int4_faure", "int4_faure", "int4_faure", "int4_faure"]
	reasoning_type="Int"

	T_2 = [
		("1","2","1","y", ""),
		("2","3","x","y",""),
		("1","4","0","y",""),
		("3","4","x","1",""),
		("3","5","x","0",""),
		("4","5","x","y",""),
		("2","2","x","y",""),
		("3","3","x","y",""),
		("4","4","x","y",""),
		("5","5","x","y",""),
	]

	T_3 = [
		("1","2","1","y", ""),
		("1","v","0","y",""),
		("2","v","x","1",""),
		("2","3","x","0",""),
		("v","3","x","y",""),
	]	

	T_1 = [
		("1","2","1","y", ""),
		("2","3","x","y",""),
		("1","3","0","y",""),
		("3","4","x","1",""),
		("4","5","x","y",""),
		("3","5","x","0",""),
		("1","1","x","y",""),
		("2","2","x","y",""),
		("3","3","x","y",""),
		("4","4","x","y",""),
		("5","5","x","y",""),
	]

	T_curr = [
		("a","b","x","y", ""),
		("b","c","x","y",""),
		("c","d","x","y",""),
		("d","e","x","y",""),
	]

	query = T_curr
	data_instance_table="T_1"
	data_instance=T_1
	print(homomorphism_test(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge_on, simplification_on, variable_clousre_on, storage_types, reasoning_type, data_instance))