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

# This name is hard coded from translator_pyotr. This should ideally be taken dynamically
OUTPUT_TABLE_NAME = "output" 

def faure_valuation(sql, domain, storage_types, reasoning_type, output_table_name, simplification):
	tree = translator_pyotr.generate_tree(sql)
	data_time = translator_pyotr.data(tree)
	upd_time = translator_pyotr.upd_condition(tree, storage_types[0]) # TODO: Need to update upd_condition to take into account different storage types for different columns
	simplification_time = 0
	if (simplification):
		simplification_time = translator_pyotr.normalization(reasoning_type)
	union_conditions, union_time = check_tautology.get_union_conditions(tablename=output_table_name, datatype=reasoning_type)
	domain_conditions, domain_time = check_tautology.get_domain_conditions(domain=domain,datatype=reasoning_type)
	print(domain_conditions)
	checktime = 0
	if union_conditions != "Or()": # i.e. Empty table
		ans, checktime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
		print(model)
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time
	else:
		model = ""
		ans = False
		return ans, model, data_time, upd_time, simplification_time, checktime+domain_time

def homomorphism(query=[("1","1",""),("1","2","")], query_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", data_summary=["1","2"], column_names=["n1","n2", "condition"], split_merge=False, simplification=True, variable_clousre=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int"):

	groups = [query]
	if (variable_clousre):
		groups = closure_group.getAllClosureGroups(query)
	ans, total_data_time, total_upd_time, total_simplification_time, total_checktime = False, 0, 0, {'contradiction': [0, 0], 'redundancy': [0, 0]}, 0
	for group in groups:
		if (split_merge):
			print() # code for split merge
		else:
			substituted_tableau = tableau.summary_substitutions(query, query_summary, data_summary)
			sql = tableau.general_convert_tableau_to_sql(substituted_tableau, data_instance_table, data_summary, column_names)
			print(sql)
			ans, model, data_time, upd_time, simplification_time, checktime = faure_valuation(sql, domain, storage_types, reasoning_type, OUTPUT_TABLE_NAME, simplification)
			total_data_time += data_time
			total_upd_time += upd_time
			total_simplification_time["contradiction"][0] += simplification_time["contradiction"][0]
			total_simplification_time["contradiction"][1] += simplification_time["contradiction"][1]
			total_simplification_time["redundancy"][0] += simplification_time["redundancy"][0]
			total_simplification_time["redundancy"][1] += simplification_time["redundancy"][1]
			total_checktime += total_checktime
			if (ans == False):
				return ans, model, total_data_time, total_upd_time, total_simplification_time, total_checktime
	return ans, "", total_data_time, total_upd_time, total_simplification_time, total_checktime
	
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

def homomorphism_test(query=[("1","1",""),("1","2","")], query_summary=["1","2"], domain={"u":["1","2"], "v":["1","2"]}, data_instance_table="T_p", data_summary=["1","2"], column_names=["n1","n2", "condition"], split_merge=False, simplification=True, variable_clousre=False, storage_types=["int4_faure","int4_faure"], reasoning_type="Int", data_instance=[("1","u",""),("u","v",""),("v","2",""), ("1","1",""), ("u","u",""), ("v","v","")]):

	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session()
	cursor = conn.cursor()
	load_table(data_instance_table, data_instance, column_names, storage_types, cursor)
	ans, model, data_time, upd_time, simplification_time, checktime = homomorphism(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge, simplification, variable_clousre, storage_types, reasoning_type)
	cursor.execute("DROP TABLE IF EXISTS {};".format(data_instance_table))
	conn.commit()
	return ans, model, data_time, upd_time, simplification_time, checktime


if __name__ == "__main__":
	query_summary=["1","2"] 
	domain={"u":["1","2"], "v":["1","2"]}
	data_summary=["1","2"]
	column_names=["n1","n2", "condition"]
	split_merge=False
	simplification=True
	variable_clousre=True
	storage_types=["int4_faure","int4_faure"]
	reasoning_type="Int"
	T_v = [
		("1","1",""),
		("1","2","")
	]

	T_p = [
		("1","u",""),
		("u","v",""),
		("v","2",""), 
		("1","1",""), 
		("u","u",""), 
		("v","v","")
	]
	T_v_prime = [
		("1","2","")
	]

	T_p_prime = [
		("1","u",""),
		("u","v",""),
		("v","2",""), 
	]

	query = T_v
	data_instance_table="T_p"
	data_instance=T_p


	print(homomorphism_test(query, query_summary, domain, data_instance_table, data_summary, column_names, split_merge, simplification, variable_clousre, storage_types, reasoning_type, data_instance))