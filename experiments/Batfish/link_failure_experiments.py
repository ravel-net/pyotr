import sys
import psycopg2
import tableau_to_config
import run_batfish as run_batfish
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import databaseconfig as cfg
import experiments.gen_large_tableau.gen_tableau_script as gen_tableau_script
import shutil

def getFirewalls(old_table):
	firewalls = []
	for link in old_table:
		if (len(link[tableau_to_config.FIREWALL_ID]) > 0):
			firewall = old_table[tableau_to_config.FIREWALL_ID][0]
			firewalls.append(firewall)
	return firewalls

# Switch the firewall policies so that network equivalence does not hold under failure
def changeFirewalls(table="fwd_4755", final_name=""):
	conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
	conn.set_session(readonly=False, autocommit=True)
	cursor = conn.cursor()
	if final_name == "":
		final_name = table+"_diff"
	cursor.execute("DROP TABLE IF EXISTS {};".format(final_name))
	cursor.execute("create table {} (n1 integer, n2 integer, s text[], condition text[]);".format(final_name))

	cursor.execute('select * from {};'.format(table))
	old_table = cursor.fetchall()
	firewalls = getFirewalls(old_table)
	switched = []
	for link in old_table:
		firewall = tableau_to_config.EMPTY_FIREWALL
		new_firewall = 0
		if (len(link[tableau_to_config.FIREWALL_ID]) > 0):
			firewall = str(link[tableau_to_config.FIREWALL_ID][0]) #TODO: Assuming single firewall
			if firewall in switched:
				new_firewall = 1
			else:
				new_firewall = 2
				switched.append(firewall)
		cursor.execute("insert into {} values('{}', '{}');".format(final_name, link[0], link[1]))
		if new_firewall != 0:
			cursor.execute("update {} set s = array_append(s, '{}') where n1 = {} and n2 = {};".format(final_name, new_firewall, link[0], link[1]))
		else:
			cursor.execute("update {} set s = array_append(s, '{}') where n1 = {} and n2 = {};".format(final_name, '', link[0], link[1]))
		if len(link[2]) > 0:
			cursor.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {};".format(final_name, link[3][0], link[0], link[1]))
		else:
			cursor.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {};".format(final_name, '', link[0], link[1]))

	conn.commit()
	conn.close()
	return final_name

# Given a tableau stored in postgres with two link failures, returns the time taken for evaluation and the answer
def equivalence_batfish(table="fwd_4755"):
	new_table_name = changeFirewalls(table)
	return run_batfish.equivalence_link_failures(table, new_table_name)

def genTableau(topo=4755, pick_num=2):
    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(topo)

    as_tablename = 'as_{}'.format(topo)
    topo_tablename = "topo_{}".format(topo)
    fwd_tablename = "fwd_{}".format(topo)

    success = gen_tableau_script.gen_tableau_for_link_failures(file_dir, filename, as_tablename, topo_tablename, fwd_tablename, pick_num)
    if success[0]:
    	source = success[1]
    	dest = success[2]
    	length = success[3]
    	return fwd_tablename, source, dest, length
    else:
    	return "","", "", ""

# if __name__ == '__main__':
# 	topos = [4755]
# 	num_runs = 1
# 	for topo in topos:
# 		comparison_time = 0
# 		snap1_eval_time = 0
# 		snap2_eval_time = 0
# 		snap3_eval_time = 0
# 		snap4_eval_time = 0
# 		removing_interfaces_time = 0
# 		total_time = 0
# 		for i in range(num_runs):
# 			fwd_name = genTableau(topo)
# 			times, answer = equivalence_batfish(fwd_name)
# 			comparison_time += times["comparison"]
# 			snap1_eval_time += times["snap1_eval"]
# 			snap2_eval_time += times["snap2_eval"]
# 			snap3_eval_time += times["snap3_eval"]
# 			snap4_eval_time += times["snap4_eval"]
# 			removing_interfaces_time += times["removing_interfaces"]
# 			total_time += times["total_time"]
# 		total_times = {"comparison":comparison_time/num_runs, "snap1_eval":snap1_eval_time/num_runs, "snap2_eval":snap2_eval_time/num_runs, "snap3_eval":snap3_eval_time/num_runs, "snap4_eval":snap4_eval_time/num_runs, "removing_interfaces":removing_interfaces_time/num_runs, "total_time":total_time/num_runs}
# 			print(answer)
# 		print(total_times)

if __name__ == '__main__':
	topos = [7018]
	num_runs = 1
	f = open("result_single_link.csv", "a")
	f.write("topo,length,eval_time,snap_time,total_time\n")
	for topo in topos:
		run = 0
		while run < num_runs:
			result = genTableau(topo)
			length = result[3]
			fwd_name = result[0]
			if fwd_name == "":
				continue
			# eval_time, snap_time, answer = run_batfish.differentialLinkFailure(fwd_name, result[1], result[2])
			eval_time, snap_time, answer = run_batfish.differentialLinkFailureSubset(fwd_name, result[1], result[2])
			shutil.rmtree(fwd_name)
			if (answer):
				print("Answer", answer)
			run += 1
			f.write("{},{},{},{},{}\n".format(topo, length, eval_time, snap_time, eval_time+snap_time))
			print("{},{},{},{},{}\n".format(topo, length, eval_time, snap_time, eval_time+snap_time))
	f.close()
