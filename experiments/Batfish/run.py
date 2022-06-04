import performance 
import tableau_to_config
import sys
import psycopg2
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import databaseconfig as cfg

def add_Tableau(tableau, tableau_name):
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(readonly=False, autocommit=True)
    cursor = conn.cursor()
    cursor.execute("DROP TABLE IF EXISTS {};".format(tableau_name))
    cursor.execute("create table {} (n1 integer, n2 integer, s text[], condition text[]);".format(tableau_name))
    for link in tableau:
        cursor.execute("insert into {} values('{}', '{}');".format(tableau_name, link[0], link[1]))
        # if link[2] != "":
        cursor.execute("update {} set s = array_append(s, '{}') where n1 = {} and n2 = {};".format(tableau_name, link[2], link[0], link[1]))
        # else:
        #     a = '{}'
        #     cursor.execute("update {} set s = array_append(s, '{}') where n1 = {} and n2 = {};".format(tableau_name, a, link[0], link[1]))
        cursor.execute("update {} set condition = array_append(condition, '{}') where n1 = {} and n2 = {};".format(tableau_name, link[3], link[0], link[1]))

def runBatfish(config1, config2):
        # no failures
        flow1_no_failure, time_config1_no_failure = performance.no_failure(config1['network_name'], config1['topo_dir'], config1['backup_links'])
        flow2_no_failure, time_config2_no_failure = performance.no_failure(config2['network_name'], config2['topo_dir'], config2['backup_links'])
        print('flow1', flow1_no_failure)
        print('flow2', flow2_no_failure)
        comp1, time_comp1 = performance.compare_flows(flow1_no_failure, flow2_no_failure)

        # one link fails
        flow1_one_link_fails, time_config1_one_link_fails = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['one_link_fails']['fail_link'], config1['one_link_fails']['backup_link'])
        flow2_one_link_fails, time_config2_one_link_fails = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['one_link_fails']['fail_link'], config2['one_link_fails']['backup_link'])
        print('flow1', flow1_one_link_fails)
        print('flow2', flow2_one_link_fails)
        comp2, time_comp2 = performance.compare_flows(flow1_one_link_fails, flow2_one_link_fails)

        # anther link fails
        flow1_another_link_fails, time_config1_another_link_fails = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['another_link_fails']['fail_link'], config1['another_link_fails']['backup_link'])
        flow2_another_link_fails, time_config2_another_link_fails = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['another_link_fails']['fail_link'], config2['another_link_fails']['backup_link'])
        print('flow1', flow1_another_link_fails)
        print('flow2', flow2_another_link_fails)
        comp3, time_comp3 = performance.compare_flows(flow1_another_link_fails, flow2_another_link_fails)

        # two links fail
        flow1_two_failures, time_config1_two_failures = performance.two_failures(config1['network_name'], config1['topo_dir'], config1['primary_links'])
        flow2_two_failures, time_config2_two_failures = performance.two_failures(config2['network_name'], config2['topo_dir'], config2['primary_links'])
        print('flow1', flow1_two_failures)
        print('flow2', flow2_two_failures)
        comp4, time_comp4 = performance.compare_flows(flow1_two_failures, flow2_two_failures)

        total_time = time_config1_no_failure + time_config2_no_failure + time_config1_one_link_fails + time_config2_one_link_fails + time_config1_another_link_fails + time_config2_another_link_fails + time_config1_two_failures + time_config2_two_failures + time_comp1 + time_comp2 + time_comp3 + time_comp4
        is_equal = comp1 and comp2 and comp3 and comp4

        f = open("result.txt", "a")
        f.write("topo1|topo2||runtime|is_equal\n")
        f.write("t{}|t{}|{}|{}\n".format(config1['network_name'], config2['network_name'], total_time, is_equal))
        f.close()
        return total_time

def getCurrentTable(tablename, cur):
    cur.execute('select * from {};'.format(tablename))
    return cur.fetchall()

def getTableau(tableau_db_name):
    conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    conn.set_session(readonly=False, autocommit=True)
    cursor = conn.cursor()
    tableau = getCurrentTable(tableau_db_name, cursor)
    conn.commit()
    conn.close()
    print(tableau)
    return tableau

def equivalence_link_failures(tableau_db_name_1, tableau_db_name_2):
    tableau1 = getTableau(tableau_db_name_1)
    tableau2 = getTableau(tableau_db_name_2)
    failure_config1 = tableau_to_config.getAndStoreConfiguration(tableau1, tableau_db_name_1)
    failure_config2 = tableau_to_config.getAndStoreConfiguration(tableau2, tableau_db_name_2)
    print(failure_config1)
    print(failure_config2)
    total_time = runBatfish(failure_config1, failure_config2)
    return total_time

if __name__ == "__main__":
    T1 = [
        ("1","20","123", "l1u == 1"),
        ("20","2","", ""),
        ("1","2","123", "l1u == 0"), 
        ("2","30","1321", "l2v == 1"), 
        ("30","40","", ""), 
        ("2","40","1321", "l2v == 0")
    ]

    T4 = [
        ("1","2","123", "x == 1"),
        ("1","30","123", "x == 0"), 
        ("2","30","", "y == 1"), 
        ("30","40","1321", ""), 
        ("2","40","1321", "y == 0")
    ]   
    
    add_Tableau(T1, "T_1")
    add_Tableau(T4, "T_4")
    print(equivalence_link_failures("T_1", "T_4"))