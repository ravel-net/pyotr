import performance 
import tableau_to_config
import sys
import psycopg2
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
sys.path.append(root)
import databaseconfig as cfg

def Merge(dict1, dict2):
    merged = {}
    for r in dict1:
        if r not in merged:
            merged[r] = []
        merged[r].append(dict1[r])
    for r in dict2:
        if r not in merged:
            merged[r] = []
        merged[r].append(dict2[r])
    return merged

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
        comparison_time = 0

        # no failures
        flow1_no_failure, time_config1_no_failure, time_snap1_config1 = performance.no_failure(config1['network_name'], config1['topo_dir'], config1['backup_links'])
        flow2_no_failure, time_config2_no_failure, time_snap1_config2 = performance.no_failure(config2['network_name'], config2['topo_dir'], config2['backup_links'])
        print('flow1', flow1_no_failure)
        print('flow2', flow2_no_failure)
        comp1, time_comp1 = performance.compare_flows(flow1_no_failure, flow2_no_failure)

        # one link fails
        flow1_one_link_fails, time_config1_one_link_fails, time_snap2_config1 = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['one_link_fails']['fail_link'], config1['one_link_fails']['backup_link'])
        flow2_one_link_fails, time_config2_one_link_fails, time_snap2_config2 = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['one_link_fails']['fail_link'], config2['one_link_fails']['backup_link'])
        print('flow1', flow1_one_link_fails)
        print('flow2', flow2_one_link_fails)
        comp2, time_comp2 = performance.compare_flows(flow1_one_link_fails, flow2_one_link_fails)

        # anther link fails
        flow1_another_link_fails, time_config1_another_link_fails, time_snap3_config1 = performance.one_link_fails(config1['network_name'], config1['topo_dir'], config1['another_link_fails']['fail_link'], config1['another_link_fails']['backup_link'])
        flow2_another_link_fails, time_config2_another_link_fails, time_snap3_config2 = performance.one_link_fails(config2['network_name'], config2['topo_dir'], config2['another_link_fails']['fail_link'], config2['another_link_fails']['backup_link'])
        print('flow1', flow1_another_link_fails)
        print('flow2', flow2_another_link_fails)
        comp3, time_comp3 = performance.compare_flows(flow1_another_link_fails, flow2_another_link_fails)

        # two links fail
        flow1_two_failures, time_config1_two_failures, time_snap4_config1 = performance.two_failures(config1['network_name'], config1['topo_dir'], config1['primary_links'])
        flow2_two_failures, time_config2_two_failures, time_snap4_config2 = performance.two_failures(config2['network_name'], config2['topo_dir'], config2['primary_links'])
        print('flow1', flow1_two_failures)
        print('flow2', flow2_two_failures)
        comp4, time_comp4 = performance.compare_flows(flow1_two_failures, flow2_two_failures)

        total_time = time_config1_no_failure + time_config2_no_failure + time_config1_one_link_fails + time_config2_one_link_fails + time_config1_another_link_fails + time_config2_another_link_fails + time_config1_two_failures + time_config2_two_failures + time_comp1 + time_comp2 + time_comp3 + time_comp4 + time_snap1_config1+time_snap2_config1+time_snap3_config1+time_snap4_config1+time_snap1_config2+time_snap2_config2+time_snap3_config2+time_snap4_config2
        is_equal = comp1 and comp2 and comp3 and comp4

        f = open("result.txt", "a")
        f.write("topo1|topo2||runtime|is_equal\n")
        f.write("{}|{}|{}|{}\n".format(config1['network_name'], config2['network_name'], total_time, is_equal))
        f.close()

        times = {"comparison":time_comp1+time_comp2+time_comp3+time_comp4, "snap1_eval":time_config1_no_failure+time_config2_no_failure, "snap2_eval":time_config1_one_link_fails+time_config2_one_link_fails, "snap3_eval":time_config1_another_link_fails+time_config2_another_link_fails, "snap4_eval":time_config1_two_failures+time_config2_two_failures, "removing_interfaces":time_snap1_config1+time_snap2_config1+time_snap3_config1+time_snap4_config1+time_snap1_config2+time_snap2_config2+time_snap3_config2+time_snap4_config2, "total_time":total_time}
        return times, is_equal

def getBackupNode(primary, backup):
    primary_nodes = []
    for node in primary:
        primary_nodes.append(node)
    for node in backup:
        if node not in primary_nodes:
            return "r_"+str(node)

def runBatfishDiffer(config):
    answer1, time_eval1, time_snap1 = performance.differentialAnalysis(config['network_name'], config['topo_dir'], Merge(config['primary_links'][0], {}), Merge(config['backup_links'][0],config['backup_links'][1]))
    print(answer1, config['primary_links'][0])
    answer2, time_eval2, time_snap2 = performance.differentialAnalysis(config['network_name'], config['topo_dir'], Merge(config['primary_links'][1], {}), Merge(config['backup_links'][0],config['backup_links'][1]))
    print(answer2, config['primary_links'][1])
    answer3, time_eval3, time_snap3 = performance.differentialAnalysis(config['network_name'], config['topo_dir'], Merge(config['primary_links'][0],config['primary_links'][1]),  Merge(config['backup_links'][0],config['backup_links'][1]))
    print(answer3, Merge(config['primary_links'][0],config['primary_links'][1]))
    return time_eval1+time_eval2+time_eval3, time_snap1+time_snap2+time_snap3, (answer1 and answer2 and answer3)

def runBatfishDifferSubset(config):
    sink = getBackupNode(config['primary_links'][0], config['backup_links'][0])
    answer1, time_eval1, time_snap1 = performance.differentialAnalysisSubset(config['network_name'], config['topo_dir'], Merge(config['primary_links'][0], {}), Merge(config['backup_links'][0],config['backup_links'][1]), sink)
    return time_eval1, time_snap1, answer1

def runReachability(config):
    answer, total_eval_time, total_snap_time = performance.NAT_reachability(config['network_name'], config['topo_dir'], config["dests"])
    destinations_num = len(config["dests"])
    return total_eval_time, total_snap_time, (total_eval_time+total_snap_time), answer

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
    return tableau

def equivalence_link_failures(tableau_db_name_1, tableau_db_name_2):
    tableau1 = getTableau(tableau_db_name_1)
    tableau2 = getTableau(tableau_db_name_2)
    failure_config1 = tableau_to_config.getAndStoreConfiguration(tableau1, tableau_db_name_1, [tableau[-4][tableau_to_config.SOURCE_ID],tableau[-4][tableau_to_config.SOURCE_ID], tableau[-4][tableau_to_config.SOURCE_ID]])
    failure_config2 = tableau_to_config.getAndStoreConfiguration(tableau2, tableau_db_name_2, [tableau[-4][tableau_to_config.SOURCE_ID],tableau[-4][tableau_to_config.SOURCE_ID], tableau[-4][tableau_to_config.SOURCE_ID]])
    # print(failure_config1)
    # print(failure_config2)
    return(runBatfish(failure_config1, failure_config2))

def differentialLinkFailure(tableau_db_name, source, dest):
    tableau = getTableau(tableau_db_name)
    failure_config = tableau_to_config.getAndStoreConfiguration(tableau, tableau_db_name, [source,source], [dest, dest], False)
    print(failure_config)
    return runBatfishDiffer(failure_config)

def differentialLinkFailureSubset(tableau_db_name, source, dest):
    tableau = getTableau(tableau_db_name)
    failure_config = tableau_to_config.getAndStoreConfiguration(tableau, tableau_db_name, [source,source, source], [dest], False)
    print(failure_config)
    return runBatfishDifferSubset(failure_config)

def NATAttack(tableau_db_name, source, dest, num_source, num_dest):
    tableau_full = getTableau(tableau_db_name)
    # Remove firewallID and conditions
    tableau = []
    for link in tableau_full:
        curr_tuple = (link[tableau_to_config.SOURCE_ID], link[tableau_to_config.DEST_ID], "", "")
        tableau.append(curr_tuple)
    sources = []
    dests = []
    for i in range(num_source):
        sources.append(source)
    for i in range(num_dest):
        dests.append(dest)
    NAT_config = tableau_to_config.getAndStoreConfiguration(tableau, tableau_db_name, sources, dests, True)
    return runReachability(NAT_config)

if __name__ == "__main__":
    T1 = [
        ("1","20","123", "l1u == 1"),
        ("20","2","", ""),
        ("1","2","", "l1u == 0"), 
        ("2","30","1321", "l2v == 1"), 
        ("30","40","", ""), 
        ("2","40","1321", "l2v == 0")
    ]

    Invariant2 = [
        ("1","20","", ""),
        ("20","2","", ""),
    ]

    # Example = [
    #     ("1","u","", ""),
    #     ("u","2","", ""),
    #     ("1","2","", ""), 
    #     ("2","v","", ""), 
    #     ("v","w","", ""), 
    #     ("2","w","", "")
    # ] 

    T4 = [
        ("1","2","123", "x == 1"),
        ("1","30","123", "x == 0"), 
        ("2","30","", "y == 1"), 
        ("30","40","1321", ""), 
        ("2","40","1321", "y == 0")
    ]   
    
    add_Tableau(T1, "T1")
    # print(NATAttack("Invariant2", int(Invariant2[0][tableau_to_config.SOURCE_ID]), int(Invariant2[-1][tableau_to_config.DEST_ID]), 3, 4))
    # print(equivalence_link_failures("T_1", "T_4"))
    print(differentialLinkFailureSubset("T1", int(T1[0][tableau_to_config.SOURCE_ID]), int(T1[-1][tableau_to_config.DEST_ID])))
    # print(equivalence_link_failures("fwd_4755", "fwd_4755_diff"))
