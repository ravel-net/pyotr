import time
from pybatfish.client.session import Session  # noqa: F401
# noinspection PyUnresolvedReferences
from pybatfish.datamodel import Edge, Interface  # noqa: F401
from pybatfish.datamodel.answer import TableAnswer
from pybatfish.datamodel.flow import HeaderConstraints, PathConstraints  # noqa: F401
# %run startup.py

bf = Session(host="localhost")

def NAT_reachability(network_name, topo_dir, dests):
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    snap_start = time.time()
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)
    snap_end = time.time()
    source_node = 1
    final_ans = False
    time_eval = 0
    for dest in dests:
        print("dest", dest)
        eval_start = time.time()
        #result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/{}/'.format(dest), srcPorts=53, dstPorts=53, ipProtocols='UDP', applications='DNS'), actions='SUCCESS', ignoreFilters=False).answer(BASE_SNAPSHOT_NAME).frame()
        result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/{}/'.format(dest)), actions='SUCCESS', ignoreFilters=False).answer(BASE_SNAPSHOT_NAME).frame()
        eval_end = time.time()
        time_spent = eval_end-eval_start
        time_eval += time_spent
        forbidden_source = ("node: source2" in str(result.Traces[1][0][0]))
        forbidden_dest = ("node: dest2" in str(result.Traces[1][0][-1]))
        print(result.Flow)
        print((forbidden_source and forbidden_dest))
        final_ans = (forbidden_source and forbidden_dest) | final_ans
    return final_ans, time_eval, snap_end-snap_start

def no_failure(network_name, topo_dir, backup_links):
    # Assign a friendly name to your network and snapshot
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)
    # no failure
    # Fork a new snapshot with backup links inactive
    LINKS_INACTIVE_SNAPSHOT_NAME = "two_b_links_inactive"
    
    interfaces = []
    for link in backup_links:
        routers = link.keys()
        for r in routers:
            intf = Interface(hostname="r_{}".format(r), interface="Ethernet{}".format(link[r]))
            interfaces.append(intf)
    begin_snap = time.time()
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, LINKS_INACTIVE_SNAPSHOT_NAME, deactivate_interfaces=interfaces, overwrite=True)
    end_snap = time.time()

    begin_no_failures = time.time()
    # result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/dest/'), actions='SUCCESS').answer(LINKS_INACTIVE_SNAPSHOT_NAME).frame()
    result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/dest/', srcPorts=53, dstPorts=53, ipProtocols='UDP', applications='DNS'), actions='SUCCESS', ignoreFilters=False).answer(LINKS_INACTIVE_SNAPSHOT_NAME).frame()
    end_no_failures = time.time()
    return result.Flow, end_no_failures-begin_no_failures, end_snap-begin_snap

def one_link_fails(network_name, topo_dir, fail_link, backup_link):
    # Assign a friendly name to your network and snapshot
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)
    # one failure
    # Fork a new snapshot with backup links inactive
    LINKS_INACTIVE_SNAPSHOT_NAME = "one_link_inactive"
    
    interfaces = []
    b_routers = backup_link.keys()
    for r in b_routers:
        intf = Interface(hostname="r_{}".format(r), interface="Ethernet{}".format(backup_link[r]))
        interfaces.append(intf)
    f_routers = fail_link.keys()
    for r in f_routers:
        intf = Interface(hostname="r_{}".format(r), interface="Ethernet{}".format(fail_link[r]))
        interfaces.append(intf)
    
    begin_snap = time.time()
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, LINKS_INACTIVE_SNAPSHOT_NAME, deactivate_interfaces=interfaces, overwrite=True)
    end_snap = time.time()

    begin_one_failure = time.time()
    result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/dest/', srcPorts=53, dstPorts=53, ipProtocols='UDP', applications='DNS'), actions='SUCCESS', ignoreFilters=False).answer(LINKS_INACTIVE_SNAPSHOT_NAME).frame()
    end_one_failure = time.time()
    return result.Flow, end_one_failure-begin_one_failure, end_snap-begin_snap

def two_failures(network_name, topo_dir, fail_links):
    # Assign a friendly name to your network and snapshot
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)
    # two failures
    # Fork a new snapshot with backup links inactive
    LINKS_INACTIVE_SNAPSHOT_NAME = "two_b_links_inactive"
    
    interfaces = []
    for link in fail_links:
        routers = link.keys()
        for r in routers:
            intf = Interface(hostname="r_{}".format(r), interface="Ethernet{}".format(link[r]))
            interfaces.append(intf)
    
    begin_snap = time.time()
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, LINKS_INACTIVE_SNAPSHOT_NAME, deactivate_interfaces=interfaces, overwrite=True)
    end_snap = time.time()
    begin_two_failures = time.time()
    result = bf.q.reachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/dest/', srcPorts=53, dstPorts=53, ipProtocols='UDP', applications='DNS'), actions='SUCCESS', ignoreFilters=False).answer(LINKS_INACTIVE_SNAPSHOT_NAME).frame()
    end_two_failures = time.time()
    return result.Flow, end_two_failures-begin_two_failures, end_snap-begin_snap

def differentialAnalysis(network_name, topo_dir, fail_links, backup_links):
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)

    interfaces = []
    for router in backup_links:
        for eth in backup_links[router]:
            intf = Interface(hostname="r_{}".format(router), interface="Ethernet{}".format(eth))
            interfaces.append(intf)    
    BASE_SNAPSHOT_NO_BACKUP_NAME = network_name+"NO_BACKUP"
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, BASE_SNAPSHOT_NO_BACKUP_NAME, deactivate_interfaces=interfaces, overwrite=True)

    interfaces = []
    for router in fail_links:
        for eth in fail_links[router]:
            intf = Interface(hostname="r_{}".format(router), interface="Ethernet{}".format(eth))
            interfaces.append(intf)

    # Fork a new snapshot with selected backup links inactive
    LINKS_INACTIVE_SNAPSHOT_NAME = "b_links_inactive"
    begin_snap = time.time()
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, LINKS_INACTIVE_SNAPSHOT_NAME, deactivate_interfaces=interfaces, overwrite=True)
    end_snap = time.time()

    begin_failures = time.time()
    diff_reachability_answer = bf.q.differentialReachability(pathConstraints=PathConstraints(startLocation = '/source/'), headers=HeaderConstraints(dstIps='/dest/', srcPorts=53, dstPorts=53, ipProtocols='UDP', applications='DNS'), actions='SUCCESS', ignoreFilters=False).answer(snapshot=LINKS_INACTIVE_SNAPSHOT_NAME, reference_snapshot=BASE_SNAPSHOT_NO_BACKUP_NAME).frame()
    end_failures = time.time()
    answer = (len(diff_reachability_answer.Flow) == 0)
    print(diff_reachability_answer.Flow)
    return answer, end_failures-begin_failures, end_snap-begin_snap

def differentialAnalysisSubset(network_name, topo_dir, fail_links, backup_links, source, sink):
    BASE_NETWORK_NAME = network_name
    BASE_SNAPSHOT_NAME = network_name
    BASE_SNAPSHOT_PATH = topo_dir
    # Now create the network and initialize the snapshot
    bf.set_network(BASE_NETWORK_NAME)
    bf.init_snapshot(BASE_SNAPSHOT_PATH, name=BASE_SNAPSHOT_NAME, overwrite=True)
    interfaces = []
    for router in backup_links:
        for eth in backup_links[router]:
            intf = Interface(hostname="r_{}".format(router), interface="Ethernet{}".format(eth))
            interfaces.append(intf) 

    print(network_name, topo_dir, fail_links, backup_links, source, sink)
    BASE_SNAPSHOT_NO_BACKUP_NAME = network_name+"NO_BACKUP"
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, BASE_SNAPSHOT_NO_BACKUP_NAME, deactivate_interfaces=interfaces, overwrite=True)

    interfaces = []
    for router in fail_links:
        for eth in fail_links[router]:
            intf = Interface(hostname="r_{}".format(router), interface="Ethernet{}".format(eth))
            interfaces.append(intf)
    print(interfaces)
    # Fork a new snapshot with selected backup links inactive
    LINKS_INACTIVE_SNAPSHOT_NAME = "b_links_inactive"
    begin_snap = time.time()
    bf.fork_snapshot(BASE_SNAPSHOT_NAME, LINKS_INACTIVE_SNAPSHOT_NAME, deactivate_interfaces=interfaces, overwrite=True)
    end_snap = time.time()
    begin_failures = time.time()
    snapshot_ref = BASE_SNAPSHOT_NO_BACKUP_NAME
    if 'source' in source:
        snapshot_ref = network_name
    # if 'source' in source:
    #     source = '/source1/'
    diff_reachability_answer1 = bf.q.differentialReachability(pathConstraints=PathConstraints(startLocation=source), headers=HeaderConstraints(srcIps='/source/', dstIps=sink), actions='SUCCESS', ignoreFilters=False).answer(snapshot=LINKS_INACTIVE_SNAPSHOT_NAME, reference_snapshot=snapshot_ref).frame()
    # if 'source' in source:
    #     source = '/source2/'
    # diff_reachability_answer2 = bf.q.differentialReachability(pathConstraints=PathConstraints(startLocation=source), headers=HeaderConstraints(srcIps='/source2/', dstIps=sink), actions='SUCCESS', ignoreFilters=False).answer(snapshot=LINKS_INACTIVE_SNAPSHOT_NAME, reference_snapshot=snapshot_ref).frame()
    # if 'source' in source:
    #     source = '/source3/'
    # diff_reachability_answer3 = bf.q.differentialReachability(pathConstraints=PathConstraints(startLocation=source), headers=HeaderConstraints(srcIps='/source3/', dstIps=sink), actions='SUCCESS', ignoreFilters=False).answer(snapshot=LINKS_INACTIVE_SNAPSHOT_NAME, reference_snapshot=snapshot_ref).frame()
    end_failures = time.time()
    answer1 = (len(diff_reachability_answer1.Flow) == 0)
    print(diff_reachability_answer1.Flow)
    return answer1, end_failures-begin_failures, end_snap-begin_snap

def compare_flows(flows1, flows2):
    begin_compare = time.time()
    if len(flows1) != len(flows2):
        return False, time.time() - begin_compare

    set1 = set()
    for flow in flows1:
        sd_pair = "{}->{}".format(flow.srcIp, flow.dstIp)
        set1.add(sd_pair)

    set2 = set()
    for flow in flows2:
        sd_pair = "{}->{}".format(flow.srcIp, flow.dstIp)
        set2.add(sd_pair)

    set3 = set1.difference(set2)
    if len(set3) == 0:
        return True, time.time() - begin_compare
    else:
        return False, time.time() - begin_compare


if __name__ == '__main__':
    network_name = 't1'
    topo_path = "./networks/t1"
    backup_links = [
        {'1':2, '2':2}, # dict(router: interface)
        {'2':3, 'w':2}
    ]
    primary_links = [
        {'1':1, 'u':0}, # dict(router: interface)
        {'2':1, 'v':0}
    ]
    backup_links2 = [
        {'1':2, 'v':2}, # dict(router: interface)
        {'2':3, 'w':2}
    ]
    flows1, time1 = no_failure('t1', './networks/t1', backup_links)
    flows2, time2 = no_failure('t2', './networks/t2', backup_links2)
    print(compare_flows(flows1, flows2))
