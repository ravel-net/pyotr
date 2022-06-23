import random
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import psycopg2
from psycopg2.extras import execute_values
import Applications.Chase.chase as chase
import databaseconfig as cfg
import experiments.gen_large_tableau.gen_tableau_script as gen_tableau_script
import experiments.gen_large_tableau.func_gen_tableau as func_gen_tableau

conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
cursor = conn.cursor()

def apply_distributed_invariants_dependencies():
    return

def gen_rewrite_dependencies(path_nodes, block_list, ingress_hosts, egress_hosts, symbolic_IP_mapping):
    """
    generate rewrite dependencies. A rewrite policy includes two dependencies, one is tgd, another one is egd.

    Parameters:
    -----------
    path_nodes: list
        the list of nodes who forms the path

    block_list: tuple
        the block list

    ingress_hosts: list
        A list of IP addresses that corresponding to a list of hosts connected to the begin of the path.
    
    egress_hosts: list
        A list of IP addresses that corresponding to a list of hosts connected to the end of the path.

    symbolic_IP_mapping: dict
        the mapping between symbolic integers and real IP addresses.
    
    Returns:
    --------
    rewrite_dependencies: dict[index:dependency]
        a list of rewrite dependencies.
    
    relevant_in_hosts: list
        a list of IP address related to the block list
    
    relevant_out_hosts: list
        a list of IP address related to the block list
    """
    #random set rewrite location
    # picked_nodes = random.sample(path_nodes, 2)
    # node1 = picked_nodes[0]
    # node2 = picked_nodes[1]
    # idx_node1 = path_nodes.index(picked_nodes[0])
    # idx_node2 = path_nodes.index(picked_nodes[1])

    # if idx_node1 > idx_node2:
    #     temp = idx_node1 
    #     idx_node1 = idx_node2
    #     idx_node2 = temp

    #     temp = node1
    #     node1 = node2
    #     node2 = temp

    # set rewrite location at first node and last node
    node1 = path_nodes[0]
    node2 = path_nodes[-1]
    idx_node1 = path_nodes.index(node1)
    idx_node2 = path_nodes.index(node2)

    relevant_in_hosts = []
    relevant_out_hosts = []
    rewrite_dependencies = {}

    s_IP = block_list[0]
    relevant_in_hosts.append(s_IP)

    egress_hosts.remove(block_list[1]) 
    # print("after deleting egress", egress_hosts)
    d_IP = random.sample(egress_hosts, 1)[0]
    relevant_out_hosts.append(d_IP)

    ingress_hosts.remove(block_list[0])
    # print("after deleting ingress", ingress_hosts)
    rewrite_src = random.sample(ingress_hosts, 1)[0]
    rewrite_value = {"source": rewrite_src, 'dest':None}

    relevant_in_hosts.append(rewrite_src)

    tgd1, egd1 = convert_rewrite_policy_to_dependency(s_IP, d_IP, rewrite_value, idx_node1, path_nodes, symbolic_IP_mapping)

    # rewrite dest to end node of block_list
    rewrite_value = {"source": None, 'dest':block_list[1]}
    s_IP = rewrite_src
    relevant_out_hosts.append(block_list[1])
    tgd2, egd2 = convert_rewrite_policy_to_dependency(s_IP, d_IP, rewrite_value, idx_node2, path_nodes, symbolic_IP_mapping)

    rewrite_dependencies[1] = tgd1
    rewrite_dependencies[2] = egd1
    rewrite_dependencies[3] = tgd2
    rewrite_dependencies[4] = egd2

    return rewrite_dependencies, relevant_in_hosts, relevant_out_hosts
    
def convert_rewrite_policy_to_dependency(source, dest, rewrite_value, loc, path_nodes, symbolic_IP_mapping):
    tgd_tuples = []
    egd_tuples = []
    node = path_nodes[loc]
    x_IP = symbolic_IP_mapping[node]
    # n_IP = symbolic_IP_mapping[node]

    prev_node = None
    if loc == 0:
        prev_node = source
    else:
        prev_node = symbolic_IP_mapping[path_nodes[loc-1]]
    
    next_node = None
    if loc == len(path_nodes)-1:
        next_node = dest
    else:
        next_node = symbolic_IP_mapping[path_nodes[loc+1]]
    
    tgd_tuples.append(('f', source, dest, prev_node, x_IP, '{}'))
    # tgd_tuples.append(('f', source, dest, n_IP, next_node, '{}'))
    egd_tuples.append(('f1', source, dest, 'n1', '{}'))

    tgd_summary = None
    for key in rewrite_value.keys():
        if key == 'source' and rewrite_value[key] is not None:
            source = rewrite_value[key]
        elif key == 'dest' and rewrite_value[key] is not None:
            dest = rewrite_value[key]
    tgd_summary = ['f', source, dest, prev_node, x_IP]
    # tgd_summary = ['f', source, dest, n_IP, next_node]
    egd_tuples.append(('f2', source, dest, 'n2', '{}'))

    tgd_summary_condition = None
    tgd_type = 'tgd'

    tdg_dependency = {
        "dependency_tuples": tgd_tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'x', 'condition'],
        "dependency_attributes_datatypes": ["inet_faure", "inet_faure", "inet_faure", "inet_faure", "inet_faure", "text[]"], 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": tgd_summary,
        "dependency_summary_condition": tgd_summary_condition,
        "dependency_type": tgd_type
    }

    egd_summary = ['f1 = f2']
    egd_summary_condition = ["n1 <= '{}'".format(x_IP), "n2 <= '{}'".format(x_IP)]
    # egd_summary_condition = ["n1 <= '{}'".format(n_IP), "n2 <= '{}'".format(n_IP)]
    # if pre_rewrite_loc is not None:
    #     pre_rewite_node_IP = symbolic_IP_mapping[path_nodes[pre_rewrite_loc]]
    #     egd_summary_condition += ["n1 >= '{}'".format(pre_rewite_node_IP), "n2 >= '{}'".format(pre_rewite_node_IP)]

    egd_type = 'egd'
    edg_dependency = {
        "dependency_tuples": egd_tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'condition'],
        "dependency_attributes_datatypes": ["inet_faure", "inet_faure", "inet_faure", "inet_faure", "text[]"], 
        "dependency_cares_attributes": ['src', 'dst'],
        "dependency_summary": egd_summary,
        "dependency_summary_condition": egd_summary_condition,
        "dependency_type": egd_type
    }

    return tdg_dependency, edg_dependency

def gen_forwarding_dependency(forwarding_attributes, forwarding_datatypes):
    """
    Generate forwarding dependency

    Parameters:
    -----------
    forwarding_attributes: list
        the attributes of forwarding dependency
    
    forwarding_datatypes: list
        the datatypes of attributes of forwarding dependency

    Returns:
    --------
    egd_dependency: dict
        the forwarding dependency
    
    """
    forwarding_tuples = [
        ('f', 's1', 'd1', '{}'),
        ('f', 's2', 'd2', '{}')
    ]

    forwarding_summary = ['s1 = s2', 'd1 = d2']
    edg_dependency = {
        "dependency_tuples": forwarding_tuples,
        "dependency_attributes": forwarding_attributes,
        "dependency_attributes_datatypes": forwarding_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst'],
        "dependency_summary": forwarding_summary,
        "dependency_summary_condition": None,
        "dependency_type": 'egd'
    }

    return edg_dependency

def gen_firewall_dependency(block_list, firewall_attributes, firewall_datatypes):
    """
    generate firewall dependency

    Parameters:
    -----------
    block_list: tuple
        the blocklist. block source to dest.
    
    firewall_atributes: list
        the attributes of firewall dependency
    
    firewall_datatypes: list
        the datatypes of the attributes of firewall dependency

    Returns:
    --------
    egd_dependency: dict
        the firewall dependency
    
    """
    firewall_tuples = [
        ('f', 's', 'd', 'n', 'x', '{}')
    ]

    firewall_summary = []
    firewall_summary_condition = ["s = '{}'".format(block_list[0]), "d = '{}'".format(block_list[1])]
    edg_dependency = {
        "dependency_tuples": firewall_tuples,
        "dependency_attributes": firewall_attributes,
        "dependency_attributes_datatypes": firewall_datatypes, 
        "dependency_cares_attributes": ['src', 'dst'],
        "dependency_summary": firewall_summary,
        "dependency_summary_condition": firewall_summary_condition,
        "dependency_type": 'egd'
    }

    return edg_dependency

def gen_gamma_table(block_list, in_hosts, out_hosts, gamma_tablename, gamma_attributes, gamma_datatypes, case):
    """ 
    generate whitelists for 'relevant' case

    Parameters:
    -----------
    block_list: tuple
        the block list

    in_hosts: list
        a list of IP address of ingress hosts
    
    out_hosts: list
        a list of IP address of egress hosts

    case: 'relevant'/'all'
        the flag to determine return all whitelists or relevant whitelists. 

    Returns:
    --------
    gamma_summary: list
        the summary of gamma table

    """
    whitelists_tuples = []
    count = 0
    for in_h in in_hosts:
        for out_h in out_hosts:
            if in_h == block_list[0] and out_h == block_list[1]:
                continue
            elif in_h != block_list[0] and out_h != block_list[1] and case == 'relevant': # when case = `relevant`, ignore this kind of whitelist
                continue
            else:
                whitelists_tuples.append(("f{}".format(count), in_h, out_h, '{}'))
                count += 1
    gamma_summary = ['f', block_list[0], block_list[1]]

    chase.load_table(gamma_attributes, gamma_datatypes, gamma_tablename, whitelists_tuples)

    return gamma_summary

def gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes):
    E_tuples, source, dest, path_nodes, symbolic_IP_mapping = gen_tableau_script.gen_tableau_for_distributed_invariants(file_dir, filename, as_tablename, topo_tablename)
    chase.load_table(E_attributes, E_datatypes, E_tablename, E_tuples)

    # ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
    # egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")

    return E_tuples, path_nodes, symbolic_IP_mapping

def gen_dependencies_for_chase_distributed_invariants(ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping):
    '''
    generate block list
    randomly pick one host from ingress hosts and one host from egress hosts
    '''
    in_block_node = random.sample(ingress_hosts, 1)[0]
    out_block_node = random.sample(egress_hosts, 1)[0]
    block_list = (in_block_node, out_block_node)
    # print("block_list", block_list)

    '''
    generate rewrite policies
    '''
    dependencies,relevant_in_hosts, relevant_out_hosts = gen_rewrite_dependencies(path_nodes, block_list, ingress_hosts, egress_hosts, symbolic_IP_mapping)
    # print("rewrite_dependencies", dependencies)

    # gen forwarding dependency
    forwarding_attributes = ['f', 'src', 'dst', 'condition']
    forwarding_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    forwarding_dependency = gen_forwarding_dependency(forwarding_attributes, forwarding_datatypes)
    # print("forwarding_dependency", forwarding_dependency)

    dependencies[0] = forwarding_dependency

    # gen firewall dependency
    firewall_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    firewall_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    firewall_dependency = gen_firewall_dependency(block_list, firewall_attributes, firewall_datatypes)
    # print("firewall_dependency", firewall_dependency)

    dependencies[5] = firewall_dependency

    return dependencies, relevant_in_hosts, relevant_out_hosts, block_list

def gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_attributes_datatypes):
    Z_tuples, gen_z_time = chase.gen_z(E_tuples, gamma_tablename)
    chase.load_table(Z_attributes, Z_attributes_datatypes, Z_tablename, Z_tuples)

    return Z_tuples, gen_z_time

def script_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes, num_hosts, case, Z_tablename, Z_attributes, Z_attributes_datatypes):
    f = open("./check_items/check.txt", "a")
    # generate topology
    E_tuples, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping = gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes, num_hosts)
    
    f.write("path_nodes = {}\n".format(path_nodes))
    f.write("symbolic_IP_mapping = {}\n".format(symbolic_IP_mapping))
    f.write("E_tuples = {}\n".format(E_tuples))
    f.write("ingress_hosts = {}\n".format(ingress_hosts))
    f.write("egress_hosts = {}\n".format(egress_hosts))

    # generate dependencies
    dependencies, relevant_in_hosts, relevant_out_hosts, block_list = gen_dependencies_for_chase_distributed_invariants(ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping)
    
    f.write("block_list = {}\n".format(block_list))
    f.write("dependencies = {}\n".format(dependencies))
    f.write("relevant_in_hosts = {}\n".format(relevant_in_hosts))
    f.write("relevant_out_hosts = {}\n".format(relevant_out_hosts))
    
    
    '''
    get whitelist
    case: relevant, all
    '''
    gamma_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    gamma_summary = None
    if case == 'relevant':
        gamma_summary = gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, "W", gamma_attributes, gamma_attributes_datatypes)
    elif case == 'all':
        gamma_summary = gen_gamma_table(block_list, ingress_hosts, egress_hosts, "W", gamma_attributes, gamma_attributes_datatypes)
    
    f.write("gamma_summary = {}\n".format(gamma_summary))
    f.write("----------------------------------------------------------\n")
    f.close()
    gamma_attributes_switch = {
        'f': True,
        'src': False,
        'dst': False,
        'n': True,
        'x': True,
    }

    # Step 1
    gen_z_time = gen_Z_for_chase_distributed_invariants(gamma_attributes, gamma_attributes_datatypes, gamma_attributes_switch, Z_tablename, Z_attributes, Z_attributes_datatypes)
    
    #step2 and step3
    run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary)

def run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary):

    ordered_indexs = sorted(list(dependencies.keys())) 
    checked_records = {} # record checked tuples
    for idx in ordered_indexs:
        checked_records[idx] = []

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, "temp")
    # print("query sql", query_sql)
    total_check_applicable_time = 0
    total_operation_time = 0
    total_check_answer_time = 0
    total_query_answer_time = 0 
    count_application = 0 # count the number of the application of the chase
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    total_query_times = 0
    # chase.applySourceDestPolicy(Z_tablename)
    current_run = 0
    while does_updated:
        temp_updated = False
        for idx in ordered_indexs:
            count_application += 1
            
            if current_run == 0 and idx == 0:
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.applySourceDestPolicy(Z_tablename)
                print("optimal", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)
            else:

                dependency = dependencies[idx]
                checked_tuples = checked_records[idx]
                
                # print("\n-------------------------------------")
                # print(dependency['dependency_type'])
                # print(dependency['dependency_tuples'])
                # print(dependency['dependency_attributes'])
                # print(dependency['dependency_attributes_datatypes'])
                # print(dependency['dependency_summary'])
                # print(dependency['dependency_summary_condition'])
                # print("-------------------------------------\n")
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.apply_dependency(dependency, Z_tablename, checked_tuples)
                print("optimal", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated
        current_run += 1

            # print("gamma_summary", gamma_summary)
    answer = None
    chase.convertToText(Z_tablename)
    answer, count_queries, query_time, check_time = chase.apply_E(query_sql, Z_tablename, gamma_summary)
    total_query_times += count_queries
    total_query_answer_time += query_time
    total_check_answer_time += check_time
    print("gamma_summary", gamma_summary)
    # answer, query_time, check_time = chase.apply_E(query_sql, gamma_summary)
    # total_query_answer_time += query_time
    # total_check_answer_time += check_time
    # print("optimal", count_application, answer)
    return answer, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times

def run_chase_distributed_invariants_in_random_repeating_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary):

    ordered_indexs = sorted(list(dependencies.keys())) 
    checked_records = {} # record checked tuples
    for idx in ordered_indexs:
        checked_records[idx] = []

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, "temp")
    # print("query sql", query_sql)
    total_check_applicable_time = 0
    total_operation_time = 0
    total_check_answer_time = 0
    total_query_answer_time = 0 
    count_application = 0 # count the number of the application of the chase
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    total_query_times = 0
    # chase.applySourceDestPolicy(Z_tablename)
    current_run = 0
    random.shuffle(ordered_indexs)
    while does_updated:
        temp_updated = False
        for idx in ordered_indexs:
            count_application += 1
            
            if current_run == 0 and idx == 0:
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.applySourceDestPolicy(Z_tablename)
                print("random_repeating", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)
            else:

                dependency = dependencies[idx]
                checked_tuples = checked_records[idx]
                # print("\n-------------------------------------")
                # print(dependency['dependency_type'])
                # print(dependency['dependency_tuples'])
                # print(dependency['dependency_attributes'])
                # print(dependency['dependency_attributes_datatypes'])
                # print(dependency['dependency_summary'])
                # print(dependency['dependency_summary_condition'])
                # print("-------------------------------------\n")
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.apply_dependency(dependency, Z_tablename, checked_tuples)
                print("random_repeating", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated
        current_run += 1

            # print("gamma_summary", gamma_summary)
    answer = None
    answer, count_queries, query_time, check_time = chase.apply_E(query_sql, Z_tablename, gamma_summary)
    total_query_times += count_queries
    total_query_answer_time += query_time
    total_check_answer_time += check_time
    # print("gamma_summary", gamma_summary)
    # answer, query_time, check_time = chase.apply_E(query_sql, gamma_summary)
    # total_query_answer_time += query_time
    # total_check_answer_time += check_time
    # print("optimal", count_application, answer)
    return answer, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times

def run_chase_distributed_invariants_in_random_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary):

    indexes = list(dependencies.keys())
    checked_records = {} # record checked tuples
    for idx in indexes:
        checked_records[idx] = []

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, "temp")
    # print("query sql", query_sql)
    total_check_applicable_time = 0
    total_operation_time = 0
    total_check_answer_time = 0
    total_query_answer_time = 0 
    count_application = 0 # count the number of the application of the chase
    total_query_times = 0
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    current_run = 0
    while does_updated:
        temp_updated = False
        temp_indexes = indexes.copy()
        # print("-----------------")
        while len(temp_indexes) > 0:
            count_application += 1
            
            idx = random.sample(temp_indexes, 1)[0]
            temp_indexes.remove(idx)

            if current_run == 0 and idx == 0: # the first time run the \sigma_{D} should call applySourceDestPolicy()
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.applySourceDestPolicy(Z_tablename)
                print("random", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)

            else:
                dependency = dependencies[idx]
                checked_tuples = checked_records[idx]
                
                # print("\n-------------------------------------")
                # print(dependency['dependency_type'])
                # print(dependency['dependency_tuples'])
                # print(dependency['dependency_attributes'])
                # print(dependency['dependency_attributes_datatypes'])
                # print(dependency['dependency_summary'])
                # print(dependency['dependency_summary_condition'])
                # print("-------------------------------------\n")
                checked_records[idx], whether_updated, check_valid_time, operate_time = chase.apply_dependency(dependency, Z_tablename, checked_tuples)
                print("random", count_application, whether_updated)
                total_check_applicable_time += check_valid_time
                total_operation_time += operate_time
                temp_updated = (temp_updated or whether_updated)
        current_run += 1
        does_updated = temp_updated
    answer = None
        # print("gamma_summary", gamma_summary)
    # answer, count_queries, query_time, check_time = chase.apply_E(query_sql, Z_tablename, gamma_summary)
    # total_query_times += count_queries
    # total_query_answer_time += query_time
    # total_check_answer_time += check_time
    # print("random", count_application, answer)
    # print("gamma_summary", gamma_summary)
    # ans, query_time, check_time = chase.apply_E(query_sql, gamma_summary)
    # total_query_answer_time += query_time
    # total_check_answer_time += check_time
    return answer, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times

def run_chase_distributed_invariants_in_static_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary):

    ordered_indexs = sorted(list(dependencies.keys())) 
    checked_records = {} # record checked tuples
    for idx in ordered_indexs:
        checked_records[idx] = []

    static_order = [5, 4, 3, 2, 1, 0] # sigma1. sigma fw, sigma D, sigma2

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, "temp")
    # print("query sql", query_sql)
    total_check_applicable_time = 0
    total_operation_time = 0
    total_check_answer_time = 0
    total_query_answer_time = 0 
    count_application = 0 # count the number of the application of the chase
    total_query_times = 0 # the number of application of queries
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    while  does_updated:
        temp_updated = False
        for idx in static_order:
            count_application += 1
            dependency = dependencies[idx]
            checked_tuples = checked_records[idx]
            
            # print("\n-------------------------------------")
            # print(dependency['dependency_type'])
            # print(dependency['dependency_tuples'])
            # print(dependency['dependency_attributes'])
            # print(dependency['dependency_attributes_datatypes'])
            # print(dependency['dependency_summary'])
            # print(dependency['dependency_summary_condition'])
            # print("-------------------------------------\n")
            checked_records[idx], whether_updated, check_valid_time, operate_time = chase.apply_dependency(dependency, Z_tablename, checked_tuples)
            print("static", count_application, whether_updated)
            
            total_check_applicable_time += check_valid_time
            total_operation_time += operate_time
            temp_updated = (temp_updated or whether_updated)
        does_updated = temp_updated
    
    # print("gamma_summary", gamma_summary)
    answer, count_queries, query_time, check_time = chase.apply_E(query_sql, Z_tablename, gamma_summary)
    total_query_times += count_queries
    total_query_answer_time += query_time
    total_check_answer_time += check_time
    # print("gamma_summary", gamma_summary)
    # ans, query_time, check_time = chase.apply_E(query_sql, gamma_summary)
    # total_query_answer_time += query_time
    # total_check_answer_time += check_time
    # print("static", count_application, answer)
    return answer, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times

if __name__ == '__main__':
    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    num_hosts = 2

    case = 'relevant'

    Z_tablename = "Z"
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_datatypes = ['text', 'text', 'text', 'inet_faure', 'inet_faure']

    # script_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes, num_hosts, case, Z_tablename, Z_attributes, Z_datatypes)


    # path_nodes = [6147, 12788, 12588, 12591, 13130, 12504, 12505, 12619, 1531]
    # symbolic_IP_mapping = {6147: '11.0.0.1', 12788: '11.0.0.2', 12588: '11.0.0.3', 12591: '11.0.0.4', 13130: '11.0.0.5', 12504: '11.0.0.6', 12505: '11.0.0.7', 12619: '11.0.0.8', 1531: '11.0.0.9'}
    # E_tuples = [('f', 's0', 'd0', 's', '11.0.0.1', '{}'), ('f', 's1', 'd1', '11.0.0.1', '11.0.0.2', '{}'), ('f', 's2', 'd2', '11.0.0.2', '11.0.0.3', '{}'), ('f', 's3', 'd3', '11.0.0.3', '11.0.0.4', '{}'), ('f', 's4', 'd4', '11.0.0.4', '11.0.0.5', '{}'), ('f', 's5', 'd5', '11.0.0.5', '11.0.0.6', '{}'), ('f', 's6', 'd6', '11.0.0.6', '11.0.0.7', '{}'), ('f', 's7', 'd7', '11.0.0.7', '11.0.0.8', '{}'), ('f', 's9', 'd9', '11.0.0.9', 'd', '{}'), ('f', 's8', 'd8', '11.0.0.8', '11.0.0.9', '{}')]
    # ingress_hosts = ['10.0.0.1', '10.0.0.2', '10.0.0.3', '10.0.0.4', '10.0.0.5']
    # egress_hosts = ['12.0.0.1', '12.0.0.2', '12.0.0.3', '12.0.0.4', '12.0.0.5']
    # block_list = ('10.0.0.1', '12.0.0.4')
    # dependencies = {1: {'dependency_tuples': [('f', '10.0.0.1', '12.0.0.1', '10.0.0.1', '11.0.0.1', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'], "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'], 'dependency_summary': ['f', '10.0.0.4', '12.0.0.1', '10.0.0.1', '11.0.0.1'], 'dependency_summary_condition': None, 'dependency_type': 'tgd'}, 2: {'dependency_tuples': [('f1', '10.0.0.1', '12.0.0.1', 'n1', '{}'), ('f2', '10.0.0.4', '12.0.0.1', 'n2', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'condition'], "dependency_cares_attributes": ['src', 'dst'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'], 'dependency_summary': ['f1 = f2'], 'dependency_summary_condition': ["n1 <= '11.0.0.1'", "n2 <= '11.0.0.1'"], 'dependency_type': 'egd'}, 3: {'dependency_tuples': [('f', '10.0.0.4', '12.0.0.1', '11.0.0.8', '11.0.0.9', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'], "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'], 'dependency_summary': ['f', '10.0.0.4', '12.0.0.4', '11.0.0.8', '11.0.0.9'], 'dependency_summary_condition': None, 'dependency_type': 'tgd'}, 4: {'dependency_tuples': [('f1', '10.0.0.4', '12.0.0.1', 'n1', '{}'), ('f2', '10.0.0.4', '12.0.0.4', 'n2', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'condition'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'], "dependency_cares_attributes": ['src', 'dst'], 'dependency_summary': ['f1 = f2'], 'dependency_summary_condition': ["n1 <= '11.0.0.9'", "n2 <= '11.0.0.9'"], 'dependency_type': 'egd'}, 0: {'dependency_tuples': [('f', 's1', 'd1', '{}'), ('f', 's2', 'd2', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'condition'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'text[]'], "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'], 'dependency_summary': ['s1 = s2', 'd1 = d2'], 'dependency_summary_condition': None, 'dependency_type': 'egd'}, 5: {'dependency_tuples': [('f', 's', 'd', 'n', 'x', '{}')], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'text[]'], "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'], 'dependency_summary': [], 'dependency_summary_condition': ["s = '10.0.0.1'", "d = '12.0.0.4'"], 'dependency_type': 'egd'}}
    # relevant_in_hosts = ['10.0.0.1', '10.0.0.4']
    # relevant_out_hosts = ['12.0.0.1', '12.0.0.4']
    # gamma_summary = ['f', '10.0.0.1', '12.0.0.4']

    # chase.load_table(E_attributes, E_datatypes, E_tablename, E_tuples)

    E_tuples, path_nodes, symbolic_IP_mapping = gen_E_for_chase_distributed_invariants(file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes)
    
    runs = 1
    for r in range(runs):
        ingress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "10.0.0.1")
        egress_hosts = func_gen_tableau.gen_hosts_IP_address(num_hosts, "12.0.0.1")

        dependencies, relevant_in_hosts, relevant_out_hosts, block_list = gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping)
        # print("block_list", block_list)
        # print("ingress", ingress_hosts)
        # print("egress", egress_hosts)
        # print("relevant in", relevant_in_hosts)
        # print("relevant out", relevant_out_hosts)
        gamma_attributes = ['f', 'n', 'x', 'condition']
        gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
        gamma_tablename = "W"

        # gamma_summary = gen_gamma_table(block_list, ingress_hosts, egress_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, 'all')
        gamma_summary = gen_gamma_table(block_list, relevant_in_hosts, relevant_out_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, 'relevant')

        Z_tuples, gen_z_time = gen_Z_for_chase_distributed_invariants(E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
        # print(Z_tuples)
        checked_tuples = {
            0: [], 
            1: [],
            2: [],
            3: [], 
            4: [],
            5: []
        }
        # chase.apply_egd(dependencies[0], Z_tablename, checked_tuples[0])
        # chase.apply_egd(dependencies[2], Z_tablename, checked_tuples[2])
        chase.apply_dependency(dependencies[0], Z_tablename, checked_tuples[0])
        # chase.apply_dependency(dependencies[1], Z_tablename, checked_tuples[1])
        # chase.apply_dependency(dependencies[2], Z_tablename, checked_tuples[2])
        # chase.apply_dependency(dependencies[3], Z_tablename, checked_tuples[3])
        # chase.apply_dependency(dependencies[4], Z_tablename, checked_tuples[4])
        # chase.apply_dependency(dependencies[5], Z_tablename, checked_tuples[5])

        # ans, _ = chase.apply_E(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
        # print("ans", ans)
        # ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = run_chase_distributed_invariants_in_optimal_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary)
        # ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = run_chase_distributed_invariants_in_random_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary)
        ans, total_check_applicable_time, total_operation_time, total_query_answer_time, total_check_answer_time, count_application, total_query_times = run_chase_distributed_invariants_in_static_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary)
        # run_chase_distributed_invariants_in_random_order(E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary)
        # print("ans", ans)
        # print("total_check_applicable_time: {:.4f}".format(total_check_applicable_time*1000))
        # print("total_operation_time: {:.4f}".format(total_operation_time*1000))
        # print("total_query_answer_time: {:.4f}".format(total_query_answer_time*1000))
        # print("total_check_answer_time: {:.4f}".format(total_check_answer_time*1000))
        # print("count_application: ", count_application)
