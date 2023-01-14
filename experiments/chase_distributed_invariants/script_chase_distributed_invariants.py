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
from utils.logging import timeit
import math
from copy import deepcopy

# conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
# cursor = conn.cursor()

@timeit
def gen_rewrite_dependencies(path_nodes, block_list, ingress_hosts, egress_hosts, symbolic_IP_mapping, inverse=False):
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
    
    inverse: Boolean
        default False. If True, inverse location of two rewrite policy
    
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

    '''
    # idx_node1 for rewriting src
    # idx_node2 for rewriting dst
    '''
    # set rewrite location at first node and last node
    idx_node1 = 0
    idx_node2 = len(path_nodes)-1

    relevant_in_hosts = []
    relevant_out_hosts = []
    rewrite_dependencies = {}

    '''
    rewrite src policy
    '''
    s_IP1 = block_list[0]
    relevant_in_hosts.append(s_IP1)
    # print("egress_hosts", egress_hosts)
    egress_hosts.remove(block_list[1]) 
    # print("after deleting egress", egress_hosts)
    d_IP1 = random.sample(egress_hosts, 1)[0]
    relevant_out_hosts.append(d_IP1)

    ingress_hosts.remove(block_list[0])
    # print("after deleting ingress", ingress_hosts)
    # rewrite src to random ingress host
    rewrite_src = random.sample(ingress_hosts, 1)[0]
    rewrite_value1 = {"source": rewrite_src, 'dest':None}

    relevant_in_hosts.append(rewrite_src)

    '''
    rewrite dst policy
    '''
    # rewrite dest to second node of block_list
    rewrite_value2 = {"source": None, 'dest':block_list[1]}
    s_IP2 = rewrite_src
    d_IP2 = d_IP1
    relevant_out_hosts.append(block_list[1])
    
    '''
    convert to dependencies
    '''
    tgd1, tgd2 = None, None
    egd1, egd2 = None, None
    if not inverse:
        tgd1, egd1 = convert_rewrite_policy_to_dependency(s_IP1, d_IP1, rewrite_value1, idx_node1, path_nodes, symbolic_IP_mapping)
        tgd2, egd2 = convert_rewrite_policy_to_dependency(s_IP2, d_IP2, rewrite_value2, idx_node2, path_nodes, symbolic_IP_mapping)
    else:
        tgd1, egd1 = convert_rewrite_policy_to_dependency(s_IP2, d_IP2, rewrite_value2, idx_node1, path_nodes, symbolic_IP_mapping)
        tgd2, egd2 = convert_rewrite_policy_to_dependency(s_IP1, d_IP1, rewrite_value1, idx_node2, path_nodes, symbolic_IP_mapping)
        
    rewrite_dependencies[1] = tgd1
    rewrite_dependencies[2] = egd1
    rewrite_dependencies[3] = tgd2
    rewrite_dependencies[4] = egd2

    return rewrite_dependencies, relevant_in_hosts, relevant_out_hosts

def gen_random_policies(num_policies, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping, num_related_policies=4, exists_security_hole=True):
    policies = {}
    block_lists = []

    # the block list for the first and the last rewrite nodes
    key_block_src = random.sample(ingress_hosts, 1)[0]
    key_block_dst = random.sample(egress_hosts, 1)[0]

    
    ingress_hosts.remove(key_block_src)
    egress_hosts.remove(key_block_dst)
    key_block_for_end_rewrites = (key_block_src, key_block_dst)
    # print("block_list", key_block_for_end_rewrites)
    block_lists.append(key_block_for_end_rewrites)

    policies, suspicious_flow, ingress_hosts, egress_hosts = gen_cascading_rewrite_policies(key_block_for_end_rewrites, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping, num_related_policies, exists_security_hole)

    '''
    # additional new policy
    '''
    middle = math.floor(num_related_policies/2)
    new_policy = gen_new_policy()
    policies[middle] = new_policy

    # print("===================================")
    # print_dependency(new_dependency)

    '''
    filter policy for key block
    '''
    key_filter1 = gen_firewall_dependency(key_block_for_end_rewrites, 0, path_nodes, symbolic_IP_mapping)
    policies[num_related_policies+1] = [key_filter1]

    key_filter2 = gen_firewall_dependency(key_block_for_end_rewrites, -1, path_nodes, symbolic_IP_mapping)
    policies[num_related_policies+1+1] = [key_filter2]

    # print("================key_filter1===================")
    # print_dependency(key_filter1)
    # print("================key_filter2===================")
    # print_dependency(key_filter2)

    '''
    rest of policies
    half is filter policies
    half is rewriting policies
    '''
    num_policies = num_policies - (num_related_policies+1+1+1)
    num_rewrite_policies = math.ceil(num_policies / 2)
    num_filter_policies = num_policies - num_rewrite_policies

    for i in range(num_rewrite_policies):
        loc = i % (len(path_nodes)-2) + 1
        if i % 2 == 0:
            # policy for rewriting source
            src = random.sample(ingress_hosts, 1)[0]
            dst = random.sample(egress_hosts, 1)[0]
            ingress_hosts.remove(src)
            egress_hosts.remove(dst)

            rewrite_src = random.sample(ingress_hosts, 1)[0]
            ingress_hosts.remove(rewrite_src)
            rewrite_value = {'source': rewrite_src, 'dest':None}
            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, loc, path_nodes, symbolic_IP_mapping)
            policies[i+7] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            # print(f'===============node {loc}====================')
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
        else:
            # policy for rewriting dest
            src = random.sample(ingress_hosts, 1)[0]
            dst = random.sample(egress_hosts, 1)[0]
            ingress_hosts.remove(src)
            egress_hosts.remove(dst)

            rewrite_dst = random.sample(egress_hosts, 1)[0]
            egress_hosts.remove(rewrite_dst)
            rewrite_value = {'source': None, 'dest':rewrite_dst}
            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, loc, path_nodes, symbolic_IP_mapping)
            policies[i+7] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            # print(f'===============node {loc}====================')
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
    
    for j in range(num_filter_policies):
        block_src = random.sample(ingress_hosts, 1)[0]
        block_dst = random.sample(egress_hosts, 1)[0]
        ingress_hosts.remove(block_src)
        egress_hosts.remove(block_dst)

        block_list = (block_src, block_dst)
        block_lists.append(block_list)

        loc = random.sample(range(len(path_nodes)), 1)[0]
        fw_dependency = gen_firewall_dependency(block_list, loc, path_nodes, symbolic_IP_mapping)
        policies[j+num_rewrite_policies+7] = [fw_dependency]

        # print(f'===================================')
        # print_dependency(fw_dependency)

    # for idx in sorted(list(policies.keys())):
    #     print(idx)
    #     policy = policies[idx]
    #     print_policy(policy)
    #     print('\n')

    return policies, suspicious_flow, block_lists

def gen_random_policies_old(num_policies, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping):
    policies = {}
    block_lists = []

    # the block list for the first and the last rewrite nodes
    key_block_src = random.sample(ingress_hosts, 1)[0]
    key_block_dst = random.sample(egress_hosts, 1)[0]
    ingress_hosts.remove(key_block_src)
    egress_hosts.remove(key_block_dst)
    key_block_for_end_rewrites = (key_block_src, key_block_dst)
    # print(key_block_for_end_rewrites)
    block_lists.append(key_block_for_end_rewrites)

    '''
    # rewrite policy at the first node
    '''
    dst = random.sample(egress_hosts, 1)[0]
    egress_hosts.remove(dst)
    suspicious_flow = (key_block_src, dst)

    rewrite_src = random.sample(ingress_hosts, 1)[0]
    ingress_hosts.remove(rewrite_src)
    rewrite_value = {'source':rewrite_src, 'dest':None}

    tdg_dependency0, edg_dependency0 = convert_rewrite_policy_to_dependency(key_block_src, dst, rewrite_value, 0, path_nodes, symbolic_IP_mapping)
    policies[0] = [tdg_dependency0, edg_dependency0]
    
    # print("===============node 0====================")
    # print_dependency(tdg_dependency0)
    # print_dependency(edg_dependency0)
    
    '''
    #rewrite at the last node
    '''
    rewrite_value = {'source':None, 'dest':key_block_dst}
    tdg_dependency1, edg_dependency1 = convert_rewrite_policy_to_dependency(rewrite_src, dst, rewrite_value, len(path_nodes)-1, path_nodes, symbolic_IP_mapping)
    policies[2] = [tdg_dependency1, edg_dependency1]
    
    # print("=================node -1==================")
    # print_dependency(tdg_dependency1)
    # print_dependency(edg_dependency1)

    '''
    # additional new policy
    '''
    new_dependency = gen_new_dependency(path_nodes, symbolic_IP_mapping)
    policies[1] = [new_dependency]

    # print("===================================")
    # print_dependency(new_dependency)

    '''
    filter policy for key block
    '''
    key_filter1 = gen_firewall_dependency(key_block_for_end_rewrites, 0, path_nodes, symbolic_IP_mapping)
    policies[3] = [key_filter1]

    key_filter2 = gen_firewall_dependency(key_block_for_end_rewrites, -1, path_nodes, symbolic_IP_mapping)
    policies[4] = [key_filter2]

    # print("================key_filter1===================")
    # print_dependency(key_filter1)
    # print("================key_filter2===================")
    # print_dependency(key_filter2)

    '''
    rest of policies
    half is filter policies
    half is rewriting policies
    '''
    num_rewrite_policies = math.ceil((num_policies-5)/2)
    num_filter_policies = num_policies-5-num_rewrite_policies

    for i in range(num_rewrite_policies):
        loc = i % (len(path_nodes)-2) + 1
        if i % 2 == 0:
            # policy for rewriting source
            src = random.sample(ingress_hosts, 1)[0]
            dst = random.sample(egress_hosts, 1)[0]
            ingress_hosts.remove(src)
            egress_hosts.remove(dst)

            rewrite_src = random.sample(ingress_hosts, 1)[0]
            ingress_hosts.remove(rewrite_src)
            rewrite_value = {'source': rewrite_src, 'dest':None}
            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, loc, path_nodes, symbolic_IP_mapping)
            policies[i+5] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            # print(f'===============node {loc}====================')
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
        else:
            # policy for rewriting dest
            src = random.sample(ingress_hosts, 1)[0]
            dst = random.sample(egress_hosts, 1)[0]
            ingress_hosts.remove(src)
            egress_hosts.remove(dst)

            rewrite_dst = random.sample(egress_hosts, 1)[0]
            egress_hosts.remove(rewrite_dst)
            rewrite_value = {'source': None, 'dest':rewrite_dst}
            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, loc, path_nodes, symbolic_IP_mapping)
            policies[i+5] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            # print(f'===============node {loc}====================')
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
    
    for j in range(num_filter_policies):
        block_src = random.sample(ingress_hosts, 1)[0]
        block_dst = random.sample(egress_hosts, 1)[0]
        ingress_hosts.remove(block_src)
        egress_hosts.remove(block_dst)

        block_list = (block_src, block_dst)
        block_lists.append(block_list)

        loc = random.sample(range(len(path_nodes)), 1)[0]
        fw_dependency = gen_firewall_dependency(block_list, loc, path_nodes, symbolic_IP_mapping)
        policies[j+num_rewrite_policies+5] = [fw_dependency]

        # print(f'===================================')
        # print_dependency(fw_dependency)

    return policies, suspicious_flow, block_lists

def gen_cascading_rewrite_policies(block_list, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping, num_policies=4, exists_security_hole=True):
    """
    Assume a security hole appear after applying a half number of policies
    """
    policies = {}
    # ingress_hosts.remove(block_list[0])
    # egress_hosts.remove(block_list[1])

    node_interval = math.floor(len(path_nodes) / num_policies)

    middle = math.floor(num_policies/2)
    node_location = 0

    src = block_list[0]
    dst = random.sample(egress_hosts, 1)[0]
    egress_hosts.remove(dst)
    suspicious_flow = (src, dst)
    # print("suspicious_flow", suspicious_flow)
    for i in range(middle):
        if i // 2 == 0:
            """
            rewrite src
            """
            rewrite_src = random.sample(ingress_hosts, 1)[0]
            ingress_hosts.remove(rewrite_src)
            rewrite_value = {'source':rewrite_src, 'dest':None}

            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, node_location, path_nodes, symbolic_IP_mapping)
            policies[i] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]
            
            src = rewrite_src
            
            # print(f"===============node {i}====================")
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
        else:
            '''
            #rewrite dst
            '''
            rewrite_dst = random.sample(egress_hosts, 1)[0]
            egress_hosts.remove(rewrite_dst)

            rewrite_value = {'source':None, 'dest':rewrite_dst}
            tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, node_location, path_nodes, symbolic_IP_mapping)
            policies[i] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            dst = rewrite_dst

            # print(f"===============node {i}====================")
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)

        node_location += node_interval

    for i in range(middle, num_policies):
        if i == middle:
            '''
            #rewrite dst
            '''
            rewrite_dst = None
            if exists_security_hole: # if exits security hole, rewrite dst to the dst of block_list
                rewrite_dst = block_list[1]
            else:
                rewrite_dst = random.sample(egress_hosts, 1)[0]
                egress_hosts.remove(rewrite_dst)
            rewrite_value = {'source':None, 'dest':rewrite_dst}

            if middle == num_policies-1:
                tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, -1, path_nodes, symbolic_IP_mapping)
                policies[i+1] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]
            else:
                tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, node_location, path_nodes, symbolic_IP_mapping)
                policies[i+1] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]

            dst = rewrite_dst

            # print(f"===============node {i}====================")
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)

        else:
            """
            rewrite src
            """
            rewrite_src = random.sample(ingress_hosts, 1)[0]
            ingress_hosts.remove(rewrite_src)
            rewrite_value = {'source':rewrite_src, 'dest':None}
            if i == num_policies-1:
                tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, -1, path_nodes, symbolic_IP_mapping)
                policies[i+1] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]
            else:
                tdg_dependency, edg_dependency = convert_rewrite_policy_to_dependency(src, dst, rewrite_value, node_location, path_nodes, symbolic_IP_mapping)
                policies[i+1] = [deepcopy(tdg_dependency), deepcopy(edg_dependency)]
            
            src = rewrite_src

            # print(f"===============node {i}====================")
            # print_dependency(tdg_dependency)
            # print_dependency(edg_dependency)
        node_location += node_interval
    
    return policies, suspicious_flow, ingress_hosts, egress_hosts

def print_dependency(dependency):
    print("***************************************************************************************************")
    for t in dependency['dependency_tuples']:
        print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*t))
    print("---------------------------------------------------------------------------------------------------")
    if len(dependency['dependency_summary']) != 0:
        print('| {} |'.format(" | ".join(["{:<16}".format(i) for i in dependency['dependency_summary']])))

    if dependency['dependency_summary_condition'] is not None:
        print('delete | {} |'.format(" | ".join(["{:<16}".format(i) for i in dependency['dependency_summary_condition']])))
    print("***************************************************************************************************\n")

def print_policy(policy):
    for dependency in policy:
        print_dependency(dependency)

def convert_rewrite_policy_to_dependency(source, dest, rewrite_value, loc, path_nodes, symbolic_IP_mapping):
    tgd_tuples = []
    egd_tuples = []
    node = path_nodes[loc]
    # x_IP = symbolic_IP_mapping[node]
    n_IP = symbolic_IP_mapping[node]

    # tgd_tuples.append(('f', source, dest, prev_node, x_IP, '{}'))
    tgd_tuples.append(('f', source, dest, ">{}".format(node), "{}>".format(node)))
    # egd_tuples.append(('f1', source, dest, 'n1', '{}'))
    egd_tuples.append(('f1', source, dest, ">{}".format(node), "{}>".format(node)))

    tgd_summary = None
    rewrite_src = rewrite_value['source']
    rewrite_dst = rewrite_value['dest']

    if rewrite_src is not None and rewrite_dst is None:
        tgd_summary = ['f', rewrite_src, dest, ">{}".format(node), "{}>".format(node)]
        egd_tuples.append(('f2', rewrite_src, dest, ">{}".format(node), "{}>".format(node)))
    elif rewrite_src is None and rewrite_dst is not None:
        egd_tuples.append(('f2', source, rewrite_dst, ">{}".format(node), "{}>".format(node)))
        tgd_summary = ['f', source, rewrite_dst, ">{}".format(node), "{}>".format(node)]
    elif rewrite_src is not None and rewrite_dst is not None:
        egd_tuples.append(('f2', rewrite_src, rewrite_dst, ">{}".format(node), "{}>".format(node)))
        tgd_summary = ['f', rewrite_src, rewrite_dst, ">{}".format(node), "{}>".format(node)]

    tgd_summary_condition = None
    tgd_type = 'tgd'

    tdg_dependency = {
        "dependency_tuples": tgd_tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_attributes_datatypes": ["text", "text", "text", "text", "text"], 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": tgd_summary,
        "dependency_summary_condition": tgd_summary_condition,
        "dependency_type": tgd_type
    }

    egd_summary = ['f1 = f2']
    # egd_summary_condition = ["n1 <= '{}'".format(x_IP), "n2 <= '{}'".format(x_IP)]
    # egd_summary_condition = ["n1 <= '{}'".format(n_IP), "n2 <= '{}'".format(n_IP)]
    # if loc == 0:
    #     egd_summary_condition = None
    # if pre_rewrite_loc is not None:
    #     pre_rewite_node_IP = symbolic_IP_mapping[path_nodes[pre_rewrite_loc]]
    #     egd_summary_condition += ["n1 >= '{}'".format(pre_rewite_node_IP), "n2 >= '{}'".format(pre_rewite_node_IP)]

    egd_type = 'egd'
    edg_dependency = {
        "dependency_tuples": egd_tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_attributes_datatypes": ["text", "text", "text", "text", "text"], 
        "dependency_cares_attributes": ['src', 'dst', 'n', 'x'],
        "dependency_summary": egd_summary,
        "dependency_summary_condition": None,
        "dependency_type": egd_type
    }

    return tdg_dependency, edg_dependency

def convert_rewrite_policy_to_dependency_old(source, dest, rewrite_value, loc, path_nodes, symbolic_IP_mapping):
    tgd_tuples = []
    egd_tuples = []
    node = path_nodes[loc]
    # x_IP = symbolic_IP_mapping[node]
    n_IP = symbolic_IP_mapping[node]

    # prev_node = None
    # if loc == 0:
    #     prev_node = source
    # else:
    #     prev_node = symbolic_IP_mapping[path_nodes[loc-1]]
    
    next_node = None
    if loc == len(path_nodes)-1 or loc == -1:
        next_node = dest
    else:
        next_node = symbolic_IP_mapping[path_nodes[loc+1]]

    # tgd_tuples.append(('f', source, dest, prev_node, x_IP, '{}'))
    tgd_tuples.append(('f', source, dest, n_IP, next_node, '{}'))
    # egd_tuples.append(('f1', source, dest, 'n1', '{}'))
    egd_tuples.append(('f1', source, dest, n_IP, next_node, '{}'))

    tgd_summary = None
    rewrite_src = rewrite_value['source']
    rewrite_dst = rewrite_value['dest']

    if rewrite_src is not None and rewrite_dst is None:
        tgd_summary = ['f', rewrite_src, dest, n_IP, next_node]
        egd_tuples.append(('f2', rewrite_src, dest, n_IP, next_node, '{}'))
    elif rewrite_src is None and rewrite_dst is not None:
        if loc == len(path_nodes) - 1 or loc == -1: # if loc is at the last node, rewrite dest will affect final dest
            egd_tuples.append(('f2', source, rewrite_dst, n_IP, rewrite_dst, '{}'))
            tgd_summary = ['f', source, rewrite_dst, n_IP, rewrite_dst]
        else:
            egd_tuples.append(('f2', source, rewrite_dst, n_IP, next_node, '{}'))
            tgd_summary = ['f', source, rewrite_dst, n_IP, next_node]
    elif rewrite_src is not None and rewrite_dst is not None:
        if loc == len(path_nodes) - 1 or loc == -1: # if loc is at the last node, rewrite dest will affect final dest
            egd_tuples.append(('f2', rewrite_src, rewrite_dst, n_IP, rewrite_dst, '{}'))
            tgd_summary = ['f', rewrite_src, rewrite_dst, n_IP, rewrite_dst]
        else:
            egd_tuples.append(('f2', rewrite_src, rewrite_dst, n_IP, next_node, '{}'))
            tgd_summary = ['f', rewrite_src, rewrite_dst, n_IP, next_node]
    # for key in rewrite_value.keys():
    #     if key == 'source' and rewrite_value[key] is not None:
    #         rewrite_source = rewrite_value[key]
    #         tgd_summary = ['f', rewrite_source, dest, n_IP, next_node]
    #         egd_tuples.append(('f2', rewrite_source, dest, n_IP, next_node, '{}'))
    #     elif key == 'dest' and rewrite_value[key] is not None:
    #         rewrite_dest = rewrite_value[key]
            

    #         # print("rewrite_dest", rewrite_dest)
    #         # print("next_node", next_node)
    #         if loc == len(path_nodes) - 1 or loc == -1: # if loc is at the last node, rewrite dest will affect final dest
    #             egd_tuples.append(('f2', source, rewrite_dest, n_IP, rewrite_dest, '{}'))
    #             tgd_summary = ['f', source, rewrite_dest, n_IP, rewrite_dest]
    #         else:
    #             egd_tuples.append(('f2', source, rewrite_dest, n_IP, next_node, '{}'))
    #             tgd_summary = ['f', source, rewrite_dest, n_IP, next_node]
            # print("egd_tuples", egd_tuples)

    # tgd_summary = ['f', source, dest, prev_node, x_IP]
    # tgd_summary = ['f', source, dest, n_IP, next_node]
    # egd_tuples.append(('f2', source, dest, 'n2', '{}'))

    # egd_tuples.append(('f2', source, dest, n_IP, next_node, '{}'))

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
    # egd_summary_condition = ["n1 <= '{}'".format(x_IP), "n2 <= '{}'".format(x_IP)]
    # egd_summary_condition = ["n1 <= '{}'".format(n_IP), "n2 <= '{}'".format(n_IP)]
    # if loc == 0:
    #     egd_summary_condition = None
    # if pre_rewrite_loc is not None:
    #     pre_rewite_node_IP = symbolic_IP_mapping[path_nodes[pre_rewrite_loc]]
    #     egd_summary_condition += ["n1 >= '{}'".format(pre_rewite_node_IP), "n2 >= '{}'".format(pre_rewite_node_IP)]

    egd_type = 'egd'
    edg_dependency = {
        "dependency_tuples": egd_tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'x', 'condition'],
        "dependency_attributes_datatypes": ["inet_faure", "inet_faure", "inet_faure", "text[]"], 
        "dependency_cares_attributes": ['src', 'dst', 'n', 'x'],
        "dependency_summary": egd_summary,
        "dependency_summary_condition": None,
        "dependency_type": egd_type
    }

    return tdg_dependency, edg_dependency

@timeit
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
        ('f', 's1', 'd1', 'n1', 'x1', '{}'),
        ('f', 's2', 'd2', 'n2', 'x2', '{}')
    ]

    forwarding_summary = ['s1 = s2', 'd1 = d2']
    edg_dependency = {
        "dependency_tuples": forwarding_tuples,
        "dependency_attributes": forwarding_attributes,
        "dependency_attributes_datatypes": forwarding_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": forwarding_summary,
        "dependency_summary_condition": None,
        "dependency_type": 'egd'
    }

    return edg_dependency

@timeit
def gen_firewall_dependency(block_list, loc, path_nodes, symbolic_IP_mapping):
    """
    generate firewall dependency

    Parameters:
    -----------
    block_list: tuple
        the blocklist. block source to dest.

    Returns:
    --------
    egd_dependency: dict
        the firewall dependency
    
    """
    n_node = path_nodes[loc]
    n_IP = symbolic_IP_mapping[n_node]

    firewall_tuples = [
        ('f', 's', 'd', ">{}".format(n_node), '{}>'.format(n_node), '{}')
    ]

    firewall_attributes = ['f', 'src', 'dst', 'n', 'x']
    firewall_datatypes = ['text', 'text', 'text', 'text', 'text']
    firewall_summary = []
    firewall_summary_condition = ["s = {}".format(block_list[0]), "d = {}".format(block_list[1])]
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

def gen_firewall_dependency_old(block_list, loc, path_nodes, symbolic_IP_mapping):
    """
    generate firewall dependency

    Parameters:
    -----------
    block_list: tuple
        the blocklist. block source to dest.

    Returns:
    --------
    egd_dependency: dict
        the firewall dependency
    
    """
    n_node = path_nodes[loc]
    n_IP = symbolic_IP_mapping[n_node]

    firewall_tuples = [
        ('f', 's', 'd', n_IP, 'x', '{}')
    ]

    firewall_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    firewall_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']
    firewall_summary = []
    firewall_summary_condition = ["s = {}".format(block_list[0]), "d = {}".format(block_list[1])]
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

@timeit
def gen_new_dependency(path_nodes, symbolic_IP_mapping):
    """
    x_f  x_s  x_d 1 2
    x_f       x_d 2 x_n
    ---------------------------
    x_f  x_s  x_d 2 x_n
    """

    # the first and the last node of the path are the rewriting node
    idx_node1 = 0
    idx_node2 = -1

    n1 = symbolic_IP_mapping[path_nodes[idx_node1]]
    n1_next = symbolic_IP_mapping[path_nodes[idx_node1+1]]

    n2 = symbolic_IP_mapping[path_nodes[idx_node2]]

    # new_dependency_tuples = [
    #     ('x_f', 'x_s1', 'x_d', n1, n1_next, '{}'),
    #     ('x_f', 'x_s2', 'x_d', n2, 'x_n', '{}')
    # ]
    new_dependency_tuples = [
        ('x_f', 'x_s1', 'x_d', 'x_n', 'x_x', '{}'),
        ('x_f', 'x_s2', 'x_d', 'x_x', 'x_next', '{}')
    ]
    new_dependency_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    new_dependency_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    # new_dependency_summary = ['x_f', 'x_s1', 'x_d', n2, 'x_n']
    new_dependency_summary = ['x_f', 'x_s1', 'x_d', 'x_x', 'x_next']

    tgd_dependency = {
        "dependency_tuples": new_dependency_tuples,
        "dependency_attributes": new_dependency_attributes,
        "dependency_attributes_datatypes": new_dependency_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": new_dependency_summary,
        "dependency_summary_condition": None,
        "dependency_type": 'tgd'
    }

    return tgd_dependency

@timeit
def gen_new_policy_old():
    """
    x_f  x_s  x_d 1 2
    x_f       x_d 2 x_n
    ---------------------------
    x_f  x_s  x_d 2 x_n
    """
    new_dependency_d_tuples = [
        ('x_f', 'x_s1', 'x_d', 'x_n', 'x_x', '{}'),
        ('x_f', 'x_s2', 'x_d', 'x_x', 'x_next', '{}')
    ]
    new_dependency_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    new_dependency_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    # new_dependency_summary = ['x_f', 'x_s1', 'x_d', n2, 'x_n']
    new_dependency_d_summary = ['x_f', 'x_s1', 'x_d', 'x_x', 'x_next']

    tgd_dependency1 = {
        "dependency_tuples": new_dependency_d_tuples,
        "dependency_attributes": new_dependency_attributes,
        "dependency_attributes_datatypes": new_dependency_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": new_dependency_d_summary,
        "dependency_summary_condition": None,
        "dependency_type": 'tgd'
    }

    new_dependency_s1_tuples = [
        ('x_f', 'x_s', 'x_d1', 'x_n', 'x_x', '{}'),
        ('x_f', 'x_s', 'x_d2', 'x_x', 'x_next', '{}')
    ]
    new_dependency_s1_summary = ['x_f', 'x_s', 'x_d1', 'x_x', 'x_next']

    tgd_dependency2 = {
        "dependency_tuples": new_dependency_s1_tuples,
        "dependency_attributes": new_dependency_attributes,
        "dependency_attributes_datatypes": new_dependency_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": new_dependency_s1_summary,
        "dependency_summary_condition": ["x_d2 != x_next"],
        "dependency_type": 'tgd'
    }

    new_dependency_s2_tuples = [
        ('x_f', 'x_s', 'x_d1', 'x_n', 'x_x', '{}'),
        ('x_f', 'x_s', 'x_d2', 'x_x', 'x_d2', '{}')
    ]
    new_dependency_s2_summary = ['x_f', 'x_s', 'x_d1', 'x_x', 'x_d1']

    tgd_dependency3 = {
        "dependency_tuples": new_dependency_s2_tuples,
        "dependency_attributes": new_dependency_attributes,
        "dependency_attributes_datatypes": new_dependency_datatypes, 
        "dependency_cares_attributes": ['f', 'src', 'dst', 'n', 'x'],
        "dependency_summary": new_dependency_s2_summary,
        "dependency_summary_condition": None,
        "dependency_type": 'tgd'
    }

    return [tgd_dependency1, tgd_dependency2, tgd_dependency3]

@timeit
def gen_gamma_table(conn, block_list, in_hosts, out_hosts, gamma_tablename, gamma_attributes, gamma_datatypes, case):
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

    chase.load_table(conn, gamma_attributes, gamma_datatypes, gamma_tablename, whitelists_tuples)

    return gamma_summary

@timeit
def gen_empty_table(conn, tablename, attributes, datatypes):
    """ 
    generate whitelists for 'relevant' case

    Parameters:
    -----------
    tablename: string
        the tablename of gamma table

    attributes: list
        a list of attributes for gamma table
    
    datatypes: list
        a list of datatypes corresponding to the attributes of gamma table

    """
    cursor = conn.cursor()

    attr_datatype = []
    for idx, attr in enumerate(attributes):
        attr_datatype.append("{} {}".format(attr, datatypes[idx]))
    
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} ({})".format(tablename, ", ".join(attr_datatype)))
    conn.commit()

@timeit
def gen_topology(conn, ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping, tablename, table_attributes, table_datatypes):
    """
    generate Table L for topology or Table Lp for sub-path

    Parameters:
    -----------
    conn: Psycopg2.connect()
        An instance of Postgres connection
    
    ingress_hosts: list
        A list of IP prefixes of ingress hosts
    
    egress_hosts: list
        A list of IP prefixes of egress hosts
    
    path_nodes: list
        A list of integer nodes with forwarding ordering 
    
    symbolic_IP_mapping: dict
        The mapping between integer node and corresponding IP prefixes

    tablename: string
        the tablename of topology in Postgres
    
    table_attributes: list
        the schema of the tablename
    
    table_datatypes: list
        the datatypes of the attributes
    """
    tuples = []

    ingress_node = path_nodes[0]
    ingress_IP = symbolic_IP_mapping[ingress_node]
    for host in ingress_hosts:
        tuples.append((host, ">{}".format(ingress_IP), '0'))
    
    for idx in range(len(path_nodes)):
        n = path_nodes[idx]
        n_IP = symbolic_IP_mapping[n]
        tuples.append(( ">{}".format(n_IP),  "{}>".format(n_IP), '1'))

        if idx != len(path_nodes) - 1:
            x = path_nodes[idx]
            x_IP = symbolic_IP_mapping[x]
            tuples.append(("{}>".format(n_IP),  ">{}".format(x_IP), '1'))
    
    egress_node = path_nodes[-1]
    egress_IP = symbolic_IP_mapping[egress_node]
    for host in egress_hosts:
        tuples.append(("{}>".format(egress_IP), host, '0'))

    attr_type = ["{} {}".format(table_attributes[idx], table_datatypes[idx]) for idx in range(len(table_attributes))]
    cursor = conn.cursor()
    cursor.execute("Drop table if exists {}".format(tablename))
    cursor.execute("create table {} ({})".format(tablename, ', '.join(attr_type)))
    execute_values(cursor, "insert into {} values %s".format(tablename), tuples)

    conn.commit()

@timeit
def gen_whitelists(block_list, in_hosts, out_hosts):
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

    Returns:
    --------
    whitelists_flows: list
        a list of whitelists of flows

    """
    whitelists_flows = []
    for in_h in in_hosts:
        for out_h in out_hosts:
            if in_h == block_list[0] and out_h == block_list[1]:
                continue
            else:
                whitelists_flows.append([in_h, out_h])

    return whitelists_flows

@timeit
def update_table(conn, tuples, tablename):
    """
    change the data instance of table `tablename`
    Assume the `tablename` table has already created

    Parameters:
    -----------
    conn: psycopg2.connect()
        the instance of Postgres connection
    
    tuples: list
        the data of updated tuples
    
    tablename:
        the tablename of gamma table
    """
    cursor = conn.cursor()
    cursor.execute("truncate table {}".format(tablename))
    execute_values(cursor, "insert into {} values %s".format(tablename), tuples)
    conn.commit()

@timeit
def gen_E_for_chase_distributed_invariants(conn, file_dir, filename, as_tablename, topo_tablename, E_tablename, E_attributes, E_datatypes):
    E_tuples, source, dest, path_nodes, symbolic_IP_mapping = gen_tableau_script.gen_tableau_for_distributed_invariants(file_dir, filename, as_tablename, topo_tablename)
    chase.load_table(conn, E_attributes, E_datatypes, E_tablename, E_tuples)

    return E_tuples, path_nodes, symbolic_IP_mapping

@timeit
def gen_dependencies_for_chase_distributed_invariants(ingress_hosts, egress_hosts, path_nodes, symbolic_IP_mapping, inverse):
    '''
    generate block list
    randomly pick one host from ingress hosts and one host from egress hosts

    Parameters:
    -----------
    ingress_hosts: list
        list of ingress hosts with IP prefix
    
    egress_hosts: list
        list of egress hosts with IP prefix

    path_nodes: list
        list of nodes(symbolic) in the chain

    symbolic_IP_mapping: dict
        mapping between the symbolic node and the assigned IP prefix

    location: list
        a pair of locations applied rewriting policy. 
        The first location is applying rewrite source, the second location is applying rewrite dest.

    Returns:
    ---------
    dependencies: list[dict]
        list of dependencies
    
    relevant_in_hosts: list
        a list of IP address related to the block list
    
    relevant_out_hosts: list
        a list of IP address related to the block list
    
    block_list: 
        forbidden IP addresses
    '''
    in_block_node = random.sample(ingress_hosts, 1)[0]
    out_block_node = random.sample(egress_hosts, 1)[0]
    block_list = (in_block_node, out_block_node)
    # print("block_list", block_list)
    # block_list = ['10.0.0.2', '10.0.0.4']
    # block_list = ['2', '4']
    '''
    generate rewrite policies
    '''
    dependencies,relevant_in_hosts, relevant_out_hosts = gen_rewrite_dependencies(path_nodes, block_list, ingress_hosts, egress_hosts, symbolic_IP_mapping, inverse)
    # print("rewrite_dependencies", dependencies)

    # gen forwarding dependency
    forwarding_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    forwarding_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']
    forwarding_dependency = gen_forwarding_dependency(forwarding_attributes, forwarding_datatypes)
    # print("forwarding_dependency", forwarding_dependency)

    dependencies[0] = forwarding_dependency

    # gen firewall dependency
    # firewall_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    # firewall_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']
    firewall_dependency1 = gen_firewall_dependency(block_list, 0, path_nodes, symbolic_IP_mapping)
    firewall_dependency2 = gen_firewall_dependency(block_list, -1, path_nodes, symbolic_IP_mapping)
    # print("firewall_dependency", firewall_dependency)

    dependencies[5] = firewall_dependency1
    dependencies[6] = firewall_dependency2

    dependencies[7] = gen_new_dependency(path_nodes, symbolic_IP_mapping)

    return dependencies, relevant_in_hosts, relevant_out_hosts, block_list

@timeit
def gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_attributes_datatypes):
    Z_tuples = chase.gen_inverse_image_with_destbasedforwarding_applied(conn, E_tuples, gamma_tablename)
    chase.load_table(conn, Z_attributes, Z_attributes_datatypes, Z_tablename, Z_tuples)

    return Z_tuples

@timeit
def run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy='random', orderings=None):
    """
    Parameters:
    ------------
    conn: psycopg2.connect()
        instance of connention

    E_tuples: list[tuple]
        The tuples of tableau query E

    E_attributes: list
        relation of tableau query E

    E_summary: list
        summary of tableau query E
    
    dependencies: list[dict]
        list of dependencies
    
    Z_tablename: string
        the tablename of inverse image
    
    gamma_summary: list
        the summary of gamma table

    order_strategy: string
        ordering strategy. choose from 'random', 'specific'. Default 'random'. if choosing 'specific', input the orderings 
    
    orderings: list
        default None. used only when `order_strategy` is specific
    """
    
    count_application = 0 # count the number of the application of the chase
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    
    chase.applySourceDestPolicy(conn, Z_tablename)
    # input()
    # chase.applySourceDestPolicy_new(conn,Z_tablename)
    # exit()
    # input()
    while does_updated:
        if order_strategy.lower() == 'random':
            ordered_indexs = list(dependencies.keys())
            random.shuffle(ordered_indexs)
        else:
            ordered_indexs = orderings

        temp_updated = False
        for idx in ordered_indexs:
            if idx == 0: # skip forwarding dependency
                continue
                # chase.applySourceDestPolicy_new(conn, Z_tablename)
            count_application += 1

            dependency = dependencies[idx]
            # print(dependency['dependency_tuples'])
            # print(dependency['dependency_summary'])
            # print(dependency['dependency_summary_condition'])
            # print("--------------------")
            # input()
            whether_updated = chase.apply_dependency(conn, dependency, Z_tablename)
            temp_updated = (temp_updated or whether_updated)
        does_updated = temp_updated
    print("#count:", count_application)
    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    print("query sql", query_sql)
    answer = chase.apply_E(conn, query_sql)

    return answer, count_application

@timeit
def run_chase_policy_distributed_invariants(conn, E_tuples, E_attributes, E_summary, policies, Z_tablename, gamma_summary, is_aggresive=False, order_strategy='random_random_permutation', orderings=None):
    """
    Parameters:
    ------------
    conn: psycopg2.connect()
        instance of connention

    E_tuples: list[tuple]
        The tuples of tableau query E

    E_attributes: list
        relation of tableau query E

    E_summary: list
        summary of tableau query E
    
    dependencies: list[dict]
        list of dependencies
    
    Z_tablename: string
        the tablename of inverse image
    
    gamma_summary: list
        the summary of gamma table

    order_strategy: string
        ordering strategy. choose from 'random_permutation', 'fixed_permutation', 'specific'. Default 'random_random_permutation'. if choosing 'specific', input the orderings 
    
    orderings: list
        default None. used only when `order_strategy` is specific
    """
    
    count_application = 0 # count the number of the application of the chase
    count_iterations = 0 # count the number of iterations
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    print("query sql", query_sql)

    ordered_indexs = list(policies.keys())
    is_shuffled = False  # for random_fixed_permutation
    answer = None
    while does_updated:
        if order_strategy.lower() == 'random_permutation':
            random.shuffle(ordered_indexs)
        elif order_strategy.lower() == 'fixed_permutation':
            if not is_shuffled:
                random.shuffle(ordered_indexs)
                is_shuffled = True
        elif order_strategy.lower() == 'specific':
            ordered_indexs = orderings
        else:
            print("wrong ordering strategy,", order_strategy, "please choose from 'random_permutation', 'fixed_permutation', 'specific'")
            exit()

        temp_updated = False
        for idx in ordered_indexs:
            # print("policy index", idx)
            policy = policies[idx]
            count_application += len(policy)
            
            whether_updated = chase.apply_policy(conn, policy, Z_tablename)
            temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated
        count_iterations += 1
        if is_aggresive:
            answer = chase.apply_E(conn, query_sql) 
            if answer: # if find the security hole, stop here
                # print("#count:", count_application)
                print("answer:", answer)
                return answer, count_application, count_iterations
    
    answer = chase.apply_E(conn, query_sql)
    # print("#count:", count_application)
    print("answer:", answer)

    return answer, count_application, count_iterations

@timeit
def run_chase_policy_atomic_distributed_invariants(conn, E_tuples, E_attributes, E_summary, policies, Z_tablename, gamma_summary, is_aggresive=False, order_strategy='random_random_permutation', orderings=None):
    """
    Parameters:
    ------------
    conn: psycopg2.connect()
        instance of connention

    E_tuples: list[tuple]
        The tuples of tableau query E

    E_attributes: list
        relation of tableau query E

    E_summary: list
        summary of tableau query E
    
    dependencies: list[dict]
        list of dependencies
    
    Z_tablename: string
        the tablename of inverse image
    
    gamma_summary: list
        the summary of gamma table

    order_strategy: string
        ordering strategy. choose from 'random_permutation', 'fixed_permutation', 'specific'. Default 'random_random_permutation'. if choosing 'specific', input the orderings 
    
    orderings: list
        default None. used only when `order_strategy` is specific
    """
    
    count_application = 0 # count the number of the application of the chase
    count_iterations = 0 # count the number of iterations
    count_E_query = 0 # count the number of E query applied
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    print("query sql", query_sql)

    ordered_indexs = list(policies.keys())
    is_shuffled = False  # for random_fixed_permutation
    answer = None
    while does_updated:
        if order_strategy.lower() == 'random_permutation':
            random.shuffle(ordered_indexs)
        elif order_strategy.lower() == 'fixed_permutation':
            if not is_shuffled:
                random.shuffle(ordered_indexs)
                is_shuffled = True
        elif order_strategy.lower() == 'specific':
            ordered_indexs = orderings
        else:
            print("wrong ordering strategy,", order_strategy, "please choose from 'random_permutation', 'fixed_permutation', 'specific'")
            exit()

        temp_updated = False
        for idx in ordered_indexs:
            # print("policy index", idx)
            policy = policies[idx]
            
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, Z_tablename)
            count_application += counts
            temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated
        count_iterations += 1
        if is_aggresive:
            answer = chase.apply_E(conn, query_sql) 
            count_E_query += 1
            if answer: # if find the security hole, stop here
                # print("#count:", count_application)
                print("answer:", answer)
                return answer, count_application, count_iterations, count_E_query
    
    answer = chase.apply_E(conn, query_sql)
    count_E_query += 1
    # print("#count:", count_application)
    print("answer:", answer)

    return answer, count_application, count_iterations, count_E_query


@timeit
def run_chase_policy_atomic_per_policy(conn, E_tuples, E_attributes, E_summary, policies, Z_tablename, gamma_summary, is_aggresive=False, order_strategy='random_random_permutation', orderings=None):
    """
    Parameters:
    ------------
    conn: psycopg2.connect()
        instance of connention

    E_tuples: list[tuple]
        The tuples of tableau query E

    E_attributes: list
        relation of tableau query E

    E_summary: list
        summary of tableau query E
    
    dependencies: list[dict]
        list of dependencies
    
    Z_tablename: string
        the tablename of inverse image
    
    gamma_summary: list
        the summary of gamma table

    order_strategy: string
        ordering strategy. choose from 'random_permutation', 'fixed_permutation', 'specific'. Default 'random_random_permutation'. if choosing 'specific', input the orderings 
    
    orderings: list
        default None. used only when `order_strategy` is specific
    """
    
    count_application = 0 # count the number of the application of the chase
    count_iterations = 0 # count the number of iterations
    count_E_query = 0 # count the number of E query applied
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    print("query sql", query_sql)

    ordered_indexs = list(policies.keys())
    is_shuffled = False  # for random_fixed_permutation
    answer = None
    finish_one_iteration = False
    while does_updated:
        if order_strategy.lower() == 'random_permutation':
            random.shuffle(ordered_indexs)
        elif order_strategy.lower() == 'fixed_permutation':
            if not is_shuffled:
                random.shuffle(ordered_indexs)
                is_shuffled = True
        elif order_strategy.lower() == 'specific':
            ordered_indexs = orderings
        else:
            print("wrong ordering strategy,", order_strategy, "please choose from 'random_permutation', 'fixed_permutation', 'specific'")
            exit()
        
        
        temp_updated = False
        for idx in ordered_indexs:
            # print("policy index", idx)
            policy = policies[idx]
            
            # print_policy(policy)
            # input()
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, Z_tablename)
            count_application += counts
            temp_updated = (temp_updated or whether_updated)

            if is_aggresive and finish_one_iteration:
                answer = chase.apply_E(conn, query_sql) 
                count_E_query += 1
                if answer: # if find the security hole, stop here
                    # print("#count:", count_application)
                    print("answer:", answer)
                    return answer, count_application, count_iterations, count_E_query

        if not finish_one_iteration: # after finishing one iteration, then begin aggressive checking
            finish_one_iteration = True

        does_updated = temp_updated
        count_iterations += 1
        
    
    answer = chase.apply_E(conn, query_sql)
    count_E_query += 1
    # print("#count:", count_application)
    print("answer:", answer)

    return answer, count_application, count_iterations, count_E_query

if __name__ == '__main__':
    # ============================test new \sigma_new: \sigma_fp and \sigma_bp=============================
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    ordering_strategy='random'
    orderings=None
    path_nodes = ['1', '2', '3']
    block_list = ['10.0.0.2', '10.0.0.4']
    ingress_hosts = ['10.0.0.1', '10.0.0.2']
    egress_hosts = ['10.0.0.3', '10.0.0.4', '10.0.0.5']

    topo_tablename = "l"
    topo_attributes = ['n', 'x', 'flag', 'condition']
    topo_datatypes = ['text', 'text', 'text', 'text[]']
    topo_tuples = [
        ('10.0.0.1', '1', '0', '{}'), 
        ('10.0.0.2', '1', '0', '{}'), 
        ('1', '2', '1', '{}'), 
        ('2', '3', '1', '{}'), 
        ('3', '10.0.0.3', '0', '{}'),
        ('3', '10.0.0.4', '0', '{}'),
        ('3', '10.0.0.5', '0', '{}')
    ]
    chase.load_table(conn, topo_attributes, topo_datatypes, topo_tablename, topo_tuples)
    # block_list = ['2', '4']
    # ingress_hosts = ['1', '2']
    # egress_hosts = ['3', '4']

    # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    symbolic_IP_mapping = {'1': '1', '2':'2', '3':'3'}
    inverse = False 

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']

    # E_tuples = [
    #     ('f', 's', 'd0', 's', '1', '{}'), 
    #     ('f', 's1', 'd1', '1', '2', '{}'), 
    #     ('f', 's1', 'd1', '2', '3', '{}'),
    #     ('f', 's2', 'd', '3', 'd', '{}')
    # ]

    E_tuples = [
        ('f', 's', 'd0', 's', '1', '{}'), 
        ('f', 's1', 'd1', '1', '2', '{}'), 
        ('f', 's2', 'd2', '2', '3', '{}'),
        ('f', 's3', 'd', '3', 'd', '{}')
    ]
    
    '''
    get whitelist
    '''
    gamma_attributes = ['f', 'n', 'x', 'condition']
    gamma_attributes_datatypes = ['text', 'text', 'text', 'text[]']
    gamma_summary = ['f', block_list[0], block_list[1]]
    print("gamma_summary", gamma_summary)
    gamma_tablename= "W_{}".format(ordering_strategy)
    gen_empty_table(conn, gamma_tablename, gamma_attributes, gamma_attributes_datatypes)
    gamma_tuples = [('f', '10.0.0.2', '10.0.0.3')]
    update_table(conn, gamma_tuples, gamma_tablename)

    
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
    Z_tablename = "Z_{}".format(ordering_strategy)
    gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
    # chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    # exit()

    # rewrite_policy = convert_rewrite_policy_to_dependency('10.0.0.2', '10.0.0.3', {'source':None, 'dest':'10.0.0.5'}, 0, path_nodes, symbolic_IP_mapping) 
    rewrite_policy1 = convert_rewrite_policy_to_dependency('10.0.0.2', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.3'}, 0, path_nodes, symbolic_IP_mapping) 
    rewrite_policy2 = convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.4'}, 1, path_nodes, symbolic_IP_mapping) 
    rewrite_policy3 = convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.4', {'source':'10.0.0.1', 'dest':'10.0.0.5'}, 2, path_nodes, symbolic_IP_mapping) 

    sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.x = t1.n and t1.flag = '1'".format(Z_tablename)
    sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.x = t1.n and t0.dst = t1.x and t1.flag = '0'".format(Z_tablename)

    sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.n = t1.x and t1.flag = '1'".format(Z_tablename)
    sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.n = t1.x and t0.src = t1.n and t1.flag = '0'".format(Z_tablename)

    sigma_new = [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]


    print("\n---------policy1------------")
    print_policy(rewrite_policy1)
    chase.apply_policy_as_atomic_unit(conn, rewrite_policy1, Z_tablename)
    for sql in sigma_new:
        chase.apply_sigma_new_atomically(conn, sql, Z_tablename)
    # input()

    print("---------policy2------------")
    print_policy(rewrite_policy2)
    chase.apply_policy_as_atomic_unit(conn, rewrite_policy2, Z_tablename)
    for sql in sigma_new:
        chase.apply_sigma_new_atomically(conn, sql, Z_tablename)
    # input()

    print("---------policy3------------")
    print_policy(rewrite_policy3)
    chase.apply_policy_as_atomic_unit(conn, rewrite_policy3, Z_tablename)
    for sql in sigma_new:
        chase.apply_sigma_new_atomically(conn, sql, Z_tablename)
    # input()

    E_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    answer = chase.apply_E(conn, E_sql)
    print("answer", answer)
    # #========================= toy example ========================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # ordering_strategy='random'
    # orderings=None
    # mode='all'
    # path_nodes = ['1', '2', '3']
    # block_list = ['10.0.0.2', '10.0.0.4']
    # ingress_hosts = ['10.0.0.1', '10.0.0.2']
    # egress_hosts = ['10.0.0.3', '10.0.0.4']
    # # block_list = ['2', '4']
    # # ingress_hosts = ['1', '2']
    # # egress_hosts = ['3', '4']

    # # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    # symbolic_IP_mapping = {'1': '1', '2':'2', '3':'3'}
    # inverse = False 

    # E_tablename = 'E'
    # E_summary = ['f', 's', 'd']
    # E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    # E_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']

    # E_tuples = [
    #     ('f', 's', 'd0', 's', '1', '{}'), 
    #     ('f', 's1', 'd1', '1', '2', '{}'), 
    #     ('f', 's1', 'd1', '2', '3', '{}'),
    #     ('f', 's2', 'd', '3', 'd', '{}')
    # ]
    # # E_tuples = [
    # #     ('f', 's', 'd', 's', '11.0.0.1', '{}'), 
    # #     ('f', 's', 'd', '11.0.0.1', '11.0.0.2', '{}'), 
    # #     ('f', 's', 'd', '11.0.0.2', 'd', '{}')
    # # ]
    
    # # generate dependencies
    # dependencies, relevant_in_hosts, relevant_out_hosts, block_list = gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping, inverse)

    # '''
    # get whitelist
    # '''
    # gamma_attributes = ['f', 'n', 'x', 'condition']
    # gamma_attributes_datatypes = ['text', 'text', 'text', 'text[]']
    # gamma_summary = None
    # gamma_tablename= "W_{}".format(ordering_strategy)
    # gamma_summary = gen_gamma_table(conn, block_list, ingress_hosts, egress_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, mode)

    
    # Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    # Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
    # Z_tablename = "Z_{}".format(ordering_strategy)
    # Z_tuples = gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
    # # print("block_list", block_list)
    # #step2 and step3
    # ans, count_application = run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
    # print("ans", ans)

    # #========================= inverse: toy example ========================
    # path_nodes = ['1', '2']
    # block_list = ['10.0.0.2', '10.0.0.4']
    # ingress_hosts = ['10.0.0.1', '10.0.0.2']
    # egress_hosts = ['10.0.0.3', '10.0.0.4']

    # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    # inverse = False
    # rewrite_dependencies, relevant_ingress, relevant_egress =  gen_rewrite_dependencies(path_nodes, block_list, ingress_hosts, egress_hosts, symbolic_IP_mapping, inverse)

    # for idx in rewrite_dependencies:
    #     dependency = rewrite_dependencies[idx]
    #     print(f"\n***************************{idx}************************************")
    #     for tuple in dependency['dependency_tuples']:
    #         print(tuple)
    #     print("------------------------------------------------------------------")
    #     print(dependency['dependency_summary'])
    #     print("****************************************************************\n")
    
    # #========================= single gamma ========================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # ordering_strategy='random'
    # orderings=None
    # path_nodes = ['1', '2', '3']
    # block_list = ['10.0.0.2', '10.0.0.4']
    # ingress_hosts = ['10.0.0.1', '10.0.0.2']
    # egress_hosts = ['10.0.0.3', '10.0.0.4']
    # # block_list = ['2', '4']
    # # ingress_hosts = ['1', '2']
    # # egress_hosts = ['3', '4']

    # # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    # symbolic_IP_mapping = {'1': '1', '2':'2', '3':'3'}
    # inverse = False 

    # E_tablename = 'E'
    # E_summary = ['f', 's', 'd']
    # E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    # E_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']

    # E_tuples = [
    #     ('f', 's', 'd0', 's', '1', '{}'), 
    #     ('f', 's1', 'd1', '1', '2', '{}'), 
    #     ('f', 's1', 'd1', '2', '3', '{}'),
    #     ('f', 's2', 'd', '3', 'd', '{}')
    # ]
    
    # # E_tuples = [
    # #     ('f', 's', 'd', 's', '1', '{}'), 
    # #     ('f', 's', 'd', '1', '2', '{}'), 
    # #     ('f', 's', 'd', '2', 'd', '{}')
    # # ]
    # # E_tuples = [
    # #     ('f', 's', 'd', 's', '11.0.0.1', '{}'), 
    # #     ('f', 's', 'd', '11.0.0.1', '11.0.0.2', '{}'), 
    # #     ('f', 's', 'd', '11.0.0.2', 'd', '{}')
    # # ]
    
    # # generate dependencies
    # dependencies, relevant_in_hosts, relevant_out_hosts, block_list = gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping, inverse)

    # '''
    # get whitelist
    # '''
    # gamma_attributes = ['f', 'n', 'x', 'condition']
    # gamma_attributes_datatypes = ['text', 'text', 'text', 'text[]']
    # gamma_summary = ['f', block_list[0], block_list[1]]
    # print("gamma_summary", gamma_summary)
    # gamma_tablename= "W_{}".format(ordering_strategy)
    # gen_empty_table(conn, gamma_tablename, gamma_attributes, gamma_attributes_datatypes)

    
    # Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    # Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
    # Z_tablename = "Z_{}".format(ordering_strategy)
    # gen_empty_table(conn, Z_tablename, Z_attributes, Z_datatypes)
    # # chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    # # exit()
    # whitelists_flows = gen_whitelists(block_list, ingress_hosts, egress_hosts)

    # for flow in whitelists_flows:
        
    #     flow_tuples = [('f', flow[0], flow[1])]
    #     update_table(conn, flow_tuples, gamma_tablename)

    #     Z_tuples = chase.gen_inverse_image_with_destbasedforwarding_applied(conn, E_tuples, gamma_tablename)
    #     update_table(conn, Z_tuples, Z_tablename)

    #     #step2 and step3
    #     ans, count_application = run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
    #     print("flow", flow)
    #     print("ans", ans)
    #     input()

    # # =============================test summary condition=====================
    # new_policy = gen_new_policy()
    # sql = chase.convert_dependency_to_sql(new_policy[2], "z_specific")
    # print(sql)


    # # ============================test new \sigma_new: \sigma_fp and \sigma_bp=============================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # ordering_strategy='random'

    # path_nodes = ['1', '2', '3']
    # security_hole = ['10.0.0.2', '10.0.0.4']
    # ingress_hosts = ['10.0.0.1', '10.0.0.2']
    # egress_hosts = ['10.0.0.3', '10.0.0.4', '10.0.0.5']
    # symbolic_IP_mapping = {'1': '1', '2':'2', '3':'3'}

    # topo_tablename = "l"
    # topo_attributes = ['n', 'x', 'flag']
    # topo_datatypes = ['text', 'text', 'text']
    # topo_tuples = [
    #     ('10.0.0.1', '>1', '0'), 
    #     ('10.0.0.2', '>1', '0'), 
    #     ('>1', '1>', '1'),
    #     ('1>', '>2', '1'),
    #     ('>2', '2>', '1'),
    #     ('2>', '>3', '1'),
    #     ('>3', '3>', '1'),
    #     ('3>', '10.0.0.3', '0'),
    #     ('3>', '10.0.0.4', '0'),
    #     ('3>', '10.0.0.5', '0')
    # ]
    # chase.load_table(conn, topo_attributes, topo_datatypes, topo_tablename, topo_tuples)

    # LP1_tablename = 'lp1'
    # LP1_tuples = [
    #     ('10.0.0.1', '>1', '0'), 
    #     ('10.0.0.2', '>1', '0'), 
    #     ('>1', '1>', '1')
    # ]
    # chase.load_table(conn, topo_attributes, topo_datatypes, LP1_tablename, LP1_tuples)

    # LP2_tablename = 'lp2'
    # LP2_tuples = [
    #     ('1>', '>2', '1'),
    #     ('>2', '2>', '1')
    # ]
    # chase.load_table(conn, topo_attributes, topo_datatypes, LP2_tablename, LP2_tuples)

    # LP3_tablename = 'lp3'
    # LP3_tuples = [
    #     ('2>', '>3', '1'),
    #     ('>3', '3>', '1')
    # ]
    # chase.load_table(conn, topo_attributes, topo_datatypes, LP3_tablename, LP3_tuples)

    # LP4_tablename = 'lp4'
    # LP4_tuples = [
    #     ('3>', '10.0.0.3', '0'),
    #     ('3>', '10.0.0.4', '0'),
    #     ('3>', '10.0.0.5', '0')
    # ]
    # chase.load_table(conn, topo_attributes, topo_datatypes, LP4_tablename, LP4_tuples)

    # # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    

    # E_tablename = 'E'
    # E_summary = ['f', 's', 'd']
    # E_attributes = ['f', 'src', 'dst', 'n', 'x']
    # E_datatypes = ['text', 'text', 'text', 'text', 'text']
    # E_tuples = [
    #     ('f', 's', 'd0', 's', '>1'), 
    #     ('f', 's', 'd0', '>1', '1>'), 
    #     ('f', 's1', 'd1', '1>', '>2'), 
    #     ('f', 's1', 'd1', '>2', '2>'), 
    #     ('f', 's2', 'd2', '2>', '>3'),
    #     ('f', 's2', 'd2', '>3', '3>'),
    #     ('f', 's3', 'd', '3>', 'd')
    # ]
    
    # '''
    # get whitelist
    # '''
    # gamma_attributes = ['f', 'n', 'x']
    # gamma_attributes_datatypes = ['text', 'text', 'text']
    # gamma_summary = ['f', security_hole[0], security_hole[1]]
    # print("gamma_summary", gamma_summary)
    # gamma_tablename= "W_{}".format(ordering_strategy)
    # chase_script.gen_empty_table(conn, gamma_tablename, gamma_attributes, gamma_attributes_datatypes)
    # gamma_tuples = [('f', '10.0.0.2', '10.0.0.3')]
    # chase_script.update_table(conn, gamma_tuples, gamma_tablename)

    
    # intial_T_attributes = ['f', 'src', 'dst', 'n', 'x']
    # intial_T_datatypes = ['text', 'text', 'text', 'text', 'text'] 
    # intial_T_tablename = "T_{}".format(ordering_strategy)

    # intial_T_tuples = [
    #     ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '>1'), 
    #     ('f', '10.0.0.2', '10.0.0.3', '>1', '1>'), 
    #     ('f', 's1', 'd1', '1>', '>2'), 
    #     ('f', 's1', 'd1', '>2', '2>'), 
    #     ('f', 's2', 'd2', '2>', '>3'),
    #     ('f', 's2', 'd2', '>3', '3>'),
    #     ('f', 's3', '10.0.0.3', '3>', '10.0.0.3')
    # ]
    # chase.load_table(conn, intial_T_attributes, intial_T_datatypes, intial_T_tablename, intial_T_tuples)
    # # chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    # # exit()

    # # rewrite_policy = convert_rewrite_policy_to_dependency('10.0.0.2', '10.0.0.3', {'source':None, 'dest':'10.0.0.5'}, 0, path_nodes, symbolic_IP_mapping) 
    # rewrite_policy1 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.2', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.3'}, 0, path_nodes, symbolic_IP_mapping) 
    # rewrite_policy2 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.4'}, 1, path_nodes, symbolic_IP_mapping) 
    # rewrite_policy3 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.4', {'source':'10.0.0.1', 'dest':'10.0.0.5'}, 2, path_nodes, symbolic_IP_mapping) 

    # print_table(conn)
    # input()

    # print("\n---------policy1------------")
    # chase_script.print_policy(rewrite_policy1)
    # # input()
    # chase.apply_policy_as_atomic_unit(conn, rewrite_policy1, intial_T_tablename)
    # chase.apply_sigma_new_atomically(conn, intial_T_tablename, LP2_tablename)
    # print_table(conn)
    # input()

    # print("---------policy2------------")
    # chase_script.print_policy(rewrite_policy2)
    # # input()
    # chase.apply_policy_as_atomic_unit(conn, rewrite_policy2, intial_T_tablename)
    # chase.apply_sigma_new_atomically(conn, intial_T_tablename, LP3_tablename)
    
    # print_table(conn)
    # input()

    # print("---------policy3------------")
    # chase_script.print_policy(rewrite_policy3)
    # # input()
    # chase.apply_policy_as_atomic_unit(conn, rewrite_policy3, intial_T_tablename)
    # chase.apply_sigma_new_atomically(conn, intial_T_tablename, LP4_tablename)
    
    # print_table(conn)
    # input()

    # E_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, intial_T_tablename, gamma_summary)
    # answer = chase.apply_E(conn, E_sql)
    # print("answer", answer)

    # print_table(conn)