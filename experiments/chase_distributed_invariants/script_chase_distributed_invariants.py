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
from ipaddress import IPv4Address
from utils.logging import timeit
import math
from copy import deepcopy

# conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
# cursor = conn.cursor()

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

def print_table(conn, intial_T_tablename='t_random', intital_T_attributes=['F', 'S', 'D', 'N', 'X']):
    cursor = conn.cursor()
    cursor.execute("select * from {} order by {}".format(intial_T_tablename, ', '.join(intital_T_attributes)))
    print(f"\n*****************************************TABLE:{intial_T_tablename}*******************************************")
    print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*intital_T_attributes))
    print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*['----------------' for i in range(len(intital_T_attributes))]))
    for row in cursor.fetchall():
        print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*row))
    print(f"\n***************************************************************************************************")

    conn.commit()

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

# @timeit
def gen_distributed_invariants_information(file_dir, filename, as_tablename, topo_tablename, num_hosts):
    path_nodes, source, dest = gen_tableau_script.gen_a_chain(file_dir, filename, as_tablename, topo_tablename)
    symbolic_IP_mapping, sourceHosts_interface_mapping, destHosts_interface_mapping, source_hosts, dest_hosts = assign_IPAddresses_to_interface_of_path_nodes(path_nodes, num_hosts)
    # print("symbolic_IP_mapping", symbolic_IP_mapping)
    # print("sourceHosts_interface_mapping", sourceHosts_interface_mapping)
    # print("destHosts_interface_mapping", destHosts_interface_mapping)
    E_tuples = gen_E_tuples(path_nodes, symbolic_IP_mapping)
    # print('E_tuples\n', "\n".join([str(t) for t in E_tuples]))
    # chase.load_table(conn, E_attributes, E_datatypes, E_tablename, E_tuples)

    nodeIdx_policies_mapping, security_hole, related_policies_position, gamma_headers = random_pick(2, 2, path_nodes, source_hosts.copy(), dest_hosts.copy())
    policies = gen_rwfw_policies_after_random_pick(nodeIdx_policies_mapping, path_nodes, symbolic_IP_mapping, source_hosts.copy(), dest_hosts.copy(), sourceHosts_interface_mapping)

    policy_p12 = gen_p12_policy(nodeIdx_policies_mapping, path_nodes, symbolic_IP_mapping)
    policies[20] = policy_p12

    additional_policy = gen_additional_policy(destHosts_interface_mapping)
    policies[21] = additional_policy

    return E_tuples, policies, security_hole, related_policies_position, gamma_headers

# @timeit
def assign_IPAddresses_to_interface_of_path_nodes(path_nodes, num_hosts, IP_address_begin='11.0.0.1'):
    symbolic_IP_mapping = {}
    interface_sourceHosts_mapping = {}
    interface_destHosts_mapping = {}
    sourceHosts_interface_mapping = {}
    destHosts_interface_mapping = {}

    source_hosts = []
    dest_hosts = []
    source_IP_address_begin = '10.0.0.1'
    dest_IP_address_begin = '12.0.0.1'
    sourceAddr = int(IPv4Address(source_IP_address_begin))
    destAddr = int(IPv4Address(dest_IP_address_begin))

    IPaddr = int(IPv4Address(IP_address_begin)) 
    for idx, node in enumerate(path_nodes):
        symbolic_IP_mapping[node] = {'in':[], 'out':[]}
        if idx == 0:
            for i in range(num_hosts):
                symbolic_IP_mapping[node]['in'].append(str(IPv4Address(IPaddr))) 
                interface_sourceHosts_mapping[str(IPv4Address(IPaddr))] = str(IPv4Address(sourceAddr))
                sourceHosts_interface_mapping[str(IPv4Address(sourceAddr))] = str(IPv4Address(IPaddr))
                source_hosts.append(str(IPv4Address(sourceAddr)))
                IPaddr += 1
                sourceAddr += 1

            symbolic_IP_mapping[node]['out'].append(str(IPv4Address(IPaddr))) 
            IPaddr += 1
        elif idx == len(path_nodes) - 1:
            symbolic_IP_mapping[node]['in'].append(str(IPv4Address(IPaddr))) 
            IPaddr += 1
            for i in range(num_hosts):
                symbolic_IP_mapping[node]['out'].append(str(IPv4Address(IPaddr))) 
                interface_destHosts_mapping[str(IPv4Address(IPaddr))] = str(IPv4Address(destAddr))
                destHosts_interface_mapping[str(IPv4Address(destAddr))] = str(IPv4Address(IPaddr))
                dest_hosts.append(str(IPv4Address(destAddr)))
                IPaddr += 1
                destAddr += 1

        else:
            symbolic_IP_mapping[node]['in'].append(str(IPv4Address(IPaddr)))
            IPaddr += 1
            symbolic_IP_mapping[node]['out'].append(str(IPv4Address(IPaddr)))
            IPaddr += 1

    return symbolic_IP_mapping, sourceHosts_interface_mapping, destHosts_interface_mapping, source_hosts, dest_hosts

# @timeit
def gen_E_tuples(path_nodes, symbolic_IP_mapping):
    E_tuples = []
    j = 0
    E_summary = ['f']
    for idx, node in enumerate(path_nodes):
        if idx == 0:
            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            j += 1
            tup = ('f', s, d, s, 'x0')
            E_tuples.append(tup)
            E_summary.append(s)

            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            j += 1
            tup = ('f', s, d, 'x0', symbolic_IP_mapping[node]['out'][0])
            E_tuples.append(tup)

        elif idx == len(path_nodes) - 1:
            
            pre_node = path_nodes[idx-1]
            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            j += 1

            tup = ('f', s, d, symbolic_IP_mapping[pre_node]['out'][0], symbolic_IP_mapping[node]['in'][0])
            E_tuples.append(tup)

            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            
            tup = ('f', s, d, symbolic_IP_mapping[node]['in'][0], 'x{}'.format(j))
            E_tuples.append(tup)
            j += 1

            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            tup = ('f', s, d, 'x{}'.format(j-1), d)
            E_tuples.append(tup)
            j += 1
            E_summary.append(d)
            
        else:
            pre_node = path_nodes[idx-1]
            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            j += 1

            tup = ('f', s, d, symbolic_IP_mapping[pre_node]['out'][0], symbolic_IP_mapping[node]['in'][0])
            E_tuples.append(tup)

            s = 's{}'.format(j)
            d = 'd{}'.format(j)
            j += 1

            tup = ('f', s, d, symbolic_IP_mapping[node]['in'][0], symbolic_IP_mapping[node]['out'][0])
            E_tuples.append(tup)
        
    return E_tuples, E_summary

# @timeit
def random_pick(total_policies, num_related_policies, path_nodes, source_hosts, dest_hosts):
    nodeIdx_policies_mapping = {}

    interval_num = len(path_nodes) / num_related_policies
    begin_idx = 0
    related_position = []
    last_header = None
    security_hole = []
    gamma_headers = []
    for idx in range(num_related_policies):
        if begin_idx not in nodeIdx_policies_mapping.keys():
            nodeIdx_policies_mapping[begin_idx] = []

        header = None
        rw_header = None
        if last_header is None:
            source = random.sample(source_hosts, 1)[0]
            dest = random.sample(dest_hosts, 1)[0]
            source_hosts.remove(source)
            dest_hosts.remove(dest)
            security_hole.append(source)
            header = (source, dest)
            gamma_headers.append(header)
        else:
            header = last_header
        # print("header", header)
        if idx % 2 == 0:
            rw_source = random.sample(source_hosts, 1)[0]
            source_hosts.remove(rw_source)
            rw_header = (rw_source, header[1])
            # print("rw_header1", rw_header)
        else:
            rw_dest = random.sample(dest_hosts, 1)[0]
            dest_hosts.remove(rw_dest)
            rw_header = (header[0], rw_dest)
            # print("rw_header2", rw_header)
        
        if idx == num_related_policies-1:
            security_hole.append(rw_header[1])

        nodeIdx_policies_mapping[begin_idx].append({'type':'rw', 'header': header, 'rw_header': rw_header})

        related_position.append(begin_idx)

        last_header = rw_header

        begin_idx = math.floor(begin_idx + interval_num)

    gamma_headers.append(last_header)
    # print("nodeIdx_policies_mapping", nodeIdx_policies_mapping)
    # print("related_position", related_position)
    # print("security hole", security_hole)

    if 0 in nodeIdx_policies_mapping.keys():
        nodeIdx_policies_mapping[0].append({'type':'fw', 'hole':tuple(security_hole)})
    else:
        nodeIdx_policies_mapping[0]= [{'type':'fw', 'hole':tuple(security_hole)}]
    
    # if 0 not in related_position:
    #     related_position.insert(0, 0)
    
    if len(path_nodes)-1 in nodeIdx_policies_mapping.keys():
        nodeIdx_policies_mapping[len(path_nodes)-1].append({'type':'fw', 'hole':tuple(security_hole)})
    else:
        nodeIdx_policies_mapping[len(path_nodes)-1]= [{'type':'fw', 'hole':tuple(security_hole)}]

    # if len(path_nodes)-1 not in related_position:
    #     related_position.append(len(path_nodes)-1)

    # print("nodeIdx_policies_mapping", nodeIdx_policies_mapping)
    # print("related_position", related_position)
    # print("security hole", security_hole)

    num_unrelated_policies = total_policies - num_related_policies

    # num_rw_policies = num_unrelated_policies
    # num_fw_policies = 0
    num_rw_policies = num_unrelated_policies // 2
    num_fw_policies = num_unrelated_policies - num_rw_policies

    for idx in range(num_rw_policies):
        p_idx = random.sample(range(len(path_nodes)), 1)[0]
        # p_idx = random.sample(related_position, 1)[0]

        source = random.sample(source_hosts, 1)[0]
        dest = random.sample(dest_hosts, 1)[0]
        header = (source, dest)

        if idx % 2 == 0:
            rw_source = random.sample(source_hosts, 1)[0]
            # while rw_source == source:
            #     rw_source = random.sample(source_hosts, 1)[0]
            rw_header = (rw_source, header[1])
        else:
            rw_dest = random.sample(dest_hosts, 1)[0]
            # while rw_dest == dest:
            #     rw_dest = random.sample(dest_hosts, 1)[0]
            rw_header = (header[0], rw_dest)

        if p_idx in nodeIdx_policies_mapping.keys():
            nodeIdx_policies_mapping[p_idx].append({'type':'rw', 'header': header, 'rw_header': rw_header})
        else:
            nodeIdx_policies_mapping[p_idx] = [{'type':'rw', 'header': header, 'rw_header': rw_header}]

    for idx in range(num_fw_policies):
        p_idx = random.sample(range(len(path_nodes)), 1)[0]
        # p_idx = random.sample(related_position, 1)[0]

        source = random.sample(source_hosts, 1)[0]
        dest = random.sample(dest_hosts, 1)[0]
        hole = (source, dest)

        if p_idx in nodeIdx_policies_mapping.keys():
            nodeIdx_policies_mapping[p_idx].append({'type':'fw', 'hole': hole})
        else:
            nodeIdx_policies_mapping[p_idx] = [{'type':'fw', 'hole': hole}]

    # print("\n")
    # print("nodeIdx_policies_mapping", nodeIdx_policies_mapping)
    return nodeIdx_policies_mapping, security_hole, related_position, gamma_headers

# @timeit
def gen_rwfw_policies_after_random_pick(nodeIdx_policies_mapping, path_nodes, symbolic_IP_mapping, source_hosts, dest_hosts, sourceHosts_interface_mapping):
    policies = {}
    nodeIdxs = sorted(list(nodeIdx_policies_mapping.keys()))
    # print("nodeIdxs", nodeIdxs)
    policy_idx = 0
    related_policy_idxs = []
    for nodeIdx in nodeIdxs:
        dependencies  = []
        filters = []
        header_rwheader_mapping = {}
        # print("policies", nodeIdx_policies_mapping[nodeIdx])
        for policy in nodeIdx_policies_mapping[nodeIdx]:
            if policy['type'] == 'fw':
                filters.append(policy['hole'])
            elif policy['type'] == 'rw':
                header_rwheader_mapping[policy['header']] = policy['rw_header']
        
        for header in header_rwheader_mapping.keys():
            dependency = convert_to_rwfw_dependency(header, header_rwheader_mapping[header], nodeIdx, path_nodes, symbolic_IP_mapping, sourceHosts_interface_mapping)
            dependencies.append(deepcopy(dependency))

        for source in source_hosts:
            for dest in dest_hosts:
                temp_header = (source, dest)

                if temp_header not in filters and temp_header not in header_rwheader_mapping.keys():
                    dependency = convert_to_rwfw_dependency(temp_header, temp_header, nodeIdx, path_nodes, symbolic_IP_mapping, sourceHosts_interface_mapping)
                    dependencies.append(deepcopy(dependency))
        
        # for dependency in dependencies:
        #     print_dependency(dependency)
        # input()
        
        related_policy_idxs.append(policy_idx)
        for i in range(len(nodeIdx_policies_mapping[nodeIdx])):
            policies[policy_idx] = deepcopy(dependencies)
            policy_idx += 1
        
        # related_policy_idxs.append(nodeIdx)
        # policies[nodeIdx] = deepcopy(dependencies)

    return policies, related_policy_idxs

# @timeit
def convert_to_rwfw_dependency(header, rw_header, loc, path_nodes, symbolic_IP_mapping, sourceHosts_interface_mapping):
    tuples = None
    
    node = path_nodes[loc]
    if loc == 0:
        tuples = [
            ('f', header[0], header[1], header[0], sourceHosts_interface_mapping[header[0]]),
            ('f', 's', 'd', sourceHosts_interface_mapping[header[0]], symbolic_IP_mapping[node]['out'][0])
        ]
    elif loc == len(path_nodes) - 1:
        pre_node = path_nodes[loc-1]
        tuples = [
            ('f', header[0], header[1], symbolic_IP_mapping[pre_node]['out'][0], symbolic_IP_mapping[node]['in'][0]),
            ('f', 's', 'd', symbolic_IP_mapping[node]['in'][0], 'x')
        ]
    else:
        pre_node = path_nodes[loc-1]
        tuples = [
            ('f', header[0], header[1], symbolic_IP_mapping[pre_node]['out'][0], symbolic_IP_mapping[node]['in'][0]),
            ('f', 's', 'd', symbolic_IP_mapping[node]['in'][0], symbolic_IP_mapping[node]['out'][0])
        ]
    summary = ["s = {}".format(rw_header[0]), "d = {}".format(rw_header[1])]
    edg_dependency = {
        "dependency_tuples": tuples,
        "dependency_attributes": ['f', 'src', 'dst', 'n', 'x'],
        # "dependency_attributes": ['c0', 'c1', 'c2', 'c3', 'c4'],
        "dependency_attributes_datatypes": ["text", "text", "text", "text", "text"], 
        "dependency_summary": summary,
        "dependency_summary_condition": None,
        "dependency_type": 'egd'
    }

    return edg_dependency

# @timeit
def gen_p12_policy(nodeIdx_policies_mapping, path_nodes, symbolic_IP_mapping):
    nodeIdxs = sorted(list(nodeIdx_policies_mapping.keys()))

    policy = []
    for idx in range(len(nodeIdxs)-1):
        fromIdx = nodeIdxs[idx]
        toIdx = nodeIdxs[idx+1]

        for nodeIdx in range(fromIdx, toIdx):
            tuples = None
            node = path_nodes[nodeIdx]
            next_node = path_nodes[nodeIdx+1]
            if nodeIdx != fromIdx:
                tuples = [
                    ('f', 's1', 'd1', 'n', symbolic_IP_mapping[node]['in'][0]),
                    ('f', 's2', 'd2', symbolic_IP_mapping[node]['in'][0], symbolic_IP_mapping[node]['out'][0])  
                ]
                egd_dependency = {
                    'dependency_tuples': tuples, 
                    'dependency_summary': ["s2 = s1", "d2 = d1"], 
                    'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
                    'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
                    'dependency_summary_condition': None, 
                    'dependency_type': 'egd'
                }
                policy.append(deepcopy(egd_dependency))

            tuples = [
                ('f', 's1', 'd1', 'n', symbolic_IP_mapping[node]['out'][0]),
                ('f', 's2', 'd2', symbolic_IP_mapping[node]['out'][0], symbolic_IP_mapping[next_node]['in'][0])  
            ]
            egd_dependency = {
                'dependency_tuples': tuples, 
                'dependency_summary': ["s2 = s1", "d2 = d1"], 
                'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
                'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
                'dependency_summary_condition': None, 
                'dependency_type': 'egd'
            }
            policy.append(deepcopy(egd_dependency))
    
    tuples = [
        ('f', 's1', 'd1', 'n', 'x'),
        ('f', 's2', 'd2', 'x', 'd2')  
    ]
    egd_dependency = {
        'dependency_tuples': tuples, 
        'dependency_summary': ["s2 = s1", "d2 = d1"], 
        'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
        'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
        'dependency_summary_condition': None, 
        'dependency_type': 'egd'
    }
    policy.append(deepcopy(egd_dependency))

    # print("idxs", nodeIdxs) 
    # for dependency in policy:
    #     print_dependency(dependency)
    return policy

# @timeit
def gen_additional_policy(destHosts_interface_mapping):

    policy = []
    for dest in destHosts_interface_mapping.keys():

        egd_dependency = {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', dest),
            ], 
            'dependency_summary': ["n = {}".format(destHosts_interface_mapping[dest])], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }

        policy.append(deepcopy(egd_dependency))
    
    return policy

@timeit
def chase_dependency_as_unit(conn, chasing_tablename, dependencies, order_strategy="random", orderings=None):
    count_application = 0 # count the number of the application of the chase
    count_iterations = 0 # count the number of iterations
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    ordered_indexs = list(dependencies.keys())
    while does_updated:
        if order_strategy.lower() == 'random':
            random.shuffle(ordered_indexs)
        elif order_strategy.lower() == 'specific':
            ordered_indexs = orderings
        else:
            print("wrong ordering strategy,", order_strategy, "please choose from 'random_permutation', 'fixed_permutation', 'specific'")
            exit()
        
        temp_updated = False
        for idx in ordered_indexs:
            # print("policy index", idx)
            dependency = dependencies[idx]
            
            # print_policy(policy)
            # input()
            whether_updated, counts = chase.apply_dependency_as_atomic(conn, dependency, chasing_tablename)
            count_application += counts
            temp_updated = (temp_updated or whether_updated)
            # print("whether_updated", whether_updated)
            # input()
        does_updated = temp_updated
        count_iterations += 1

        # print("iteration", count_iterations)
        # print("#applications", count_application)
    return count_application, count_iterations

@timeit
def chase_policy_as_unit(conn, chasing_tablename, policies, order_strategy="random", orderings=None):
    count_application = 0 # count the number of the application of the chase
    count_iterations = 0 # count the number of iterations
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 

    ordered_indexs = list(policies.keys())
    # print_table(conn, chasing_tablename, ['f', 'src', 'dst', 'n', 'x'])
    # input()
    while does_updated:
        if order_strategy.lower() == 'random':
            random.shuffle(ordered_indexs)
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
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, chasing_tablename)
            # print("counts", counts, "#dep in policy", len(policy))
            # print_policy(policy)
            # print_table(conn, chasing_tablename, ['f', 'src', 'dst', 'n', 'x'])
            # input()
            count_application += counts
            temp_updated = (temp_updated or whether_updated)
        
        does_updated = temp_updated
        count_iterations += 1
        # print("iteration", count_iterations)
        # print("#applications", count_application)
        # print_table(conn, chasing_tablename, ['f', 'src', 'dst', 'n', 'x'])
        # print("count_iterations", count_iterations)
        # input()
    return count_application, count_iterations

# @timeit
def gen_inverse_image(E_tuples, gamma_tuples, sourceHosts_interface_mapping):
    inverse_image_tuples = []
    for g_idx, gamma_tup in enumerate(gamma_tuples):
        for tup in E_tuples:
            t = []
            for item in tup:
                if item == 'f':
                    t.append(gamma_tup[0])
                elif item == 's0':
                    t.append(gamma_tup[1])
                elif item == 'd0':
                    t.append(gamma_tup[2])
                elif item == 'x0':
                    t.append(sourceHosts_interface_mapping[gamma_tup[1]])
                elif item.startswith('s') or item.startswith('d') or item.startswith('x'):
                    t.append("{}_{}".format(item, g_idx))
                else:
                    t.append(item)
            inverse_image_tuples.append(t)
        
    # print("\n".join([str(t) for t in inverse_image_tuples]))

    return inverse_image_tuples


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

@timeit
def the_chase(conn, initial_T, policies):
    """
    Parameters:
    ------------
    conn: psycopg2.connect()
        instance of connention

    initial_T_tablename: string
        The tablename of input table (initial table)

    initial_T_tuples: list
        A list of tuples for `initial_T_tablename`

    policies: list
        A list of policies. A policy contains multiple dependencies. The format of dependency:
        {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }
    """
    initial_T_tablename, initial_T_tuples, initial_T_attributes, initial_T_datatypes = initial_T['tablename'], initial_T['tuples'], initial_T['attributes'], initial_T['datatypes']
    
    chase.load_table(conn, initial_T_attributes, initial_T_datatypes, initial_T_tablename, initial_T_tuples)
    dict_policies = {}
    for idx in range(len(policies)):
        dict_policies[idx] = policies[idx]
    
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    orderings = list(dict_policies.keys()) 
    while does_updated:
        random.shuffle(orderings)
        # print_table(conn, initial_T_tablename)
        # input()
        temp_updated = False
        for idx in orderings:
            policy = dict_policies[idx]
            # print_policy(policy)
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, initial_T_tablename)
            temp_updated = (temp_updated or whether_updated)
            # print_table(conn, initial_T_tablename)
            # input()
        does_updated = temp_updated
    print_table(conn, initial_T_tablename, initial_T_attributes)

if __name__ == '__main__':
    # ============================test new \sigma_new: \sigma_fp and \sigma_bp=============================
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    AS_num = 7018

    file_dir  = '/../../topo/ISP_topo/'
    filename = "{}_edges.txt".format(AS_num)

    as_tablename = 'as_{}'.format(AS_num)
    topo_tablename = "topo_{}".format(AS_num)
    E_tablename = 'E'
    E_attributes = ['f', 'src', 'dst', 'n', 'x']
    E_datatypes = ['text', 'text', 'text', 'text', 'text']
    num_hosts = 3
    gen_distributed_invariants_information(file_dir, filename, as_tablename, topo_tablename, num_hosts)    
    # # replace A with 9, B with 10, C with 11, D with 12
    # initial_T_tuples = [
    #     ('f2', '10', '11', '10', '2'),
    #     ('f2', 's9', 'd9', '2', '3'),
    #     ('f2', 's10', 'd10', '3', '4'),
    #     ('f2', 's11', 'd11', '4', '5'),
    #     ('f2', 's12', 'd12', '5', '6'),
    #     ('f2', 's13', 'd13', '6', 'x13'),
    #     ('f2', 's14', 'd14', 'x13', 'd14'),
    # ]

    # initial_T = {
    #     'tablename': 'T',
    #     'tuples': initial_T_tuples,
    #     'attributes': ['f', 'src', 'dst', 'n', 'x'],
    #     'datatypes': ['text', 'text', 'text', 'text', 'text']
    # }

    # policy_p1 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '10', '11', '10', '2'),
    #             ('f', 's', 'd', '2', '3')
    #         ], 
    #         'dependency_summary': ["s = 9", "d = 11"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }, 
    #     {
    #         'dependency_tuples': [
    #             ('f', '9', '11', '9', '1'),
    #             ('f', 's', 'd', '1', '3')
    #         ], 
    #         'dependency_summary': ["s = 9", "d = 11"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', '9', '12', '9', '1'),
    #             ('f', 's', 'd', '1', '3')
    #         ], 
    #         'dependency_summary': ["s = 9", "d = 12"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # policy_p2 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '9', '11', '5', '6'),
    #             ('f', 's', 'd', '6', 'x')
    #         ], 
    #         'dependency_summary': ["s = 9", "d = 12"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }, 
    #     {
    #         'dependency_tuples': [
    #             ('f', '9', '12', '5', '6'),
    #             ('f', 's', 'd', '6', 'x')
    #         ], 
    #         'dependency_summary': ["s = 9", "d = 12"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', '10', '11', '5', '6'),
    #             ('f', 's', 'd', '6', 'x')
    #         ], 
    #         'dependency_summary': ["s = 10", "d = 11"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # policy_p12 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', 's1', 'd1', 'n', '3'),
    #             ('f', 's2', 'd2', '3', '4')
    #         ], 
    #         'dependency_summary': ["s2 = s1", "d2 = d1"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', 's1', 'd1', 'n', '4'),
    #             ('f', 's2', 'd2', '4', '5')
    #         ], 
    #         'dependency_summary': ["s2 = s1", "d2 = d1"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', 's1', 'd1', 'n', '5'),
    #             ('f', 's2', 'd2', '5', '6')
    #         ], 
    #         'dependency_summary': ["s2 = s1", "d2 = d1"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', 's1', 'd1', 'n', 'x1'),
    #             ('f', 's2', 'd2', 'x1', 'd2')
    #         ], 
    #         'dependency_summary': ["s2 = s1", "d2 = d1"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # additional_policy = [
    #     {
    #         'dependency_tuples': [
    #             ('f', 's', 'd', 'n', '11'),
    #         ], 
    #         'dependency_summary': ["n = 7"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', 's', 'd', 'n', '12'),
    #         ], 
    #         'dependency_summary': ["n = 8"], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # policies = [policy_p1, policy_p2, policy_p12, additional_policy]

    # start_time = time.time()
    # the_chase(conn, initial_T, policies)
    # end_time = time.time()
    # print("running time", end_time- start_time)