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
    print("egress_hosts", egress_hosts)
    egress_hosts.remove(block_list[1]) 
    print("after deleting egress", egress_hosts)
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
    
def convert_rewrite_policy_to_dependency(source, dest, rewrite_value, loc, path_nodes, symbolic_IP_mapping):
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
    for key in rewrite_value.keys():
        if key == 'source' and rewrite_value[key] is not None:
            rewrite_source = rewrite_value[key]
            tgd_summary = ['f', rewrite_source, dest, n_IP, next_node]
            egd_tuples.append(('f2', rewrite_source, dest, n_IP, next_node, '{}'))
        elif key == 'dest' and rewrite_value[key] is not None:
            rewrite_dest = rewrite_value[key]
            

            print("rewrite_dest", rewrite_dest)
            print("next_node", next_node)
            if loc == len(path_nodes) - 1 or loc == -1: # if loc is at the last node, rewrite dest will affect final dest
                egd_tuples.append(('f2', source, rewrite_dest, n_IP, rewrite_dest, '{}'))
                tgd_summary = ['f', source, rewrite_dest, n_IP, rewrite_dest]
            else:
                egd_tuples.append(('f2', source, rewrite_dest, n_IP, next_node, '{}'))
                tgd_summary = ['f', source, rewrite_dest, n_IP, next_node]
            print("egd_tuples", egd_tuples)
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
    block_list = ['2', '4']
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
    firewall_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    firewall_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']
    firewall_dependency = gen_firewall_dependency(block_list, firewall_attributes, firewall_datatypes)
    # print("firewall_dependency", firewall_dependency)

    dependencies[5] = firewall_dependency

    dependencies[6] = gen_new_dependency(path_nodes, symbolic_IP_mapping)

    return dependencies, relevant_in_hosts, relevant_out_hosts, block_list

@timeit
def gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_attributes_datatypes):
    Z_tuples = chase.gen_inverse_image(conn, E_tuples, gamma_tablename)
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
    
    # chase.applySourceDestPolicy(conn, Z_tablename)
    chase.applySourceDestPolicy_new(conn,Z_tablename)
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
            print(dependency['dependency_tuples'])
            print(dependency['dependency_summary'])
            print(dependency['dependency_summary_condition'])
            print("--------------------")
            # input()
            whether_updated = chase.apply_dependency(conn, dependency, Z_tablename)
            temp_updated = (temp_updated or whether_updated)
        does_updated = temp_updated
    print("#count:", count_application)
    query_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, Z_tablename, gamma_summary)
    print("query sql", query_sql)
    answer = chase.apply_E(conn, query_sql)

    return answer, count_application

if __name__ == '__main__':
    #========================= toy example ========================
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    ordering_strategy='random'
    orderings=None
    mode='all'
    path_nodes = ['1', '2']
    # block_list = ['10.0.0.2', '10.0.0.4']
    # ingress_hosts = ['10.0.0.1', '10.0.0.2']
    # egress_hosts = ['10.0.0.3', '10.0.0.4']
    block_list = ['2', '4']
    ingress_hosts = ['1', '2']
    egress_hosts = ['3', '4']

    # symbolic_IP_mapping = {'1': '11.0.0.1', '2':'11.0.0.2'}
    symbolic_IP_mapping = {'1': '1', '2':'2'}
    inverse = True 

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_datatypes = ['text', 'text', 'text', 'text', 'text', 'text[]']

    E_tuples = [
        ('f', 's0', 'd0', 's', '1', '{}'), 
        ('f', 's1', 'd1', '1', '2', '{}'), 
        ('f', 's2', 'd2', '2', 'd', '{}')
    ]
    # E_tuples = [
    #     ('f', 's0', 'd0', 's', '11.0.0.1', '{}'), 
    #     ('f', 's1', 'd1', '11.0.0.1', '11.0.0.2', '{}'), 
    #     ('f', 's2', 'd2', '11.0.0.2', 'd', '{}')
    # ]
    
    # generate dependencies
    dependencies, relevant_in_hosts, relevant_out_hosts, block_list = gen_dependencies_for_chase_distributed_invariants(ingress_hosts.copy(), egress_hosts.copy(), path_nodes, symbolic_IP_mapping, inverse)

    '''
    get whitelist
    '''
    gamma_attributes = ['f', 'n', 'x', 'condition']
    gamma_attributes_datatypes = ['text', 'text', 'text', 'text[]']
    gamma_summary = None
    gamma_tablename= "W_{}".format(ordering_strategy)
    gamma_summary = gen_gamma_table(conn, block_list, ingress_hosts, egress_hosts, gamma_tablename, gamma_attributes, gamma_attributes_datatypes, mode)

    
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_datatypes = ['text', 'text', 'text', 'text', 'text'] # text is much faster than inet_faure?
    Z_tablename = "Z_{}".format(ordering_strategy)
    Z_tuples = gen_Z_for_chase_distributed_invariants(conn, E_tuples, gamma_tablename, Z_tablename, Z_attributes, Z_datatypes)
    # print("block_list", block_list)
    #step2 and step3
    ans, count_application = run_chase_distributed_invariants(conn, E_tuples, E_attributes, E_summary, dependencies, Z_tablename, gamma_summary, order_strategy=ordering_strategy, orderings=orderings)
    print("ans", ans)

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
    