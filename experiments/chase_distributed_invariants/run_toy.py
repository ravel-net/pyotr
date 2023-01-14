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
import experiments.chase_distributed_invariants.script_chase_distributed_invariants as chase_script
import databaseconfig as cfg
from utils.logging import timeit
import math
from copy import deepcopy

def gen_topo(conn, topo_tablename, topo_tuples, topo_attributes = ['n', 'x', 'flag'], topo_datatypes = ['text', 'text', 'text']):
    chase.load_table(conn, topo_attributes, topo_datatypes, topo_tablename, topo_tuples)

def gen_intial_table(conn, intial_T_tuples, intial_T_tablename):
    intial_T_attributes = ['f', 'src', 'dst', 'n', 'x']
    intial_T_datatypes = ['text', 'text', 'text', 'text', 'text'] 

    # intial_T_tuples = [
    #     ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '>1'), 
    #     ('f', '10.0.0.2', '10.0.0.3', '>1', '1>'), 
    #     ('f', 's1', 'd1', '1>', '>2'), 
    #     ('f', 's1', 'd1', '>2', '2>'), 
    #     ('f', 's2', 'd2', '2>', '>3'),
    #     ('f', 's2', 'd2', '>3', '3>'),
    #     ('f', 's3', '10.0.0.3', '3>', '10.0.0.3')
    # ]
    chase.load_table(conn, intial_T_attributes, intial_T_datatypes, intial_T_tablename, intial_T_tuples)

def print_table(conn, intial_T_tablename='t_random'):
    cursor = conn.cursor()
    cursor.execute("select * from {}".format(intial_T_tablename))
    print(f"\n*****************************************TABLE:{intial_T_tablename}*******************************************")
    print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*['F', 'S', 'D', 'N', 'X']))
    print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*['----------------', '----------------', '----------------','----------------','----------------',]))
    for row in cursor.fetchall():
        print('| {:<16} | {:<16} | {:<16} | {:<16} | {:<16} |'.format(*row))
    print(f"\n***************************************************************************************************")

    conn.commit()

def gen_sigma_new_sqls(pairs_tables=[], rewrite_infos=[]):
    sigma_new_sqls = []
    for idx, pairs in enumerate(pairs_tables):
        rewriting = rewrite_infos[idx]

        '''
        f(x_f, 10.2, 10.3, x_x, x_next) :- f(x_f, 10.2, 10.3, x_n, x_x), lp1(x_x, x_next, 1)
        f(x_f, 10.2, 10.3, x_x, 10.3) :- f(x_f, 10.2, 10.3, x_n, x_x), lp1(x_x, 10.3, 0)
        f(x_f, 10.2, 10.3, x_pre, x_n) :- f(x_f, 10.2, 10.3, x_n, x_x), lp1(x_pre, x_n, 1)
        f(x_f, 10.2, 10.3, 10.2, x_n) :- f(x_f, 10.2, 10.3, x_n, x_x), lp1(10.2, x_n, 0)
        '''
        sigma_fp1_sql = "select t0.f as f, '{src}' as src, '{dst}' as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.src = '{src}' and t0.dst = '{dst}' and t0.x = t1.n and t1.flag = '1'".format(
            src=rewriting[0],
            dst=rewriting[1],
            f=pairs[0],
            l=pairs[1])
        sigma_fp2_sql = "select t0.f as f, '{src}' as src, '{dst}' as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.src = '{src}' and t0.dst = '{dst}' and t0.x = t1.n and t1.x = '{dst}' and t1.flag = '0'".format(
            src=rewriting[0],
            dst=rewriting[1],
            f=pairs[0],
            l=pairs[1])

        sigma_bp1_sql = "select t0.f as f, '{src}' as src, '{dst}' as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.src = '{src}' and t0.dst = '{dst}' and t0.n = t1.x and t1.flag = '1'".format(
            src=rewriting[0],
            dst=rewriting[1],
            f=pairs[0],
            l=pairs[1])
        sigma_bp2_sql = "select t0.f as f, '{src}' as src, '{dst}' as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.src = '{src}' and t0.dst = '{dst}' and t0.n = t1.x and t1.n = '{src}' and t1.flag = '0'".format(
            src=rewriting[0],
            dst=rewriting[1],
            f=pairs[0],
            l=pairs[1])

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def run_the_chase(conn, intitial_T_tablename, initial_T_tuples, policies, sigma_new_sqls, E_tuples, security_hole):
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
        if the dependency is a firewall dependency, the dependency summary must be emtpy. It's a deletion
    
    E_tuples: list
        A list of tuples for mapping E query
    
    security_hole: tuple
        (source, dest). The checking security hole from source to dest
    
    """
    
    gen_intial_table(conn, initial_T_tuples, intitial_T_tablename)
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    answer = None
    while does_updated:

        temp_updated = False
        for policy in policies:
            # print(policy)
            # exit()
            chase_script.print_policy(policy)
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, intitial_T_tablename)
            temp_updated = (temp_updated or whether_updated)

        whether_updated = chase.apply_sigma_new_atomically_toy(conn, sigma_new_sqls, intitial_T_tablename)
        temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated

    E_tablename = 'E'
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x']
    gamma_summary = ['f', security_hole[0], security_hole[1]]
    E_sql = chase.gen_E_query(E_tuples, E_attributes, E_summary, intitial_T_tablename, gamma_summary)

    answer = chase.apply_E(conn, E_sql)
    # print("answer:", answer)

    return answer
    

if __name__ == '__main__':
    # ============================toy example in the paper=============================
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    
    security_hole = ['10.0.0.2', '10.0.0.4']
    rewrite_policy1 = [
        {
            'dependency_tuples': [
                ('f', '10.0.0.2', '10.0.0.3', '1', '2')
            ], 
            'dependency_summary': ['f', '10.0.0.1', '10.0.0.3', '1', '2'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '10.0.0.2', '10.0.0.3', '1', '2'), 
                ('f2', '10.0.0.1', '10.0.0.3', '1', '2')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy2 = [
        {
            'dependency_tuples': [
                ('f', '10.0.0.1', '10.0.0.3', '3', '10.0.0.3')
            ], 
            'dependency_summary': ['f', '10.0.0.1', '10.0.0.4', '3', '10.0.0.4'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '10.0.0.1', '10.0.0.3', '3', '10.0.0.3'), 
                ('f2', '10.0.0.1', '10.0.0.4', '3', '10.0.0.4')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    firewall_policy1 = [
        {
            'dependency_tuples': [
                ('f', 's', 'd', '1', 'x_x')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': [],  # summary is empty for firewall dependency
            'dependency_summary_condition': ["s = 10.0.0.2", "d = 10.0.0.4"], 
            'dependency_type': 'egd'
        }
    ]

    firewall_policy2 = [
        {
            'dependency_tuples': [
                ('f', 's', 'd', '3', 'x_x')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': [],  # summary is empty for firewall dependency
            'dependency_summary_condition': ["s = 10.0.0.2", "d = 10.0.0.4"], 
            'dependency_type': 'egd'
        }
    ]

    intial_T_tablename = "T"
    intial_T_tuples = [
        ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '1')
    ]

    E_tuples = [
        ('f', 's', 'd0', 's', '1'), 
        ('f', 's1', 'd1', '1', '2'), 
        ('f', 's2', 'd2', '2', '3'),
        ('f', 's3', 'd', '3', 'd')
    ]

    topology_tablename = "L"
    topo_attributes = ['f', 'src', 'dst']
    topo_datatypes = ['text', 'text', 'text']
    topo_tuples = [
        ('10.0.0.1', '1', '0'), 
        ('10.0.0.2', '1', '0'), 
        ('1', '2', '1'),
        ('2', '3', '1'),
        ('3', '10.0.0.3', '0'),
        ('3', '10.0.0.4', '0'),
        ('3', '10.0.0.5', '0')
    ]
    
    gen_topo(conn, topo_tablename=topology_tablename, topo_tuples=topo_tuples)

    sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t1.flag = '1'".format(intial_T_tablename, topology_tablename)
    sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t0.dst = t1.x and t1.flag = '0'".format(intial_T_tablename, topology_tablename)

    sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t1.flag = '1'".format(intial_T_tablename, topology_tablename)
    sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t0.src = t1.n and t1.flag = '0'".format(intial_T_tablename, topology_tablename)


    sigma_new_sqls = [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    policies = [rewrite_policy1, rewrite_policy2, firewall_policy1, firewall_policy2]

    answer = run_the_chase(conn=conn, 
                    intitial_T_tablename=intial_T_tablename, 
                    initial_T_tuples=intial_T_tuples, 
                    policies=policies, 
                    sigma_new_sqls=sigma_new_sqls, 
                    E_tuples=E_tuples, 
                    security_hole=security_hole
                )
    
    print_table(conn, intial_T_tablename)
    print("Answer:", answer)


    # # ============================test idea=============================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # ordering_strategy='random'

    # path_nodes = ['1', '2', '3']  # the node of the chain
    # security_hole = ['10.0.0.2', '10.0.0.4']  # the security hole
    # ingress_hosts = ['10.0.0.1', '10.0.0.2'] # list of ingress hosts, IP prefixes
    # egress_hosts = ['10.0.0.3', '10.0.0.4', '10.0.0.5'] # list of egress hosts, IP prefixes
    # symbolic_IP_mapping = {'1': '1', '2':'2', '3':'3'} 
    
    # LP1_tablename = 'lp1'
    # LP1_tuples = [
    #     ('10.0.0.1', '>1', '0'), 
    #     ('10.0.0.2', '>1', '0'), 
    #     ('>1', '1>', '1')
    # ]
    # gen_topo(conn, topo_tablename=LP1_tablename, topo_tuples=LP1_tuples)

    # LP2_tablename = 'lp2'
    # LP2_tuples = [
    #     ('1>', '>2', '1'),
    #     ('>2', '2>', '1')
    # ]
    # gen_topo(conn, topo_tablename=LP2_tablename, topo_tuples=LP2_tuples)

    # LP3_tablename = 'lp3'
    # LP3_tuples = [
    #     ('2>', '>3', '1'),
    #     ('>3', '3>', '1')
    # ]
    # gen_topo(conn, topo_tablename=LP3_tablename, topo_tuples=LP3_tuples)

    # LP4_tablename = 'lp4'
    # LP4_tuples = [
    #     ('3>', '10.0.0.3', '0'),
    #     ('3>', '10.0.0.4', '0'),
    #     ('3>', '10.0.0.5', '0')
    # ]
    # gen_topo(conn, topo_tablename=LP4_tablename, topo_tuples=LP4_tuples)

    # E_tuples = [
    #     ('f', 's', 'd0', 's', '>1'), 
    #     ('f', 's', 'd0', '>1', '1>'), 
    #     ('f', 's1', 'd1', '1>', '>2'), 
    #     ('f', 's1', 'd1', '>2', '2>'), 
    #     ('f', 's2', 'd2', '2>', '>3'),
    #     ('f', 's2', 'd2', '>3', '3>'),
    #     ('f', 's3', 'd', '3>', 'd')
    # ]
    
    # intial_T_tablename = "T_{}".format(ordering_strategy)

    # intial_T_tuples = [
    #     ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '>1'), 
    #     ('f', '10.0.0.2', '10.0.0.3', '>1', '1>')
    # ]

    # rewrite_policy1 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.2', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.3'}, 0, path_nodes, symbolic_IP_mapping) 
    # rewrite_policy2 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.4'}, 1, path_nodes, symbolic_IP_mapping) 
    # rewrite_policy3 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.4', {'source':'10.0.0.1', 'dest':'10.0.0.5'}, 2, path_nodes, symbolic_IP_mapping) 
    # # rewrite_policy3 = chase_script.convert_rewrite_policy_to_dependency('10.0.0.1', '10.0.0.3', {'source':'10.0.0.1', 'dest':'10.0.0.4'}, 2, path_nodes, symbolic_IP_mapping) 

    # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4'), ('10.0.0.1', '10.0.0.5')]
    # # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4')]
    # # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]

    # sigma_new_sqls = gen_sigma_new_sqls(pairs_tables, rewrite_infos)

    # answer = run_the_chase(conn, intial_T_tablename, intial_T_tuples, [rewrite_policy1, rewrite_policy2, rewrite_policy3], sigma_new_sqls, E_tuples, security_hole)
    
    # print_table(conn, intial_T_tablename)
    # print("answer", answer)