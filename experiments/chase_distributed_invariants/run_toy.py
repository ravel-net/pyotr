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
from Core.Homomorphism.Datalog.program import DT_Program
from utils.logging import timeit
import math
from copy import deepcopy

def gen_topo(conn, topo_tablename, topo_tuples, topo_attributes = ['c0', 'c1', 'c2'], topo_datatypes = ['text', 'text', 'integer']):
    chase.load_table(conn, topo_attributes, topo_datatypes, topo_tablename, topo_tuples)

def gen_intial_table(conn, intial_T_tuples, intial_T_tablename):
    intial_T_attributes = ['f', 'src', 'dst', 'n', 'x']
    # intial_T_attributes = ['c0', 'c1', 'c2', 'c3', 'c4']
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

def gen_sigma_new_sqls2(pairs_tables=[]):
    sigma_new_sqls = []
    for idx, pairs in enumerate(pairs_tables):
        '''
        f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, 1), B1(x_s1, x_d2), x_s != x_s1, x_d != x_d1
        f(x_f, x_s, x_d, x_x, x_d) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_d, 0), B1(x_s1, x_d2), x_s != x_s1, x_d != x_d1
        f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, 1), B1(x_s1, x_d2), x_s != x_s1, x_d != x_d1
        f(x_f,  x_s, x_d, x_s, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_s, x_n, 0), B1(x_s1, x_d2), x_s != x_s1, x_d != x_d1
        '''
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, {b} t2 where t0.x = t1.n and t1.flag = '1' and (t0.src != t2.src and t0.dst != t2.dst)".format(
            f=pairs[0],
            l=pairs[1], 
            b=pairs[2])
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, {b} t2 where t0.x = t1.n and t1.x = t0.dst and t1.flag = '0' and (t0.src != t2.src and t0.dst != t2.dst)".format(
            f=pairs[0],
            l=pairs[1], 
            b=pairs[2])

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, {b} t2 where t0.n = t1.x and t1.flag = '1' and (t0.src != t2.src and t0.dst != t2.dst)".format(
            f=pairs[0],
            l=pairs[1], 
            b=pairs[2])
        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, {b} t2 where t0.n = t1.x and t1.n = t0.src and t1.flag = '0' and (t0.src != t2.src and t0.dst != t2.dst)".format(
            f=pairs[0],
            l=pairs[1], 
            b=pairs[2])

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

        # sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x \
        #                 from {f} t0 inner join {l} t1 \
        #                 on t0.x = t1.n and t1.flag = '1' \
        #                 left join {b} t2 on t0.src != t2.src and t0.dst != t2.dst".format(
        #     f=pairs[0],
        #     l=pairs[1], 
        #     b=pairs[2])
        # sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x \
        #                 from {f} t0 inner join {l} t1 \
        #                 on t0.x = t1.n and t1.x = t0.dst and t1.flag = '0' \
        #                 left join {b} t2 on t0.src != t2.src and t0.dst != t2.dst".format(
        #     f=pairs[0],
        #     l=pairs[1], 
        #     b=pairs[2])

        # sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x \
        #                 from {f} t0 inner join {l} t1 \
        #                 on t0.n = t1.x and t1.flag = '1'\
        #                 left join {b} t2 on t0.src != t2.src and t0.dst != t2.dst".format(
        #     f=pairs[0],
        #     l=pairs[1], 
        #     b=pairs[2])
        # sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x \
        #                 from {f} t0 inner join {l} t1 on t0.n = t1.x and t1.n = t0.src and t1.flag = '0'\
        #                 left join {b} t2 on t0.src != t2.src and t0.dst != t2.dst".format(
        #     f=pairs[0],
        #     l=pairs[1], 
        #     b=pairs[2])

    return sigma_new_sqls

def gen_sigma_new_sqls3(pairs_tables=[], rewriting_infos=[]):
    '''
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, 1), x_s != 2, x_d != 8
    f(x_f, x_s, x_d, x_x, x_d) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_d, 0), x_s != 2, x_d != 8
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, 1)
    f(x_f,  x_s, x_d, x_s, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_s, x_n, 0)
    '''
    sigma_new_sqls = []
    block_conditions = []
    for idx, pairs in enumerate(pairs_tables):
        if idx != 0:
            rewriting = rewriting_infos[idx-1]
            condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
            block_conditions.append(condition)
        
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.flag = '1'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.x = t0.dst and t1.flag = '0'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.flag = '1'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.n = t0.src and t1.flag = '0'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls_general(pairs_tables=[]):
    sigma_new_sqls = []
    for idx, pairs in enumerate(pairs_tables):
        '''
        f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp(x_x, x_next, 1)
        f(x_f, x_s, x_d, x_x, x_d) :- f(x_f, x_s, x_d, x_n, x_x), lp(x_x, x_d, 0)
        f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp(x_pre, x_n, 1)
        f(x_f, x_s, x_d, x_s, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp(x_s, x_n, 0)
        '''
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.flag = '1'".format(
            f=pairs[0],
            l=pairs[1])
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.x = t0.dst and t1.flag = '0'".format(
            f=pairs[0],
            l=pairs[1])

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.flag = '1'".format(
            f=pairs[0],
            l=pairs[1])
        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.n = t0.src and t1.flag = '0'".format(
            f=pairs[0],
            l=pairs[1])

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls_DT_program(string_program, databaseTypes={}):
    program = DT_Program(string_program, databaseTypes)

    sqls = []
    for rule in program._rules:
        sql = rule.convertRuleToSQL()
        sqls.append(sql)

    return sqls

def run_the_chase(conn, initial_T_tablename, initial_T_tuples, policies, sigma_new_program, databaseTypes={}):
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
    
    sigma_new_program: string
        A datalog program. Format: program = "rule1\nrule2\n..."
    
    databaseTypes: dict
        it is a dictionary {"database name":[ordered list of column types]}. 
        By default, all column types are integers. 
        If we need some other datatype, we need to specify using this parameter
    """
    
    gen_intial_table(conn, initial_T_tuples, initial_T_tablename)
    sigma_new_sqls = gen_sigma_new_sqls_DT_program(sigma_new_program, databaseTypes=databaseTypes)
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    answer = None
    while does_updated:

        temp_updated = False
        for policy in policies:
            # print(policy)
            # exit()
            chase_script.print_policy(policy)
            # input()
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, initial_T_tablename)
            temp_updated = (temp_updated or whether_updated)
            # print_table(conn, intial_T_tablename)

        # input()
        whether_updated = chase.apply_sigma_new_atomically_toy(conn, sigma_new_sqls, initial_T_tablename)
        # print_table(conn, intial_T_tablename)
        temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated

    # print("answer:", answer)

    print_table(conn, initial_T_tablename)

    return answer

def run_the_chase_sqls(conn, intitial_T_tablename, initial_T_tuples, policies, sigma_new_sqls):
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
    
    sigma_new_sqls: list
        A list of SQLs corresponding to a datalog program.
    
    databaseTypes: dict
        it is a dictionary {"database name":[ordered list of column types]}. 
        By default, all column types are integers. 
        If we need some other datatype, we need to specify using this parameter
    """
    
    gen_intial_table(conn, initial_T_tuples, intitial_T_tablename)
    # sigma_new_sqls = gen_sigma_new_sqls_DT_program(sigma_new_program, databaseTypes=databaseTypes)
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    answer = None
    while does_updated:
        print_table(conn, intial_T_tablename)
        input()
        temp_updated = False
        for policy in policies:
            # print(policy)
            # exit()
            chase_script.print_policy(policy)
            input()
            whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, intitial_T_tablename)
            temp_updated = (temp_updated or whether_updated)
            print_table(conn, intial_T_tablename)

        input()
        whether_updated = chase.apply_sigma_new_atomically_toy(conn, sigma_new_sqls, intitial_T_tablename)
        print_table(conn, intial_T_tablename)
        temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated

    return answer
    

if __name__ == '__main__':
    # # ============================toy example in the paper=============================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    
    # security_hole = ['10.0.0.2', '10.0.0.4']
    # rewrite_policy1 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '10.0.0.2', '10.0.0.3', '1', '2')
    #         ], 
    #         'dependency_summary': ['f', '10.0.0.1', '10.0.0.3', '1', '2'], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '10.0.0.2', '10.0.0.3', '1', '2'), 
    #             ('f2', '10.0.0.1', '10.0.0.3', '1', '2')
    #         ], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # rewrite_policy2 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '10.0.0.1', '10.0.0.3', '3', '10.0.0.3')
    #         ], 
    #         'dependency_summary': ['f', '10.0.0.1', '10.0.0.4', '3', '10.0.0.4'], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '10.0.0.1', '10.0.0.3', '3', '10.0.0.3'), 
    #             ('f2', '10.0.0.1', '10.0.0.4', '3', '10.0.0.4')
    #         ], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # firewall_policy1 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', 's', 'd', '1', 'x_x')
    #         ], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': [],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': ["s = 10.0.0.2", "d = 10.0.0.4"], 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # firewall_policy2 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', 's', 'd', '3', 'x_x')
    #         ], 
    #         'dependency_attributes': ['c0', 'c1', 'c2', 'c3', 'c4'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': [],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': ["s = 10.0.0.2", "d = 10.0.0.4"], 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # intial_T_tablename = "T"
    # intial_T_tuples = [
    #     ('f', '10.0.0.2', '10.0.0.3', '10.0.0.2', '1')
    # ]

    # E_tuples = [
    #     ('f', 's', 'd0', 's', '1'), 
    #     ('f', 's1', 'd1', '1', '2'), 
    #     ('f', 's2', 'd2', '2', '3'),
    #     ('f', 's3', 'd', '3', 'd')
    # ]

    # topology_tablename = "L"
    # topo_attributes = ['c0', 'c1', 'c2']
    # topo_datatypes = ['text', 'text', 'text']
    # topo_tuples = [
    #     ('10.0.0.1', '1', '0'), 
    #     ('10.0.0.2', '1', '0'), 
    #     ('1', '2', '1'),
    #     ('2', '3', '1'),
    #     ('3', '10.0.0.3', '0'),
    #     ('3', '10.0.0.4', '0'),
    #     ('3', '10.0.0.5', '0')
    # ]
    
    # gen_topo(conn, topo_tablename=topology_tablename, topo_tuples=topo_tuples)

    # sigma_program = "T(x_f, x_s, x_d, x_x, x_next) :- T(x_f, x_s, x_d, x_n, x_x), L(x_x, x_next, 1)\nT(x_f, x_s, x_d, x_x, x_d) :- T(x_f, x_s, x_d, x_n, x_x), L(x_x, x_d, 0)\nT(x_f, x_s, x_d, x_pre, x_n) :- T(x_f, x_s, x_d, x_n, x_x), L(x_pre, x_n, 1)\nT(x_f, x_s, x_d, x_s, x_n) :- T(x_f, x_s, x_d, x_n, x_x), L(x_s, x_n, 0)"

    # policies = [rewrite_policy1, rewrite_policy2, firewall_policy1, firewall_policy2]

    # answer = run_the_chase(conn=conn, 
    #                 intitial_T_tablename=intial_T_tablename, 
    #                 initial_T_tuples=intial_T_tuples, 
    #                 policies=policies, 
    #                 sigma_new_program=sigma_program, 
    #                 E_tuples=E_tuples, 
    #                 security_hole=security_hole,
    #                 databaseTypes={intial_T_tablename:['text', 'text', 'text', 'text', 'text'], topology_tablename:['text', 'text', 'integer']}
    #             )
    
    # print_table(conn, intial_T_tablename)
    # print("Answer:", answer)


    # ============================test idea=============================
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    topo_attributes = ['n', 'x', 'flag']
    topo_datatypes = ['text', 'text', 'integer']
    LP1_tablename = 'lp1'
    LP1_tuples = [
        ('1', '31', '0'),
        ('2', '32', '0'),
        ('31', '33', '1'),
        ('32', '33', '1')
    ]
    gen_topo(conn, topo_tablename=LP1_tablename, topo_tuples=LP1_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP2_tablename = 'lp2'
    LP2_tuples = [
        ('31', '33', '1'),
        ('32', '33', '1'),
        ('33', '41', '1'),
        ('41', '42', '1')
    ]
    gen_topo(conn, topo_tablename=LP2_tablename, topo_tuples=LP2_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP3_tablename = 'lp3'
    LP3_tuples = [
        ('41', '42', '1'),
        ('42', '51', '1'),
        ('51', '52', '1'),
        ('52', '61', '1'),
        ('61', '62', '1'),
    ]
    gen_topo(conn, topo_tablename=LP3_tablename, topo_tuples=LP3_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP4_tablename = 'lp4'
    LP4_tuples = [
        ('61', '62', '1'),
        ('62', '71', '1'),
        ('71', '72', '1'),
        ('71', '73', '1'),
        ('71', '74', '1'),
        ('72', '8', '0'),
        ('73', '9', '0'),
        ('74', '10', '0'),
    ]
    gen_topo(conn, topo_tablename=LP4_tablename, topo_tuples=LP4_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    blocktable_attributes = ['src', 'dst']
    blocktable_datatypes = ['text', 'text']
    B1_tablename = 'b1'
    B1_tupels = []
    chase.load_table(conn, blocktable_attributes, blocktable_datatypes, B1_tablename, B1_tupels)

    B2_tablename = 'b2'
    B2_tupels = [
        ('2', '8')
    ]
    chase.load_table(conn, blocktable_attributes, blocktable_datatypes, B2_tablename, B2_tupels)

    B3_tablename = 'b3'
    B3_tupels = [
        ('2', '8'),
        ('1', '8')
    ]
    chase.load_table(conn, blocktable_attributes, blocktable_datatypes, B3_tablename, B3_tupels)

    B4_tablename = 'b4'
    B4_tupels = [
        ('2', '8'),
        ('1', '8'),
        ('1', '9')
    ]
    chase.load_table(conn, blocktable_attributes, blocktable_datatypes, B4_tablename, B4_tupels)


    intial_T_tablename = "T"

    intial_T_tuples = [
        ('f', '1', '8', '1', '31')
    ]

    rewrite_policy1 = [
        {
            'dependency_tuples': [
                ('f', '2', '8', '32', '33')
            ], 
            'dependency_summary': ['f', '1', '8', '31', '33'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '2', '8', '32', '33'), 
                ('f2', '1', '8', '31', '33')
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
                ('f', '1', '8', '41', '42')
            ], 
            'dependency_summary': ['f', '1', '9', '41', '42'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '8', '41', '42'), 
                ('f2', '1', '9', '41', '42')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy3 = [
        {
            'dependency_tuples': [
                ('f', '1', '9', '61', '62')
            ], 
            'dependency_summary': ['f', '1', '10', '61', '62'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '9', '61', '62'), 
                ('f2', '1', '10', '61', '62')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]


    # rewrite_infos = [('2', '8'), ('1', '8'), ('1', '9'), ('1', '10')]
    rewrite_infos = [('2', '8'), ('1', '8'), ('1', '9')]
    # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4')]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP4_tablename)]
    pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename, B1_tablename), (intial_T_tablename, LP2_tablename, B2_tablename), (intial_T_tablename, LP3_tablename, B3_tablename), (intial_T_tablename, LP4_tablename, B4_tablename)]

    # sigma_new_sqls = gen_sigma_new_sqls(pairs_tables, rewrite_infos)
    # sigma_new_sqls = gen_sigma_new_sqls2(pairs_tables)
    sigma_new_sqls = gen_sigma_new_sqls3(pairs_tables, rewrite_infos)
    # sigma_new_program = "T(x_f, '2', '8', x_x, x_next) :- T(x_f, '2', '8', x_n, x_x), lp1(x_x, x_next, '1')\nT(x_f, '2', '8', x_x, '8') :- T(x_f, '2', '8', x_n, x_x), lp1(x_x, '8', '0')\nT(x_f, '2', '8', x_pre, x_n) :- T(x_f, '2', '8', x_n, x_x), lp1(x_pre, x_n, '1')\nT(x_f, '2', '8', '2', x_n) :- T(x_f, '2', '8', x_n, x_x), lp1('2', x_n, '0')\nT(x_f, '1', '8', x_x, x_next) :- T(x_f, '1', '8', x_n, x_x), lp2(x_x, x_next, '1')\nT(x_f, '1', '8', x_x, '8') :- T(x_f, '1', '8', x_n, x_x), lp2(x_x, '8', '0')\nT(x_f, '1', '8', x_pre, x_n) :- T(x_f, '1', '8', x_n, x_x), lp2(x_pre, x_n, '1')\nT(x_f, '1', '8', '1', x_n) :- T(x_f, '1', '8', x_n, x_x), lp2('1', x_n, 0)\nT(x_f, '1', '9', x_x, x_next) :- T(x_f, '1', '9', x_n, x_x), lp3(x_x, x_next, '1')\nT(x_f, '1', '9', x_x, '9') :- T(x_f, '1', '9', x_n, x_x), lp3(x_x, '9', '0')\nT(x_f, '1', '9', x_pre, x_n) :- T(x_f, '1', '9', x_n, x_x), lp3(x_pre, x_n, '1')\nT(x_f, '1', '9', '1', x_n) :- T(x_f, '1', '9', x_n, x_x), lp3('1', x_n, '0')\nT(x_f, '1', '10', x_x, x_next) :- T(x_f, '1', '10', x_n, x_x), lp4(x_x, x_next, '1')\nT(x_f, '1', '10', x_x, '10') :- T(x_f, '1', '10', x_n, x_x), lp4(x_x, '10', '0')\nT(x_f, '1', '10', x_pre, x_n) :- T(x_f, '1', '10', x_n, x_x), lp4(x_pre, x_n, '1')\nT(x_f, '1', '10', '1', x_n) :- T(x_f, '1', '10', x_n, x_x), lp4('1', x_n, '0')"
    # sigma_new_sqls = gen_sigma_new_sqls_general(pairs_tables)

    run_the_chase_sqls(conn, 
        intial_T_tablename, 
        intial_T_tuples, 
        [rewrite_policy1, rewrite_policy2, rewrite_policy3], 
        sigma_new_sqls)
    
    # run_the_chase(conn=conn, 
    #         initial_T_tablename=intial_T_tablename, 
    #         initial_T_tuples=intial_T_tuples, 
    #         policies=[rewrite_policy1, rewrite_policy2, rewrite_policy3], 
    #         sigma_new_program=sigma_new_program, 
    #         databaseTypes={intial_T_tablename:['text', 'text', 'text', 'text', 'text'], 
    #                     LP1_tablename:topo_datatypes, 
    #                     LP2_tablename:topo_datatypes, 
    #                     LP3_tablename:topo_datatypes, 
    #                     LP4_tablename:topo_datatypes}
    #     )
    
    