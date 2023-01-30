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
    cursor.execute("select * from {} order by f, src, dst, n, x".format(intial_T_tablename))
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
            rewritings = rewriting_infos[idx-1]
            for rewriting in rewritings:
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

def gen_sigma_new_sqls4(pairs_tables=[], rewriting_infos=[]):
    '''
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, 0, bd), not(x_s = 2, x_d = 8)
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, x_d, bd), not(x_s = 2, x_d = 8)
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, 0)
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, x_s)
    '''
    sigma_new_sqls = []
    block_conditions = []
    for idx, pairs in enumerate(pairs_tables):
        if idx != 0:
            rewritings = rewriting_infos[idx-1]
            for rewriting in rewritings:
                condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
                block_conditions.append(condition)
        
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = '0'{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = t0.src{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls5(pairs_tables=[], rewriting_infos=[]):
    '''
    add conditions for filter
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, 0, bd), not(x_s = 2, x_d = 8)
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, x_d, bd), not(x_s = 2, x_d = 8)
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, 0)
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, x_s)
    '''
    sigma_new_sqls = []
    block_conditions = []
    pairs = pairs_tables[0]
    sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and (t1.n != '31' and t1.n != '32'){and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst  and (t1.n != '31' and t1.n != '32'){and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    
    condition = "Not(t0.src = '2' and t0.dst = '9')"
    block_conditions.append(condition)
    sigma_fp3_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and (t1.n = '31' or t1.n = '32'){and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp4_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst and (t1.n = '31' or t1.n = '32'){and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    
    # pairs = pairs_tables[0]
    # sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0'{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))
    # sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))

    rewriting = rewriting_infos[0][0]
    condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
    block_conditions.append(condition)
    pairs = pairs_tables[1]
    sigma_fp5_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp6_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    
    rewriting = rewriting_infos[1][0]
    condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
    block_conditions.append(condition)
    pairs = pairs_tables[2]
    sigma_fp7_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp8_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    # sigma_fp7_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and t1.n != '61'{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))
    # sigma_fp8_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst and t1.n != '61'{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))
    
    # # condition = "Not(t0.src = '1' and t0.dst = '10')"
    # # block_conditions.append(condition)
    # sigma_fp9_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and t1.n = '61'{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))
    # sigma_fp10_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst and t1.n = '61'{and_}{condition}".format(
    #     f=pairs[0],
    #     l=pairs[1], 
    #     and_= ' and ' if len(block_conditions) != 0 else "",
    #     condition=" and ".join(block_conditions))

    rewriting = rewriting_infos[2][0]
    condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
    block_conditions.append(condition)
    pairs = pairs_tables[3]
    sigma_fp11_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and t1.n != '71'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp12_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst and t1.n != '71'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))

    condition = "Not(t0.src = '1' and t0.dst = '10')"
    block_conditions.append(condition)
    sigma_fp13_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0' and t1.n = '71'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))
    sigma_fp14_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst and t1.n = '71'{and_}{condition}".format(
        f=pairs[0],
        l=pairs[1], 
        and_= ' and ' if len(block_conditions) != 0 else "",
        condition=" and ".join(block_conditions))

    # sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_fp3_sql, sigma_fp4_sql, sigma_fp5_sql, sigma_fp6_sql, sigma_fp7_sql, sigma_fp8_sql, sigma_fp9_sql, sigma_fp10_sql, sigma_fp11_sql, sigma_fp12_sql]
    # sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_fp5_sql, sigma_fp6_sql, sigma_fp7_sql, sigma_fp8_sql, sigma_fp9_sql, sigma_fp10_sql, sigma_fp11_sql, sigma_fp12_sql]
    sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_fp3_sql, sigma_fp4_sql, sigma_fp5_sql, sigma_fp6_sql, sigma_fp7_sql, sigma_fp8_sql, sigma_fp11_sql, sigma_fp12_sql, sigma_fp13_sql, sigma_fp14_sql]

    for pairs in pairs_tables:

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = '0'".format(
            f=pairs[0],
            l=pairs[1])

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = t0.src".format(
            f=pairs[0],
            l=pairs[1])

        sigma_new_sqls += [sigma_bp1_sql, sigma_bp2_sql]
    

    # sigma_new_sqls = []
    # block_conditions = []
    # for idx, pairs in enumerate(pairs_tables):
    #     if idx != 0:
    #         rewritings = rewriting_infos[idx-1]
    #         for rewriting in rewritings:
    #             condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
    #             block_conditions.append(condition)
        
    #     sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = '0'{and_}{condition}".format(
    #         f=pairs[0],
    #         l=pairs[1], 
    #         and_= ' and ' if len(block_conditions) != 0 else "",
    #         condition=" and ".join(block_conditions))
    #     sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t1.forward = t0.dst{and_}{condition}".format(
    #         f=pairs[0],
    #         l=pairs[1], 
    #         and_= ' and ' if len(block_conditions) != 0 else "",
    #         condition=" and ".join(block_conditions))

    #     sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = '0'{and_}{condition}".format(
    #         f=pairs[0],
    #         l=pairs[1], 
    #         and_= ' and ' if len(block_conditions) != 0 else "",
    #         condition=" and ".join(block_conditions))

    #     sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t1.backward = t0.src{and_}{condition}".format(
    #         f=pairs[0],
    #         l=pairs[1], 
    #         and_= ' and ' if len(block_conditions) != 0 else "",
    #         condition=" and ".join(block_conditions))

    #     sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls6(pairs_tables=[], rewriting_infos=[]):
    '''
    the topology has fork
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, fd, bd), len(fd) = 0, not(x_s = 2, x_d = 8)
    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next, fd, bd), x_d \in fd, not(x_s = 2, x_d = 8)
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, bd),  len(bd) = 0
    f(x_f,  x_s, x_d, x_pre, x_n) :- f(x_f,  x_s, x_d, x_n, x_x), lp1(x_pre, x_n, fd, bd), x_s \in bd
    '''
    sigma_new_sqls = []
    
    for idx, pairs in enumerate(pairs_tables):
        block_conditions = []
        if idx != 0:
            rewritings = rewriting_infos[idx-1]
            for rewriting in rewritings:
                condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
                block_conditions.append(condition)
        
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and cardinality(t1.forward) = 0{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.x = t1.n and t0.dst=ANY(t1.forward){and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and cardinality(t1.backward) = 0{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1 where t0.n = t1.x and t0.src=ANY(t1.backward){and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls7(pairs_tables=[], rewriting_infos=[]):
    '''
    using interface table
    f(x_f, x_s, x_d, x_x, x_next ) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next), inf(x_d, x_next)									
    f(x_f, x_s, x_d, x_x, x_next ) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next), inf(x_d, x_x)									
    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_pre, x_n), inf(x_s,x_pre)									
    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_pre, x_n), inf(x_s,x_n)									
    '''
    sigma_new_sqls = []
    
    for idx, pairs in enumerate(pairs_tables):
        block_conditions = []
        if idx != 0:
            rewritings = rewriting_infos[idx-1]
            for rewriting in rewritings:
                condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
                block_conditions.append(condition)
        
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.x = t1.n and t0.dst = t2.host and t1.x = t2.interface{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.x = t1.n and t0.dst = t2.host and t1.n = t2.interface{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.n = t1.x and t0.src = t2.host and t1.n = t2.interface{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.n = t1.x and t0.src = t2.host and t1.x = t2.interface{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_new_sqls += [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]

    return sigma_new_sqls

def gen_sigma_new_sqls8(pairs_tables=[], rewriting_infos=[]):
    '''
    using new interface table
    f(x_f, x_s, x_d, x_x, x_next ) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next), inf(x_d, x_x, x_next)
    f(x_f, x_s, x_d, x_x, x_next ) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_x, x_next), inf(x_d, x_in, x_x)
    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_pre, x_n), inf(x_s, x_n, x_pre)
    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), lp1(x_pre, x_n), inf(x_s, x_in, x_n)
    '''
    sigma_new_sqls = []
    
    for idx, pairs in enumerate(pairs_tables):
        block_conditions = []
        if idx != 0:
            rewritings = rewriting_infos[idx-1]
            for rewriting in rewritings:
                condition = "Not(t0.src = '{}' and t0.dst = '{}')".format(rewriting[0], rewriting[1])
                block_conditions.append(condition)
        
        sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.x = t1.n and t0.dst = t2.host and t1.n = t2.ingress and t1.x = t2.egress{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))
        sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.x = t1.n and t0.dst = t2.host and t1.n = t2.egress{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.n = t1.x and t0.src = t2.host and t1.n = t2.egress and t1.x = t2.ingress{and_}{condition}".format(
            f=pairs[0],
            l=pairs[1], 
            and_= ' and ' if len(block_conditions) != 0 else "",
            condition=" and ".join(block_conditions))

        sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {f} t0, {l} t1, inf t2 where t0.n = t1.x and t0.src = t2.host and t1.x = t2.egress{and_}{condition}".format(
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

def run_the_chase_sqls(conn, initial_T_tablename, initial_T_tuples, policies, sigma_new_sqls):
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
    
    gen_intial_table(conn, initial_T_tuples, initial_T_tablename)
    # sigma_new_sqls = gen_sigma_new_sqls_DT_program(sigma_new_program, databaseTypes=databaseTypes)
    dict_policies = {0: sigma_new_sqls}
    for idx in range(len(policies)):
        dict_policies[idx+1] = policies[idx]
    
    does_updated = True # flag for whether the Z table changes after applying all kinds of dependencies 
    answer = None
    orderings = list(dict_policies.keys()) 
    while does_updated:
        random.shuffle(orderings)
        print_table(conn, initial_T_tablename)
        input()
        temp_updated = False
        for idx in orderings:
            if idx == 0:
                whether_updated = chase.apply_sigma_new_atomically_toy(conn, sigma_new_sqls, initial_T_tablename)
                temp_updated = (temp_updated or whether_updated)
                # print_table(conn, initial_T_tablename)
                # input()
            else:
                policy = dict_policies[idx]
                chase_script.print_policy(policy)
                whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, initial_T_tablename)
                temp_updated = (temp_updated or whether_updated)
            # print_table(conn, initial_T_tablename)
            # input()


        # for policy in policies:
        #     # print(policy)
        #     # exit()
        #     chase_script.print_policy(policy)
        #     input()
        #     whether_updated, counts = chase.apply_policy_as_atomic_unit(conn, policy, intitial_T_tablename)
        #     temp_updated = (temp_updated or whether_updated)
        # whether_updated = chase.apply_sigma_new_atomically_toy(conn, sigma_new_sqls, intitial_T_tablename)
        # print_table(conn, intial_T_tablename)
        # temp_updated = (temp_updated or whether_updated)

        does_updated = temp_updated
    print_table(conn, initial_T_tablename)
    return answer

def test_fork_forward_backward():
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    topo_attributes = ['n', 'x', 'forward', 'backward']
    topo_datatypes = ['text', 'text', 'text[]', 'text[]']
    LP1_tablename = 'lp1'
    LP1_tuples = [
        ('1', '31', [], ['1']),
        ('2', '32', [], ['2']),
        ('31', '33', [], ['1']),
        ('32', '33', [], ['2'])
    ]
    gen_topo(conn, topo_tablename=LP1_tablename, topo_tuples=LP1_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP2_tablename = 'lp2'
    LP2_tuples = [
        ('31', '33', [], ['1']),
        ('32', '33', [], ['2']),
        ('33', '41', [], []),
        ('41', '42', [], []),
        ('42', '51', [], []),
        ('51', '52', ['8', '9'], []),
        ('51', '53', ['11', '12'], [])
    ]
    gen_topo(conn, topo_tablename=LP2_tablename, topo_tuples=LP2_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP3_tablename = 'lp3'
    LP3_tuples = [
        ('51', '52', ['8', '9'], []),
        ('52', '61', ['8', '9'], []),
        ('61', '62', ['9'], []),
        ('61', '63', ['8'], []),
        ('51', '53', ['11', '12'], []),
        ('53', '101', ['11', '12'], []),
        ('101', '102', ['11'], []),
        ('101', '103', ['12'], [])
    ]
    gen_topo(conn, topo_tablename=LP3_tablename, topo_tuples=LP3_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP4_tablename = 'lp4'
    LP4_tuples = [
        ('61', '62', ['9'], []),
        ('62', '9', ['9'], []),
        ('61', '63', ['8'], []),
        ('63', '71', ['8'], []),
        ('71', '72', ['8'], []),
        ('72', '8', ['8'], []),
    ]
    gen_topo(conn, topo_tablename=LP4_tablename, topo_tuples=LP4_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP5_tablename = 'lp5'
    LP5_tuples = [
        ('101', '102', ['11'], []),
        ('101', '103', ['12'], []),
        ('102', '11', ['11'], []),
        ('103', '12', ['12'], [])
    ]
    gen_topo(conn, topo_tablename=LP5_tablename, topo_tuples=LP5_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    intial_T_tablename = "T"

    intial_T_tuples = [
        ('f', '2', '8', '2', '32')
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
        },
        {
            'dependency_tuples': [
                ('f', '2', '8', '31', '33')
            ], 
            'dependency_summary': ['f', '1', '8', '31', '33'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '2', '8', '31', '33'), 
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
                ('f', '1', '8', '51', '52')
            ], 
            'dependency_summary': ['f', '1', '12', '51', '53'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '8', '51', '52'), 
                ('f2', '1', '12', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '8', '51', '53')
            ], 
            'dependency_summary': ['f', '1', '12', '51', '53'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '8', '51', '53'), 
                ('f2', '1', '12', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
    ]

    rewrite_policy3 = [
        {
            'dependency_tuples': [
                ('f', '1', '9', '61', '62')
            ], 
            'dependency_summary': ['f', '1', '8', '61', '63'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '9', '61', '62'), 
                ('f2', '1', '8', '61', '63')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '9', '61', '63')
            ], 
            'dependency_summary': ['f', '1', '8', '61', '63'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '9', '61', '63'), 
                ('f2', '1', '8', '61', '63')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy4 = [
        {
            'dependency_tuples': [
                ('f', '1', '12', '101', '102')
            ], 
            'dependency_summary': ['f', '1', '11', '101', '102'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '12', '101', '102'), 
                ('f2', '1', '11', '101', '102')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '12', '101', '103')
            ], 
            'dependency_summary': ['f', '1', '11', '101', '102'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '12', '101', '103'), 
                ('f2', '1', '11', '101', '102')
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
                ('f', '2', '9', '31', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '2', '13', '31', '33'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '2', '9', '31', '33'),
                ('y_f', '2', '13', '31', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '9', '32', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '2', '13', '32', '33'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '2', '9', '32', '33'),
                ('y_f', '2', '13', '32', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    firewall_policy2 = [
        {
            'dependency_tuples': [
                ('f', '1', '11', '51', '52')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '1', '13', '51', '52'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '1', '11', '51', '52'),
                ('y_f', '1', '13', '51', '52')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '11', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '1', '13', '51', '53'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '1', '11', '51', '53'),
                ('y_f', '1', '13', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]
    
    # rewrite_infos = [('2', '8'), ('1', '8'), ('1', '9'), ('1', '10')]
    rewrite_infos = [[('2', '8'), ('2', '9')], [('1', '8'), ('1', '11')], [('1', '9')], [('1', '12')]]
    # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4')]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename), (intial_T_tablename, LP5_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename, B1_tablename), (intial_T_tablename, LP2_tablename, B2_tablename), (intial_T_tablename, LP3_tablename, B3_tablename), (intial_T_tablename, LP4_tablename, B4_tablename)]

    # sigma_new_sqls = gen_sigma_new_sqls(pairs_tables, rewrite_infos)
    # sigma_new_sqls = gen_sigma_new_sqls2(pairs_tables)
    # sigma_new_sqls = gen_sigma_new_sqls3(pairs_tables, rewrite_infos)
    sigma_new_sqls = gen_sigma_new_sqls6(pairs_tables, rewrite_infos)

    run_the_chase_sqls(conn, 
        intial_T_tablename, 
        intial_T_tuples, 
        [rewrite_policy1, rewrite_policy2, rewrite_policy3, rewrite_policy4, firewall_policy1, firewall_policy2], 
        sigma_new_sqls)

def test_fork_interface_table():
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    topo_attributes = ['n', 'x']
    topo_datatypes = ['text', 'text']
    LP1_tablename = 'lp1'
    LP1_tuples = [
        ('1', '31'),
        ('2', '32'),
        ('31', '33'),
        ('32', '33')
    ]
    gen_topo(conn, topo_tablename=LP1_tablename, topo_tuples=LP1_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP2_tablename = 'lp2'
    LP2_tuples = [
        ('31', '33'),
        ('32', '33'),
        ('33', '41'),
        ('41', '42'),
        ('42', '51'),
        ('51', '52'),
        ('51', '53')
    ]
    gen_topo(conn, topo_tablename=LP2_tablename, topo_tuples=LP2_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP3_tablename = 'lp3'
    LP3_tuples = [
        ('51', '52'),
        ('52', '61'),
        ('61', '62'),
        ('61', '63'),
        ('51', '53'),
        ('53', '101'),
        ('101', '102'),
        ('101', '103')
    ]
    gen_topo(conn, topo_tablename=LP3_tablename, topo_tuples=LP3_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP4_tablename = 'lp4'
    LP4_tuples = [
        ('61', '62'),
        ('62', '9'),
        ('61', '63'),
        ('63', '71'),
        ('71', '72'),
        ('72', '8'),
    ]
    gen_topo(conn, topo_tablename=LP4_tablename, topo_tuples=LP4_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    LP5_tablename = 'lp5'
    LP5_tuples = [
        ('101', '102'),
        ('101', '103'),
        ('102', '11'),
        ('103', '12')
    ]
    gen_topo(conn, topo_tablename=LP5_tablename, topo_tuples=LP5_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    inf_tablename = 'inf'
    inf_attributes = ['host', 'interface']
    inf_datatypes = ['text', 'text']
    inf_tuples = [
        ('8',  '72'),
        ('8',  '63'),
        ('8',  '52'),
        ('8',  '42'),
        ('8',  '33'),
        ('9',  '62'),
        ('9',  '52'),
        ('9',  '42'),
        ('9',  '33'),
        ('11',  '102'),
        ('11',  '53'),
        ('11',  '42'),
        ('11',  '33'),
        ('12',  '103'),
        ('12',  '53'),
        ('12',  '42'),
        ('12',  '33'),
        ('1',  '31'),
        ('1',  '41'),
        ('1',  '51'),
        ('1',  '61'),
        ('1',  '71'),
        ('1',  '101'),
        ('2',  '32'),
        ('2',  '41'),
        ('2',  '51'),
        ('2',  '61'),
        ('2',  '71'),
        ('2',  '101')
    ]
    
    # inf_tablename = 'inf'
    # inf_attributes = ['host', 'ingress', 'egress']
    # inf_datatypes = ['text', 'text', 'text']
    # inf_tuples = [
    #     ('8', '71', '72'),
    #     ('8',  '61', '63'),
    #     ('8',  '51', '52'),
    #     ('8',  '41', '42'),
    #     ('8',  '32', '33'),
    #     ('8',  '31', '33'),
    #     ('9',  '61', '62'),
    #     ('9',  '51', '52'),
    #     ('9',  '41', '42'),
    #     ('9',  '31', '33'),
    #     ('9',  '32', '33'),
    #     ('11',  '101', '102'),
    #     ('11',  '51', '53'),
    #     ('11',  '41', '42'),
    #     ('11',  '31', '33'),
    #     ('11',  '32', '33'),
    #     ('12',  '101', '103'),
    #     ('12',  '51', '53'),
    #     ('12',  '41', '42'),
    #     ('12',  '31', '33'),
    #     ('12',  '32', '33'),
    #     ('1',  '33', '31'),
    #     ('1',  '42', '41'),
    #     ('1',  '52', '51'),
    #     ('1',  '53', '51'),
    #     ('1',  '61',  '62'),
    #     ('1', '61', '63'),
    #     ('1',  '72', '71'),
    #     ('1', '102', '101'),
    #     ('1', '103', '101'),
    #      ('2',  '32', '31'),
    #     ('2',  '42', '41'),
    #     ('2',  '52', '51'),
    #     ('2',  '53', '51'),
    #     ('2',  '61',  '62'),
    #     ('2', '61', '63'),
    #     ('2',  '72', '71'),
    #     ('2', '102', '101'),
    #     ('2', '103', '101'),
    # ]
    chase.load_table(conn, inf_attributes, inf_datatypes, inf_tablename, inf_tuples)

    intial_T_tablename = "T"

    intial_T_tuples = [
        ('f', '2', '8', '2', '32')
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
        },
        {
            'dependency_tuples': [
                ('f', '2', '8', '31', '33')
            ], 
            'dependency_summary': ['f', '1', '8', '31', '33'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '2', '8', '31', '33'), 
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
                ('f', '1', '8', '51', '52')
            ], 
            'dependency_summary': ['f', '1', '12', '51', '53'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '8', '51', '52'), 
                ('f2', '1', '12', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '8', '51', '53')
            ], 
            'dependency_summary': ['f', '1', '12', '51', '53'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '8', '51', '53'), 
                ('f2', '1', '12', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
    ]

    rewrite_policy3 = [
        {
            'dependency_tuples': [
                ('f', '1', '9', '61', '62')
            ], 
            'dependency_summary': ['f', '1', '8', '61', '63'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '9', '61', '62'), 
                ('f2', '1', '8', '61', '63')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '9', '61', '63')
            ], 
            'dependency_summary': ['f', '1', '8', '61', '63'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '9', '61', '63'), 
                ('f2', '1', '8', '61', '63')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy4 = [
        {
            'dependency_tuples': [
                ('f', '1', '12', '101', '102')
            ], 
            'dependency_summary': ['f', '1', '11', '101', '102'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '12', '101', '102'), 
                ('f2', '1', '11', '101', '102')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
            'dependency_summary': ['f1 = f2'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '12', '101', '103')
            ], 
            'dependency_summary': ['f', '1', '11', '101', '102'], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        }, 
        {   
            'dependency_tuples': [
                ('f1', '1', '12', '101', '103'), 
                ('f2', '1', '11', '101', '102')
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
                ('f', '2', '9', '31', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '2', '13', '31', '33'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '2', '9', '31', '33'),
                ('y_f', '2', '13', '31', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '9', '32', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '2', '13', '32', '33'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '2', '9', '32', '33'),
                ('y_f', '2', '13', '32', '33')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    firewall_policy2 = [
        {
            'dependency_tuples': [
                ('f', '1', '11', '51', '52')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '1', '13', '51', '52'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '1', '11', '51', '52'),
                ('y_f', '1', '13', '51', '52')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '11', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['f', '1', '13', '51', '53'],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'tgd'
        },
        {
            'dependency_tuples': [
                ('x_f', '1', '11', '51', '53'),
                ('y_f', '1', '13', '51', '53')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]
    
    # rewrite_infos = [('2', '8'), ('1', '8'), ('1', '9'), ('1', '10')]
    rewrite_infos = [[('2', '8'), ('2', '9')], [('1', '8'), ('1', '11')], [('1', '9')], [('1', '12')]]
    # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4')]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename), (intial_T_tablename, LP5_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename, B1_tablename), (intial_T_tablename, LP2_tablename, B2_tablename), (intial_T_tablename, LP3_tablename, B3_tablename), (intial_T_tablename, LP4_tablename, B4_tablename)]

    # sigma_new_sqls = gen_sigma_new_sqls(pairs_tables, rewrite_infos)
    # sigma_new_sqls = gen_sigma_new_sqls2(pairs_tables)
    # sigma_new_sqls = gen_sigma_new_sqls3(pairs_tables, rewrite_infos)
    sigma_new_sqls = gen_sigma_new_sqls7(pairs_tables, rewrite_infos)

    run_the_chase_sqls(conn, 
        intial_T_tablename, 
        intial_T_tuples, 
        [rewrite_policy1, rewrite_policy2, rewrite_policy3, rewrite_policy4, firewall_policy1, firewall_policy2], 
        sigma_new_sqls)

def test_new_idea():
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    intial_T_tablename = "T"

    intial_T_tuples = [
        # ('f1', '9', '12', '9', '1'),
        # ('f1', 's2', 'd2', '1', '3'),
        # ('f1', 's3', 'd3', '3', '4'),
        # ('f1', 's4', 'd4', '4', '5'),
        # ('f1', 's5', 'd5', '5', '6'),
        # ('f1', 's6', 'd6', '6', 'x6'),
        # ('f1', 's7', 'd7', 'x6', 'd7'),
        ('f2', '10', '11', '10', '2'),
        ('f2', 's9', 'd9', '2', '3'),
        ('f2', 's10', 'd10', '3', '4'),
        ('f2', 's11', 'd11', '4', '5'),
        ('f2', 's12', 'd12', '5', '6'),
        ('f2', 's13', 'd13', '6', 'x13'),
        ('f2', 's14', 'd14', 'x13', 'd14'),
        # ('f3', '9', '11', '9', '1'),
        # ('f3', 's16', 'd16', '1', '3'),
        # ('f3', 's17', 'd17', '3', '4'),
        # ('f3', 's18', 'd18', '4', '5'),
        # ('f3', 's19', 'd19', '5', '6'),
        # ('f3', 's20', 'd20', '6', 'x20'),
        # ('f3', 's21', 'd21', 'x20', 'd21')
    ]

    rewrite_policy1 = [
        {
            'dependency_tuples': [
                ('f', '10', '11', '10', '2'),
                ('f', 's', 'd', '2', '3')
            ], 
            'dependency_summary': ["s = 9", "d = 11"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {   
            'dependency_tuples': [
                ('f', 's1', 'd1', 's1', 'x1'), 
                ('f', 's2', 'd2', 'x2', '3')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['s1 = s2', 'd1 = d2'], 
            'dependency_summary_condition': ["s1 != 10 or d1 != 11"], 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy3 = [
        {
            'dependency_tuples': [
                ('f', '9', '11', '5', '6'),
                ('f', 's', 'd', '6', 'x')
            ], 
            'dependency_summary': ["s = 9", "d = 12", "x = 8"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {   
            'dependency_tuples': [
                ('f', 's1', 'd1', '5', '6'), 
                ('f', 's2', 'd2', '6', 'x')
            ], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary': ['s1 = s2', 'd1 = d2'], 
            'dependency_summary_condition': ['s1 != 9 or d1 != 11'], 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy2 = [
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', 'x1'),
                ('f', 's2', 'd2', 'x1', 'x2')
            ], 
            'dependency_summary': ["s1 = s2", "d1 = d2"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': ['x1 != 6 and x2 != 3'], 
            'dependency_type': 'egd'
        }
    ]

    additional_policy = [
        {
            'dependency_tuples': [
                ('f', 's', 'd', '9', 'x'),
            ], 
            'dependency_summary': ["x = 1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's', 'd', '10', 'x'),
            ], 
            'dependency_summary': ["x = 2"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', '11'),
            ], 
            'dependency_summary': ["n = 7"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', '12'),
            ], 
            'dependency_summary': ["n = 8"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    policy_fork = [
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', '6', 'x1'),
                ('f', 's2', 'd2', 'x2', 'd2')
            ], 
            'dependency_summary': ["x2 = x1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 's1', 'x1'),
                ('f', 's2', 'd2', 'x2', '3')
            ], 
            'dependency_summary': ["x2 = x1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]
    run_the_chase_sqls(conn, 
        intial_T_tablename, 
        intial_T_tuples, 
        [rewrite_policy1, rewrite_policy2, rewrite_policy3, additional_policy], 
        [])

def test_straightforward_idea():
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    intial_T_tablename = "T"

    # intial_T_tuples = [
    #     # ('f1', '9', '12', '9', '1'),
    #     # ('f1', 's2', 'd2', '1', '3'),
    #     # ('f1', 's3', 'd3', '3', '4'),
    #     # ('f1', 's4', 'd4', '4', '5'),
    #     # ('f1', 's5', 'd5', '5', '6'),
    #     # ('f1', 's6', 'd6', '6', 'x6'),
    #     # ('f1', 's7', 'd7', 'x6', 'd7'),
    #     ('f2', '10', '11', '10', '2'),
    #     ('f2', 's9', 'd9', '2', '3'),
    #     ('f2', 's10', 'd10', '3', '4'),
    #     ('f2', 's11', 'd11', '4', '5'),
    #     ('f2', 's12', 'd12', '5', '6'),
    #     ('f2', 's13', 'd13', '6', 'x13'),
    #     ('f2', 's14', 'd14', 'x13', 'd14'),
    #     # ('f3', '9', '11', '9', '1'),
    #     # ('f3', 's16', 'd16', '1', '3'),
    #     # ('f3', 's17', 'd17', '3', '4'),
    #     # ('f3', 's18', 'd18', '4', '5'),
    #     # ('f3', 's19', 'd19', '5', '6'),
    #     # ('f3', 's20', 'd20', '6', 'x20'),
    #     # ('f3', 's21', 'd21', 'x20', 'd21')
    # ]
    
    intial_T_tuples = [
        # ('f1', '2', '17', '2', '4'),
        # ('f1', 's2', 'd2', '4', '5'),
        # ('f1', 's3', 'd3', '5', '6'),
        # ('f1', 's4', 'd4', '6', '7'),
        # ('f1', 's5', 'd5', '7', '8'),
        # ('f1', 's6', 'd6', '8', '9'),
        # ('f1', 's7', 'd7', '9', '10'),
        # ('f1', 's8', 'd8', '10', '11'),
        # ('f1', 's9', 'd9', '11', '12'),
        # ('f1', 's10', 'd10', '12', 'x10'),
        # ('f1', 's11', 'd11', 'x10', 'd11'),
        ('f2', '2', '16', '2', '4'),
        ('f2', 's12', 'd12', '4', '5'),
        ('f2', 's13', 'd13', '5', '6'),
        ('f2', 's14', 'd14', '6', '7'),
        ('f2', 's15', 'd15', '7', '8'),
        ('f2', 's16', 'd16', '8', '9'),
        ('f2', 's17', 'd17', '9', '10'),
        ('f2', 's18', 'd18', '10', '11'),
        ('f2', 's19', 'd19', '11', '12'),
        ('f2', 's20', 'd20', '12', 'x20'),
        ('f2', 's21', 'd21', 'x20', 'd21'),
        ('f3', '1', '18', '1', '3'),
        ('f3', 's22', 'd22', '3', '5'),
        ('f3', 's23', 'd23', '5', '6'),
        ('f3', 's24', 'd24', '6', '7'),
        ('f3', 's25', 'd25', '7', '8'),
        ('f3', 's26', 'd26', '8', '9'),
        ('f3', 's27', 'd27', '9', '10'),
        ('f3', 's28', 'd28', '10', '11'),
        ('f3', 's29', 'd29', '11', '12'),
        ('f3', 's30', 'd30', '12', 'x30'),
        ('f3', 's31', 'd31', 'x30', 'd31')
    ]

    rewrite_policy1 = [
        {
            'dependency_tuples': [
                ('f', '2', '16', '2', '4'),
                ('f', 's', 'd', '4', '5')
            ], 
            'dependency_summary': ["s = 1", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '1', '16', '1', '3'),
                ('f', 's', 'd', '3', '5')
            ], 
            'dependency_summary': ["s = 1", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '17', '1', '3'),
                ('f', 's', 'd', '3', '5')
            ], 
            'dependency_summary': ["s = 1", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '18', '1', '3'),
                ('f', 's', 'd', '3', '5')
            ], 
            'dependency_summary': ["s = 1", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '18', '2', '4'),
                ('f', 's', 'd', '4', '5')
            ], 
            'dependency_summary': ["s = 2", "d = 10"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
    ]

    rewrite_policy2 = [
        {
            'dependency_tuples': [
                ('f', '1', '16', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 1", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '1', '17', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 1", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '18', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 1", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '16', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 2", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '17', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 2", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '18', '5', '6'),
                ('f', 's', 'd', '6', '7')
            ], 
            'dependency_summary': ["s = 2", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    firewall_policy1 = [
        {
            'dependency_tuples': [
                ('f', '1', '16', '9', '10'),
                ('f', 's', 'd', '10', '11')
            ], 
            'dependency_summary': ["s = 1", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '1', '17', '9', '10'),
                ('f', 's', 'd', '10', '11')
            ], 
            'dependency_summary': ["s = 1", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },  
        {
            'dependency_tuples': [
                ('f', '2', '16', '9', '10'),
                ('f', 's', 'd', '10', '11')
            ], 
            'dependency_summary': ["s = 2", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '2', '17', '9', '10'),
                ('f', 's', 'd', '10', '11')
            ], 
            'dependency_summary': ["s = 2", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '2', '18', '9', '10'),
                ('f', 's', 'd', '10', '11')
            ], 
            'dependency_summary': ["s = 2", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    rewrite_policy3 = [
        {
            'dependency_tuples': [
                ('f', '1', '17', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 1", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }, 
        {
            'dependency_tuples': [
                ('f', '1', '16', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 1", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '1', '18', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 1", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '16', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 2", "d = 16"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '17', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 2", "d = 17"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', '2', '18', '11', '12'),
                ('f', 's', 'd', '12', 'x')
            ], 
            'dependency_summary': ["s = 2", "d = 18"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    policy12 = [
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', '5'),
                ('f', 's2', 'd2', '5', '6')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', '7'),
                ('f', 's2', 'd2', '7', '8')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', '8'),
                ('f', 's2', 'd2', '8', '9')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', '9'),
                ('f', 's2', 'd2', '9', '10')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', '11'),
                ('f', 's2', 'd2', '11', '12')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's1', 'd1', 'n', 'x1'),
                ('f', 's2', 'd2', 'x1', 'd2')
            ], 
            'dependency_summary': ["s2 = s1", "d2 = d1"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    additional_policy = [
        {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', '16'),
            ], 
            'dependency_summary': ["n = 13"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', '17'),
            ], 
            'dependency_summary': ["n = 14"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        },
        {
            'dependency_tuples': [
                ('f', 's', 'd', 'n', '18'),
            ], 
            'dependency_summary': ["n = 15"], 
            'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
            'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
            'dependency_summary_condition': None, 
            'dependency_type': 'egd'
        }
    ]

    run_the_chase_sqls(conn, 
        intial_T_tablename, 
        intial_T_tuples, 
        [rewrite_policy1, policy12, rewrite_policy2, firewall_policy1, rewrite_policy3, policy12, additional_policy], 
        [])



if __name__ == '__main__':
    # test_fork_forward_backward()
    # test_fork_interface_table()
    # test_new_idea()
    test_straightforward_idea()
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


    # # ============================test idea=============================
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    # topo_attributes = ['n', 'x', 'forward', 'backward']
    # topo_datatypes = ['text', 'text', 'text', 'text']
    # LP1_tablename = 'lp1'
    # LP1_tuples = [
    #     ('1', '31', '0', '1'),
    #     ('2', '32', '0', '2'),
    #     ('31', '33', '0', '1'),
    #     ('32', '33', '0', '2')
    # ]
    # gen_topo(conn, topo_tablename=LP1_tablename, topo_tuples=LP1_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    # LP2_tablename = 'lp2'
    # LP2_tuples = [
    #     ('31', '33', '0', '1'),
    #     ('32', '33', '0', '2'),
    #     ('33', '41', '0', '0'),
    #     ('41', '42', '0', '0')
    # ]
    # gen_topo(conn, topo_tablename=LP2_tablename, topo_tuples=LP2_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    # LP3_tablename = 'lp3'
    # LP3_tuples = [
    #     ('41', '42', '0', '0'),
    #     ('42', '51', '0', '0'),
    #     ('51', '52', '0', '0'),
    #     ('52', '61', '0', '0'),
    #     ('61', '62', '0', '0'),
    # ]
    # gen_topo(conn, topo_tablename=LP3_tablename, topo_tuples=LP3_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    # LP4_tablename = 'lp4'
    # LP4_tuples = [
    #     ('61', '62', '0', '0'),
    #     ('62', '71', '0', '0'),
    #     ('71', '72', '8', '0'),
    #     ('71', '73', '9', '0'),
    #     ('71', '74', '10', '0'),
    #     ('72', '8', '8', '0'),
    #     ('73', '9', '9', '0'),
    #     ('74', '10', '10', '0'),
    # ]
    # gen_topo(conn, topo_tablename=LP4_tablename, topo_tuples=LP4_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    # # LP5_tablename = 'lp5'
    # # LP5_tuples = [
    # #     # ('61', '62', '0', '0'),
    # #     # ('62', '71', '0', '0'),
    # #     ('71', '72', '8', '0'),
    # #     ('71', '73', '9', '0'),
    # #     ('71', '74', '10', '0'),
    # #     ('72', '8', '8', '0'),
    # #     ('73', '9', '9', '0'),
    # #     ('74', '10', '10', '0'),
    # # ]
    # # gen_topo(conn, topo_tablename=LP5_tablename, topo_tuples=LP5_tuples, topo_datatypes=topo_datatypes, topo_attributes=topo_attributes)

    # intial_T_tablename = "T"

    # intial_T_tuples = [
    #     ('f', '1', '8', '1', '31')
    # ]

    # rewrite_policy1 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '2', '8', '32', '33')
    #         ], 
    #         'dependency_summary': ['f', '1', '8', '31', '33'], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '2', '8', '32', '33'), 
    #             ('f2', '1', '8', '31', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', '2', '8', '31', '33')
    #         ], 
    #         'dependency_summary': ['f', '1', '8', '31', '33'], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '2', '8', '31', '33'), 
    #             ('f2', '1', '8', '31', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # rewrite_policy2 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '1', '8', '41', '42')
    #         ], 
    #         'dependency_summary': ['f', '1', '9', '41', '42'], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '1', '8', '41', '42'), 
    #             ('f2', '1', '9', '41', '42')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # rewrite_policy3 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '1', '9', '61', '62')
    #         ], 
    #         'dependency_summary': ['f', '1', '10', '61', '62'], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     }, 
    #     {   
    #         'dependency_tuples': [
    #             ('f1', '1', '9', '61', '62'), 
    #             ('f2', '1', '10', '61', '62')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'],  
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'],  
    #         'dependency_summary': ['f1 = f2'], 
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # # firewall_policy1 = [
    # #     {
    # #         'dependency_tuples': [
    # #             ('f', '2', '9', '31', '33')
    # #         ], 
    # #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    # #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    # #         'dependency_summary': [],  # summary is empty for firewall dependency
    # #         'dependency_summary_condition': None, 
    # #         'dependency_type': 'egd'
    # #     },
    # #     {
    # #         'dependency_tuples': [
    # #             ('f', '2', '9', '32', '33')
    # #         ], 
    # #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    # #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    # #         'dependency_summary': [],  # summary is empty for firewall dependency
    # #         'dependency_summary_condition': None, 
    # #         'dependency_type': 'egd'
    # #     }
    # # ]

    # # firewall_policy2 = [
    # #     {
    # #         'dependency_tuples': [
    # #             ('f', '1', '10', '71', '72')
    # #         ], 
    # #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    # #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    # #         'dependency_summary': [],  # summary is empty for firewall dependency
    # #         'dependency_summary_condition': None, 
    # #         'dependency_type': 'egd'
    # #     },
    # #     {
    # #         'dependency_tuples': [
    # #             ('f', '1', '10', '71', '73')
    # #         ], 
    # #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    # #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    # #         'dependency_summary': [],  # summary is empty for firewall dependency
    # #         'dependency_summary_condition': None, 
    # #         'dependency_type': 'egd'
    # #     },
    # #     {
    # #         'dependency_tuples': [
    # #             ('f', '1', '10', '71', '74')
    # #         ], 
    # #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    # #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    # #         'dependency_summary': [],  # summary is empty for firewall dependency
    # #         'dependency_summary_condition': None, 
    # #         'dependency_type': 'egd'
    # #     }
    # # ]

    # firewall_policy1 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '2', '9', '31', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f', '2', '11', '31', '33'],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('x_f', '2', '9', '31', '33'),
    #             ('y_f', '2', '11', '31', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', '2', '9', '32', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f', '2', '11', '32', '33'],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('x_f', '2', '9', '32', '33'),
    #             ('y_f', '2', '11', '32', '33')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
    # ]

    # firewall_policy2 = [
    #     {
    #         'dependency_tuples': [
    #             ('f', '1', '10', '71', '72')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f', '1', '11', '71', '72'],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('x_f', '1', '10', '71', '72'),
    #             ('y_f', '1', '11', '71', '72')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
        
    #     {
    #         'dependency_tuples': [
    #             ('f', '1', '10', '71', '73')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f', '1', '11', '71', '73'],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('x_f', '1', '10', '71', '73'),
    #             ('y_f', '1', '11', '71', '73')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('f', '1', '10', '71', '74')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ['f', '1', '11', '71', '74'],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'tgd'
    #     },
    #     {
    #         'dependency_tuples': [
    #             ('x_f', '1', '10', '71', '74'),
    #             ('y_f', '1', '11', '71', '74')
    #         ], 
    #         'dependency_attributes': ['f', 'src', 'dst', 'n', 'x'], 
    #         'dependency_attributes_datatypes': ['text', 'text', 'text', 'text', 'text'], 
    #         'dependency_summary': ["x_f = y_f"],  # summary is empty for firewall dependency
    #         'dependency_summary_condition': None, 
    #         'dependency_type': 'egd'
    #     }
        
    # ]
    
    # # rewrite_infos = [('2', '8'), ('1', '8'), ('1', '9'), ('1', '10')]
    # rewrite_infos = [[('2', '8'), ('2', '9')], [('1', '8')], [('1', '9')], [('1', '10')]]
    # # rewrite_infos = [('10.0.0.2', '10.0.0.3'), ('10.0.0.1', '10.0.0.3'), ('10.0.0.1', '10.0.0.4')]
    # # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename)]
    # # pairs_tables = [(intial_T_tablename, LP1_tablename), (intial_T_tablename, LP2_tablename), (intial_T_tablename, LP3_tablename), (intial_T_tablename, LP4_tablename), (intial_T_tablename, LP5_tablename)]
    # # pairs_tables = [(intial_T_tablename, LP1_tablename, B1_tablename), (intial_T_tablename, LP2_tablename, B2_tablename), (intial_T_tablename, LP3_tablename, B3_tablename), (intial_T_tablename, LP4_tablename, B4_tablename)]

    # # sigma_new_sqls = gen_sigma_new_sqls(pairs_tables, rewrite_infos)
    # # sigma_new_sqls = gen_sigma_new_sqls2(pairs_tables)
    # # sigma_new_sqls = gen_sigma_new_sqls3(pairs_tables, rewrite_infos)
    # sigma_new_sqls = gen_sigma_new_sqls5(pairs_tables, rewrite_infos)
    # # sigma_new_program = "T(x_f, '2', '8', x_x, x_next) :- T(x_f, '2', '8', x_n, x_x), lp1(x_x, x_next, '1')\nT(x_f, '2', '8', x_x, '8') :- T(x_f, '2', '8', x_n, x_x), lp1(x_x, '8', '0')\nT(x_f, '2', '8', x_pre, x_n) :- T(x_f, '2', '8', x_n, x_x), lp1(x_pre, x_n, '1')\nT(x_f, '2', '8', '2', x_n) :- T(x_f, '2', '8', x_n, x_x), lp1('2', x_n, '0')\nT(x_f, '1', '8', x_x, x_next) :- T(x_f, '1', '8', x_n, x_x), lp2(x_x, x_next, '1')\nT(x_f, '1', '8', x_x, '8') :- T(x_f, '1', '8', x_n, x_x), lp2(x_x, '8', '0')\nT(x_f, '1', '8', x_pre, x_n) :- T(x_f, '1', '8', x_n, x_x), lp2(x_pre, x_n, '1')\nT(x_f, '1', '8', '1', x_n) :- T(x_f, '1', '8', x_n, x_x), lp2('1', x_n, 0)\nT(x_f, '1', '9', x_x, x_next) :- T(x_f, '1', '9', x_n, x_x), lp3(x_x, x_next, '1')\nT(x_f, '1', '9', x_x, '9') :- T(x_f, '1', '9', x_n, x_x), lp3(x_x, '9', '0')\nT(x_f, '1', '9', x_pre, x_n) :- T(x_f, '1', '9', x_n, x_x), lp3(x_pre, x_n, '1')\nT(x_f, '1', '9', '1', x_n) :- T(x_f, '1', '9', x_n, x_x), lp3('1', x_n, '0')\nT(x_f, '1', '10', x_x, x_next) :- T(x_f, '1', '10', x_n, x_x), lp4(x_x, x_next, '1')\nT(x_f, '1', '10', x_x, '10') :- T(x_f, '1', '10', x_n, x_x), lp4(x_x, '10', '0')\nT(x_f, '1', '10', x_pre, x_n) :- T(x_f, '1', '10', x_n, x_x), lp4(x_pre, x_n, '1')\nT(x_f, '1', '10', '1', x_n) :- T(x_f, '1', '10', x_n, x_x), lp4('1', x_n, '0')"
    # # sigma_new_sqls = gen_sigma_new_sqls_general(pairs_tables)

    # run_the_chase_sqls(conn, 
    #     intial_T_tablename, 
    #     intial_T_tuples, 
    #     [rewrite_policy1, rewrite_policy2, rewrite_policy3, firewall_policy1, firewall_policy2], 
    #     sigma_new_sqls)
    
    # # run_the_chase(conn=conn, 
    # #         initial_T_tablename=intial_T_tablename, 
    # #         initial_T_tuples=intial_T_tuples, 
    # #         policies=[rewrite_policy1, rewrite_policy2, rewrite_policy3], 
    # #         sigma_new_program=sigma_new_program, 
    # #         databaseTypes={intial_T_tablename:['text', 'text', 'text', 'text', 'text'], 
    # #                     LP1_tablename:topo_datatypes, 
    # #                     LP2_tablename:topo_datatypes, 
    # #                     LP3_tablename:topo_datatypes, 
    # #                     LP4_tablename:topo_datatypes}
    # #     )
    
    