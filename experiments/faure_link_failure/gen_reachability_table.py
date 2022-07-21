import sys
from os.path import dirname, abspath
from turtle import pos

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as cfg

import Backend.reasoning.Z3.check_tautology.check_tautology as check_tautology
import Core.Homomorphism.translator_pyotr as translator_pyotr


CONN = psycopg2.connect(host=cfg.postgres['host'], user=cfg.postgres['user'], database=cfg.postgres['db'], password=cfg.postgres["password"])
cursor = CONN.cursor()

def r1(f_table, AS_num):
    r1 = "r1_{}".format(AS_num)
    sql = "DROP TABLE IF EXISTS {} CASCADE;".format(r1)
    cursor.execute(sql)

    sql = "CREATE TABLE {} AS SELECT n1, n2, s, ARRAY[n1, n2] as path, condition FROM {};".format(r1, f_table)
    r1_begin = time.time()
    cursor.execute(sql)
    r1_end = time.time()
    CONN.commit()

    return r1_end - r1_begin

def rn(f_table, AS_num):
    count = 2
    rn_time = 0
    while True:
        r_next = "r{}_{}".format(count, AS_num)
        r_prev = "r{}_{}".format(count - 1, AS_num)

        sql = "drop table if exists {};".format(r_next)
        cursor.execute(sql)

        sql = "create table {r_next} as SELECT \
                {r_prev}.n1 as n1, {f_table}.n2 as n2, \
                array_cat({r_prev}.s, {f_table}.s) as s, \
                array_cat({r_prev}.path, ARRAY[{f_table}.n2]) as path, \
                array_cat({r_prev}.condition, {f_table}.condition) as condition \
                FROM {r_prev}, {f_table} \
                WHERE {r_prev}.n2 = {f_table}.n1 and {r_prev}.n1 != {f_table}.n2 \
                and not {f_table}.n2 = ANY({r_prev}.path);" \
                .format(r_next=r_next, 
                r_prev=r_prev, f_table=f_table)

        rn_begin = time.time()
        cursor.execute(sql)
        rn_end = time.time()

        rn_time += rn_end - rn_begin
        num = cursor.rowcount
        
        CONN.commit()

        if num == 0:
            return count, rn_time
        
        count = count + 1
        
def union(count, AS_num, source, dest):
    reachability_table = "R_{}".format(AS_num)
    sql = "drop table if exists {};".format(reachability_table)
    cursor.execute(sql)

    sql = "create table {} as ".format(reachability_table)

    select_sqls = []
    for i in range(1, count):
        r_table = "r{}_{}".format(i, AS_num)
        sql = "select n1, n2, s, condition from {} where n1 = '{}' and n2 = '{}'".format(r_table, source, dest)
        select_sqls.append(sql)
    
    sql = "create table {} as {}".format(reachability_table, " union ".join(select_sqls))

    union_begin = time.time()
    cursor.execute(sql)
    union_end = time.time()
    CONN.commit()

    return reachability_table, union_end - union_begin

def clean(count, AS_num):
    for i in range(1, count+1):
        r_table = "r{}_{}".format(i, AS_num)
        sql = "drop table if exists {}".format(r_table)
        cursor.execute(sql)
    CONN.commit()

def check(r_table, Z3_datatype):

    check_begin = time.time()
    translator_pyotr.normalization(Z3_datatype, r_table)
    check_end = time.time()
    # cursor.execute("select * from {}".format(r_table))

    # domains = []
    # for var in vars_domains.keys():
    #     domain_cond = check_tautology.get_domain_conditions(vars_domains[var], [var], 'Int')
    #     domains.append(domain_cond)
    
    # domain_condition = ", ".join(domains)
    # print("domain_condition", domain_condition)
    return check_end-check_begin

    


