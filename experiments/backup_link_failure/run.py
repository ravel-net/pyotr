import sys
import os
from os.path import dirname, abspath, join, isfile
from xml import dom

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import time 
import databaseconfig as cfg
import psycopg2
import pyotr_translator.translator_pyotr as translator
import util.merge_tuples.merge_tuples_tautology as merge_tuples
import util.check_tautology.check_tautology as check_tautology
import util.check_tautology.condition_analyze as condition_analyze
import util.tableau.instantiate_tableau as instantiate_tableau

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def run_program_T3(input_table, domain, variables):
    sqls = [
        "select 1, 2, 'w' from {input_table} t1, \
                        {input_table} t2,\
                        {input_table} t3\
                where t1.n1 = '1' AND t1.n2 = '2' AND\
                        t2.n1 = t1.n2 AND t2.n2 = t3.n1".format(input_table=input_table),
        "SELECT 1, 2, 'w' from {input_table} t1,\
                        {input_table} t2\
                where t1.n1 = '1' AND t1.n2 = '2' AND\
                        t2.n1 = '2'".format(input_table=input_table),
        "SELECT 1, 'w' from {input_table} t1,\
                {input_table} t2\
                where t1.n1 = '1' AND t2.n1 = t1.n2;".format(input_table=input_table)
    ]

    union_tables = []
    for idx, sql in enumerate(sqls):
        tree = translator.generate_tree(sql)
        translator.data(tree)
        translator.upd_condition(tree)
        translator.normalization()
        new_table = "T3_{}".format(idx+1)
        merge_tuples.merge_tuples("output", new_table, domain, variables)

        union_tables.append(new_table)
    
    conditions = []
    for table in union_tables:
        cursor.execute("alter table {} drop column if exists id".format(table))
        cursor.execute("select * from {}".format(table))
        tuples = cursor.fetchall()
        for t in tuples:
            condition = t[-1]
            pred_condition = condition_analyze.analyze("And({})".format(", ".join(condition)))
            
            conditions.append(pred_condition)

    union_conditions = "Or({})".format(", ".join(conditions))
    domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=domain, variables_list=variables, datatype="Int")
    domain_conditions += ", Or(z3.Int('x') == z3.IntVal(0), z3.Int('x') == z3.IntVal(1)), Or(z3.Int('y') == z3.IntVal(0), z3.Int('y') == z3.IntVal(1))"
    
    ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
    if ans == False:
        print("It is not a tautology")
        print(model)

        mapping = instantiate_tableau.gen_mapping(model)
        instantiate_tableau.instantiate_tableau(input_table, mapping, "ins_"+input_table)
        instantiate_tableau.instantiate_tableau("T_3", mapping, "ins_T_3")
    else:
        print("It is a tautology")

def run_program_T2(input_table, domain, variables):
    sqls = [
        "select 1, 2, 'w' from {input_table} t1, \
                        {input_table} t2,\
                        {input_table} t3,\
                        {input_table} t4\
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND \
                        t2.n2 = '2'AND t3.n1 = '2' AND t3.n2 = t4.n1".format(input_table=input_table),
        "SELECT 1, 2, 'w' from {input_table} t1,\
                        {input_table} t2,\
                        {input_table} t3\
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND\
                        t2.n2 = '2' AND\
                        t3.n1 = '2'".format(input_table=input_table),
        "SELECT 1, 'w' from {input_table} t1,\
                {input_table} t2\
                where t1.n1 = '1' AND t2.n1 = t1.n2 ;".format(input_table=input_table)
    ]

    union_tables = []
    for idx, sql in enumerate(sqls):
        tree = translator.generate_tree(sql)
        translator.data(tree)
        translator.upd_condition(tree)
        translator.normalization()
        new_table = "T2_{}".format(idx+1)
        merge_tuples.merge_tuples("output", new_table, domain, variables)

        union_tables.append(new_table)
    
    conditions = []
    for table in union_tables:
        cursor.execute("alter table {} drop column if exists id".format(table))
        cursor.execute("select * from {}".format(table))
        tuples = cursor.fetchall()
        for t in tuples:
            condition = t[-1]
            pred_condition = condition_analyze.analyze("And({})".format(", ".join(condition)))
            
            conditions.append(pred_condition)

    union_conditions = "Or({})".format(", ".join(conditions))

    domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=domain, variables_list=variables, datatype="Int")
    domain_conditions += ", Or(z3.Int('x') == z3.IntVal(0), z3.Int('x') == z3.IntVal(1)), Or(z3.Int('y') == z3.IntVal(0), z3.Int('y') == z3.IntVal(1))"
    ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
    if ans == False:
        print(model)

        mapping = instantiate_tableau.gen_mapping(model)
        instantiate_tableau.instantiate_tableau(input_table, mapping, "ins_"+input_table)
        instantiate_tableau.instantiate_tableau("T_2", mapping, "ins_T_2")
    else:
        print("It is a tautology")

def run_program_T1(input_table, domain, variables):
    sqls = [
        "select 1, 2, 'w' from {input_table} t1, \
                        {input_table} t2,\
                        {input_table} t3,\
                        {input_table} t4\
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND \
                        t2.n2 = '2'AND \
                        t3.n1 = '2' AND t3.n2 = t4.n1".format(input_table=input_table),
        "SELECT 1, 2, 'w' from {input_table} t1,\
                        {input_table} t2,\
                        {input_table} t3\
                where t1.n1 = '1' AND t1.n2 = '2' AND\
                        t2.n1 = '2' AND  t2.n2 = t3.n1".format(input_table=input_table),
        "SELECT 1, 2, 'w' from {input_table} t1,\
                        {input_table} t2,\
                        {input_table} t3\
                where t1.n1 = '1' AND t1.n2 = t2.n1 AND\
                        t2.n2 = '2' AND \
                        t3.n1 = '2'".format(input_table=input_table),
        "SELECT 1, 2, 'w' from {input_table} t1,\
                {input_table} t2\
                where t1.n1 = '1' AND t1.n2 = '2' AND t2.n1 = '2'".format(input_table=input_table)
    ]

    union_tables = []
    for idx, sql in enumerate(sqls):
        tree = translator.generate_tree(sql)
        translator.data(tree)
        translator.upd_condition(tree)
        translator.normalization()
        new_table = "T1_{}".format(idx+1)
        merge_tuples.merge_tuples("output", new_table, domain, variables)

        union_tables.append(new_table)
    
    conditions = []
    for table in union_tables:
        cursor.execute("alter table {} drop column if exists id".format(table))
        cursor.execute("select * from {}".format(table))
        tuples = cursor.fetchall()
        for t in tuples:
            condition = t[-1]
            pred_condition = condition_analyze.analyze("And({})".format(", ".join(condition)))
            
            conditions.append(pred_condition)

    union_conditions = "Or({})".format(", ".join(conditions))

    domain_conditions, domain_time = check_tautology.get_domain_conditions(overlay_nodes=domain, variables_list=variables, datatype="Int")
    domain_conditions += ", Or(z3.Int('x') == z3.IntVal(0), z3.Int('x') == z3.IntVal(1)), Or(z3.Int('y') == z3.IntVal(0), z3.Int('y') == z3.IntVal(1))"
    ans, runtime, model = check_tautology.check_is_tautology(union_conditions, domain_conditions)
    if ans == False:
        print(model)

        mapping = instantiate_tableau.gen_mapping(model)
        instantiate_tableau.instantiate_tableau(input_table, mapping, "ins_"+input_table)
        instantiate_tableau.instantiate_tableau("T_1", mapping, "ins_T_1")
    else:
        print("It is a tautology")

if __name__ == '__main__':
    domain = [1, 2]
    variables = ['v', 'w']
    
    begin = time.time()
    run_program_T2("T_3",domain, variables)
    print(time.time() - begin)
    # run_program_T1("T_3", domain, variables)


    