import sys
from os.path import dirname, abspath

root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)

import psycopg2 
import time
import re
from tqdm import tqdm
import databaseconfig as cfg
from psycopg2.extras import execute_values

conn = psycopg2.connect(host=cfg.postgres["host"], database="arch", user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def gen_arch_query(path_node_list, tablename):
    """
    generate a arch query according to a path
    """
    tuples = []
    summary = []
    j = 1
    for i in range(len(path_node_list)):
        t = None
        if i == 0:
            summary.append("s{}".format(i+1))
            t = ("s{}".format(j), "d{}".format(j), "s{}".format(j), path_node_list[i], 'allow')
            tuples.append(t)
            j += 1
            t = ("s{}".format(j), "d{}".format(j), path_node_list[i], path_node_list[i+1], 'allow')
        elif i == len(path_node_list) - 1:
            summary.append("d{}".format(i+1))
            t = ("s{}".format(j), "d{}".format(j), path_node_list[i], "d{}".format(j), 'allow')
        else:
            t = ("s{}".format(j), "d{}".format(j), path_node_list[i], path_node_list[i+1], 'allow')
        j += 1
        tuples.append(t)
    
    sql = "drop table if exists {tablename}".format(tablename=tablename)
    cursor.execute(sql)

    sql = "create table {tablename} (s text, d text, n text, x text, a text)".format(tablename=tablename)
    cursor.execute(sql)

    sql = "insert into {tablename} values %s".format(tablename=tablename)
    execute_values(cursor, sql, tuples)

    print("Done!")
    return summary

def apply_firewall(firewall_table, arch_table):
    """
    apply firewall policies in firewall table
    """
    sql = "select * from {}".format(firewall_table)
    cursor.execute(sql)

    row_num = cursor.rowcount
    for i in tqdm(range(row_num)):
        row = cursor.fetchone()
        sqls = firewall_sqls(row, arch_table)
        for sql in sqls:
            cursor.execute(sql)
    print("Done!")

def firewall_sqls(firewall_rule, arch_table):
    """
    generate update SQLs for a firewall policy
    """
    sqls = []
    attributes = ['s', 'd', 'n', 'x']
    where_conditions = []
    for i in range(len(attributes)):
        where_conditions.append("{} = '{}'".format(attributes[i], firewall_rule[i]))
    sql = "update {table_name} set a = '{a}' where {conditions}".format(table_name=arch_table, a=firewall_rule[-2], conditions=" and ".join(where_conditions))
    sqls.append(sql)
    print(sql)

    conditions = firewall_rule[-1]
    for cond in conditions:
        items = cond.split()
        left_opd = items[0]
        op = items[1]
        right_opd = items[2]

        if op == '==':
            op = '='

        for attr in attributes:
            sql = "update {table_name} set {attribute} = '{value}' where {attribute} {op} '{attr_value}'".format(
                                                table_name=arch_table, 
                                                attribute=attr, 
                                                value= right_opd,
                                                op=op, 
                                                attr_value=left_opd)
            sqls.append(sql)
            print(sql)
    return sqls

def apply_rewrite(rewrite_table, arch_table):
    sqls = rewrite_sqls(rewrite_table, arch_table)

    for sql in sqls:
        cursor.execute(sql)
    print("Done!")

def rewrite_sqls(rewrite_table, arch_table):
    sql = "select * from {rewrite_table} where cardinality(condition) = 0".format(rewrite_table=rewrite_table)
    cursor.execute(sql)
    nodes_before_rw = cursor.fetchall()

    nodes_before_rw_list = []
    for node in nodes_before_rw:
        nodes_before_rw_list.append({"s":node[0], "d":node[1], "n":node[2], "x":node[3]})
    
    for i in range(len(nodes_before_rw_list)):
        node = nodes_before_rw_list[i]
        sql = "select s, d from {} where n = '{}' and x = '{}'".format(arch_table, node["n"], node["x"])
        cursor.execute(sql)
        row = cursor.fetchone()

        node[node["s"]] = row[0]
        node[node["d"]] = row[1]

    print(nodes_before_rw_list)

    attributes = ["s", "d", "n", "x"]
    sqls = []
    for i in range(len(nodes_before_rw_list)):
        sql = "select * from {rewrite_table} where cardinality(condition) != 0 and '%= r(%)' <~~ ANY(condition)".format(rewrite_table=rewrite_table)
        cursor.execute(sql)
        node = nodes_before_rw_list[i]
        rows = cursor.fetchall()
        for row in rows:
            conditions = row[-1]
            function_pattern = re.compile("\((.+)\)")
            for cond in conditions:
                results = re.findall(function_pattern, cond)
                attr_value = results[0].strip()
                assignment = node[attr_value]

                rewrite_assignment = rewrite_toy(assignment)
                cond = cond.replace(node["s"], node[node["s"]])
                cond = cond.replace(node["d"], node[node["d"]])

                items = cond.split()
                left_opd = items[0]
                op = items[1]
                right_opd = items[2]

                for attr in attributes:
                    # sql = "update {table_name} set {attribute} = '{value}' where {attribute} {op} '{attr_value}'".format(
                    #                                     table_name=arch_table, 
                    #                                     attribute=attr, 
                    #                                     value= right_opd,
                    #                                     op=op, 
                    #                                     attr_value=left_opd)
                    sql = "update {table_name} set {attribute} = '{value}' where {attribute} {op} '{attr_value}'".format(
                                                        table_name=arch_table, 
                                                        attribute=attr, 
                                                        value= rewrite_assignment,
                                                        op=op, 
                                                        attr_value=left_opd)
                    sqls.append(sql)
                    print(sql)
    return sqls

def apply_plain_forward(arch_query, apply_firewall_rewrite, firewall_nodes, rewrite_nodes):
    """
    apply plain forward policy

    apply_firewall_rewrite: Boolean
        True if applying plain forward policy after applying firewall and rewrite policy; False if applying plain forward policy before applying firewall and rewrite policy.
    """
    sqls = plain_forward_sqls(arch_query, apply_firewall_rewrite, firewall_nodes, rewrite_nodes)
    for sql in sqls:
        cursor.execute(sql)
    
    print("Done!")

def plain_forward_sqls(arch_query, apply_firewall_rewrite, firewall_nodes, rewrite_nodes):
    sql = "select * from {arch_query}".format(arch_query=arch_query)
    cursor.execute(sql)

    replace_s = None
    replace_d = None
    tuples = cursor.fetchall()
    sqls = []
    attributes = ['s', 'd', 'n', 'x']
    for tuple in tuples:
        if apply_firewall_rewrite:
            if tuple[2] in firewall_nodes or tuple[2] in rewrite_nodes:
                continue
        
        if replace_s == None or replace_d == None:
            replace_s = tuple[0]
            replace_d = tuple[1]
        
        s = tuple[0]
        d = tuple[1]
        for attr in attributes:
            sql = "update {arch_query} set {attribute} = '{value}' where {attribute} = '{attr_value}'".format(arch_query=arch_query, attribute=attr, value=replace_s, attr_value=s)
            print(sql)
            sqls.append(sql)

            sql = "update {arch_query} set {attribute} = '{value}' where {attribute} = '{attr_value}'".format(arch_query=arch_query, attribute=attr, value=replace_d, attr_value=d)
            print(sql)
            sqls.append(sql)
        
    return sqls

def rewrite_function(network, is_source):
    sql = ""
    if is_source:
        sql = "select p.source, p.dest, d.source, d.dest from permit_rules p, deny_rules d where (p.source << d.source or p.source <> d.source or p.dest <> d.dest) and p.{} = '{}' ORDER BY random() LIMIT 1;".format("source", network)
        cursor.execute(sql)
        row = cursor.fetchall()[0]
    else:
        sql = "select p.source, p.dest, d.source, d.dest from permit_rules p, deny_rules d where (p.source << d.source or p.source <> d.source or p.dest <> d.dest) and p.{} = '{}' ORDER BY random() LIMIT 1;".format("dest", network)
    
def generate_firewall(firewall_pair_nodes, tablename):
    sql = "drop table if exists {}".format(tablename)
    cursor.execute(sql)

    sql = "create table {} (s text, d text, n text, x text, a text, condition text[])".format(tablename)
    cursor.execute(sql)

    sql = "select * from permit_rules order by ransdom() limit {}".format(len(firewall_pair_nodes))
    cursor.execute(sql)
    firewall_rules = cursor.fetchall()
    for idx, pair in enumerate(firewall_pair_nodes):
        conditions = []
        conditions.append("{} == {}".format(pair[0], firewall_rules[idx][0]))
        conditions.append("{} == {}".format(pair[1], firewall_rules[idx][1]))
        sql = "insert into firewall_"
        

def rewrite_toy(input_value):
    if input_value == '1.2.3.4':
        return '1.2.3.5'
    elif input_value == '5.6.7.8':
        return '5.6.7.9'
    return "10.0.0.1"


def get_attribute(str):
    """
    get attribute name from condition 
    """
    for i in range(len(str)):
        if str[i] == '_' or str[i].isdigit():
            return str[:i]
    return str 

def load_firewall_toy():
    """
    load a toy example of firewall policy
    """
    sql = "drop table if exists toy_firewall"
    cursor.execute(sql)

    sql = "create table toy_firewall (s text, d text, n text, x text, a text, condition text[])"
    cursor.execute(sql)

    sql = "insert into toy_firewall values (%s, %s, %s, %s, %s, %s)"
    cursor.execute(sql, ('s8', 'd8', '483', '479', 'allow', '{"s8 == 1.2.3.4", "d8 == 5.6.7.8"}'))

def load_rewrite_toy():
    sql = "drop table if exists toy_rewrite"
    cursor.execute(sql)

    sql = "create table toy_rewrite (s text, d text, n text, x text, condition text[])"
    cursor.execute(sql)

    sql = "insert into toy_rewrite values (%s, %s, %s, %s, %s)"
    cursor.execute(sql, ('s8', 'd8', '483', '479', '{}'))

    sql = "insert into toy_rewrite values (%s, %s, %s, %s, %s)"
    cursor.execute(sql, ('s9', 'd9', '479', '5892', '{"s9 = r(s8)", "d9 = r(d8)"}'))

if __name__ == '__main__':
    path = [11292, 2215, 10897, 8224, 3356, 8925, 483, 479, 5892, 9602, 11295]
    summary = gen_arch_query(path, "arch_test")
    print(summary)

    load_firewall_toy()
    load_rewrite_toy()

    begin = time.time()
    apply_firewall("toy_firewall", "arch_test")
    end = time.time()
    print("firewall:", end-begin)

    begin = time.time()
    apply_rewrite("toy_rewrite", "arch_test")
    end = time.time()
    print("rewrite:", end-begin)

    apply_plain_forward("arch_test", True, ['483'], ['479'])



