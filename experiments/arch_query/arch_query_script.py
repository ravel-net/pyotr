import random
import sys
from os.path import dirname, abspath, join

root = dirname(dirname(abspath(__file__)))
print(root)
sys.path.append(root)

import psycopg2 
import time
import re
from tqdm import tqdm
import databaseconfig as cfg
from psycopg2.extras import execute_values
import arch_query.shortest_paths as shortest_paths

conn = psycopg2.connect(host=cfg.postgres["host"], database="arch", user=cfg.postgres["user"], password=cfg.postgres["password"])
conn.set_session(readonly=False, autocommit=True)
cursor = conn.cursor()

def gen_arch_query(paths, source, dest, tablename):
    """
    generate a arch query according to a path
    """
    all_nodes = []
    links = []
    tuples = []
    a = 'allow'

    k = 1
    s = 's{}'.format(k)
    d = 'd{}'.format(k)
    tuples.append((s, d, s, str(source), a))
    begin_node = s
    k += 1

    for i in range(len(paths[0])):
        for j in range(len(paths)):
            if paths[j][i] not in all_nodes:
                all_nodes.append(paths[j][i])
            
            if i < len(paths[0]) - 1:
                link = (paths[j][i], paths[j][i+1])
                if link not in links:
                    links.append(link)

                    s = 's{}'.format(k)
                    d = 'd{}'.format(k)
                    tuples.append((s, d, str(paths[j][i]), str(paths[j][i+1]), a))
                    k += 1
    s = 's{}'.format(k)
    d = 'd{}'.format(k)
    tuples.append((s, d, str(dest), d, a))
    end_node = d
    
    summary = (begin_node, end_node)

    # print(all_nodes)
    # print(links)
    # print(tuples)
    
    sql = "drop table if exists {tablename}".format(tablename=tablename)
    cursor.execute(sql)

    sql = "create table {tablename} (s text, d text, n text, x text, a text)".format(tablename=tablename)
    cursor.execute(sql)

    sql = "insert into {tablename} values %s".format(tablename=tablename)
    execute_values(cursor, sql, tuples)

    # print("Done!")
    return summary, all_nodes, links

def generate_firewall_rules(firewall_nodes, tablename, arch_query_tablename):
    """
    generate firewall rules 
    """
    sql = "drop table if exists {}".format(tablename)
    cursor.execute(sql)

    sql = "create table {} (s text, d text, n text, x text, a text, condition text[])".format(tablename)
    cursor.execute(sql)

    sql = "select * from permit_rules order by random() limit {}".format(len(firewall_nodes))
    cursor.execute(sql)
    firewall_rules = cursor.fetchall()

    tuples = []
    for idx, node in enumerate(firewall_nodes):
        sql = "select * from {} where n = '{}'".format(arch_query_tablename, node)
        cursor.execute(sql)
        links = cursor.fetchall()

        for link in links:
            conditions = []
            conditions.append('"{} == {}"'.format(link[0], firewall_rules[idx][0]))
            conditions.append('"{} == {}"'.format(link[1], firewall_rules[idx][1]))
            t = list(link).copy()
            t.append("{"+"{conditions}".format(conditions=", ".join(conditions))+"}")
            tuples.append(t)

    sql = "insert into {} values %s".format(tablename)
    execute_values(cursor, sql, tuples)

    print("Done!")

def generate_rewrite_rules(rewrite_nodes, tablename, arch_query_tablename):
    """
    generate rewrite rules
    """
    sql = "drop table if exists {}".format(tablename)
    cursor.execute(sql)

    sql = "create table {} (s text, d text, n text, x text, condition text[])".format(tablename)
    cursor.execute(sql)

    tuples = []
    for node in rewrite_nodes:
        sql = "select * from {} where x = '{}'".format(arch_query_tablename, node)
        print(sql)
        cursor.execute(sql)
        prev_links = cursor.fetchall()
        print(prev_links)
        sql = "select * from {} where n = '{}'".format(arch_query_tablename, node)
        cursor.execute(sql)
        after_links = cursor.fetchall()

        for p_link in prev_links:
            t = list(p_link).copy()
            t.remove('allow')
            t.append("{}")
            print(t)
            tuples.append(t)

            for a_link in after_links:
                conditions = []
                conditions.append('"{} = r({})"'.format(a_link[0], p_link[0]))
                conditions.append('"{} = r({})"'.format(a_link[1], p_link[1]))
                t = list(a_link).copy()
                t.remove('allow')
                t.append("{"+"{conditions}".format(conditions=", ".join(conditions))+"}")
                tuples.append(t)
    print(tuples)
    sql = "insert into {} values %s".format(tablename)
    execute_values(cursor, sql, tuples)

    print("Done!")

def apply_firewall(path, firewall_nodes, firewall_table, arch_table):
    """
    apply firewall policies in firewall table
    """
    sqls = firewall_sqls(path, firewall_nodes, firewall_table, arch_table)

    begin_update = time.time()
    for sql in sqls:
        cursor.execute(sql)
    end_update = time.time()
    # print("#update sqls:", len(sqls))
    # print("Done!")
    is_apply = len(sqls) != 0 
    return end_update - begin_update, is_apply

def firewall_sqls(path, firewall_nodes, firewall_table, arch_table):
    """
    generate update SQLs for a firewall policy
    """
    firewall_rule = None
    for idx, node in enumerate(path): 
        if node in firewall_nodes:
            sql = "select * from {} where n = '{}'".format(firewall_table, node)
            cursor.execute(sql)
            rows = cursor.fetchall()

            for row in rows:
                if row[3] == path[idx+1]:
                    firewall_rule = list(row).copy()

    sqls = []
    if firewall_rule is None:
        return sqls

    attributes = ['s', 'd', 'n', 'x']
    where_conditions = []
    for i in range(len(attributes)):
        where_conditions.append("{} = '{}'".format(attributes[i], firewall_rule[i]))
    sql = "update {table_name} set a = '{a}' where {conditions}".format(table_name=arch_table, a=firewall_rule[-2], conditions=" and ".join(where_conditions))
    sqls.append(sql)

    conditions = firewall_rule[-1]

    attributes_mapping = {}
    for cond in conditions:
        items = cond.split()
        left_opd = items[0]
        right_opd = items[2]

        attributes_mapping[left_opd.strip()] = right_opd.strip()
    
    sql = "update {table_name} set {attribute1} = '{value1}', {attribute2} = '{value2}' where {attribute1} = '{attr_value1}' and {attribute2} = '{attr_value2}'".format(
                                        table_name=arch_table, 
                                        attribute1="s", 
                                        value1=attributes_mapping[firewall_rule[0]],
                                        attribute2="d",
                                        value2=attributes_mapping[firewall_rule[1]],
                                        attr_value1=firewall_rule[0],
                                        attr_value2=firewall_rule[1])

    sqls.append(sql)

    sql = "update {table_name} set n = '{value}' where x = '{attr_value}'".format(table_name=arch_table, value=attributes_mapping[firewall_rule[0]], attr_value=firewall_rule[0])
    sqls.append(sql)

        # for attr in attributes:
        #     sql = "update {table_name} set {attribute} = '{value}' where {attribute} = '{attr_value}'".format(
        #                                         table_name=arch_table, 
        #                                         attribute=attr, 
        #                                         value= right_opd,
        #                                         attr_value=left_opd)
        #     sqls.append(sql)
        # sql = "update {table_name} set {attribute1} = '{value1}', {attribute2} = '{value2}' where {attribute1} = '{attr_value1}' and {attribute2} = '{attr_value2}'".format(
        #                                 table_name=arch_table, 
        #                                 attribute1="s", 
        #                                 value1=right_opd,
        #                                 attribute2="d",
        #                                 value2=rewrite_dest,
        #                                 attr_value1=row[0],
        #                                 attr_value2=row[1])
    return sqls

def apply_rewrite(path, firewall_nodes, rewrite_nodes, rewrite_table, arch_table):
    """
    apply to run SQLs for rewrite policy
    """
    sqls = rewrite_sqls(path, firewall_nodes, rewrite_nodes, rewrite_table, arch_table)

    begin_update = time.time()
    for sql in sqls:
        cursor.execute(sql)
    end_update = time.time()
    # print("#update sqls:", len(sqls))
    # print("Done!")
    is_apply = len(sqls) != 0 
    return end_update-begin_update, is_apply

def rewrite_sqls(path, firewall_nodes, rewrite_nodes, rewrite_table, arch_table):
    """
    generate update SQLs for rewrite policy
    """
    sqls = []

    IS_APPLY_FIREWALL = False
    for idx, node in enumerate(path):
        if node in firewall_nodes:
            sql = "select * from {} where n = '{}' and x = '{}'".format(arch_table, node, path[idx+1])
            cursor.execute(sql)
            row = cursor.fetchone()

            if row[0].startswith('s') or row[1].startswith('d'):
                IS_APPLY_FIREWALL = False
            else:
                IS_APPLY_FIREWALL = True
        elif node in rewrite_nodes:
            if IS_APPLY_FIREWALL:
                sql = "select * from {rewrite_table} where n = '{node_before_rewrite_node}' and x = '{rewrite_node}'".format(rewrite_table=rewrite_table, node_before_rewrite_node= path[idx-1], rewrite_node=node)
                cursor.execute(sql)
                row = cursor.fetchone()

                node_mapping = {"s":row[0], "d":row[1], "n":row[2], "x":row[3]}

                sql = "select s, d from {} where n = '{}' and x = '{}'".format(arch_table, node_mapping["n"], node_mapping["x"])
                cursor.execute(sql)
                row = cursor.fetchone()

                node_mapping[node_mapping["s"]] = row[0]
                node_mapping[node_mapping["d"]] = row[1]

                # if rewrite node locates at the final node of the path, the value of x is equal to value of d
                sql = "select * from {rewrite_table} where n = '{rewrite_node}' and x = '{node_after_rewrite_node}' and ('%{s}%' <~~ ANY(condition))".format(rewrite_table=rewrite_table, rewrite_node=node, node_after_rewrite_node = path[idx+1] if idx < len(path)-1 else node_mapping["d"], s=node_mapping["s"]) 
                cursor.execute(sql)
                
                row = cursor.fetchone()
                conditions = row[-1]
                function_pattern = re.compile("\((.+)\)")

                source = None
                dest = None
                for cond in conditions:
                    results = re.findall(function_pattern, cond)
                    attr_value = results[0].strip()
                    assignment = node_mapping[attr_value]

                    # if attr_value == node[attr_value]:
                    #     assignment = "r({})".format(assignment)

                    if cond.startswith("s"):
                        source = assignment
                    else:
                        dest = assignment
                
                rewrite_source = None
                rewrite_dest = None

                # print("source", source, "dest", dest)
                if source.startswith("s") or dest.startswith("d"):
                    rewrite_source = "r({})".format(source)
                    rewrite_dest = "r({})".format(dest)
                else:
                    rewrite_source, rewrite_dest = rewrite_function(source, dest)
                # print("rewrite_source", rewrite_source, "rewrite_dest", rewrite_dest)

                sql = "update {table_name} set {attribute1} = '{value1}', {attribute2} = '{value2}' where {attribute1} = '{attr_value1}' and {attribute2} = '{attr_value2}'".format(
                                                            table_name=arch_table, 
                                                            attribute1="s", 
                                                            value1=rewrite_source,
                                                            attribute2="d",
                                                            value2=rewrite_dest,
                                                            attr_value1=row[0],
                                                            attr_value2=row[1])
                sqls.append(sql)

                sql = "update {table_name} set x = '{value}' where x = '{attr_value}'".format(table_name=arch_table, value=rewrite_dest, attr_value=row[1])
                sqls.append(sql)

                break
    return sqls

def rewrite_function(source, destination):
    """
    rewrite function for rewrite policy
    """
    sql = "select d.source, d.dest from permit_rules p, deny_rules d where (p.source << d.source or p.source <> d.source or p.dest <> d.dest) and p.source = '{}' and p.dest = '{}' ORDER BY random() LIMIT 1;".format(source, destination)

    cursor.execute(sql)
    row = cursor.fetchone()
    rewrite_source = None
    if row[0] == '0.0.0.0':
        rewrite_source = source
    else:
        rewrite_source = row[0]
    
    rewrite_dest = None
    if row[1] == '0.0.0.0':
        rewrite_dest = source
    else:
        rewrite_dest = row[1]

    return rewrite_source, rewrite_dest

def apply_forward_sqls(sqls):
    begin_update = time.time()
    for sql in sqls:
        cursor.execute(sql)
    end_update = time.time()
    return end_update-begin_update

def plain_forward_sqls(path, firewall_nodes, rewrite_nodes, arch_table):
    """
    generate forward sqls and apply them seperately: tuples in [begin, firewall), (firewall, rewrite), (rewrite, end]
    """
    sqls = []

    total_time = 0
    replace_s = None
    replace_d = None
    for idx, node in enumerate(path):
        if idx == 0:
            sql = "select * from {arch_table} where n like 's%' and x = '{node}'".format(arch_table=arch_table, node=node)
            cursor.execute(sql)
            row = cursor.fetchone()

            replace_s = row[0]
            replace_d = row[1]
        elif node in firewall_nodes:
            rewrite_time_brefore_firewall = apply_forward_sqls(sqls)
            total_time += rewrite_time_brefore_firewall
            sqls.clear()

            sql = "select * from {arch_table} where n = '{firewall_node}' and x = '{node_after_firewall_node}'".format(arch_table=arch_table, firewall_node=node, node_after_firewall_node=path[idx+1])
            cursor.execute(sql)
            row = cursor.fetchone()

            replace_s = row[0]
            replace_d = row[1]
        elif node in rewrite_nodes:
            rewrite_time_after_firewall = apply_forward_sqls(sqls)
            total_time += rewrite_time_after_firewall
            sqls.clear()

            if idx < len(path) - 1:
                sql = "select * from {arch_table} where n = '{node_before_rewrite_node}' and x = '{rewrite_node}'".format(arch_table=arch_table, rewrite_node=node, node_before_rewrite_node=path[idx-1])
                cursor.execute(sql)
                row = cursor.fetchone()
                
                if replace_s.startswith('s') or replace_d.startswith('d'): # it is under no firewall case
                    replace_s = "{}".format(replace_s)
                    replace_d = "{}".format(replace_d)
                else:
                    replace_s, replace_d  = rewrite_function(row[0], row[1])

        tuple = None
        if idx == len(path)-1:
            sql = "select * from {arch_table} where n = '{node}'".format(arch_table=arch_table, node=node)
            cursor.execute(sql)
            tuple = cursor.fetchone()
        else:
            sql = "select * from {arch_table} where n = '{node}' and x = '{node_after_node}'".format(arch_table=arch_table, node=node, node_after_node=path[idx+1])
            cursor.execute(sql)
            tuple = cursor.fetchone()
        sql = "update {arch_table} set {attribute1} = '{value1}', {attribute2} = '{value2}' where {attribute1} = '{attr_value1}' and {attribute2} = '{attr_value2}'".format(
                                            arch_table=arch_table, 
                                            attribute1="s", 
                                            value1=replace_s,
                                            attribute2="d",
                                            value2=replace_d,
                                            attr_value1=tuple[0],
                                            attr_value2=tuple[1])
        sqls.append(sql)

        sql = "update {arch_table} set x = '{value2}' where x = '{attr_value2}'".format(arch_table=arch_table, value2=replace_d, attr_value2=tuple[1])
        sqls.append(sql)

    rewrite_time_to_end = apply_forward_sqls(sqls)
    total_time += rewrite_time_to_end
    sqls.clear()       
    return total_time

if __name__ == '__main__':
    as_file = "7018"
    root = "../"
    filename = join(root, 'arch_query/ISP_topo/')
    nodes = join(filename,as_file+"_nodes.txt")
    edges = join(filename,as_file+"_edges.txt")
    f = open(nodes,"r")
    lines = f.readlines()
    num_vertices = len(lines)
    nodes = []
    for node in lines:
        nodes.append(node.strip())
    mapping = shortest_paths.createNodeMappings(nodes)
    f.close()
    f = open(edges,"r")
    edgeslines = f.readlines()
    f.close()

    dat_times_sums = []
    closure_group_length = []
    closure_group_num = []
    all_dat_times = []

    g = shortest_paths.makeGraph(edgeslines, num_vertices, mapping)
    paths, source, dest = shortest_paths.getPaths(g, num_vertices)

    # paths = [
    #     ['2965', '3838', '8953', '3829', '7131', '3354', '7693', '5289'], 
    #     ['2965', '3838', '8951', '3829', '7131', '3354', '7693', '5289'], 
    #     ['2965', '3838', '8950', '3829', '7131', '3354', '7693', '5289'], 
    #     ['2965', '3838', '8953', '3829', '7131', '3356', '7693', '5289'], 
    #     ['2965', '3838', '8951', '3829', '7131', '3356', '7693', '5289'], 
    #     ['2965', '3838', '8950', '3829', '7131', '3356', '7693', '5289'], 
    #     ['2965', '3838', '8953', '3829', '7131', '4546', '7693', '5289'], 
    #     ['2965', '3838', '8951', '3829', '7131', '4546', '7693', '5289'], 
    #     ['2965', '3838', '8950', '3829', '7131', '4546', '7693', '5289']]
    # source = '2965'
    # dest = '5289'
    summary, all_nodes, links = gen_arch_query(paths, source, dest, "arch_test")

    selected = random.sample(range(len(all_nodes)), 2)

    firewall_nodes = []
    rewrite_nodes = []

    if selected[0] > selected[1]:
        firewall_nodes.append(all_nodes[selected[1]])
        rewrite_nodes.append(all_nodes[selected[0]])
    else:
        firewall_nodes.append(all_nodes[selected[0]])
        rewrite_nodes.append(all_nodes[selected[1]])

    print("firewall_nodes", firewall_nodes)
    print("rewrite_nodes", rewrite_nodes)

    # firewall_nodes = ['3838']
    # rewrite_nodes = ['7693']
    # begin_nodes = ['s1']

    generate_firewall_rules(firewall_nodes, "firewall_rules", "arch_test")
    generate_rewrite_rules(rewrite_nodes, "rewrite_rules", "arch_test")

    runs = 20
    for path in paths:
        total_firewall = 0
        total_rewrite = 0
        total_forward = 0
        is_apply_firewall = None
        is_apply_rewrite = None
        for run in range(runs):
            firewall_time, is_apply_firewall = apply_firewall(path, firewall_nodes, "firewall_rules", "arch_test")
            rewrite_time, is_apply_rewrite = apply_rewrite(path, firewall_nodes, rewrite_nodes, "rewrite_rules", "arch_test")
            forward_time = plain_forward_sqls(path, firewall_nodes, rewrite_nodes, "arch_test")

            total_firewall += firewall_time
            total_rewrite += rewrite_time
            total_forward += forward_time
            gen_arch_query(paths, source, dest, "arch_test")

        print("|{:.5f}|{:.5f}|{:.5f}|{}|".format(total_firewall/runs if is_apply_firewall else 0, total_rewrite/runs if is_apply_rewrite else 0, total_forward/runs, path))
        
        # sql = "select * from arch_test"
        # cursor.execute(sql)
        # for row in cursor.fetchall():
        #     print(row)
        # print("------------------\n")
        # break
        

        
    