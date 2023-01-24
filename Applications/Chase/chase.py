from copy import copy
import sys
from os.path import dirname, abspath

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import time
from psycopg2.extras import execute_values
import databaseconfig as cfg
from tqdm import tqdm
from ipaddress import IPv4Address
from utils.logging import timeit
from copy import deepcopy

FAURE_DATATYPES = ['int4_faure', 'inet_faure']
INT4_FAURE = 'int4_faure'
INET_FAURE = 'inet_faure'

DIGIT_RELATED_TYPES = ['integer', 'double', 'float']
STR_RELATED_TYPES = ['char', 'text']

# conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
# cursor = conn.cursor()

@timeit
def load_table(conn, attributes, datatypes, tablename, data_instance):
    """
    Load data instance into database

    Parameters:
    ------------
    columns: list, 
        a list of attributes, e.g. [name, age]

    datatypes: list, 
        a list of datatypes corresponding to columns, e.g. [text, integer] corresponding to columns [name, age]

    tablename: string, 
        database table which stores tableau

    data_instance: list, 
        data instance
    """
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    cursor = conn.cursor()
    cursor.execute("drop table if exists {}".format(tablename))
    columns = ["{} {}".format(attributes[i], datatypes[i]) for i in range(len(attributes))]
    cursor.execute("create table {} ({})".format(tablename, ", ".join(columns)))
    # conn.commit()

    execute_values(cursor, "insert into {} values %s".format(tablename), data_instance)
    conn.commit()

@timeit
def gen_inverse_image(conn, E_tuples, gamma_tablename):
    """
    generate inverse image of gamma table over end-to-end connectivity view

    Parameters:
    -----------
    E_tuples: list[tuple]
        a list of tuples in table E(end-to-end connectivity view, i.e., tableau query of topology). 
        the tuple contains condition column
    
    gamma_tablename: string 
        name of gamma table

    Returns:
    --------
    Z_tuples: list[tuple]
        a list of tuples for Z table(inverse image of gamma). Convert gamma table to Z table.
    """
    cursor = conn.cursor()

    sql = "select * from {}".format(gamma_tablename)
    cursor.execute(sql)

    gamma_table = cursor.fetchall()
    conn.commit()
    
    Z_tuples = []
    z_tuple_num = 1

    for gamma_tuple in gamma_table:
        f = gamma_tuple[0]
        src = gamma_tuple[1]
        dst = gamma_tuple[2]

        for e_tuple in E_tuples:
            z_tuple = list(e_tuple)[:-1]
            z_tuple[0] = f

            s = 's{}'.format(z_tuple_num)
            d = 'd{}'.format(z_tuple_num)

            z_tuple[1] = s
            z_tuple[2] = d
                
            if e_tuple[3] == 's':
                z_tuple[1] = src
                z_tuple[3] = src
            if e_tuple[4] == 'd':
                z_tuple[2] = dst
                z_tuple[4] = dst

            Z_tuples.append(z_tuple)

            z_tuple_num += 1
    
    return Z_tuples

def gen_inverse_image_with_destbasedforwarding_applied(conn, E_tuples, gamma_tablename):
    """
    generate inverse image of gamma table over end-to-end connectivity view

    Parameters:
    -----------
    E_tuples: list[tuple]
        a list of tuples in table E(end-to-end connectivity view, i.e., tableau query of topology). 
        the tuple contains condition column
    
    gamma_tablename: string 
        name of gamma table

    Returns:
    --------
    Z_tuples: list[tuple]
        a list of tuples for Z table(inverse image of gamma). Convert gamma table to Z table.
    """
    cursor = conn.cursor()

    sql = "select * from {}".format(gamma_tablename)
    cursor.execute(sql)

    gamma_table = cursor.fetchall()
    conn.commit()
    
    Z_tuples = []
    z_tuple_num = 1

    for gamma_tuple in gamma_table:
        f = gamma_tuple[0]
        src = gamma_tuple[1]
        dst = gamma_tuple[2]

        for e_tuple in E_tuples:
            z_tuple = list(e_tuple)[:-1]
            z_tuple[0] = f

            # s = 's{}'.format(z_tuple_num)
            # d = 'd{}'.format(z_tuple_num)

            z_tuple[1] = src
            z_tuple[2] = dst
                
            if e_tuple[3] == 's':
                z_tuple[3] = src
            if e_tuple[4] == 'd':
                z_tuple[4] = dst

            Z_tuples.append(z_tuple)

            z_tuple_num += 1
    
    return Z_tuples

def isIPAddress(value):
    if len(value.strip().split('.')) == 4:
        return True
    else:
        return False

def is_variable(value):
    if value[0].isdigit():
        return False
    else:
        return True

def print_dependency(dependency):
    print("*************************")
    for t in dependency['dependency_tuples']:
        print(t)
    print("---------------------------")
    print(dependency['dependency_summary'])
    print(dependency['dependency_summary_condition'])
    print("*************************")

@timeit
def apply_policy(conn, policy, inverse_image_tablename):
    # print("\n=====================policy begin============================")

    does_update = False
    for dependency in policy:
        # print_dependency(dependency)
        temp_update = apply_dependency(conn, dependency, inverse_image_tablename)

        if temp_update:
            does_update = True
    # print("=====================policy end============================\n")
    return does_update


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

@timeit
def apply_policy_as_atomic_unit(conn, policy, inverse_image_tablename):
    # print("\n=====================policy begin============================")

    count_application = 0
    iterations = 0
    does_update = True
    while does_update:
        iterations += 1
        does_update = False
        for dependency in policy:
            # print_dependency(dependency)
            temp_update = apply_dependency(conn, dependency, inverse_image_tablename)
            # print_table(conn, inverse_image_tablename)
            count_application += 1
            does_update = (does_update or temp_update)
            # input()
    atomic_unit_update = False
    if iterations > 1:
        atomic_unit_update = True
    # print("=====================policy end============================\n")
    return atomic_unit_update, count_application

@timeit
def apply_dependency(conn, dependency, inverse_image_tablename):
    """
    Main function of chase to apply dependencies. Calls apply_tgd and apply_egd.
    
    Parameters:
    -----------
    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    inverse_image_tablename: string
        the table of inverse image

    Returns:
    ---------
    does_updated: Boolean
        does the application of the dependency change the inverse image

    """
    type = dependency['dependency_type']
    dependency_summary = dependency['dependency_summary']

    does_updated = True
    
    if type.lower() == 'tgd':
        does_updated= apply_tgd(conn, dependency, inverse_image_tablename)
    elif type.lower() == 'egd':
        # if dependency_summary is empty, it is a deletion for firewall policy
        if len(dependency_summary) == 0: # if dependency summary is empty, the matched tuples are deleted
            does_updated = apply_edg_for_firewall(conn, dependency, inverse_image_tablename)
        else:
            does_updated = apply_egd(conn, dependency, inverse_image_tablename)
    else:
        does_updated = False
        print("wrong type!")
        exit()

    return does_updated

@timeit
def apply_edg_for_firewall(conn, dependency, inverse_image_tablename):
    """
    If the dependency_summary of dependency is empty, it is a firewall, i.e., deletion
    
    Parameters:
    -----------
    conn: psycopg2.connect()
        the instance of postgres connection

    dependency:dict
        format: {
                'dependency_tuples': list,
                'dependency_attributes': list
                'dependency_attributes_datatypes': list,
                'dependency_cares_attributes': list,
                'dependency_summary': list,
                'dependency_summary_condition': list[string]
                'dependency_type': 'tgd'/'egd'
            }
    
    inverse_image_tablename: string
        the table of inverse image

    Returns:
    ---------
    does_updated: Boolean
        does the application of the dependency change the inverse image
    """
    egd_deletion_sql = convert_dependency_to_sql(dependency, inverse_image_tablename)

    cursor = conn.cursor()
    cursor.execute(egd_deletion_sql)

    does_updated = False
    if cursor.rowcount != 0:
        does_updated = True
    conn.commit()

    return does_updated

@timeit
def apply_sigma_new_atomically_toy(conn, sqls, inverse_image_tablename):
    '''
    forward propogation forwarding
    f(f, src, dst, n, x)
    l(n, x)

    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), 
                                                    l(x_x, x_next)
    '''
    
    # forward_propogation_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.x = t1.n".format(inverse_image_tablename)

    '''
    back propogation forwarding
    f(f, src, dst, n, x)
    l(n, x)

    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), 
                                                l(x_pre, x_n)
    '''

    # sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t1.flag = '1'".format(inverse_image_tablename, subpath_tablename)
    # sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t0.dst = t1.x and t1.flag = '0'".format(inverse_image_tablename, subpath_tablename)

    # sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t1.flag = '1'".format(inverse_image_tablename, subpath_tablename)
    # sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t0.src = t1.n and t1.flag = '0'".format(inverse_image_tablename, subpath_tablename)

    # sqls = [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]
    # back_propogation_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.n = t1.x".format(inverse_image_tablename)
    does_updated = False # if \sigma_new affects inverse image
    cursor = conn.cursor()
    while True:
        temp_updated = False # if \sigma_new converges
        for sql in sqls:
            print("sigma_sql", sql)
            difference_sql = "{} except select * from {}".format(sql, inverse_image_tablename)
            cursor.execute(difference_sql)
            if cursor.rowcount != 0:
                # print("insert rows:", cursor.rowcount)
                does_updated = True
                temp_updated = True
                inserting_tuples = cursor.fetchall()
                print('inserting_tuples', inserting_tuples)
                execute_values(cursor, "insert into {} values %s".format(inverse_image_tablename), inserting_tuples)
        
        if not temp_updated:
            break

    conn.commit()
    return does_updated

def apply_sigma_new_atomically(conn, inverse_image_tablename, subpath_tablename):
    print("run sigma_new")
    '''
    forward propogation forwarding
    f(f, src, dst, n, x)
    l(n, x)

    f(x_f, x_s, x_d, x_x, x_next) :- f(x_f, x_s, x_d, x_n, x_x), 
                                                    l(x_x, x_next)
    '''
    
    # forward_propogation_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.x = t1.n".format(inverse_image_tablename)

    '''
    back propogation forwarding
    f(f, src, dst, n, x)
    l(n, x)

    f(x_f, x_s, x_d, x_pre, x_n) :- f(x_f, x_s, x_d, x_n, x_x), 
                                                l(x_pre, x_n)
    '''

    sigma_fp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t1.flag = '1'".format(inverse_image_tablename, subpath_tablename)
    sigma_fp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.x = t1.n and t0.dst = t1.x and t1.flag = '0'".format(inverse_image_tablename, subpath_tablename)

    sigma_bp1_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t1.flag = '1'".format(inverse_image_tablename, subpath_tablename)
    sigma_bp2_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, {} t1 where t0.n = t1.x and t0.src = t1.n and t1.flag = '0'".format(inverse_image_tablename, subpath_tablename)

    sqls = [sigma_fp1_sql, sigma_fp2_sql, sigma_bp1_sql, sigma_bp2_sql]
    # back_propogation_sql = "select t0.f as f, t0.src as src, t0.dst as dst, t1.n as n, t1.x as x from {} t0, l t1 where t0.n = t1.x".format(inverse_image_tablename)
    does_updated = False # if \sigma_new affects inverse image
    cursor = conn.cursor()
    while True:
        temp_updated = False # if \sigma_new converges
        for sql in sqls:
            difference_sql = "{} except select * from {}".format(sql, inverse_image_tablename)
            cursor.execute(difference_sql)
            if cursor.rowcount != 0:
                # print("insert rows:", cursor.rowcount)
                does_updated = True
                temp_updated = True
                inserting_tuples = cursor.fetchall()
                execute_values(cursor, "insert into {} values %s".format(inverse_image_tablename), inserting_tuples)
        
        if not temp_updated:
            break

    conn.commit()
    return does_updated

@timeit
def apply_tgd(conn, dependency, inverse_image_tablename):
    """
    Apply tgd dependency, calls by apply_dependency()

    current version:
    1. for he given pattern, using EXCEPT in SQL to remove the return tuples which are already in the inverse image
    2. if there are new tuples returned, add the new tuples.
    
    The old version loads data instance of inverse image into python set, which is expensive.

    old version:
    1. Checks for the given pattern and returns the summary (i.e. the tuple to add) IF the given pattern exists. 
    2. Then computes the difference between the summary and the Z_table. 
    3. Adds the extra tuple only if it does not already exist in the Z_table (preventing unnecessary additions)
    
    Parameters:
    -----------
    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    inverse_image_tablename: string
        the table of inverse image

    Returns:
    ---------
    does_updated: Boolean
        does the application of the dependency change the inverse image
    """
    cursor = conn.cursor()

    tgd_sql = convert_dependency_to_sql(dependency, inverse_image_tablename)
    # print("\n***tgd_sql", tgd_sql)
    # cursor.execute(tgd_sql)
    # results = cursor.fetchall()

    # start = time.time()
    difference_sql = "{} except select * from {}".format(tgd_sql, inverse_image_tablename)
    # print("\n***tgd_sql", tgd_sql)
    # print("\n***insert_sql", insert_sql)
    cursor.execute(difference_sql)

    does_updated = False
    if cursor.rowcount != 0:
        # print("insert rows:", cursor.rowcount)
        does_updated = True
        tuples = cursor.fetchall()
        execute_values(cursor, "insert into {} values %s".format(inverse_image_tablename), tuples)
    conn.commit()
    # print('insert time:', time.time()-start)

    # z_tuples = getCurrentTable(conn, inverse_image_tablename)

    # results_set = set(results)
    # z_tuples_set = set(z_tuples)
    # inserted_tuples_set = results_set.difference(z_tuples_set)

    # inserted_tuples = list(inserted_tuples_set)
    # does_updated = False

    # if len(inserted_tuples) != 0:
    #     print("insert rows:", len(inserted_tuples))
    #     does_updated = True
    #     execute_values(cursor, "insert into {} values %s".format(inverse_image_tablename), inserted_tuples)
    
    # conn.commit()
    return does_updated

@timeit
def getCurrentTable(conn, tablename):
    """
    Returns the table tuples from postgres of the table given as a parameter
    """
    cursor = conn.cursor()
    cursor.execute('select * from {};'.format(tablename))
    table = cursor.fetchall()
    conn.commit()
    return table

@timeit
def replace_z_table(conn, tablename, new_table):
    """
    Replaces a given table with a new one (new_table given as tuples)
    """
    # cursor = conn.cursor()
    # cursor.execute("drop table if exists {}".format(tablename))
    # conn.commit()
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    load_table(conn, Z_attributes, Z_attributes_datatypes, tablename, new_table)

@timeit
def applySourceDestPolicy_new(conn, Z_tablename):
    """
    Apply dest-based forwarding policy in Postgres
    Heavy updates that updating every row

    The source must be first hop and the destination must be last hop. 
    This is applied at the start to get rid of variables

    Parameters:
    -----------
    Z_tablename: string
        the tablename of inverse image
    """
    
    upd_sql, upd_tuples = gen_update_SQLs_for_dest_based_forwarding(conn, Z_tablename)
    # print("upd_sql", upd_sql)
    # print("upd_tuples", upd_tuples)
    does_updated = False
    # exit()
    if len(upd_tuples) != 0:
        does_updated = True

        # method 2
        # cursor = conn.cursor()
        # execute_values(cursor, upd_sql, upd_tuples)
        # conn.commit()

        # method 4
        # step 1: store replacement information to a table
        cursor = conn.cursor()
        cursor.execute("drop table if exists update_src_dst")
        cursor.execute("create table update_src_dst (flowid text, src text, dst text);")
        execute_values(cursor, "insert into update_src_dst values %s", upd_tuples)
        conn.commit()

        # step 2: using left join to get the replaced data and storing them into a new table
        cursor.execute("drop table if exists temp_{}".format(Z_tablename))
        cursor.execute("create table temp_{z_table} AS SELECT t.f, u.src, u.dst, t.n, t.x FROM {z_table} t LEFT JOIN update_src_dst u on t.f = u.flowid".format(z_table=Z_tablename))
        conn.commit()

        # step 3: drop the old table
        cursor.execute("drop table if exists {}".format(Z_tablename))
        # cursor.execute("truncate {}".format(Z_tablename))
        # conn.commit()

        # step 4: rename the new table
        # cursor.execute("insert into {z_table} table temp_{z_table}".format(z_table=Z_tablename))
        cursor.execute("alter table temp_{z_table} rename to {z_table}".format(z_table=Z_tablename))
        conn.commit()

    return does_updated

@timeit
def gen_update_SQLs_for_dest_based_forwarding(conn, Z_tablename):

    forwarding_sql = "select f, array_agg(src) as src, array_agg(dst) as dst from {Z_tablename} group by f".format(Z_tablename=Z_tablename)
    # print("\ndependency_sql", dependency_sql)

    cursor = conn.cursor()
    cursor.execute(forwarding_sql)

    results = cursor.fetchall()
    conn.commit()

    upd_tuples = []
    for (flowid, src, dst) in results:
        # input()
        src_set = set(src)
        dst_set = set(dst)

        src_replace = None
        dst_replace = None
        if len(src_set) == 1:
            src_replace = src_set[0]
        else:
            for param in src_set:
                if param[0].isdigit():
                    src_replace = param
                    break
            if src_replace is None:
                print("src_set", src_set)
                exit()
        
        if len(dst_set) == 1:
            dst_replace = dst_set[0]
        else:
            for param in dst_set:
                if param[0].isdigit():
                    dst_replace = param
                    break
            if dst_replace is None:
                print("dst_set", dst_set)
                exit()
        
        upd_tuples.append((flowid, src_replace, dst_replace))
        # print("upd_tuples", upd_tuples)
    upd_sql = "update {} set src = updated_src, dst = updated_dst from ( values %s) as updatedvalues (flowid, updated_src, updated_dst) where f = flowid".format(Z_tablename)
    return upd_sql, upd_tuples

@timeit
def applySourceDestPolicy(conn, Z_tablename):
    """
    Apply dest-based forwarding policy in main memory with python

    The source must be first hop and the destination must be last hop. 
    This is applied at the start to get rid of variables

    Parameters:
    -----------
    Z_tablename: string
        the tablename of inverse image
    """
    z_table = getCurrentTable(conn, Z_tablename)
    unique_flows = {}
    for i, tuple in enumerate(z_table):
        flowid = tuple[0]
        if flowid not in unique_flows:
            unique_flows[flowid] = [] #0th element is the source, last element is the destination
            src = tuple[1]
            unique_flows[flowid].append(src)

        elif i >= len(z_table)-1 or (z_table[i+1][0] != flowid and flowid in unique_flows): # get destination from last hop
            dest = tuple[2]
            unique_flows[flowid].append(dest)
    new_z_table = []
    for tuple in z_table:
        flowid = tuple[0]
        if flowid not in unique_flows:
            print("Unknown flow id encountered. Something went wrong. Exiting")
            exit()
        if (len(unique_flows[flowid]) < 2):
            exit()
        newTuple = (flowid, unique_flows[flowid][0], unique_flows[flowid][1], tuple[3], tuple[4])
        new_z_table.append(newTuple)

    # Replace Z table code
    replace_z_table(conn, Z_tablename, new_z_table)

    return True

@timeit
def applyRewritePolicy(conn, dependency, Z_tablename):
    """
    # For rewrite policy (equalizing flow ids).
    # Searches for the flow ID of the first tuple pattern. Then searches for all flow IDs of the second tuple pattern. Replaces the later flow IDs with the former. This is a tableau wide substitutions (all replace flow IDs are replaced)
    # TODO: Unlike tgds, this is not general. It is specific to flow id equalization
    """
    z_table = getCurrentTable(conn, Z_tablename)
    pattern_source = dependency['dependency_tuples'][0][1]
    pattern_dest = dependency['dependency_tuples'][0][2]
    pattern_n = IPv4Address(dependency['dependency_tuples'][0][3])
    pattern_x = IPv4Address(dependency['dependency_tuples'][0][4])
    # pattern_condition = dependency['dependency_summary_condition'][0] # assuming it is always less than equal to policy
    # pattern_condition_IP = IPv4Address(pattern_condition[7:-1])    

    if (len(dependency['dependency_tuples']) < 2):
        return False

    replace_source = dependency['dependency_tuples'][1][1]
    replace_dest = dependency['dependency_tuples'][1][2]
    replace_n = IPv4Address(dependency['dependency_tuples'][1][3])
    replace_x = IPv4Address(dependency['dependency_tuples'][1][4])
    # replace_condition = dependency['dependency_summary_condition'][1] # assuming it is always less than equal to policy
    # replace_condition_IP = IPv4Address(replace_condition[7:-1])

    # extract flow id of pattern tuple
    targetFlow = ""
    for tuple in z_table:
        flowid = tuple[0]
        src = tuple[1]
        dest = tuple[2]
        n = IPv4Address(tuple[3])
        x = IPv4Address(tuple[4])
        if (src == pattern_source and dest == pattern_dest and n == pattern_n and x == pattern_x):
            targetFlow = flowid
            break
    if targetFlow == "":
        # print("No flow found. Hacky solution might not be working")
        return False

    flowids_required_replaced = []
    for tuple in z_table:
        flowid = tuple[0]
        # if flow id is already in list, skip check the remaining attributes
        if flowid in flowids_required_replaced:
            continue

        src = tuple[1]
        dest = tuple[2]
        n = IPv4Address(tuple[3])
        x = IPv4Address(tuple[4])

        if (src == replace_source and dest == replace_dest and n == replace_n and x == replace_x):
            if flowid != targetFlow:
                flowids_required_replaced.append(flowid)
                
    new_z_table = []
    does_update = False
    for tuple in z_table:
        flowid = tuple[0]
        src = tuple[1]
        dest = tuple[2]
        n = IPv4Address(tuple[3])
        if flowid in flowids_required_replaced:
            new_z_table.append((targetFlow, tuple[1], tuple[2], tuple[3], tuple[4]))
            does_update = True
        else:
            new_z_table.append((tuple[0], tuple[1], tuple[2], tuple[3], tuple[4]))

    replace_z_table(conn, Z_tablename, new_z_table)

    return does_update

def analyze_egd(dependency):
    dependency_summary = dependency['dependency_summary']
    dependency_tuples = dependency['dependency_tuples']

    replaced_symbol_idxs = []  
    replacing_symbol_idxs = []
    replacing_constant = False
    for summary in dependency_summary:
        items = summary.split()
        left_opd = items[0].strip()
        opr = items[1].strip()
        right_opd = items[2].strip()

        for tup_idx, tup in enumerate(dependency_tuples):
            for col_idx, item in enumerate(tup):
                if left_opd == item:
                    replaced_symbol_idxs.append(tup_idx*len(tup) + col_idx)
                    break

        if right_opd[0].isdigit() or isIPAddress(right_opd):
            replacing_symbol_idxs.append(right_opd)
            replacing_constant = True
        else:
            for tup_idx, tup in enumerate(dependency_tuples):
                for col_idx, item in enumerate(tup):
                    if right_opd == item:
                        replacing_symbol_idxs.append(tup_idx*len(tup) + col_idx)
                        break
    return replaced_symbol_idxs, replacing_symbol_idxs, replacing_constant

def get_update_sqls_for_egd(conn, dependency, Z_tablename):
    dependency_sql = convert_dependency_to_sql(dependency, Z_tablename)
    # print("dependency_sql", dependency_sql)
    replaced_symbol_idxs, replacing_symbol_idxs, replacing_constant = analyze_egd(dependency)
    dependency_attributes = dependency['dependency_attributes']
    cursor = conn.cursor()
    cursor.execute(dependency_sql)

    results = cursor.fetchall()
    conn.commit()

    len_tuple = len(dependency['dependency_tuples'][0])    

    update_sqls = []
    for record in results:
        # print("\nrecord", record)
        replaced_values = ['' for i in range(len(replaced_symbol_idxs))]
        replacing_values = ['' for i in range(len(replaced_symbol_idxs))]
        constrains = None

        if replacing_constant:
            replacing_values = replacing_symbol_idxs

        for p_idx, item_idx in enumerate(replaced_symbol_idxs):
            replacing_v_idx = replacing_symbol_idxs[p_idx]

            if record[item_idx].isdigit() or isIPAddress(record[item_idx]):
                begin_idx = (item_idx // len_tuple) * len_tuple 
                end_idx = begin_idx + len_tuple
                constrains = record[begin_idx:end_idx]

            replaced_values[p_idx] = record[item_idx]
            if not replacing_constant:
                replacing_values[p_idx] = record[replacing_v_idx]

        # print("replaced_values", replaced_values)
        # print("replacing_values", replacing_values)
        # print("constrains", constrains)
        sqls = []           
        if constrains is None: # replace all variables with constants
            for i in range(len(replacing_values)):
                replacing_v = replacing_values[i]
                replaced_v = replaced_values[i]
                # col_idx = get_col_idx_from_item_idx_in_record(replacing_symbol_idxs[i], len_tuple)
                for attr in dependency_attributes:
                    if attr  == 'f':
                        continue

                    sql = "update {} set {} = '{}' where {} = '{}'".format(Z_tablename, attr, replacing_v, attr, replaced_v)
                    sqls.append(sql)
        else:  # some replaced values are constants, some are not
            set_clause = []
            variable_idx_lists = []
            for i in range(len(replaced_values)):
                replacing_v = replacing_values[i]
                replaced_v = replaced_values[i]

                col_idx = replaced_symbol_idxs[i] % len_tuple # get_col_idx_from_item_idx_in_record
                set_clause.append("{} = '{}'".format(dependency_attributes[col_idx], replacing_v))

                if not replaced_v.isdigit() and not isIPAddress(replaced_v):
                    variable_idx_lists.append(i)
            
            sql = "update {} set {} where ({}) = ({})".format(Z_tablename, ", ".join(set_clause), ", ".join(dependency_attributes), ", ".join(["'{}'".format(c) for c in constrains]))
            sqls.append(sql)

            for var_idx in variable_idx_lists:
                replacing_v = replacing_values[var_idx]
                replaced_v = replaced_values[var_idx]
                for attr in dependency_attributes:
                    if attr  == 'f':
                        continue

                    sql = "update {} set {} = {} where {} = '{}'".format(Z_tablename, attr, replacing_v, attr, replaced_v)
                    sqls.append(sql) 
        # print("sqls", "\n".join(sqls))
        update_sqls += sqls
    return update_sqls

def get_col_idx_from_item_idx_in_record(item_idx, len_tuple):
    return item_idx % len_tuple     

def get_update_sqls_for_egd_old(conn, dependency, Z_tablename):
    """
    Generate update SQLs by given a egd dependency
    #TODO: the update SQLs might be efficient enough, later it needs to be optimized

    Parameters:
    -----------
    conn: psycopg2.connect()
        the instance of connection for Postgres

    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    Z_tablename: string
        the table of inverse image

    Returns:
    ---------
    update_sqls: list
        A list of update SQLs for the input egd dependency
    
    """
    dependency_tuples = dependency["dependency_tuples"]
    dependency_attributes=dependency["dependency_attributes"]
    dependency_summary = dependency["dependency_summary"]
    dependency_sql = convert_dependency_to_sql(dependency, Z_tablename)
    print("\ndependency_sql", dependency_sql)
    node_dict, _ = analyze_dependency(dependency_tuples, dependency_attributes, Z_tablename)

    cursor = conn.cursor()
    cursor.execute(dependency_sql)

    columns = [row[0] for row in cursor.description]
    
    results = cursor.fetchall()
    conn.commit()

    is_replacing_constant = False
    replace_value = {}
    care_attr_idxs = []
    for idx, summary in enumerate(dependency_summary):
        items = summary.split()
        left_opd = items[0]
        right_opd = items[2]

        left_param = ''
        right_param = ''

        left_tup_idx = list(node_dict[left_opd].keys())[0]
        left_attr_idx = node_dict[left_opd][left_tup_idx][0]
        care_attr_idxs.append(left_attr_idx)

        if right_opd.isdigit():
            right_param = "'{}'".format(right_opd)  
            is_replacing_constant = True
            replace_value[left_attr_idx] = right_param
            
        else:
            right_tup_idx = list(node_dict[right_opd].keys())[0]
            right_attr_idx = node_dict[right_opd][right_tup_idx][0]
            right_param = "t{}.{}".format(right_tup_idx, dependency_attributes[right_attr_idx])

    if is_replacing_constant:  # if summary looks like s = 9; that is replacing a constant
        update_list = []
        variable_list = {}
        for record in results:
            add_to_upd_list = False
            for attr_idx in care_attr_idxs:
                if record[attr_idx].isdigit():
                    if add_to_upd_list:
                        continue
                    update_list.append(record)
                    add_to_upd_list = True
                else:
                    if attr_idx not in variable_list.keys():
                        variable_list[attr_idx] = []
                    variable_list[attr_idx].append("'{}'".format(record[attr_idx]))
        
        set_clause = []
        for attr_idx in replace_value.keys():
            set_clause.append("{} = {}".format(dependency_attributes[attr_idx], replace_value[attr_idx]))
        
        update_sqls = []
        for constraint in update_list:
            sql = "update {} set {} where ({}) = ({})".format(Z_tablename, ", ".join(set_clause), ", ".join(dependency_attributes), ", ".join(["'{}'".format(c) for c in constraint]))
            update_sqls.append(sql)
        
        for attr_idx in variable_list.keys():
            for attr in dependency_attributes:
                if attr == 'f':
                    continue
                sql = ""
                if len(variable_list[attr_idx]) == 1:
                    sql = "update {} set {} = {} where {} = {}".format(Z_tablename, attr, replace_value[attr_idx], attr, variable_list[attr_idx][0])
                else:
                    sql = "update {} set {} = {} where {} in ({})".format(Z_tablename, attr, replace_value[attr_idx], attr, ', '.join(variable_list[attr_idx]))
                update_sqls.append(sql)
        return update_sqls
                
    else:  # if summary looks like s1 = s2; that is making two elements equal
        commonattr_idx_mapping = {}
        flowid_idx = 0 # assume flowid is a common attribute
        for record_idx, record in enumerate(results):
            print("record", record)
            tuples = [record[0:len(dependency["dependency_attributes"])], record[len(dependency["dependency_attributes"]):]]
            
            commonattr = record[flowid_idx]
            temp_idx_mapping = {} # idx: [(1, 3), (2, 4)]

            for attr_idx in care_attr_idxs:
                set1 = set()
                for tup in tuples:
                    set1.add(tup[attr_idx])
                temp_idx_mapping[attr_idx] = set1

                # if attr_idx not in temp_idx_mapping.keys():
                #     temp_idx_mapping[attr_idx] = []
                
                # for s_idx, s in enumerate(temp_idx_mapping[attr_idx]):
                #     if s.isdisjoint(set1):
                #         temp_idx_mapping[attr_idx].append(deepcopy(set1))
                #     else:
                #         temp_idx_mapping[attr_idx][s_idx].update(set1)
            # print("temp_idx_mapping", temp_idx_mapping)
            
            if commonattr in commonattr_idx_mapping.keys():
                for attr_idx in temp_idx_mapping.keys():
                    l_set = set(temp_idx_mapping[attr_idx])

                    is_disjoint = True
                    for s_idx, s in enumerate(commonattr_idx_mapping[commonattr][attr_idx]):
                        if not l_set.isdisjoint(s):
                            commonattr_idx_mapping[commonattr][attr_idx][s_idx].update(l_set)
                            is_disjoint = False
                            break
                    if is_disjoint:
                        commonattr_idx_mapping[commonattr][attr_idx].append(deepcopy(l_set))
                # idx_mapping = commonattr_idx_mapping[commonattr]
                # if idx in idx_mapping.keys():
                #     l_set = set(temp_idx_mapping[idx])
                #     for s_idx, subset in enumerate(idx_mapping[idx]):
                #         if not l_set.isdisjoint(subset):
                #             idx_mapping[idx][s_idx] = subset.union(l_set)
                #             break
                #     idx_mapping[idx].append(deepcopy(l_set))
            
            else:
                commonattr_idx_mapping[commonattr] = {}
                for idx in temp_idx_mapping.keys():
                    commonattr_idx_mapping[commonattr][idx] = [set(temp_idx_mapping[idx])]
            
            print("commonattr_idx_mapping", commonattr_idx_mapping)
        
        print("commonattr_idx_mapping", commonattr_idx_mapping)

        for commonattr in commonattr_idx_mapping:
            idx_mapping = commonattr_idx_mapping[commonattr]
            for idx in idx_mapping.keys():
                if len(idx_mapping[idx]) <= 1:
                    continue

                removing_s_idxes = []
                for s_idx1, subset1 in enumerate(idx_mapping[idx]):
                    if s_idx1 in removing_s_idxes:
                        continue
                    for s_idx2, subset2 in enumerate(idx_mapping[idx]):
                        if s_idx1 == s_idx2:
                            continue
                        if s_idx2 in removing_s_idxes:
                            continue
                        
                        if not subset1.isdisjoint(subset2):
                            removing_s_idxes.append(s_idx2)
                            subset1.update(subset2)
                for s_idx in removing_s_idxes:
                    idx_mapping[idx].pop(s_idx)
        
        # print("commonattr_idx_mapping", commonattr_idx_mapping)    
        
        update_sqls = []
        for commonattr in commonattr_idx_mapping.keys():
            for attr_idx in commonattr_idx_mapping[commonattr].keys():
                for group in commonattr_idx_mapping[commonattr][attr_idx]:
                    group = list(group)
                    target_value = "'{}'".format(group[0])
                    replaced_vars = []
                    for val in group:
                        if val.isdigit():
                            target_value = "'{}'".format(val)
                        else:
                            replaced_vars.append("'{}'".format(val))

                    for attr in dependency_attributes:
                        if attr == 'f':
                            continue
                        sql = ""
                        if len(replaced_vars) == 1:
                            sql = "update {} set {} = {} where {} = {}".format(Z_tablename, attr, target_value, attr, replaced_vars[0])
                        else:
                            sql = "update {} set {} = {} where {} in ({})".format(Z_tablename, attr, target_value, attr, ", ".join(replaced_vars))
                        update_sqls.append(sql)
        return update_sqls

@timeit
def apply_egd(conn, dependency, inverse_image_tablename):
    """
    Apply egd dependency, calls by apply_dependency()

    Applies egd (specifically the one to set flow ids equal) in memory
    
    Parameters:
    -----------
    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    inverse_image_tablename: string
        the table of inverse image

    Returns:
    ---------
    does_updated: Boolean
        does the application of the dependency change the inverse image
    """
    update_sqls = get_update_sqls_for_egd(conn, dependency, inverse_image_tablename)
    cursor = conn.cursor()
    for sql in update_sqls:
        # print(sql)
        cursor.execute(sql)
    conn.commit()

    if len(update_sqls) != 0:
        return True
    return False

@timeit
def analyze_dependency(dependency_tuples, dependency_attributes, Z):
    """
    Returns the position of each variable/constant in the dependency. Useful to check for equivalent variables/constants when converting to sql
    e.g. for \sigma_new x_f appears in the 0th and 1st tuple both in the 0th column: {'x_f': {0: [0], 1: [0]}, 'x_s1': {0: [1]}, 'x_d': {0: [2], 1: [2]}, 'x_n': {0: [3]}, 'x_x': {0: [4], 1: [3]}, 'x_s2': {1: [1]}, 'x_next': {1: [4]}}

    Parameters:
    -----------
    dependency_tuples: list
        the list of tuples of dependency
    
    dependency_attributes: list
        relation of dependency in database
    
    Z: string
        the tablename of sql-applied table
    """
    node_dict = {}
    tables = []
    for idx, tup in enumerate(dependency_tuples):
        tables.append("{} t{}".format(Z, idx))
        for i in range(len(tup)):
            var = tup[i]
            # print("var", var)
            # print("i", i)
            if dependency_attributes[i] == 'condition':
                continue
            if var not in node_dict.keys():
                node_dict[var] = {}
                node_dict[var][idx] = []
                node_dict[var][idx].append(i)
            else:
                if idx not in node_dict[var].keys():
                    node_dict[var][idx] = []
                    node_dict[var][idx].append(i)
                else:
                    node_dict[var][idx].append(i)
    return node_dict, tables

@timeit
def convert_dependency_to_sql(dependency, Z):
    """
    Convert dependency to SQL 

    Parameters:
    -----------
    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    Z: string
        the table of inverse image

    Returns:
    ---------
    sql: string
        corresponding SQL
    """
    dependency_type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_conditions = dependency['dependency_summary_condition']
    
    node_dict, tables = analyze_dependency(dependency_tuples, dependency_attributes, Z)

    conditions = []
    for var in node_dict.keys():
        # print("\nnode_dict", node_dict)
        # print("var", var)
        if type(var) is not int and not var.strip('>').isdigit() and not isIPAddress(var.strip('>')):
            tup_idxs = list(node_dict[var].keys())
            # print("tup_idxs:", tup_idxs)
            for idx in range(len(tup_idxs)-1):
                t_idx = tup_idxs[idx]
                name_idxs = node_dict[var][t_idx]

                # print("col_idx:", name_idxs)
                if len(name_idxs) > 1:
                    for j in range(len(name_idxs)-1):
                        left_opd = "t{}.{}".format(t_idx, dependency_attributes[name_idxs[j]])
                        right_opd = "t{}.{}".format(t_idx, dependency_attributes[name_idxs[j+1]])
                        conditions.append("{} = {}".format(left_opd, right_opd))

                n_idx = name_idxs[-1]
                left_opd = "t{}.{}".format(t_idx, dependency_attributes[n_idx])

                # print(node_dict[var])
                t_idx2 = tup_idxs[idx+1]
                name_idxs2 = node_dict[var][t_idx2]
                # print("col_idxs2:", name_idxs2)

                n_idx2 = name_idxs2[-1]
                right_opd = "t{}.{}".format(t_idx2, dependency_attributes[n_idx2])

                conditions.append("{} = {}".format(left_opd, right_opd))
                # print("conditions:", conditions)
            
            tup_idx = tup_idxs[-1]
            col_idxs = node_dict[var][tup_idx]
            # print("col_idxs", col_idxs)
            if len(col_idxs) > 1:
                for j in range(len(col_idxs)-1):
                    left_opd = "t{}.{}".format(tup_idx, dependency_attributes[col_idxs[j]])
                    right_opd = "t{}.{}".format(tup_idx, dependency_attributes[col_idxs[j+1]])
                    conditions.append("{} = {}".format(left_opd, right_opd))

            # print("***********************************\n")
        else:
            tup_idxs = node_dict[var].keys()
            for t_idx in tup_idxs:
                name_idxs = node_dict[var][t_idx]

                for n_idx in name_idxs:
                    left_opd = "t{}.{}".format(t_idx, dependency_attributes[n_idx])
                    conditions.append("{} = '{}'".format(left_opd, var))
    
    
    # print(conditions) 
    # add summary conditions
    summary_conditions = get_summary_condition(dependency_attributes, dependency_summary_conditions, node_dict)
    if len(summary_conditions) != 0:
        conditions.append( " and ".join(summary_conditions))

    sql = None
    '''
    summary
    '''
    select_clause = []
    if dependency_type == 'tgd':
        for i in range(len(dependency_summary)):
            if type(dependency_summary[i]) is not int and not dependency_summary[i].strip('>').isdigit() and not isIPAddress(dependency_summary[i].strip('>')):
                var = dependency_summary[i]
                # print(node_dict[var])
                first_tup = list(node_dict[var].keys())[0] # first tuple appears var
                # print(node_dict[var][first_tup])
                first_col = node_dict[var][first_tup][0] # first col appears var
                select_clause.append("t{}.{}".format(first_tup, dependency_attributes[first_col]))
            else:
                select_clause.append("'{}'".format(dependency_summary[i]))

        sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
    elif dependency_type == 'egd':
        if len(dependency_summary) == 0:
            sql = "delete from {} where {}".format(", ".join(tables), " and ".join(conditions))
        else:

            # convert_summary_to_condition
            additional_condition = [] 
            # select_clause.append("t0.f as f")
            is_replacing_constant = False
            for idx, summary in enumerate(dependency_summary):
                select_items = []
                items = summary.split()
                left_opd = items[0]
                right_opd = items[2]

                left_param = ''
                right_param = ''
                
                left_tup_idx = list(node_dict[left_opd].keys())[0]
                left_attr_idx = node_dict[left_opd][left_tup_idx][0]
                left_param = "t{}.{}".format(left_tup_idx, dependency_attributes[left_attr_idx])
                select_items.append(left_param)
                
                if right_opd.isdigit():
                    right_param = "'{}'".format(right_opd)  
                    is_replacing_constant = True
                    # select_items.append(right_param)
                else:
                    right_tup_idx = list(node_dict[right_opd].keys())[0]
                    right_attr_idx = node_dict[right_opd][right_tup_idx][0]
                    right_param = "t{}.{}".format(right_tup_idx, dependency_attributes[right_attr_idx])
                    select_items.append(right_param)
                additional_condition.append(("{} = {}").format(left_param, right_param))
                # select_clause.append("Array[{}] as {}".format(", ".join(select_items), replaced_value)) # for summary f1 = f2, store f1, f2 into an array, e.g., [f1, f2]
            
            conditions.append("not({})".format(" and ".join(additional_condition))) 

            # if not is_replacing_constant:
            #     # common attributes for variable elements
            #     # common_clause = []
            #     # for var in node_dict.keys():
            #     #     if is_variable(var):
            #     #         if len(node_dict[var]) == len(dependency_tuples): # if the attribute of all tuples have the same variable, this is a common attribute
            #     #             tup_idxs = list(node_dict[var].keys())
            #     #             attr_idxs1 = set(node_dict[var][tup_idxs[0]])
            #     #             for tup_idx in tup_idxs[1:]:
            #     #                 attr_idxs2 = set(node_dict[var][tup_idx])

            #     #                 attr_idxs1.intersection_update(attr_idxs2)

            #     #             if len(attr_idxs1) != 0:
            #     #                 tup_idx = 0
            #     #                 attr_idx = list(attr_idxs1)[0] 
            #     #                 common_clause.append("t{}.{} as {}".format(tup_idx, dependency_attributes[attr_idx], dependency_attributes[attr_idx]))
            #     # select_clause += common_clause
            #     for tup_idx in range(len(dependency_tuples)):
            #         select_clause += ["t{}.{}".format(tup_idx, attr, attr) for attr in dependency_attributes]
            # else:
            #     select_clause = ["t{}.{} as {}".format(range(len(dependency_tuples))[-1], attr, attr) for attr in dependency_attributes] # default the last tuple
            for tup_idx in range(len(dependency_tuples)):
                select_clause += ["t{}.{}".format(tup_idx, attr, attr) for attr in dependency_attributes]
            

            # print("additional_condition", additional_condition)
            # select_clause.append("*")
            # for idx in range(len(tables)):
            #     for attr in dependency_attributes:
            #         if 'condition' in attr:
            #             continue
            #         select_clause.append("t{}.{}".format(idx, attr))
            # sqls = []
            
                
            #     sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
            #     sqls.append(sql)
            # return sqls
            sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
    else:
        print("Wrong dependency type!")
        exit()
    
    return sql

def convert_dependency_to_sql_old(dependency, Z):
    """
    Convert dependency to SQL 

    Parameters:
    -----------
    dependency: dict
        format: {
            'dependency_tuples': list,
            'dependency_attributes': list
            'dependency_attributes_datatypes': list,
            'dependency_cares_attributes': list,
            'dependency_summary': list,
            'dependency_summary_condition': list[string]
            'dependency_type': 'tgd'/'egd'
        }

    Z: string
        the table of inverse image

    Returns:
    ---------
    sql: string
        corresponding SQL
    """
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_conditions = dependency['dependency_summary_condition']
    
    node_dict, tables = analyze_dependency(dependency_tuples, dependency_attributes, Z)

    # print("node_dict", node_dict)
    conditions = []
    for var in node_dict.keys():
        # print("\nnode_dict", node_dict)
        # print("var", var)
        if not var.isdigit() and not isIPAddress(var):
            tup_idxs = list(node_dict[var].keys())
            # print("tup_idxs:", tup_idxs)
            for idx in range(len(tup_idxs)-1):
                t_idx = tup_idxs[idx]
                name_idxs = node_dict[var][t_idx]

                # print("col_idx:", name_idxs)
                if len(name_idxs) > 1:
                    for j in range(len(name_idxs)-1):
                        left_opd = "t{}.{}".format(t_idx, dependency_attributes[name_idxs[j]])
                        right_opd = "t{}.{}".format(t_idx, dependency_attributes[name_idxs[j+1]])
                        conditions.append("{} = {}".format(left_opd, right_opd))

                n_idx = name_idxs[-1]
                left_opd = "t{}.{}".format(t_idx, dependency_attributes[n_idx])

                # print(node_dict[var])
                t_idx2 = tup_idxs[idx+1]
                name_idxs2 = node_dict[var][t_idx2]
                # print("col_idxs2:", name_idxs2)

                n_idx2 = name_idxs2[-1]
                right_opd = "t{}.{}".format(t_idx2, dependency_attributes[n_idx2])

                conditions.append("{} = {}".format(left_opd, right_opd))
                # print("conditions:", conditions)
            
            tup_idx = tup_idxs[-1]
            col_idxs = node_dict[var][tup_idx]
            # print("col_idxs", col_idxs)
            if len(col_idxs) > 1:
                for j in range(len(col_idxs)-1):
                    left_opd = "t{}.{}".format(tup_idx, dependency_attributes[col_idxs[j]])
                    right_opd = "t{}.{}".format(tup_idx, dependency_attributes[col_idxs[j+1]])
                    conditions.append("{} = {}".format(left_opd, right_opd))

            # print("***********************************\n")
        else:
            tup_idxs = node_dict[var].keys()
            for t_idx in tup_idxs:
                name_idxs = node_dict[var][t_idx]

                for n_idx in name_idxs:
                    left_opd = "t{}.{}".format(t_idx, dependency_attributes[n_idx])
                    conditions.append("{} = '{}'".format(left_opd, var))
    
    
    # print(conditions) 
    # add summary conditions
    conditions += get_summary_condition(dependency_attributes, dependency_summary_conditions, node_dict)

    sql = None
    '''
    summary
    '''
    select_clause = []
    if type == 'tgd':
        for i in range(len(dependency_summary)):
            if not dependency_summary[i].isdigit() and not isIPAddress(dependency_summary[i]):
                var = dependency_summary[i]
                # print(node_dict[var])
                first_tup = list(node_dict[var].keys())[0] # first tuple appears var
                # print(node_dict[var][first_tup])
                first_col = node_dict[var][first_tup][0] # first col appears var
                select_clause.append("t{}.{}".format(first_tup, dependency_attributes[first_col]))
            else:
                select_clause.append("'{}'".format(dependency_summary[i]))

        sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
    elif type == 'egd':
        if len(dependency_summary) == 0:
            sql = "delete from {} where {}".format(", ".join(tables), " and ".join(conditions))
        else:
            # convert_summary_to_condition
            additional_condition = [] 
            for idx, summary in enumerate(dependency_summary):
                items = summary.split()
                left_opd = items[0]
                right_opd = items[2]
                left_tup_idx = list(node_dict[left_opd].keys())[0]
                left_attr_idx = node_dict[left_opd][left_tup_idx][0]
                right_tup_idx = list(node_dict[right_opd].keys())[0]
                right_attr_idx = node_dict[right_opd][right_tup_idx][0]

                left_param = "t{}.{}".format(left_tup_idx, dependency_attributes[left_attr_idx])
                right_param = "t{}.{}".format(right_tup_idx, dependency_attributes[right_attr_idx])
                additional_condition.append(("{} != {}").format(left_param, right_param))
                select_clause.append("Array[{}, {}] as {}".format(left_param, right_param, dependency_attributes[left_attr_idx])) # for summary f1 = f2, store f1, f2 into an array, e.g., [f1, f2]
            if len(additional_condition) == 1:
                conditions += additional_condition
            else:
                conditions.append("({})".format(" or ".join(additional_condition))) 

            # print("additional_condition", additional_condition)
            # select_clause.append("*")
            # for idx in range(len(tables)):
            #     for attr in dependency_attributes:
            #         if 'condition' in attr:
            #             continue
            #         select_clause.append("t{}.{}".format(idx, attr))
            sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
    else:
        print("Wrong dependency type!")
        exit()
    
    return sql

@timeit
def get_summary_condition(dependency_attributes, dependency_summary_conditions, node_dict):
    """
    generate summary condition

    Parameters:
    -----------
    dependency_attributes: list
        relation of dependency in database

    dependency_summary_conditions: list
        a list of conditions for dependency summary

    node_dict: dict
        generated by analyze_dependency()
    
    Returns:
    ---------
    conditions: list
        a list of conditions
    """
    conditions = []
    if dependency_summary_conditions is not None:
        for smy_condition in dependency_summary_conditions:
            # print("smy_condition", smy_condition)
            temp_condition = []
            smy_conds = []
            logic_opr = None
            if ' and ' in smy_condition.lower():
                logic_opr = ' and '
                smy_conds = smy_condition.split(logic_opr)
            elif ' or ' in smy_condition.lower():
                logic_opr = ' or '
                smy_conds = smy_condition.split(logic_opr)
            else:
                smy_conds[smy_condition]
            
            for smy_cond in smy_conds:
                items = smy_cond.split()
                left_opd = items[0]
                opr = items[1]
                right_opd = items[2]

                left_items = []
                if not left_opd.isdigit() and not isIPAddress(left_opd):
                    for tup_idx in node_dict[left_opd].keys():
                        # for col_idx in node_dict[left_opd][tup_idx]:
                        #     left_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
                        col_idx = node_dict[left_opd][tup_idx][0]
                        left_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
                        break
                else:
                    left_items.append(left_opd)

                right_items = []  
                if not right_opd.isdigit() and not isIPAddress(right_opd):
                    for tup_idx in node_dict[right_opd].keys():
                        # for col_idx in node_dict[right_opd][tup_idx]:
                        #     right_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
                        col_idx = node_dict[right_opd][tup_idx][0]
                        right_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
                        break
                else:
                    right_items.append(right_opd)

                for i in range(len(left_items)):
                    for j in range(len(right_items)):
                        left = left_items[i]
                        right = right_items[j]

                        if left_items[i].isdigit() or isIPAddress(left_items[i]):
                            left = "'{}'".format(left_items[i])
                        
                        if right_items[j].isdigit() or isIPAddress(right_items[j]):
                            right = "'{}'".format(right_items[j])
                            
                        temp_condition.append("{} {} {}".format(left, opr, right))
            conditions.append("({})".format(logic_opr.join(temp_condition)))
            # print("conditions", conditions)
    return conditions

@timeit
def apply_E(conn, sql):
    """
    sql query is the tableau E in query form. 
    Gamma_summary is the forbidden source and destination
    
    Parameters:
    -----------
    conn: psycopg2.connect()
        the instance of connection for Postgres

    sql: string
        the SQL of tableau query of topology

    Returns:
    ---------
    answer: Boolean
        if the gamma summary in the inverse image
    """
    cursor = conn.cursor()
    cursor.execute(sql)
    # results = cursor.rowcount
    results = cursor.fetchall()
    conn.commit()

    answer = True
    if len(results) == 0:
        answer = False

    # # whether w in E(Z)
    # check_cols = []
    # for var_idx, var in enumerate(gamma_summary):
    #     if var.isdigit() or isIPAddress(var):
    #         check_cols.append(var_idx)
    # # print("check_cols", check_cols)

    # gama_summary_item = "|".join([gamma_summary[i] for i in check_cols])

    # # Checking for each flow id individually. This optimization might no longer be very useful since after we fixed chase
    # flow_sql = "select f, count(f) as num from {} group by f order by num desc".format(Z_tablename)
    # cursor.execute(flow_sql)

    # flow_ids_with_num = cursor.fetchall()
    # conn.commit()

    # answer = False
    # count_queries = 0
    # for idx in tqdm(range(len(flow_ids_with_num))):
    #     flow_id = flow_ids_with_num[idx]
    #     count_queries += 1

    #     cursor.execute("drop table if exists temp")
    #     # Select distinct attributes
    #     # temp_sql = "create table temp as select distinct * from {} where f = '{}'".format(Z_tablename, flow_id[0])
    #     temp_sql = "with temp as (select distinct * from {} where f = '{}') {}".format(Z_tablename, flow_id[0], sql)
    #     # print("temp_sql", temp_sql)
    #     cursor.execute(temp_sql)
    #     # conn.commit()

    #     # Execute the query of tableau E to see reachabilities
    #     # cursor.execute(sql)

    #     # The result is a set of all possible source and destinations that are reachable
    #     results = cursor.fetchall()
    #     conn.commit()
    #     # print("results", results) 
        
    #     result_items = []
    #     for res_tup in results:
    #         res_item = "|".join([res_tup[i] for i in check_cols])
    #         result_items.append(res_item)


    #     # Checking if the forbidden pair of source and destinations are in the reachability table
    #     if gama_summary_item in result_items:
    #         # print("gama_summary_item", gama_summary_item)
    #         # print("res_item", res_item)
    #         answer = True
    #         # break
    
    return answer

@timeit
def gen_E_query(E, E_attributes, E_summary, Z, gamma_summary=None):
    """
    generate SQL of end-to-end connectivity view(tableau query of topology)

    Parameters:
    -----------
    E: list[tuple]
        A list of tuples of tableau E(end-to-end connectivity view)
    
    E_attributes: list
        the relation of tableau E in the database
    
    E_summary: list
        the summary of tableau E
    
    Z: string
        the tablename of inverse image

    gamma_summary: list
        the summary of gamma table

    Returns:
    ---------
    sql: string
        the SQL of tableau E 
    """
    node_dict, tables = analyze_dependency(E, E_attributes, Z)
    # print("node_dict", node_dict)
    conditions = []
    for var in node_dict.keys():
        if not var.isdigit() and not isIPAddress(var):
            tup_idxs = list(node_dict[var].keys())
            # print("tup_idxs:", tup_idxs)
            for idx in range(len(tup_idxs)-1):
                t_idx = tup_idxs[idx]
                name_idxs = node_dict[var][t_idx]

                # print("col_idx:", name_idxs)
                if len(name_idxs) > 1:
                    for j in range(len(name_idxs)-1):
                        left_opd = "t{}.{}".format(t_idx, E_attributes[name_idxs[j]])
                        right_opd = "t{}.{}".format(t_idx, E_attributes[name_idxs[j+1]])
                        # print("{} = {}".format(left_opd, right_opd))
                        conditions.append("{} = {}".format(left_opd, right_opd))

                n_idx = name_idxs[-1]
                left_opd = "t{}.{}".format(t_idx, E_attributes[n_idx])

                # print(node_dict[var])
                t_idx2 = tup_idxs[idx+1]
                name_idxs2 = node_dict[var][t_idx2]
                # print("col_idxs2:", name_idxs2)

                n_idx2 = name_idxs2[-1]
                right_opd = "t{}.{}".format(t_idx2, E_attributes[n_idx2])

                conditions.append("{} = {}".format(left_opd, right_opd))
                # print("conditions:", conditions)
                # print()
            
            idx = tup_idxs[-1]
            col_idxs = node_dict[var][idx]
            # print("col_idx:", col_idxs)
            if len(col_idxs) > 1:
                for j in range(len(col_idxs)-1):
                    left_opd = "t{}.{}".format(idx, E_attributes[col_idxs[j]])
                    right_opd = "t{}.{}".format(idx, E_attributes[col_idxs[j+1]])
                    # print("{} = {}".format(left_opd, right_opd))
                    conditions.append("{} = {}".format(left_opd, right_opd))

            # print("***********************************\n")
        else:
            tup_idxs = node_dict[var].keys()
            for t_idx in tup_idxs:
                name_idxs = node_dict[var][t_idx]

                for n_idx in name_idxs:
                    left_opd = "t{}.{}".format(t_idx, E_attributes[n_idx])
                    conditions.append("{} = '{}'".format(left_opd, var))
    # print(conditions) 

    '''
    summary
    '''
    select_clause = []
    for idx, var in enumerate(E_summary):
        # choose first tuple and first colomn var appears
        tup_idx = list(node_dict[var].keys())[0]
        col_idx = node_dict[var][tup_idx][0]

        selected_param = "t{}.{}".format(tup_idx, E_attributes[col_idx])
        select_clause.append(selected_param)
        if gamma_summary is not None: # add additional conditionfrom head, to directly find the summary of gamma table
            if not is_variable(gamma_summary[idx]):
                conditions.append("{} = '{}'".format(selected_param, gamma_summary[idx]))
    sql = "select " + ", ".join(select_clause) + " from " + ", ".join(tables) + " where " + " and ".join(conditions)
    # print(sql)
    return sql


if __name__ == '__main__':
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])


    # E_tuples = [
    #     ('f', 's1', 'd1', 's', '11.0.0.1', '{}'),
    #     ('f', 's2', 'd2', '11.0.0.1', '11.0.0.2', '{}'),
    #     ('f', 's3', 'd3', '11.0.0.2', 'd', '{}')
    # ]
    cursor = conn.cursor()
    cursor.execute("select * from e")
    E_tuples = cursor.fetchall()
    conn.commit()

    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    sql = gen_E_query(E_tuples, E_attributes, E_summary, 'Z_random')

    apply_E(conn, sql, 'Z_random', [])
    # load_table(conn, E_attributes, E_attributes_datatypes, "E", E_tuples)

    # # 1.2 => 4, 1.1 =>3, 1.3 => 5, 1.4 =>6
    # gamma_tuples = [
    #     ('f1', '10.0.0.2', '12.0.0.3', '{}'),
    #     ('f2', '10.0.0.1', '12.0.0.4', '{}')
    # ]
    # gamma_summary = ['f3', '10.0.0.2', '12.0.0.4']
    # gamma_attributes = ['f', 'n', 'x', 'condition']
    # gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    
    # load_table(conn, gamma_attributes, gamma_attributes_datatypes, "W", gamma_tuples)

    # Z_tuples = gen_inverse_image(conn, E_tuples, "W")
    # Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    # Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    # load_table(conn, Z_attributes, Z_attributes_datatypes, "Z", Z_tuples)

    # dependency1 = {'dependency_tuples': [('f', '10.0.0.8', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}')
    #     ], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'
    #     ], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'
    #     ], 'dependency_cares_attributes': ['f', 'src', 'dst', 'n', 'x'
    #     ], 'dependency_summary': ['f', '10.0.0.5', '12.0.0.1', '11.0.0.1', '11.0.0.2'
    #     ], 'dependency_summary_condition': None, 'dependency_type': 'tgd'
    # }
    # apply_dependency(conn, dependency1, "Z")

    # dependency2 = {'dependency_tuples': [('f1', '10.0.0.8', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}'), ('f2', '10.0.0.5', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}')
    #     ], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'
    #     ], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'text[]'
    #     ], 'dependency_cares_attributes': ['src', 'dst', 'n', 'x'
    #     ], 'dependency_summary': ['f1 = f2'
    #     ], 'dependency_summary_condition': None, 'dependency_type': 'egd'
    # }

    # apply_dependency(conn, dependency2, "Z")

    


