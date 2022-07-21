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

FAURE_DATATYPES = ['int4_faure', 'inet_faure']
INT4_FAURE = 'int4_faure'
INET_FAURE = 'inet_faure'

DIGIT_RELATED_TYPES = ['integer', 'double', 'float']
STR_RELATED_TYPES = ['char', 'text']

conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
cursor = conn.cursor()

# TODO: checked_tuples is redundant everywhere. Not deleting yet since it might break some things

def load_table(attributes, datatypes, tablename, tableau):
    """
    Load data instance into database

    Parameters:
    ------------
    columns: list, a list of attributes, e.g. [name, age]

    datatypes: list, a list of datatypes corresponding to columns, e.g. [text, integer] corresponding to columns [name, age]

    tablename: string, database table which stores tableau

    tableau: list, data instance
    """
    # conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
    # cursor = conn.cursor()

    cursor.execute("drop table if exists {}".format(tablename))
    columns = ["{} {}".format(attributes[i], datatypes[i]) for i in range(len(attributes))]
    cursor.execute("create table {} ({})".format(tablename, ", ".join(columns)))
    conn.commit()

    execute_values(cursor, "insert into {} values %s".format(tablename), tableau)
    conn.commit()
    # cursor.execute("select * from {}".format(tablename))
    # conn.commit()
    # conn.close()

def gen_z(E_tuples, gamma_tablename):
    """
    generate the tuples of Z table

    Parameters:
    -----------
    E_tuples: list[tuple]
        a list of tuples in table E. the tuple contains condition column
    
    gamma_tablename: string 
        name of gamma table

    Returns:
    --------
    Z_tuples: list[tuple]
        a list of tuples for Z table. Convert gamma table to Z table.

    gen_z: float
        the time for generating a list of tuples for Z table.
    
    """
    sql = "select * from {}".format(gamma_tablename)
    cursor.execute(sql)

    gamma_table = cursor.fetchall()
    conn.commit()
    
    Z_tuples = []
    z_tuple_num = 1

    begin_time = time.time()
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
    
    end_time = time.time()

    return Z_tuples, end_time-begin_time

def isIPAddress(value):
    if len(value.strip().split('.')) == 4:
        return True
    else:
        return False

def is_variable(value, datatype):
    if datatype.lower() in FAURE_DATATYPES:
        if datatype.lower() == INT4_FAURE:
            return not value.isdigit()
        else:
            return not isIPAddress(value)
    else:
        return False

# Main function of chase to apply dependencies. Calls apply_tgd and apply_egd.
def apply_dependency(dependency, Z_tablename, checked_tuples):
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # cursor = conn.cursor()
    # print("starting dependency")
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']

    does_updated = True
    operate_time = 0
    check_valid_time = 0
    
    if type.lower() == 'tgd':
        checked_tuples, does_updated, check_valid_time, operate_time = apply_tgd(dependency, Z_tablename, checked_tuples)
    elif type.lower() == 'egd':
        # if dependency_summary is empty, it is a deletion for firewall policy
        if len(dependency_summary) == 0: # if dependency summary is empty, the matched tuples are deleted
            node_dict, _ = analyze_dependency(dependency_tuples, dependency_attributes, Z_tablename)
            # print("node_dict", node_dict)

            egd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
            # f = open("./sqls.txt", "a")
            # f.write("{}\n".format(egd_sql))
            # f.close()
            # print(egd_sql)
            check_valid_egd_begin = time.time()
            cursor.execute(egd_sql)
            check_valid_egd_end = time.time()
            # f = open("./sqls_time.txt", "a")
            # f.write("{:.4f}\n".format(check_valid_egd_end - check_valid_egd_begin))
            # f.close()

            check_valid_time += (check_valid_egd_end - check_valid_egd_begin)
            operate_time += (check_valid_egd_end - check_valid_egd_begin)

            check_valid_begin = time.time()
            if cursor.rowcount == 0:
                does_updated = False
            check_valid_end = time.time()
            check_valid_time += (check_valid_end - check_valid_begin)
            conn.commit()
            print("ending dependency")
            return checked_tuples, does_updated, check_valid_time, operate_time
        else:
            # print("apply_egd")
            checked_tuples, does_updated, check_valid_time, operate_time = apply_egd(dependency, Z_tablename, checked_tuples)
            # checked_tuples, does_updated, check_valid_time, operate_time = apply_egd_old(dependency, Z_tablename, checked_tuples)
    else:
        check_valid_begin = time.time()
        does_updated = False
        print("wrong type!")
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)
    conn.commit()
    # print("ending dependency")
    return checked_tuples, does_updated, check_valid_time, operate_time

# Checks for the given pattern and returns the summary (i.e. the tuple to add) IF the given pattern exists. Then computes the difference between the summary and the Z_table. Adds the extra tuple only if it does not already exist in the Z_table (preventing unnecessary additions)
def apply_tgd(dependency, Z_tablename, checked_tuples):
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']
    check_valid_time = 0
    operate_time = 0

    tgd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
    # print(tgd_sql)
    check_valid_begin = time.time()
    cursor.execute(tgd_sql)
    check_valid_end = time.time()
    check_valid_time += (check_valid_end - check_valid_begin)

    # matched_tuples = []
    results = cursor.fetchall()
    # print("results", results)
    conn.commit()

    z_tuples = getCurrentTable(Z_tablename)

    results_set = set(results)
    z_tuples_set = set(z_tuples)
    # print("results_set", results_set)
    # print("z_tuples_set", z_tuples_set)
    inserted_tuples_set = results_set.difference(z_tuples_set)
    # print("inserted_tuples_set", inserted_tuples_set)
    inserted_tuples = list(inserted_tuples_set)
    does_updated = False
    operation_time = 0
    print("inserted_tuples", inserted_tuples)
    if len(inserted_tuples) != 0:
        does_updated = True

        begin_time = time.time()
        execute_values(cursor, "insert into {} values %s".format(Z_tablename), inserted_tuples)
        conn.commit()
        end_time = time.time()
        operation_time += (end_time - begin_time)
    return [], does_updated, 0, operation_time

# Returns the table tuples from postgres of the table given as a parameter
def getCurrentTable(tablename):
    cursor.execute('select * from {};'.format(tablename))
    table = cursor.fetchall()
    conn.commit()
    return table

# Replaces a given table with a new one (new_table given as tuples)
def replace_z_table(tablename, new_table):
    cursor.execute("drop table if exists {}".format(tablename))
    conn.commit()
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    load_table(Z_attributes, Z_attributes_datatypes, tablename, new_table)

# The source must be first hop and the destination must be last hop. This is applied at the start to get rid of variables
def applySourceDestPolicy(Z_tablename):
    begin_time = time.time()
    z_table = getCurrentTable(Z_tablename)
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
    end_time = time.time()
    # Replace Z table code
    replace_z_table(Z_tablename, new_z_table)

    return [], True, 0, end_time-begin_time

# For rewrite policy (equalizing flow ids).
# Searches for the flow ID of the first tuple pattern. Then searches for all flow IDs of the second tuple pattern. Replaces the later flow IDs with the former. This is a tableau wide substitutions (all replace flow IDs are replaced)
# TODO: Unlike tgds, this is not general. It is specific to flow id equalization
def applyRewritePolicy(dependency, Z_tablename):
    start_time = time.time()
    z_table = getCurrentTable(Z_tablename)
    pattern_source = dependency['dependency_tuples'][0][1]
    pattern_dest = dependency['dependency_tuples'][0][2]
    pattern_n = IPv4Address(dependency['dependency_tuples'][0][3])
    pattern_x = IPv4Address(dependency['dependency_tuples'][0][4])
    # pattern_condition = dependency['dependency_summary_condition'][0] # assuming it is always less than equal to policy
    # pattern_condition_IP = IPv4Address(pattern_condition[7:-1])    

    if (len(dependency['dependency_tuples']) < 2):
        end_time = time.time()
        return [], False, 0, end_time - start_time
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
        end_time = time.time()
        return [], False, 0, end_time - start_time

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

    replace_z_table(Z_tablename, new_z_table)
    end_time = time.time()
    # exit()
    return [], does_update, 0, end_time - start_time


# Applies egd (specifically the one to set flow ids equal) in memory
def apply_egd(dependency, Z_tablename, checked_tuples):
    return applyRewritePolicy(dependency, Z_tablename)

# Returns the position of each variable/constant in the dependency. Useful to check for equivalent variables/constants when converting to sql
# e.g. for \sigma_new x_f appears in the 0th and 1st tuple both in the 0th column: {'x_f': {0: [0], 1: [0]}, 'x_s1': {0: [1]}, 'x_d': {0: [2], 1: [2]}, 'x_n': {0: [3]}, 'x_x': {0: [4], 1: [3]}, 'x_s2': {1: [1]}, 'x_next': {1: [4]}}
def analyze_dependency(dependency_tuples, dependency_attributes, Z):
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

def convert_dependency_to_sql(type, dependency, Z, dependency_attributes, dependency_summary, dependency_summary_conditions=None):
    
    node_dict, tables = analyze_dependency(dependency, dependency_attributes, Z)
    # print(node_dict)
    # print(tables)

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
                    for j in range(len(col_idxs)-1):
                        left_opd = "t{}.{}".format(t_idx, dependency_attributes[j])
                        right_opd = "t{}.{}".format(t_idx, dependency_attributes[j+1])
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
                # print()
            
            col_idxs = node_dict[var][tup_idxs[-1]]
            if len(col_idxs) > 1:
                for j in range(len(col_idxs)-1):
                    left_opd = "t{}.{}".format(idx, dependency_attributes[j])
                    right_opd = "t{}.{}".format(idx, dependency_attributes[j+1])
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
            for summary in  dependency_summary:
                items = summary.split()
                left_opd = items[0]
                right_opd = items[2]
                left_tup_idx = list(node_dict[left_opd].keys())[0]
                left_attr_idx = node_dict[left_opd][left_tup_idx][0]
                right_tup_idx = list(node_dict[right_opd].keys())[0]
                right_attr_idx = node_dict[right_opd][right_tup_idx][0]
                additional_condition.append(("t{}.{} != t{}.{}".format(left_tup_idx, dependency_attributes[left_attr_idx], right_tup_idx, dependency_attributes[right_attr_idx])))
            conditions += additional_condition
            # print("additional_condition", additional_condition)
            # select_clause.append("*")
            for idx in range(len(tables)):
                for attr in dependency_attributes:
                    if 'condition' in attr:
                        continue
                    select_clause.append("t{}.{}".format(idx, attr))
            sql = "select {} from {} where {}".format(", ".join(select_clause), ", ".join(tables), " and ".join(conditions))
    else:
        print("Wrong dependency type!")
        exit()
    
    return sql

def get_summary_condition(dependency_attributes, dependency_summary_conditions, node_dict):
    conditions = []
    if dependency_summary_conditions is not None:
        for smy_condition in dependency_summary_conditions:
            items = smy_condition.split()
            left_opd = items[0]
            opr = items[1]
            right_opd = items[2]

            left_items = []
            if not left_opd.isdigit() and not isIPAddress(left_opd):
                for tup_idx in node_dict[left_opd].keys():
                    for col_idx in node_dict[left_opd][tup_idx]:
                        left_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
            else:
                left_items.append(left_opd)

            right_items = []  
            if not right_opd.isdigit() and not isIPAddress(right_opd):
                for tup_idx in node_dict[right_opd].keys():
                    for col_idx in node_dict[right_opd][tup_idx]:
                        right_items.append("t{}.{}".format(tup_idx, dependency_attributes[col_idx]))
            else:
                right_items.append(right_opd)

            for i in range(len(left_items)):
                for j in range(len(right_items)):
                    left = left_items[i]
                    right = right_items[j]

                    if left_items[i].isdigit() or isIPAddress(left_items[i]):
                        left = "{}".format(left_items[i])
                    
                    if right_items[j].isdigit() or isIPAddress(right_items[j]):
                        right = "{}".format(right_items[j])
                        
                    conditions.append("{} {} {}".format(left, opr, right))
    
    return conditions

# sql query is the tableau E in query form. Gamma_summary is the forbidden source and destination
def apply_E(sql, Z_tablename, gama_summary):
    # whether w in E(Z)
    check_cols = []
    for var_idx, var in enumerate(gama_summary):
        if var.isdigit() or isIPAddress(var):
            check_cols.append(var_idx)
    # print("check_cols", check_cols)

    gama_summary_item = "|".join([gama_summary[i] for i in check_cols])

    # Checking for each flow id individually. This optimization might no longer be very useful since after we fixed chase
    flow_sql = "select f, count(f) as num from {} group by f order by num desc".format(Z_tablename)
    cursor.execute(flow_sql)

    flow_ids_with_num = cursor.fetchall()
    conn.commit()

    total_query_time = 0
    total_check_time = 0
    answer = False
    count_queries = 0
    for flow_id in flow_ids_with_num:
        count_queries += 1

        cursor.execute("drop table if exists temp")
        # Select distinct attributes
        temp_sql = "create table temp as select distinct * from {} where f = '{}'".format(Z_tablename, flow_id[0])
        cursor.execute(temp_sql)
        conn.commit()
        # flow_condition = "t0.f = '{}'".format(flow_id[0])
        # sql += " and {}".format(flow_condition)
        # print(sql)
        # exit()
        query_begin = time.time()
        # Execute the query of tableau E to see reachabilities
        cursor.execute(sql)
        query_end = time.time()
        total_query_time += (query_end-query_begin)
        # print("query_begin", query_begin, query_end)
        # print(query_end-query_begin)

        # The result is a set of all possible source and destinations that are reachable
        results = cursor.fetchall()
        conn.commit()
        # print("results", results) 
        
        result_items = []
        for res_tup in results:
            res_item = "|".join([res_tup[i] for i in check_cols])
            result_items.append(res_item)

        check_begin = time.time()

        # Checking if the forbidden pair of source and destinations are in the reachability table
        if gama_summary_item in result_items:
            # print("gama_summary_item", gama_summary_item)
            # print("res_item", res_item)
            answer = True
            check_end = time.time()
            total_check_time += (check_end-check_begin)
            break
        check_end = time.time()
        total_check_time += (check_end-check_begin)
        
    return answer,count_queries, total_query_time, total_check_time

def gen_E_query(E, E_attributes, E_summary, Z):
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
                    for j in range(len(col_idxs)-1):
                        left_opd = "t{}.{}".format(t_idx, E_attributes[j])
                        right_opd = "t{}.{}".format(t_idx, E_attributes[j+1])
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
            
            col_idxs = node_dict[var][tup_idxs[-1]]
            if len(col_idxs) > 1:
                for j in range(len(col_idxs)-1):
                    left_opd = "t{}.{}".format(idx, E_attributes[j])
                    right_opd = "t{}.{}".format(idx, E_attributes[j+1])
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
    for var in E_summary:
        # choose first tuple and first colomn var appears
        tup_idx = list(node_dict[var].keys())[0]
        col_idx = node_dict[var][tup_idx][0]

        select_clause.append("t{}.{}".format(tup_idx, E_attributes[col_idx]))
    sql = "select distinct " + ", ".join(select_clause) + " from " + ", ".join(tables) + " where " + " and ".join(conditions)
    # print(sql)
    return sql


if __name__ == '__main__':
    

    E_tuples = [
        ('f', 's1', 'd1', 's', '11.0.0.1', '{}'),
        ('f', 's2', 'd2', '11.0.0.1', '11.0.0.2', '{}'),
        ('f', 's3', 'd3', '11.0.0.2', 'd', '{}')
    ]
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    load_table(E_attributes, E_attributes_datatypes, "E", E_tuples)

    # 1.2 => 4, 1.1 =>3, 1.3 => 5, 1.4 =>6
    gamma_tuples = [
        ('f1', '10.0.0.2', '12.0.0.3', '{}'),
        ('f2', '10.0.0.1', '12.0.0.4', '{}')
    ]
    gamma_summary = ['f3', '10.0.0.2', '12.0.0.4']
    gamma_attributes = ['f', 'n', 'x', 'condition']
    gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    
    load_table(gamma_attributes, gamma_attributes_datatypes, "W", gamma_tuples)

    Z_tuples = gen_z(E_tuples, "W")
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', '', 'text', 'text', 'text']
    load_table(Z_attributes, Z_attributes_datatypes, "Z", Z_tuples)

    tgd = [
        ('f', '4', '5', '4', '1', '{}')
    ]
    tgd_summary = ['f', '3', '5', '4', '1']
    tgd_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    tgd_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    # load_table(tgd_attributes, tgd_attributes_datatypes, "tgd", tgd)
    # gen_tgd_sql("Z", "tgd", tgd_summary, tgd_attributes)
    # convert_dependency_to_sql("tgd", tgd, 'Z', tgd_attributes, tgd_summary)
    apply_dependency("tgd", "Z", Z_attributes, tgd, tgd_summary, tgd_attributes)

    egd = [
        ('f1', '4', '5', 'n', '{}'),
        ('f2', '3', '5', 'n', '{}')
    ]
    egd_attributes = ['f', 'src', 'dst', 'x', 'condition']
    egd_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    egd_condition = ['n <= 1']
    egd_summary = ['f1 = f2']
    # convert_dependency_to_sql("egd", egd, 'Z', egd_attributes, egd_summary, egd_condition)
    # apply_dependency("egd", "Z", Z_attributes, egd, egd_summary, egd_attributes, egd_condition)

    # egd2 = [
    #     ('f1', '3', '5', 'n', '{}'),
    #     ('f2', '3', '6', 'n', '{}'),
    # ]
    egd2 = [
        ('f1', '3', '5', 'n', '{}'),
        ('f2', '3', '6', 'n', '{}'),
        ('f3', '4', '5', 'n', '{}')
    ]
    egd2_attributes = ['f', 'src', 'dst', 'x', 'condition']
    egd2_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    egd2_condition = ['n <= 2']
    egd2_summary = ['f1 = f2', 'f2 = f3']
    # apply_dependency("egd", "Z", Z_attributes, egd2, egd2_summary, egd2_attributes, egd2_condition)

    egd3 = [
        ('f', 's1', 'd1', '{}'),
        ('f', 's2', 'd2', '{}')
    ]
    egd3_attributes = ['f', 'src', 'dst', 'condition']
    egd3_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    # egd3_condition = ['n <= 2']
    egd3_summary = ['s1 = s2', 'd1 = d2']
    apply_dependency("egd", "Z", Z_attributes, egd3, egd3_summary, egd3_attributes)


