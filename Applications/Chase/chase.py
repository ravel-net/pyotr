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

            egd_sql = convert_dependency_to_sql(dependency, inverse_image_tablename)

            cursor = conn.cursor()
            cursor.execute(egd_sql)
            if cursor.rowcount == 0:
                does_updated = False
            conn.commit()
            return does_updated
        else:
            does_updated = apply_egd(conn, dependency, inverse_image_tablename)
    else:
        does_updated = False
        print("wrong type!")
        exit()

    return does_updated

@timeit
def apply_tgd(conn, dependency, inverse_image_tablename):
    """
    Apply tgd dependency, calls by apply_dependency()

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

    cursor.execute(tgd_sql)

    results = cursor.fetchall()
    conn.commit()

    z_tuples = getCurrentTable(conn, inverse_image_tablename)

    results_set = set(results)
    z_tuples_set = set(z_tuples)
    inserted_tuples_set = results_set.difference(z_tuples_set)

    inserted_tuples = list(inserted_tuples_set)
    does_updated = False

    if len(inserted_tuples) != 0:
        does_updated = True
        execute_values(cursor, "insert into {} values %s".format(inverse_image_tablename), inserted_tuples)
    
    conn.commit()
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
    cursor = conn.cursor()
    cursor.execute("drop table if exists {}".format(tablename))
    conn.commit()
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    load_table(conn, Z_attributes, Z_attributes_datatypes, tablename, new_table)

@timeit
def applySourceDestPolicy(conn, Z_tablename):
    """
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
    return applyRewritePolicy(conn, dependency, inverse_image_tablename)

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
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_conditions = dependency['dependency_summary_condition']
    
    node_dict, tables = analyze_dependency(dependency_tuples, dependency_attributes, Z)

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

@timeit
def apply_E(conn, sql, Z_tablename, gamma_summary):
    """
    sql query is the tableau E in query form. 
    Gamma_summary is the forbidden source and destination
    
    Parameters:
    -----------
    sql: string
        the SQL of tableau query of topology

    Z_tablename:string
        the tablename of inverse image

    gamma_summary: list
        the summary of gamma table

    Returns:
    ---------
    answer: Boolean
        if the gamma summary in the inverse image
    """
    # whether w in E(Z)
    check_cols = []
    for var_idx, var in enumerate(gamma_summary):
        if var.isdigit() or isIPAddress(var):
            check_cols.append(var_idx)
    # print("check_cols", check_cols)

    gama_summary_item = "|".join([gamma_summary[i] for i in check_cols])

    cursor = conn.cursor()
    # Checking for each flow id individually. This optimization might no longer be very useful since after we fixed chase
    flow_sql = "select f, count(f) as num from {} group by f order by num desc".format(Z_tablename)
    cursor.execute(flow_sql)

    flow_ids_with_num = cursor.fetchall()
    conn.commit()

    answer = False
    count_queries = 0
    for flow_id in flow_ids_with_num:
        count_queries += 1

        cursor.execute("drop table if exists temp")
        # Select distinct attributes
        # temp_sql = "create table temp as select distinct * from {} where f = '{}'".format(Z_tablename, flow_id[0])
        temp_sql = "with temp as (select distinct * from {} where f = '{}') {}".format(Z_tablename, flow_id[0], sql)
        # print("temp_sql", temp_sql)
        cursor.execute(temp_sql)
        # conn.commit()

        # Execute the query of tableau E to see reachabilities
        # cursor.execute(sql)

        # The result is a set of all possible source and destinations that are reachable
        results = cursor.fetchall()
        conn.commit()
        # print("results", results) 
        
        result_items = []
        for res_tup in results:
            res_item = "|".join([res_tup[i] for i in check_cols])
            result_items.append(res_item)


        # Checking if the forbidden pair of source and destinations are in the reachability table
        if gama_summary_item in result_items:
            # print("gama_summary_item", gama_summary_item)
            # print("res_item", res_item)
            answer = True
            break
    
    return answer

@timeit
def gen_E_query(E, E_attributes, E_summary, Z, block_list=None):
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
    add additional condition: not head
    '''
    if block_list is not None:
        tuple_idx1= list(node_dict['s'].keys())[0] 
        tuple_idx2= list(node_dict['d'].keys())[0] 
        col_idx1 = node_dict['s'][tuple_idx1][0]
        col_idx2 = node_dict['d'][tuple_idx2][0]
        conditions.append("t{}.{} != '{}' and t{}.{} != '{}'".format(tuple_idx1, E_attributes[col_idx1], block_list[0], tuple_idx2, E_attributes[col_idx2], block_list[1]))

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
    conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])

    E_tuples = [
        ('f', 's1', 'd1', 's', '11.0.0.1', '{}'),
        ('f', 's2', 'd2', '11.0.0.1', '11.0.0.2', '{}'),
        ('f', 's3', 'd3', '11.0.0.2', 'd', '{}')
    ]
    E_summary = ['f', 's', 'd']
    E_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    E_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]']

    load_table(conn, E_attributes, E_attributes_datatypes, "E", E_tuples)

    # 1.2 => 4, 1.1 =>3, 1.3 => 5, 1.4 =>6
    gamma_tuples = [
        ('f1', '10.0.0.2', '12.0.0.3', '{}'),
        ('f2', '10.0.0.1', '12.0.0.4', '{}')
    ]
    gamma_summary = ['f3', '10.0.0.2', '12.0.0.4']
    gamma_attributes = ['f', 'n', 'x', 'condition']
    gamma_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'text[]']
    
    load_table(conn, gamma_attributes, gamma_attributes_datatypes, "W", gamma_tuples)

    Z_tuples = gen_inverse_image(conn, E_tuples, "W")
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    load_table(conn, Z_attributes, Z_attributes_datatypes, "Z", Z_tuples)

    dependency1 = {'dependency_tuples': [('f', '10.0.0.8', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}')
        ], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'
        ], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'text[]'
        ], 'dependency_cares_attributes': ['f', 'src', 'dst', 'n', 'x'
        ], 'dependency_summary': ['f', '10.0.0.5', '12.0.0.1', '11.0.0.1', '11.0.0.2'
        ], 'dependency_summary_condition': None, 'dependency_type': 'tgd'
    }
    apply_dependency(conn, dependency1, "Z")

    dependency2 = {'dependency_tuples': [('f1', '10.0.0.8', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}'), ('f2', '10.0.0.5', '12.0.0.1', '11.0.0.1', '11.0.0.2', '{}')
        ], 'dependency_attributes': ['f', 'src', 'dst', 'n', 'x', 'condition'
        ], 'dependency_attributes_datatypes': ['inet_faure', 'inet_faure', 'inet_faure', 'text[]'
        ], 'dependency_cares_attributes': ['src', 'dst', 'n', 'x'
        ], 'dependency_summary': ['f1 = f2'
        ], 'dependency_summary_condition': None, 'dependency_type': 'egd'
    }

    apply_dependency(conn, dependency2, "Z")


