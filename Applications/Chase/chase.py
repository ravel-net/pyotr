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
        
        # if len(dependency_summary) == 0: # if dependency summary is empty, the matched tuples are deleted
        #     node_dict, _ = analyze_dependency(dependency_tuples, dependency_attributes, Z_tablename)
        #     # print("node_dict", node_dict)

        #     egd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
        #     # f = open("./sqls.txt", "a")
        #     # f.write("{}\n".format(egd_sql))
        #     # f.close()
        #     # print(egd_sql)
        #     check_valid_egd_begin = time.time()
        #     cursor.execute(egd_sql)
        #     check_valid_egd_end = time.time()
        #     # f = open("./sqls_time.txt", "a")
        #     # f.write("{:.4f}\n".format(check_valid_egd_end - check_valid_egd_begin))
        #     # f.close()

        #     check_valid_time += (check_valid_egd_end - check_valid_egd_begin)
        #     operate_time += (check_valid_egd_end - check_valid_egd_begin)

        #     check_valid_begin = time.time()
        #     if cursor.rowcount == 0:
        #         does_updated = False
        #     check_valid_end = time.time()
        #     check_valid_time += (check_valid_end - check_valid_begin)
        #     conn.commit()
        #     print("ending dependency")
        #     return checked_tuples, does_updated, check_valid_time, operate_time
        # else:
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

def apply_tgd_new(dependency, Z_tablename, checked_tuples):
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']
    check_valid_time = 0
    operate_time = 0

    tgd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
    print(tgd_sql)
    check_valid_begin = time.time()
    cursor.execute(tgd_sql)
    check_valid_end = time.time()
    check_valid_time += (check_valid_end - check_valid_begin)

    # matched_tuples = []
    results = cursor.fetchall()
    print("results", results[:2])
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
    if len(inserted_tuples) != 0:
        does_updated = True

        begin_time = time.time()
        execute_values(cursor, "insert into {} values %s".format(Z_tablename), inserted_tuples)
        conn.commit()
        end_time = time.time()
        operation_time += (end_time - begin_time)
    return [], does_updated, 0, operation_time

def apply_tgd(dependency, Z_tablename, checked_tuples):
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']
    check_valid_time = 0
    operate_time = 0

    tgd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
    check_valid_begin = time.time()
    cursor.execute(tgd_sql)
    check_valid_end = time.time()
    check_valid_time += (check_valid_end - check_valid_begin)

    # matched_tuples = []
    results = cursor.fetchall()
    conn.commit()
    # print(results)

    does_updated = True
    inserted_tuples = []
    check_valid_begin = time.time()
    for valid_match in results:
        if str(valid_match) in checked_tuples:
            continue
        else:
            inserted_tuples.append(valid_match)
            checked_tuples.append(str(valid_match))

    if len(inserted_tuples) > 0:
        # print("inserted_tuples", inserted_tuples)
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)
        # print("insert", results)
        # f = open("./sqls.txt", "a")
        # f.write("{}\n".format(results))
        # f.close()
        begin_time = time.time()
        execute_values(cursor, "insert into {} values %s".format(Z_tablename), inserted_tuples)
        end_time = time.time()
        # f = open("./sqls_time.txt", "a")
        # f.write("{:.4f}\n".format(end_time - begin_time))
        # f.close()
        operate_time += (end_time - begin_time)
        conn.commit()
        
    else:  # if all matches are already checked, the algorithm is done
        does_updated = False
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)
        conn.commit()
        return  checked_tuples, does_updated, check_valid_time, operate_time
    
    return  checked_tuples, does_updated, check_valid_time, operate_time

def checkCondition(where):
    # print("================")
    print(where)
    # print("================")

def getCurrentTable(tablename):
    cursor.execute('select * from {};'.format(tablename))
    table = cursor.fetchall()
    conn.commit()
    return table

def replace_z_table(tablename, new_table):
    cursor.execute("drop table if exists {}".format(tablename))
    conn.commit()
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    # Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    Z_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure']
    load_table(Z_attributes, Z_attributes_datatypes, tablename, new_table)

def convertToText(tablename):
    table = getCurrentTable(tablename)
    cursor.execute("drop table if exists {}".format(tablename))
    conn.commit()
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    # Z_attributes_datatypes = ['inet_faure', 'inet_faure', 'inet_faure', 'inet_faure', 'inet_faure']
    load_table(Z_attributes, Z_attributes_datatypes, tablename, table)

# The source must be first hop and the destination must be last hop
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

def applyDestinationPolicy(dependency, Z_tablename):
    start_time = time.time()
    z_table = getCurrentTable(Z_tablename)

    # extract unique flows
    unique_flows = {}
    for tuple in z_table:
        flowid = tuple[0]
        if flowid not in unique_flows:
            src = tuple[1]
            dest = tuple[2]
            unique_flows[flowid] = (src,dest)

    new_z_table = []
    does_update = False
    for tuple in z_table:
        flowid = tuple[0]
        if flowid not in unique_flows:
            print("Unknown flow id encountered. Something went wrong. Exiting")
            exit()
        newTuple = (flowid, unique_flows[flowid][0], unique_flows[flowid][1], tuple[3], tuple[4])
        if (unique_flows[flowid][0] != tuple[1] or unique_flows[flowid][1] != tuple[2]):
            does_update = True
        new_z_table.append(newTuple)

    replace_z_table(Z_tablename, new_z_table)
    end_time = time.time()
    return [], does_update, 0, end_time - start_time

def applyRewritePolicy(dependency, Z_tablename):
    start_time = time.time()
    z_table = getCurrentTable(Z_tablename)
    pattern_source = dependency['dependency_tuples'][0][1]
    pattern_dest = dependency['dependency_tuples'][0][2]
    pattern_condition = dependency['dependency_summary_condition'][0] # assuming it is always less than equal to policy
    # pattern_condition_IP = IPv4Address(pattern_condition[7:-1])    

    if (len(dependency['dependency_tuples']) < 2):
        end_time = time.time()
        return [], False, 0, end_time - start_time
    replace_source = dependency['dependency_tuples'][1][1]
    replace_dest = dependency['dependency_tuples'][1][2]
    replace_condition = dependency['dependency_summary_condition'][1] # assuming it is always less than equal to policy
    # replace_condition_IP = IPv4Address(replace_condition[7:-1])

    # extract flow id of pattern tuple
    targetFlow = ""
    for tuple in z_table:
        flowid = tuple[0]
        src = tuple[1]
        dest = tuple[2]
        n = IPv4Address(tuple[3])
        if (src == pattern_source and dest == pattern_dest):
            targetFlow = flowid
            break
    if targetFlow == "":
        # print("No flow found. Hacky solution might not be working")
        end_time = time.time()
        return [], False, 0, end_time - start_time

    new_z_table = []
    does_update = False
    for tuple in z_table:
        flowid = tuple[0]
        src = tuple[1]
        dest = tuple[2]
        n = IPv4Address(tuple[3])
        if (src == replace_source and dest == replace_dest):
            if flowid != targetFlow:
                does_update = True
            new_z_table.append((targetFlow, tuple[1], tuple[2], tuple[3], tuple[4]))
        # elif (src == pattern_source and dest == pattern_dest and n <= pattern_condition_IP):
        #     if flowid != targetFlow:
        #         does_update = True
        #         new_z_table.append((targetFlow, tuple[1], tuple[2], tuple[3], tuple[4]))
        #     else:
        #         new_z_table.append((tuple[0], tuple[1], tuple[2], tuple[3], tuple[4]))
        else:
            new_z_table.append((tuple[0], tuple[1], tuple[2], tuple[3], tuple[4]))
    replace_z_table(Z_tablename, new_z_table)
    end_time = time.time()
    # exit()
    return [], does_update, 0, end_time - start_time

    

    # extract first source and destination

# def apply_egd_in_memory(dependency, Z_tablename, checked_tuples):
def apply_egd(dependency, Z_tablename, checked_tuples):
    # print("Starting egd")
    if ('f' in dependency['dependency_cares_attributes']):
        # print("ending egd")
        conn.commit()
        return applyDestinationPolicy(dependency, Z_tablename)
    else:
        conn.commit()
        # print("ending egd")
        return applyRewritePolicy(dependency, Z_tablename)

def apply_egd_old(dependency, Z_tablename, checked_tuples):
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']
    check_valid_time = 0
    operate_time = 0

    node_dict, _ = analyze_dependency(dependency_tuples, dependency_attributes, Z_tablename)
    print(getCurrentTable(Z_tablename))
    print("===============================")
    print("dependency", dependency)
    # print("Z_tablename", Z_tablename)
    # print("checked_tuples", checked_tuples)
    # print("node_dict", node_dict)
    print("===============================")
    value_index_mapping = {}
    flag_value = {}
    for var in node_dict.keys():
        if var not in value_index_mapping.keys():
            value_index_mapping[var] = []
        
        for tup_idx in node_dict[var].keys():
            col_idxs = node_dict[var][tup_idx]
            value_index_mapping[var] += [tup_idx*(len(dependency_attributes)-1)+col_idx for col_idx in col_idxs]

        if var.isdigit() or isIPAddress(var) or len(value_index_mapping[var])>1:
            for idx in value_index_mapping[var]:
                flag_value[idx] = var 
        
    # print("value_index_mapping", value_index_mapping)
    # print("flag_value", flag_value)

    equality_pairs = analyze_summary(dependency)
    # print("equality_pairs", equality_pairs)
    
    check_valid_begin = time.time()
    egd_sql = convert_dependency_to_sql(type, dependency_tuples, Z_tablename, dependency_attributes, dependency_summary, dependency_summary_condition)
    check_valid_end = time.time()
    check_valid_time += (check_valid_end-check_valid_begin)
    print("egd_sql", egd_sql)

    check_valid_begin = time.time()
    cursor.execute(egd_sql)
    check_valid_end = time.time()
    check_valid_time += (check_valid_end-check_valid_begin)
    
    space_pool = {}
    where_clause_correspond_to_flag = {}

    row = cursor.fetchone()
    while row is not None:
        # check_valid_begin = time.time()
        if str(row) in checked_tuples:
            row = cursor.fetchone()
            # check_valid_end = time.time()
            # check_valid_time += (check_valid_end - check_valid_begin)
            continue
        else:
            checked_tuples.append(str(row))
        # check_valid_end = time.time()
        # check_valid_time += (check_valid_end - check_valid_begin)
        
        flag = None
        flag_list = []
        flag_where_clause = []
        where_clause = []
        current_tup_idx = 0
        for idx in sorted(list(flag_value.keys())):
            flag_list.append(row[idx])

            if idx // (len(dependency_attributes)-1) > current_tup_idx: # change to another tuple's where clause(only for two-tuple pattern) # TODO generalize to multi-tuple pattern
                flag_where_clause.append(where_clause.copy())
                current_tup_idx = idx // (len(dependency_attributes)-1)
                where_clause = []
            
            attr_idx = idx % (len(dependency_attributes)-1)
            where_clause.append("{} = '{}'".format(dependency_attributes[attr_idx], row[idx]))
        flag_where_clause.append(where_clause.copy())


        flag = "|".join(flag_list)

        if flag not in space_pool.keys():
            space_pool[flag] = {}
            where_clause_correspond_to_flag[flag] = flag_where_clause.copy() # generate where clause for each result who matches pattern

        for var in equality_pairs.keys():
            var_idx_in_attributes = value_index_mapping[var][0] % (len(dependency_attributes)-1)
            attribute_correspond_to_var = dependency_attributes[var_idx_in_attributes]

            if attribute_correspond_to_var not in space_pool[flag].keys():
                space_pool[flag][attribute_correspond_to_var] = {}

            var_idx_in_row = value_index_mapping[var][0]
            val_idx_in_row = value_index_mapping[var][0]
            if row[var_idx_in_row] in space_pool[flag][attribute_correspond_to_var].keys():
                space_pool[flag][attribute_correspond_to_var][row[var_idx_in_row]] += 1
            else:
                space_pool[flag][attribute_correspond_to_var][row[var_idx_in_row]] = 1
            
            if row[val_idx_in_row] in space_pool[flag][attribute_correspond_to_var].keys():
                space_pool[flag][attribute_correspond_to_var][row[val_idx_in_row]] += 1
            else:
                space_pool[flag][attribute_correspond_to_var][row[val_idx_in_row]] = 1

        row = cursor.fetchone()
    conn.commit()
    # print("space_pool", space_pool)
    # print("where_clause_correspond_to_flag", where_clause_correspond_to_flag)
    check_valid_begin = time.time()
    if len(space_pool.keys()) == 0: # if space_pool is empty, no tuples match to the pattern
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)
        return checked_tuples, False, check_valid_time, operate_time

    # generate set clause
    set_clause_correspond_to_flag = {}
    
    for flag in space_pool.keys():
        if flag not in set_clause_correspond_to_flag.keys():
            set_clause_correspond_to_flag[flag] = []
        
        for attr in space_pool[flag].keys():
            space = space_pool[flag][attr]

            # if space has values, set max number of value
            max_num_value = 0
            value = None

            max_num_var = 0
            var = None
            for v in space.keys():
                if v.isdigit() or isIPAddress(v):
                    if max_num_value < space[v]:
                        max_num_value = space[v]
                        value = v
                else:
                    if max_num_var < space[v]:
                        max_num_var = space[v]
                        var = v
            if value is not None:
                set_clause_correspond_to_flag[flag].append("{} = '{}'".format(attr, value))
            else:
                set_clause_correspond_to_flag[flag].append("{} = '{}'".format(attr, var))
        
    # print("set_clause_correspond_to_flag", set_clause_correspond_to_flag)

    summary_condition_clause = None
    if dependency_summary_condition is not None:
        summary_condition_clause = analyze_summary_condition(dependency, node_dict)
    
    # print("summary_condition_clause", summary_condition_clause)
    
    #generate update sqls 
    update_sqls = []
    for flag in set_clause_correspond_to_flag:
        set_clause = set_clause_correspond_to_flag[flag]

        for where_clause in where_clause_correspond_to_flag[flag]: 
            if summary_condition_clause is not None:
                where_clause += summary_condition_clause
            if (checkCondition(where_clause)):
                a = 2
                # update row
            upd_sql = "update {} set {} where {}".format(Z_tablename, ", ".join(set_clause), " and ".join(where_clause))
            if upd_sql not in update_sqls:
                update_sqls.append(upd_sql)

    # f1 = open("./sqls.txt", "a")
    # f2 = open("./sqls_time.txt", "a")
    does_update = False
    for sql in update_sqls:
        print(sql)
        # f1.write("{}\n".format(sql))
        operate_begin = time.time()
        cursor.execute(sql)
        operate_end = time.time()
        operate_time += (operate_end-operate_begin)
        # f2.write("{:.4f}\n".format(operate_end-operate_begin))
        if cursor.rowcount == 0:
            does_update = (does_update or False)
        else:
            does_update = (does_update or True)
    # f1.close()
    # f2.close()
    conn.commit()
    print(getCurrentTable(Z_tablename))

    return checked_tuples, does_update, check_valid_time, operate_time

def analyze_summary(dependency): #when summary is not empty
    dependency_summary = dependency["dependency_summary"]

    equality_pairs = {}
    #assume the operands of summary are variables. # TODO: generate it to variables and values.
    for summary in dependency_summary:
        items = summary.split()
        left_opd = items[0]
        right_opd = items[2]

        equality_pairs[left_opd] = right_opd

    return equality_pairs

def analyze_summary_condition(dependency, node_dict):
    dependency_attributes = dependency["dependency_attributes"]
    dependency_summary_condition = dependency["dependency_summary_condition"]
    summary_condition_clause = []
    for condition in dependency_summary_condition:
        # consider left opd is a variable, right opd is a value
        # TODO:generate it for two variables or left is a value and right is a variable
        items = condition.split()
        left_opd = items[0]
        opr = items[1]
        right_opd = items[2]

        for tup_idx in node_dict[left_opd]:
            for col_idx in node_dict[left_opd][tup_idx]:
                clause = "{} {} {}".format(dependency_attributes[col_idx], opr, right_opd)

                if clause not in summary_condition_clause:
                    summary_condition_clause.append(clause)
    return summary_condition_clause



def gen_repalce_mapping_for_egd(dependency, node_dict):
    # print("node_dict", node_dict)
    dependency_summary = dependency['dependency_summary']
    attributes = dependency['dependency_attributes']
    mapping_replace = {}
    for equation in dependency_summary:
        items = equation.split()
        left_opd = items[0]
        
        left_idxs = set()
        for tup_idx in node_dict[left_opd].keys():
            for col_idx in node_dict[left_opd][tup_idx]:
                res_idx = tup_idx * (len(attributes)-1) + col_idx # len(attributes)-1 minus condition column
                left_idxs.add(res_idx)
        
        right_opd = items[2]
        right_idxs = set()
        for tup_idx in node_dict[right_opd].keys():
            for col_idx in node_dict[right_opd][tup_idx]:
                res_idx = tup_idx * (len(attributes)-1) + col_idx
                right_idxs.add(res_idx)

        mapping_keys = set(mapping_replace.keys())

        if left_idxs.isdisjoint(mapping_keys) and right_idxs.isdisjoint(mapping_keys):
            replace_value = list(left_idxs)[0] # first left_idxs
            for idx in left_idxs:
                mapping_replace[idx] = replace_value
            for idx in right_idxs:
                mapping_replace[idx] = replace_value
        elif left_idxs.isdisjoint(mapping_keys) and not right_idxs.isdisjoint(mapping_keys):
            common_idxs = right_idxs.intersection(mapping_keys)
            c_idx = list(common_idxs)[0]
            replace_value = mapping_replace[c_idx]
            for idx in left_idxs:
                mapping_replace[idx] = replace_value
        elif not left_idxs.isdisjoint(mapping_keys) and right_idxs.isdisjoint(mapping_keys):
            common_idxs = left_idxs.intersection(mapping_keys)
            c_idx = list(common_idxs)[0]
            replace_value = mapping_replace[c_idx]
            for idx in right_idxs:
                mapping_replace[idx] = replace_value
    # print("mapping_replace", mapping_replace)
    return mapping_replace

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

def apply_E(sql, Z_tablename, gama_summary):
    # whether w in E(Z)
    check_cols = []
    for var_idx, var in enumerate(gama_summary):
        if var.isdigit() or isIPAddress(var):
            check_cols.append(var_idx)
    # print("check_cols", check_cols)

    gama_summary_item = "|".join([gama_summary[i] for i in check_cols])

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
        temp_sql = "create table temp as select distinct * from {} where f = '{}'".format(Z_tablename, flow_id[0])
        cursor.execute(temp_sql)
        conn.commit()
        # flow_condition = "t0.f = '{}'".format(flow_id[0])
        # sql += " and {}".format(flow_condition)
        # print(sql)
        # exit()
        query_begin = time.time()
        cursor.execute(sql)
        query_end = time.time()
        total_query_time += (query_end-query_begin)
        # print("query_begin", query_begin, query_end)
        # print(query_end-query_begin)

        results = cursor.fetchall()
        conn.commit()
        # print("results", results) 
        
        result_items = []
        for res_tup in results:
            res_item = "|".join([res_tup[i] for i in check_cols])
            result_items.append(res_item)

        check_begin = time.time()
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

