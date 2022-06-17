from copy import copy
import sys
from os.path import dirname, abspath
from unittest import result

root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)

import psycopg2
import time
from psycopg2.extras import execute_values
import databaseconfig as cfg
from tqdm import tqdm

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

def gen_z(T, W, W_attributes, W_attributes_datatypes, W_attributes_swtich=None):
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # cursor = conn.cursor()

    sql = "select * from {}".format(W)
    # print(sql)
    cursor.execute(sql)
    # row = cursor.fetchone()
    # while row is not None:
    #     print(row)
    #     row = cursor.fetchone()
    gama_table = cursor.fetchall()
    conn.commit()

    begin_time = time.time()
    Z_table = []
    z_tuple_num = 0
    n_idx = W_attributes.index('n')
    x_idx = W_attributes.index('x')
    for idx, tuple in enumerate(gama_table):
        '''
        # N is on, X is off
        '''
        w_attr_switch = copy(W_attributes_swtich) 
        w_attr_switch['n'] = True
        w_attr_switch['x'] = False
        
        sql = gen_sql_gama_tuple(tuple, T, W_attributes, W_attributes_datatypes, w_attr_switch)
        # print(sql)
        cursor.execute(sql) # get the first node of path
        results = cursor.fetchall()
        # print("results", results)
        next_node = None
        if len(results) == 1:
            next_node = results[0][x_idx]
        else:
            for row in results:
                if not is_variable(row[n_idx], W_attributes_datatypes[n_idx]):
                    next_node = row[x_idx]
                else:
                    continue
        
        # print("next_node", next_node)

        derived_tuple = list(tuple)
        derived_tuple[x_idx] = next_node
        
        z_tuple = gen_z_tuple(derived_tuple, z_tuple_num, idx, W_attributes, W_attributes_datatypes)
        Z_table.append(z_tuple)
        z_tuple_num += 1
        
        '''
        When the next_hop is a variable and the next_hop is equal to the tuple's X(next hop), done.
        '''
        while not is_variable(next_node, W_attributes_datatypes[x_idx]) and next_node != tuple[x_idx]:
            derived_tuple[n_idx] = next_node
            derived_tuple[x_idx] = 'd'
            sql = gen_sql_gama_tuple(derived_tuple, T, W_attributes, W_attributes_datatypes, W_attributes_swtich)
            # print(sql)
            cursor.execute(sql)
            # next_node = cursor.fetchone()[x_idx]
            results = cursor.fetchall()
            # print("results", results)
            if len(results) == 1:
                next_node = results[0][x_idx]
            else:
                for row in results:
                    if not is_variable(row[n_idx], W_attributes_datatypes[n_idx]):
                        next_node = row[x_idx]
                    else:
                        continue

            '''
            if the next_hop is a variable, it reaches the end of the path
            '''
            if is_variable(next_node, W_attributes_datatypes[x_idx]):
                derived_tuple[x_idx] = tuple[x_idx]
            else:
                derived_tuple[x_idx] = next_node

            z_tuple = gen_z_tuple(derived_tuple, z_tuple_num, idx, W_attributes, W_attributes_datatypes)
            Z_table.append(z_tuple)
            z_tuple_num += 1
            
    end_time = time.time()
    # print("Z_table", Z_table)
        
    # conn.close()
    return Z_table, end_time-begin_time

def gen_z_tuple(tuple, z_tuple_num, gama_index, attributes, attributes_datatypes):
    z_tuple = []
    for t_idx, val in enumerate(tuple):
        if attributes_datatypes[t_idx].lower() in FAURE_DATATYPES:
            z_tuple.append(val)
            # consider generated src and dst are variables
            # if val.isdigit():
            #     z_tuple.append(val)
            # else:
            #     if attributes[t_idx] == 'f':
            #         z_tuple.append("f{}".format(gama_index))
            #     elif attributes[t_idx] == 'src':
            #         z_tuple.append("s{}".format(z_tuple_num))
            #     elif attributes[t_idx] == 'dst':
            #         z_tuple.append("d{}".format(z_tuple_num))
            #     elif attributes[t_idx] == 'n':
            #         z_tuple.append("s{}".format(z_tuple_num))
            #     elif attributes[t_idx] == 'd':
            #         z_tuple.append("d{}".format(z_tuple_num))
            #     else:
            #         z_tuple.append(val)
        else:
            if 'condition' in attributes[t_idx]:
                # z_tuple.append("{"+ ", ".join(val) + "}")
                continue
            else:
                z_tuple.append(val)
    return z_tuple

def gen_sql_gama_tuple(gama_tuple, tablename, attributes, attributes_datatypes, attributes_swtich=None):
    """
    Parameters:
    -----------
    gama_tuple: tuple, one tuple of gama table. (f, src, dst, n, x)

    tablename: string. 

    attributes: list[string]. attributes for gama tuple.

    attributes_datatypes: list[string]. attributes datatypes

    attributes_switch: dict{attribute: Boolean}, default True. Whether cares augments when generating sql

    Returns:
    -----------
    sql: string, a SQL query
    """
    if attributes_swtich is None:
        for attr in attributes:
            attributes_swtich[attr] = True

    where_clauses = []
    for idx, val in enumerate(gama_tuple):
        if 'condition' in attributes_datatypes[idx]:
            continue

        '''
        if datatype of attribute is faure_datatype, the first charater of value is an alphabet, it is a variable.
        if the datatype is int4_faure and the value is a number, it should be determined in where clause.
        if the datatype is inet_faure and the value is an IP address, it should be determined in where clause.
        '''
        if attributes_datatypes[idx] in FAURE_DATATYPES:
            if attributes_datatypes[idx].lower() == INT4_FAURE:
                if val.isdigit() and attributes_swtich[attributes[idx]]:
                    where_clauses.append("{} = '{}'".format(attributes[idx], val))
            else:
                if isIPAddress(val) and attributes_swtich[attributes[idx]]:
                    where_clauses.append("{} = '{}'".format(attributes[idx], val))
        else:
            if attributes_datatypes[idx].lower() in DIGIT_RELATED_TYPES:
                where_clauses.append("{} = {}".format(attributes[idx], val))
            elif attributes_datatypes[idx].lower() in STR_RELATED_TYPES:
                where_clauses.append("{} = '{}'".format(attributes[idx], val))

    sql = "select * from {} where {}".format(tablename, ' and '.join(where_clauses))

    return sql

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

# def apply_dependency(type, Z, Z_attributes, dependency, dependency_summary, dependency_attributes, dependency_condition=None):
#     # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
#     # cursor = conn.cursor()
#     operate_time = 0
#     if type.lower() == 'tgd':
#         tgd_sql = convert_dependency_to_sql(type, dependency, Z, dependency_attributes, dependency_summary, dependency_condition)
#         cursor.execute(tgd_sql)

#         matched_tuples = []
#         results = cursor.fetchall()
#         # print(results)
#         while len(results) > 0:
#             for idx, valid_match in enumerate(results):
#                 if "|".join(valid_match) in matched_tuples:
#                     results.pop(idx)
#                 else:
#                     matched_tuples.append("|".join(valid_match))

#             if len(results) > 0:
#                 # print("insert", results)
#                 begin_time = time.time()
#                 execute_values(cursor, "insert into {} values %s".format(Z), results)
#                 end_time = time.time()
#                 operate_time += end_time - begin_time
#                 # conn.commit()
                
#             else:
#                 # if all matches are already checked, the algorithm is done
                
#                 break
        
#             cursor.execute(tgd_sql)
#             results = cursor.fetchall()
#         # print("tgd Done!")
#         conn.commit()

#     elif type.lower() == 'egd':
#         node_dict, _ = analyze_dependency(dependency, dependency_attributes, Z)
#         # print("node_dict", node_dict)

#         mapping_replace = {}
#         for equation in dependency_summary:
#             items = equation.split()
#             left_opd = items[0]

            
#             left_idxs = set()
#             for tup_idx in node_dict[left_opd].keys():
#                 for col_idx in node_dict[left_opd][tup_idx]:
#                     res_idx = tup_idx * len(Z_attributes) + col_idx
#                     left_idxs.add(res_idx)
            
#             right_opd = items[2]
#             right_idxs = set()
#             for tup_idx in node_dict[right_opd].keys():
#                 for col_idx in node_dict[right_opd][tup_idx]:
#                     res_idx = tup_idx * len(Z_attributes) + col_idx
#                     right_idxs.add(res_idx)

#             mapping_keys = set(mapping_replace.keys())

#             if left_idxs.isdisjoint(mapping_keys) and right_idxs.isdisjoint(mapping_keys):
#                 replace_value = list(left_idxs)[0] # first left_idxs
#                 for idx in left_idxs:
#                     mapping_replace[idx] = replace_value
#                 for idx in right_idxs:
#                     mapping_replace[idx] = replace_value
#             elif left_idxs.isdisjoint(mapping_keys) and not right_idxs.isdisjoint(mapping_keys):
#                 common_idxs = right_idxs.intersection(mapping_keys)
#                 c_idx = list(common_idxs)[0]
#                 replace_value = mapping_replace[c_idx]
#                 for idx in left_idxs:
#                     mapping_replace[idx] = replace_value
#             elif not left_idxs.isdisjoint(mapping_keys) and right_idxs.isdisjoint(mapping_keys):
#                 common_idxs = left_idxs.intersection(mapping_keys)
#                 c_idx = list(common_idxs)[0]
#                 replace_value = mapping_replace[c_idx]
#                 for idx in right_idxs:
#                     mapping_replace[idx] = replace_value
        
#         # print("mapping_replace", mapping_replace)

#         egd_sql = convert_dependency_to_sql(type, dependency, Z, dependency_attributes, dependency_summary, dependency_condition)

#         cursor.execute(egd_sql)
#         results = cursor.fetchall()

#         # print("gen update sql")        
#         update_sqls = []
#         for valid_match in results:
#             set_clause = []
#             where_clause = []
#             for var_idx, var in enumerate(valid_match):
#                 col_idx = var_idx % len(Z_attributes)
#                 if var_idx in mapping_replace.keys():
#                     set_clause.append("{} = '{}'".format(Z_attributes[col_idx], valid_match[mapping_replace[var_idx]]))
#                 where_clause.append("{} = '{}'".format(Z_attributes[col_idx], var))

#                 if col_idx == len(Z_attributes) - 1:
#                     sql = "update {} set {} where {}".format(Z, ", ".join(set_clause), " and ".join(where_clause))
#                     if sql not in update_sqls:
#                         update_sqls.append(sql)
#                     set_clause.clear()
#                     where_clause.clear()
#         # print("update_sqls", update_sqls)
#         # print("begin update")
#         begin_time = time.time()
#         # print("len(upd_sqls)", len(update_sqls))
#         for sql in update_sqls:
#             # print(sql)
#             cursor.execute(sql)
#         end_time = time.time()
#         # print("upd time", end_time-begin_time)
#         operate_time += end_time - begin_time
#         conn.commit()

#         # print('egd')
#     else:
#         print("wrong type!")

#     return operate_time

def apply_dependency(dependency, Z, checked_tuples):
    # conn = psycopg2.connect(host=cfg.postgres['host'], database=cfg.postgres['db'], user=cfg.postgres['user'], password=cfg.postgres['password'])
    # cursor = conn.cursor()
    type = dependency['dependency_type']
    dependency_tuples = dependency['dependency_tuples']
    dependency_attributes = dependency['dependency_attributes']
    dependency_summary = dependency['dependency_summary']
    dependency_summary_condition = dependency['dependency_summary_condition']

    does_updated = True
    operate_time = 0
    check_valid_time = 0
    if type.lower() == 'tgd':
        tgd_sql = convert_dependency_to_sql(type, dependency_tuples, Z, dependency_attributes, dependency_summary, dependency_summary_condition)
        check_valid_begin = time.time()
        cursor.execute(tgd_sql)
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)

        # matched_tuples = []
        results = cursor.fetchall()
        conn.commit()
        # print(results)

        inserted_tuples = []
        check_valid_begin = time.time()
        for valid_match in results:
            if str(valid_match) in checked_tuples:
                continue
            else:
                inserted_tuples.append(valid_match)
                checked_tuples.append(str(valid_match))

        if len(inserted_tuples) > 0:
            check_valid_end = time.time()
            check_valid_time += (check_valid_end - check_valid_begin)
            # print("insert", results)
            begin_time = time.time()
            execute_values(cursor, "insert into {} values %s".format(Z), inserted_tuples)
            end_time = time.time()
            operate_time += (end_time - begin_time)
            conn.commit()
        else:  # if all matches are already checked, the algorithm is done
            does_updated = False
            check_valid_end = time.time()
            check_valid_time += (check_valid_end - check_valid_begin)
            conn.commit()
            return  checked_tuples, does_updated, check_valid_time, operate_time
    elif type.lower() == 'egd':
        node_dict, _ = analyze_dependency(dependency_tuples, dependency_attributes, Z)
        # print("node_dict", node_dict)

        egd_sql = convert_dependency_to_sql(type, dependency_tuples, Z, dependency_attributes, dependency_summary, dependency_summary_condition)

        check_valid_egd_begin = time.time()
        cursor.execute(egd_sql)
        check_valid_egd_end = time.time()
        check_valid_time += (check_valid_egd_end - check_valid_egd_begin)

        if len(dependency_summary) == 0: # if dependency summary is empty, the matched tuples are deleted
            operate_time += (check_valid_egd_end - check_valid_egd_begin)
            check_valid_begin = time.time()
            if cursor.rowcount == 0:
                does_updated = False
            check_valid_end = time.time()
            check_valid_time += (check_valid_end - check_valid_begin)
            conn.commit()
            return checked_tuples, does_updated, check_valid_time, operate_time
        else:
            results = cursor.fetchall()
            conn.commit()
            
            mapping_replace = gen_repalce_mapping_for_egd(dependency, node_dict)
            # print("mapping_replace", mapping_replace)
            updated_tuples = []
            for valid_match in results:
                if str(valid_match) in checked_tuples:
                    continue
                else:
                    updated_tuples.append(valid_match)
                    checked_tuples.append(str(valid_match))

            summary_condition_mapping = {}
            if dependency_summary_condition is not None:
                for condition in dependency_summary_condition:
                    items = condition.split()

                    left_opd = items[0]
                    opr = items[1]
                    right_opd = items[2]

                    # consider left opd is a variable, right opd is a value
                    # TODO:generate it for two variables or left is a value and right is a variable
                    tup_idx = list(node_dict[left_opd].keys())[0]
                    col_idx = node_dict[left_opd][tup_idx][0]

                    res_idx = tup_idx*(len(dependency_attributes)-1) + col_idx
                    summary_condition_mapping[res_idx] = (opr, right_opd)

            # print("gen update sql")        
            set_clause = []
            where_clause = []

            
            where_clause_set_clause_mapping = {}
            if len(updated_tuples) > 0:
                for upd_tuple in updated_tuples:
                    # print("upd_tuple", upd_tuple)
                    
                    where_key_list = []
                    set_key_list = []
                    for var_idx, var in enumerate(upd_tuple):
                        # print("var_idx", var_idx)
                        # print("var", var)
                        # print("upd_tuple", upd_tuple)
                        col_idx = var_idx % (len(dependency_attributes)-1)
                        if var_idx in mapping_replace.keys():
                            set_clause.append("{} = '{}'".format(dependency_attributes[col_idx], upd_tuple[var_idx]))
                            # set_clause.append("{} = '{}'".format(dependency_attributes[col_idx], upd_tuple[mapping_replace[var_idx]]))

                        if dependency_attributes[col_idx] in dependency["dependency_cares_attributes"]:
                            where_clause.append("{} = '{}'".format(dependency_attributes[col_idx], var))

                        if col_idx == len(dependency_attributes) - 2: # minus condition column
                            '''
                            add summary conditions for update SQLs
                            '''
                            cond_idxs = summary_condition_mapping.keys()
                            for idx in cond_idxs:
                                if idx <= col_idx:
                                    where_clause.append("{} {} {}".format(dependency_attributes[idx], summary_condition_mapping[idx][0], summary_condition_mapping[idx][1]))
                            
                            where_key = " and ".join(where_clause)
                            set_key = ", ".join(set_clause)
                            where_key_list.append(where_key)
                            set_key_list.append(set_key)
 
                            # print("where_key", where_key)
                            # print("set_key", set_key)

                            set_clause.clear()
                            where_clause.clear()
                    
                    # combine several where key for a updated tuple 
                    combine_where_key_list = "|".join(where_key_list)

                    if combine_where_key_list not in where_clause_set_clause_mapping.keys():
                        where_clause_set_clause_mapping[combine_where_key_list] = {}
                    
                    # count set_key for a where_clause
                    for set_key in set_key_list:
                        if set_key in where_clause_set_clause_mapping[combine_where_key_list].keys():
                            where_clause_set_clause_mapping[combine_where_key_list][set_key] += 1
                        else:
                            where_clause_set_clause_mapping[combine_where_key_list][set_key] = 1

                            

                # print("where_clause_set_clause_mapping", where_clause_set_clause_mapping)
                update_sqls = []
                
                for where_key in where_clause_set_clause_mapping.keys():
                    set_key = None
                    max_num = 0
                    set_keys = where_clause_set_clause_mapping[where_key].keys()
                    for k in set_keys:
                        if where_clause_set_clause_mapping[where_key][k] > max_num:
                            set_key = k
                            max_num = where_clause_set_clause_mapping[where_key][k]
                    
                    where_key_list = where_key.split("|")
                    for where_key in where_key_list:
                        sql = "update {} set {} where {}".format(Z, set_key, where_key)
                        if sql not in update_sqls:
                            update_sqls.append(sql)
                    
            else:
                does_updated = False
                conn.commit()
                return checked_tuples, does_updated, check_valid_time, operate_time
                
            temp_does_updated = False
            for sql in update_sqls:
                # print(sql)
                operate_beign = time.time()
                cursor.execute(sql)
                operate_end = time.time()
                operate_time += (operate_end - operate_beign)
                
                check_valid_begin = time.time()
                if cursor.rowcount == 0:
                    temp_does_updated = (temp_does_updated or False)
                else:
                    temp_does_updated = (temp_does_updated or True)
                check_valid_end = time.time()
                check_valid_time += (check_valid_end - check_valid_begin)

            does_updated = temp_does_updated
            conn.commit()
    else:
        check_valid_begin = time.time()
        does_updated = False
        print("wrong type!")
        check_valid_end = time.time()
        check_valid_time += (check_valid_end - check_valid_begin)
    conn.commit()
    return checked_tuples, does_updated, check_valid_time, operate_time

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

def apply_E(sql, gama_summary):
    
    query_begin = time.time()
    cursor.execute(sql)
    query_end = time.time()
    # print(query_end-query_begin)

    results = cursor.fetchall()
    conn.commit()
    # print("results", results) 

    # whether w in E(Z)
    check_cols = []
    for var_idx, var in enumerate(gama_summary):
        if var.isdigit() or isIPAddress(var):
            check_cols.append(var_idx)
    # print("check_cols", check_cols)
    gama_summary_item = "|".join([gama_summary[i] for i in check_cols])
    check_begin = time.time()
    answer = False
    for res_tup in results:
        res_item = "|".join(res_tup[i] for i in check_cols)
        if res_item == gama_summary_item:
            # print("gama_summary_item", gama_summary_item)
            # print("res_item", res_item)
            answer = True
            break
    check_end = time.time()
    conn.commit()
    return answer, query_end-query_begin, check_end-check_begin

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
    T = [
        ('f', 's1', 'd1', 's', '1', '{}'),
        ('f', 's2', 'd2', '1', '2', '{}'),
        ('f', 's3', 'd3', '2', 'd', '{}')
    ]
    T_summary = ['f', 's', 'd']
    T_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    T_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    E = (T, T_summary)

    # 1.2 => 4, 1.1 =>3, 1.3 => 5, 1.4 =>6
    W = [
        ('f1', '4', '5', '4', '1', '{}'),
        ('f2', '3', '6', '3', '6', '{}')
    ]
    W_summary = ['f3', '4', '6']
    W_attributes = ['f', 'src', 'dst', 'n', 'x', 'condition']
    W_attributes_datatypes = ['int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'int4_faure', 'text[]']
    Gama = (W, W_summary)

    load_table(T_attributes, T_attributes_datatypes, "T", T)
    load_table(W_attributes, W_attributes_datatypes, "W", W)

    W_attributes_switch = {
        'f': True,
        'src': False,
        'dst': False,
        'n': True,
        'x': True,
    }

    source_hosts = ['3', '4']
    dest_hosts = ['5', '6']

    Z_table = gen_z("T", "W", W_attributes, W_attributes_datatypes, W_attributes_switch)
    Z_attributes = ['f', 'src', 'dst', 'n', 'x']
    Z_attributes_datatypes = ['text', 'text', 'text', 'text', 'text']
    load_table(Z_attributes, Z_attributes_datatypes, "Z", Z_table)

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

