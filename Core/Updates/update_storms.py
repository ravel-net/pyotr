import sys
from os.path import dirname, abspath, join
root = dirname(dirname(dirname(abspath(__file__))))
print(root)
sys.path.append(root)
import psycopg2
from psycopg2.extras import execute_values
import databaseconfig as dbconfig
from utils.logging import timeit
import time
from Backend.reasoning.Z3.z3smt import z3SMTTools


def create_db_connection():
    host = dbconfig.postgres['host']
    user = dbconfig.postgres['user']
    password = dbconfig.postgres['password']
    db = dbconfig.postgres['db']

    conn = psycopg2.connect(host=host, user=user, password=password, database=db)

    return conn

def shut_down_db(conn):
    conn.close()

def merge_sorted(conn, existing_tablename, delta_tablename):
    """
    Merge sorted(PostgreSQL-based)

    merge a delta c-table into a exsiting c-table 

    c-table schema: C(priority, header, action, condition)
    Attributes:  priority - constant
                header - c-variable
                action - constant
            

    Parameters:
    ------------
    conn: instance of psycopg2.connect()
        the connection of PostgreSQL

    existing_tablename: string
        the tablename of a existing c-table

    delta_tablename: string
        the tablename of a delta c-table

    Returns:
    -----------
    sorted_tuples: tuples
        the list of tuples sorted by attribute `priority`

    """
    sorted_tuples = []

    '''
    merge two tables
    '''
    sql = "INSERT INTO {existing_table} SELECT * FROM {delta_table} ON CONFLICT DO NOTHING;".format(existing_table=existing_tablename, delta_table=delta_tablename)
    cursor = conn.cursor()
    cursor.execute(sql)

    conn.commit()
    '''
    get sorted tuples w.r.t attribute `priority`
    '''
    cursor.execute("select * from {existing_table} order by priority desc;".format(existing_table=existing_tablename))
    sorted_tuples = cursor.fetchall()

    conn.commit() 

    return sorted_tuples


def transform_conditions(sorted_tuples):
    """
    transform conditions according to the priority.
    The value range of priority is [0, 3], 3 is the highest priority, 0 is the lowest.

    1. keeping the condition of tuple in which the value of priority is 3 as it and tracing the conditions
    2. For the condition of the tuple in which the value of priority is lower than 3, add the negation of the disjunction of all conditions of the highest-priority tuples. Trace the condition
    3. iterate all tuples

    psceudocode
    transform_conditions:
        input: sorted_tuples, array
        output: transformed_tuples

        transformed_tuples := empty array
        traced_conditions := empty array

        for tp in sorted_tuples
            if tp.priority is 3
                traced_conditions = traced_conditions \/ [conjunction of tp.condition]
            else:
                tobe_transformed_condition = conjunction of tp.condition
                transformed_condition = tobe_transformed_condition /\ negation of traced_conditions
                traced_conditions = transformed_condition
                tp.condition = transformed_condition
                transformed_tuples <- tp
            end if
        end for
    
    Parameters:
    -----------
    sorted_tuples: list
        A list of tuples sorted by attribute `priority`

    Returns:
    -----------
    transformed_tuples: list
        A list of tuples in which condition is transformed 
    """
    traced_conditions = ""
    transformed_tuples = []

    temp_conditions = []
    current_priority = None
    for tp in sorted_tuples:
        # print("\ntp", tp)
        # print("temp_conditions", temp_conditions)
        

        transformed_tp = list(tp)
        tp_priority = tp[0]
        tp_condition = tp[-1]

        if current_priority != tp_priority:
            if len(temp_conditions) == 1:
                traced_conditions = temp_conditions[0]
            elif len(temp_conditions) > 1:
                traced_conditions = "Or({})".format(", ".join(temp_conditions))
            temp_conditions = []
            current_priority = tp_priority

        # print("traced_conditions", traced_conditions)
        
        tobe_transformed_condition = None
        if len(tp_condition) == 0:
            tobe_transformed_condition = ""
        elif len(tp_condition) == 1:
            tobe_transformed_condition = tp_condition[0]
        else:
            tobe_transformed_condition = "And({})".format(", ".join(tp_condition))

        transformed_condition = None
        if tobe_transformed_condition != "" and traced_conditions != "":
            transformed_condition = "And({}, Not({}))".format(tobe_transformed_condition, traced_conditions)
        elif tobe_transformed_condition == "" and traced_conditions != "":
            transformed_condition = "Not({})".format(traced_conditions)
        elif tobe_transformed_condition != "" and traced_conditions == "":
            transformed_condition = tobe_transformed_condition
        
        if transformed_condition is None:
            transformed_tp[-1] = []
            temp_conditions = []
        else:
            transformed_tp[-1] = [transformed_condition]
            temp_conditions.append(transformed_condition)
        transformed_tuples.append(transformed_tp)

        # print("transformed_tp", transformed_tp)

    return transformed_tuples  


def aggregate_condition_wrt_action(conn, transformed_tuples, tablename):
    """
    aggregate condition for tuples in which the value action are the same
    then, restore the aggregated tuples into a c-table

    Parameters:
    conn: instance of psycopg2.connect()
        the connection of PostgreSQL

    transformed_tuples: list
        A list of tuples in which condition is transformed 

    tablename: string
        the tablename of a existing c-table
    
    """        
    action_conditions_mapping = {}
    action_header_mapping = {}
    headervariables_mappings = {}
    always_true_action = []
    for tp in transformed_tuples:
        # print("\ntp", tp)
        tp_header = tp[1]
        tp_action = tp[2]

        if tp_action in always_true_action:
            continue

        tp_condition = tp[-1]
        # print(tp_condition)
        if tp_action in action_conditions_mapping:

            target_header_var = action_header_mapping[tp_action]
            headervariables_mappings[tp_header] = target_header_var
            # to_be_replaced_vars = []
            # if header_var in headervariables_mappings.keys():
            #     headervariables_mappings[header_var].append(tp_header)
            #     to_be_replaced_vars = headervariables_mappings[header_var]
            # else:
            #     headervariables_mappings[header_var] = [tp_header]
            #     to_be_replaced_vars.append(tp_header)
            
            # print("target var", target_header_var)
            # print("to_be_replaced_vars", headervariables_mappings)

            if len(tp_condition) > 1:
                cond = "And({})".format(", ".join(tp_condition))
                action_conditions_mapping[tp_action].append(cond)
            elif len(tp_condition) == 1:
                cond = tp_condition[0]
                action_conditions_mapping[tp_action].append(cond)
            else:
                always_true_action.append(tp_action)
            # print(tp_condition)
        else:
            if len(tp_condition) > 1:
                action_conditions_mapping[tp_action] = ["And({})".format(", ".join(tp_condition))]
            elif len(tp_condition) == 1:
                action_conditions_mapping[tp_action] = tp_condition
            else:
                always_true_action.append(tp_action)
            action_header_mapping[tp_action] = tp_header

    res_tuples = []
    for action in action_conditions_mapping.keys():
        header = action_header_mapping[action]
        if action in always_true_action:
            res_tuples.append((header, action, []))
        else:
            cond = action_conditions_mapping[action]
            processed_cond = None
            if len(cond) == 0:
                processed_cond = cond
            elif len(cond) == 1:
                processed_cond = cond
                processed_cond = [replace_vars(processed_cond[0], headervariables_mappings)]
            else:
                processed_cond = ["Or({})".format(", ".join(cond))]
                processed_cond = [replace_vars(processed_cond[0], headervariables_mappings)]
            res_tuples.append((header, action, processed_cond))
            

    
    cursor = conn.cursor()
    cursor.execute("drop table if exists {}".format(tablename))
    sql = "create table {}(header int4_faure, action text, condition text[])".format(tablename)
    cursor.execute(sql)

    sql = "insert into {} values %s".format(tablename)
    execute_values(cursor, sql, res_tuples)

    conn.commit()

def replace_vars_naive(condition, headervariables_mappings):
    for var in headervariables_mappings.keys():
        target_var = headervariables_mappings[var]
        condition = condition.replace(var, target_var)
    return condition

def replace_vars(condition, headervariables_mappings):
    # for target_var in headervariables_mappings.keys():
    #     tobe_replaced_var_list = headervariables_mappings[target_var]

    replaced_condition = ""
    ptr = 0
    scanned_position = 0
    while ptr < len(condition):
        if condition[ptr: ptr+2] == "==":  # assume currently operator only is ==
            back_ptr = ptr
            # print("ptr", ptr)
            while back_ptr > 0 and condition[back_ptr] != '(' and condition[back_ptr] != ",":
                back_ptr -= 1
            # print("back_ptr", back_ptr)

            var = None
            if back_ptr == 0:
                replaced_condition += condition[scanned_position: back_ptr]
                var = condition[back_ptr: ptr].strip()
            else:
                replaced_condition += condition[scanned_position: back_ptr + 1]
                var = condition[back_ptr+1: ptr].strip()

            # print("var", var)
            # print("replaced_condition", replaced_condition)
            if var in headervariables_mappings.keys():
                target_var = headervariables_mappings[var]
                replaced_condition += target_var
            else:
                replaced_condition += var
            replaced_condition += " "
            replaced_condition += condition[ptr: ptr+2]
            ptr += 2
            scanned_position = ptr
            # print("replaced_condition", replaced_condition)
            
            # print("scanned_position", scanned_position)
        else:
            ptr += 1
    
    if scanned_position < len(condition):
        replaced_condition += condition[scanned_position:]
    return replaced_condition



def update_storms(conn, existing_tablename, delta_tablename, output_tablename):
    # step 1: merge sorted
    sorted_tuples = merge_sorted(conn, existing_tablename, delta_tablename)

    transformed_tuples = transform_conditions(sorted_tuples)

    # input()
    aggregate_condition_wrt_action(conn, transformed_tuples, output_tablename)
