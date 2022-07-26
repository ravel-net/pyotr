from array import array

from matplotlib.pyplot import table

def reorder_closure_group(group):
    ordered_group = []

    if len(group) == 1:
        return group

    for i in range(len(group)):
        n1 = group[i][0]
        n2 = group[i][1]
        if n1 != n2:
            ordered_group.append(group[i])
        else:
            for j in range(len(ordered_group)-1):
                n3 = ordered_group[j][1]
                n4 = ordered_group[j+1][0]
                if n3 == n1 and n4 == n2:
                    ordered_group.insert(j+1, group[i])
                    break
    # print(ordered_group)
    return ordered_group

def gen_splitjoin_sql(group, tablename, table_attributes, summary):
    """
    Generate all SQLs when split a multi-join SQL into several subjoins

    Parameters:
    -----------
    group: list[tuple]
        a closure group
    
    tablename: string
        the name of data instance table
    
    table_attributes: list[string]
        the attributes of data instance table
    
    summary: list
        the summary of the query

    Returns:
    ----------
    sqls: list[string]
        A list of SQLs that are subjoin SQLs
    
    output_tables: list[string]
        A list of table names. Each table is the intermediate resulting table of the subjoin SQL.
    """
    sqls = []
    output_tables = []
    comp_link = ""
    sql = ""
    contains_condition = False
    if "condition" in table_attributes:
        contains_condition = True

    if len(group) == 1:
        tables = [tablename, None]
        tables_attributes = [table_attributes, None]

        sql = general_convert_tableau_to_sql(group, tables, tables_attributes, True, contains_condition, summary, None, None)
        sqls.append(sql)
        output_tables.append("R1")
        return sqls, output_tables
    elif len(group) == 2: # do not contains composition view but is final join
        tables = [tablename, tablename]
        tables_attributes = [table_attributes, table_attributes]
        sql = general_convert_tableau_to_sql(group, tables, tables_attributes, True, contains_condition, summary, None, None) # the final join does not need comp_link_attributes and comp_link_attributes_alias
        sqls.append(sql)
        output_tables.append("R1_2")
        return sqls, output_tables

    tables_attributes = None
    for idx, link in enumerate(group):
        if idx == 0:
            continue
        elif idx == 1:
            links = [group[idx-1], link]
            tables = [tablename, tablename]
            tables_attributes = [table_attributes, table_attributes]
            node_dict = generate_node_dict(links)
            comp_link, comp_link_attributes, comp_link_attributes_alias = generate_composite_link(node_dict, tables.copy(), tables_attributes, contains_condition)
            
            sql = general_convert_tableau_to_sql(links, tables, tables_attributes, False, contains_condition, summary, comp_link_attributes, comp_link_attributes_alias)

            tables_attributes = [comp_link_attributes_alias, table_attributes]
            
        else:
            links = [comp_link, link]
            tables = ["R1_{}".format(idx), tablename]
            node_dict = generate_node_dict(links)
            comp_link, comp_link_attributes, comp_link_attributes_alias = generate_composite_link(node_dict, tables.copy(), tables_attributes, contains_condition)

            if idx == len(group) - 1: # contains composition view and is final join
                sql = general_convert_tableau_to_sql(links, tables, tables_attributes, True, contains_condition, summary, comp_link_attributes, comp_link_attributes_alias)
            else:
                sql = general_convert_tableau_to_sql(links, tables, tables_attributes, False, contains_condition, summary, comp_link_attributes, comp_link_attributes_alias)
            
            tables_attributes = [comp_link_attributes_alias, table_attributes]

        output_tables.append("R1_{}".format(idx+1))
        sqls.append(sql)
    return sqls, output_tables

def generate_node_dict(tableau):
    """
    Generate node dict for tableau.

    Parameters:
    -----------
    tableau: list
        A tableau

    Returns:
    ----------
    node_dict: dict
        the position information of each value in the tableau.The format is 
        {   
            value1: 
                {   
                    tuple_idx1: [column_idx1, column_idx2, ...], 
                    tuple_idx2: [...], 
                    ...
                }, 
            value2:{...}, 
            ...
        } 
        For example, the node_dict is {1:{0:[0]}, 2:{0:[1], 1:[0], 3:{2:[1]}, 'x':{1:[1]}}}
          | n1  n2   
        --+------------
          | 1    2
        T | 2    x   
          | x    3
        --+-----------
        u | 1    3
    """
    node_dict = {}
    for idx, tup in enumerate(tableau):
        for i in range(len(tup)):
            var = tup[i]
            # print(var)
            # print(type(var))
            if type(var) == list or type(var) == array or var == '{}' or var == '': # skip condition column
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
    # print("node_dict", node_dict)
    return node_dict

def generate_composite_link(node_dict, tables, tables_attributes, contains_condition):
    """
    Generate the headers of intermediate resulting table after applying subjoin

    Parameters:
    -----------
    node_dict: dict
        return by `generate_node_dict()`
    
    tables: list
        list of table names
    
    tables_attributes:
        list of attributes list for each table
    
    contains_condition: boolean
        whether the attributes of data instance contains condition column 
    
    Returns:
    ----------
    composite_link: list
        the selected values after applying subjoin
    
    comp_link_attributes:
        the select clause of subjoin
    
    comp_link_attributes_alias:
        the alias of each select clause of subjoin
    """
    # print("tables_attributes", tables_attributes)
    if tables[0] == tables[1]: # defualt 2 tables
        tables[0] = tables[0]+'0'
        tables[1] = tables[1]+'1'

    composite_link = []
    composite_link_attributes = []
    composite_link_attributes_alias = []
    attr_mapping = {}
    for var in node_dict.keys():
        tup_idx = list(node_dict[var].keys())[0]
        col_idx = node_dict[var][tup_idx][0]

        attr_name = tables_attributes[tup_idx][col_idx]
        composite_link_attributes.append("t{}.{}".format(tup_idx, attr_name))

        if '___' in tables_attributes[tup_idx][col_idx]:
            temp = tables_attributes[tup_idx][col_idx].split('___')[1]
            attr_name = temp.split('__')[0]

        t = tables[tup_idx]

        if t in attr_mapping.keys():
            if attr_name in attr_mapping[t].keys():
                attr_mapping[t][attr_name] += 1
            else:
                attr_mapping[t][attr_name] = 0
        else:
            attr_mapping[t] = {}
            attr_mapping[t][attr_name] = 0

        composite_link_attributes_alias.append("{}___{}__{}".format(t, attr_name, attr_mapping[t][attr_name]))
        composite_link.append(var)
    # for condition column
    if contains_condition:
        composite_link.append("")
        composite_link_attributes.append("condition")
        composite_link_attributes_alias.append("condition")
    # print("composite_link", composite_link)
    # print("composite_link_attributes", composite_link_attributes)
    # print("composite_link_attributes_alias", composite_link_attributes_alias)
    return composite_link, composite_link_attributes, composite_link_attributes_alias

def general_convert_tableau_to_sql(tableau, tables, tableau_attributes, is_final_join, contains_condition, summary, comp_link_attributes, comp_link_attributes_alias):
    """
    Convert tableau to SQL

    Parameters:
    -----------
    tableau: list
        one or two tuples by default. 
    
    tables: list
        one or two table names. first table name is the table name of the first line of `tableau`, second table name is the table name of the second line of `tableau`
    
    tableau_attributes: list[list]
        one or two list of table attributes. 
    
    is_final_join: boolean
        Whether it is a final subjoin
    
    contains_condition: boolean
        whether the attributes of data instance contains condition column
    
    summary: list
        the summary of the query
    
    comp_link_attributes:
        the select clause of subjoin
    
    comp_link_attributes_alias:
        the alias of each select clause of subjoin

    Returns:
    ----------
    sql: string
        the subjoin SQL
    
    """
    # print("links", tableau)
    node_dict = generate_node_dict(tableau)
    # print("node_dict", node_dict)
    conditions = []
    for var in node_dict.keys():
        if var.isdigit() or isIPAddress(var):
            for tup_idx in node_dict[var].keys():
                for i in node_dict[var][tup_idx]:
                    conditions.append("{}.{} = '{}'".format("t{}".format(tup_idx), tableau_attributes[tup_idx][i], var))
        # elif isIPAddress(var):
        #     for tup_idx in node_dict[var].keys():
        #         for i in range(len(node_dict[var][tup_idx])):
        #             conditions.append("{}.{} = '{}'".format("t{}".format(tup_idx), tableau_attributes[tup_idx][i], var))
        else:
            last_tup_idx = None
            for tup_idx in node_dict[var].keys():
                if last_tup_idx is None:
                    last_tup_idx = tup_idx
                else:
                    # print("var", var)
                    # print("tableau_attributes", tableau_attributes)
                    one_col_idx_of_var_in_last_tup = node_dict[var][last_tup_idx][0]
                    # print("last_tup_idx", last_tup_idx)
                    # print("one_col_idx_of_var_in_last_tup", one_col_idx_of_var_in_last_tup)
                    one_col_idx_of_var_in_current_tup = node_dict[var][tup_idx][0]
                    # print("tup_idx", tup_idx)
                    # print("one_col_idx_of_var_in_current_tup", one_col_idx_of_var_in_current_tup)
                    conditions.append("{}.{} = {}.{}".format("t{}".format(last_tup_idx), 
                                                                            tableau_attributes[last_tup_idx][one_col_idx_of_var_in_last_tup], 
                                                                            "t{}".format(tup_idx), 
                                                                            tableau_attributes[tup_idx][one_col_idx_of_var_in_current_tup]))
                
                for i in range(len(node_dict[var][tup_idx])-1):
                    conditions.append("{}.{} = {}.{}".format("t{}".format(tup_idx), tableau_attributes[tup_idx][i], "t{}".format(tup_idx), tableau_attributes[tup_idx][i+1]))
    # print("conditions", conditions)
    

    sql = None
    if is_final_join:
        if not contains_condition: # for the data instance is constant
            select_clause = []
            for val in summary:
                select_clause.append('{} as "{}"'.format(val, val))
            sql = "select {} from {} {}, {} {}".format(", ".join(select_clause), tables[0], "t0", tables[1], "t1")
        else:
            sql = "select {} from {} {}, {} {}".format(", ".join(summary), tables[0], "t0", tables[1], "t1")
    else:
        select_clause = []
        for i in range(len(comp_link_attributes)):
            if comp_link_attributes[i] == 'condition':
                continue
            select_clause.append("{} {}".format(comp_link_attributes[i], comp_link_attributes_alias[i]))
        sql = "select {} from {} {}, {} {}".format(", ".join(select_clause), tables[0], "t0", tables[1], "t1")

    if len(conditions) != 0:
        sql += " where {}".format(" and ".join(conditions))
    # print(sql)
    # print("------------------------\n")
    return sql

def isIPAddress(value):
    if len(value.strip().split('.')) == 4:
        return True
    else:
        return False

def convert_tuples_to_sql(tuples, tablename1, t1_rename, tablename2, t2_rename, includeCompView, is_final_join, summary):
    """
    includeCompView: composition view(e.g. R1_2)
    is_final_join: whether it is a final join
    """
    cols = []
    constraints = []
    if len(tuples) == 2:
        n1 = tuples[0][0]
        n2 = tuples[0][1]
        n3 = tuples[1][0]
        n4 = tuples[1][1]

        if n1.isdigit():
            cols.append(n1)
            if not includeCompView:

                constraints.append("{}.n1 = '{}'".format(t1_rename, n1))
        else:
            cols.append("{}.n1 as n1".format(t1_rename))
            if n1 == n2:
                constraints.append("{}.n1 = {}.n2".format(t1_rename, t1_rename))
        
        if n2 == n3:
            constraints.append("{}.n2 = {}.n1".format(t1_rename, t2_rename))
        
        if n3 == n4:
            constraints.append("{}.n1 = {}.n2".format(t2_rename, t2_rename))

        if n4.isdigit():
            cols.append(n4)
            constraints.append("{}.n1 = '{}'".format(t2_rename, n4))
        else:
            cols.append("{}.n2 as n2".format(t2_rename))  
        
        if is_final_join:
            sql = "select " + ", ".join(summary) + " from " + tablename1 + " " + t1_rename + ", " + tablename2 + " " + t2_rename + " where " + " and ".join(constraints)
        else:
            sql = "select " + ", ".join(cols) + " from " + tablename1 + " " + t1_rename + ", " + tablename2 + " " + t2_rename + " where " + " and ".join(constraints)
    else:
        n1 = tuples[0][0]
        n2 = tuples[0][1]
        if n1.isdigit():
            # cols.append(n1)
            constraints.append("{}.n1 = '{}'".format(t1_rename, n1))
        else:
            cols.append("{}.n1 as n1".format(t1_rename))
        
        if n2.isdigit():
            # cols.append(n2)
            constraints.append("{}.n2 = '{}'".format(t1_rename, n2))
        else:
            cols.append("{}.n2 as n2".format(t1_rename))

        if n1 == n2 and not n1.isdigit()and not n2.isdigit():
            constraints.append("{}.n1 = {}.n2".format(t1_rename, t1_rename))
        
        sql = "select " + ", ".join(summary) + " from " + tablename1 + " " + t1_rename + " where " + " and ".join(constraints)
    
    # print(sql)    
    return sql


if __name__ == '__main__':
    # group = [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x4'), ('x4', 'x5'), ('x5', 'x6'), ('x6', '6'),
    #      ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3'), ('x4', 'x4'), ('x5', 'x5'), ('x6', 'x6')]
    # group = [('1', 'x1')]
    group = [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x4'), ('x4', 'x5'), ('x5', 'x6'), ('x6', '6'),
         ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3'), ('x6', 'x6')]
    ordered_group = reorder_closure_group(group)
    # ordered_group = [('a', 'b', 'x', 'y', ''), ('b', 'c', 'x', 'y', ''), ('c', 'd', 'x', 'y', ''), ('d', 'e', 'x', 'y', '')]
    # table_attributes = ['A', 'B', 'C', 'D', 'condition']
    table_attributes = ['n1', 'n2']
    sqls, output_tables = gen_splitjoin_sql(ordered_group, "test", table_attributes, summary=['1', '2', '3', '4', '5'])

    for s in sqls:
        print(s)

    for t in output_tables:
        print(t)
