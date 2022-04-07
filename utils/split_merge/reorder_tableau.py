
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

def gen_splitjoin_sql(ordered_group, tablename, summary):
    sqls = []
    output_tables = []
    comp_link = ""
    sql = ""
    if len(ordered_group) == 1:
        sql = convert_tuples_to_sql(ordered_group, tablename, "t1", "", "", False, True, summary)
        sqls.append(sql)
        output_tables.append("R1")
        return sqls, output_tables
    elif len(ordered_group) == 2: # do not contains composition view but is final join
        sql = convert_tuples_to_sql(ordered_group, tablename, "t1", tablename, "t2", False, True, summary)
        sqls.append(sql)
        output_tables.append("R1_2")
        return sqls, output_tables

    for idx, link in enumerate(ordered_group):
        if idx == 0:
            continue
        elif idx == 1:
            n1 = ordered_group[idx-1][0]
            n2 = link[1]
            links = [ordered_group[idx-1], link]
            comp_link = (n1, n2)
            sql = convert_tuples_to_sql(links, tablename, "t1", tablename, "t2", False, False, summary)
            
        else:
            n1 = comp_link[0]
            n2 = link[1]
            links = [comp_link, link]
            if idx == len(ordered_group) - 1: # contains composition view and is final join
                sql = convert_tuples_to_sql(links, "R1_{}".format(idx), "t1", tablename, "t2", True, True, summary)
            else:
                sql = convert_tuples_to_sql(links, "R1_{}".format(idx), "t1", tablename, "t2", True, False, summary)
            comp_link = (n1, n2)

        output_tables.append("R1_{}".format(idx+1))
        sqls.append(sql)
    return sqls, output_tables

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
    group = [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x4'), ('x4', 'x5'), ('x5', 'x6'), ('x6', '6'),
         ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3'), ('x4', 'x4'), ('x5', 'x5'), ('x6', 'x6')]
    group = [('1', 'x1')]
    group = [('1', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x4'), ('x4', 'x5'), ('x5', 'x6'), ('x6', '6'),
         ('x1', 'x1'), ('x2', 'x2'), ('x3', 'x3'), ('x6', 'x6')]
    ordered_group = reorder_closure_group(group)
    sqls, output_tables = gen_splitjoin_sql(ordered_group, "test", summary=['1', '2', '3', '4', '5'])

    for s in sqls:
        print(s)

    for t in output_tables:
        print(t)
