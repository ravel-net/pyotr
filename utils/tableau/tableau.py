import random
import psycopg2
import re


"""
 /- u -\
1       2 - w - 3
 \_ v _/ 
"""
def gen_tableau(path, overlay):
    """
    Generate tableau table

    Parameters:
    ------------
    path : list
        a list of pairwise link in forward path

    ovelay : list
        a list of nodes in overlay network

    Returns:
    ------------
    tuples : list
        the list of links with n1, n2

    self_tuples : list
        the list of links with self-connected
    """
    max_val = get_max(overlay)
    self_tuples = []
    tuples = []
    i = 0
    while i < len(path) - 1:
        (n1, n2) = path[i]
        (n3, n4) = path[i+1]
        
        self_tuples.append((n1, n1, '{}'))

        if n2 in overlay:
            tuples.append((n1, "{}".format(int(n2)+max_val), '{}'))
            tuples.append(("{}".format(int(n2)+max_val), n3, '{}'))
        else:
            tuples.append((n1, n2, '{}'))
        
        i += 1

    (n1, n2) = path[i]
    self_tuples.append((n1, n1, '{}'))
    tuples.append((n1, n2, '{}'))

    return tuples, self_tuples

def gen_large_chain(size=10, rate=0.3):
    """
    Generate chain with size and rate

    Parameters:
    ------------
    size : integer, default=10
        the number of nodes(including variable nodes and constant nodes) in physical path

    rate : float, default=0.3
    the percentage of constant nodes in physical path 

    Returns
    ------------
    forward_path : list
        the list of pairwise link in physical path

    node_list : list
        the nodes(including variable nodes and constant nodes) of physical path in forwarding order

    overlay_path : list
        the list of pairwise link in overlay path

    overlay_nodes : list
        the constant nodes of overlay path in forwarding order
    """
    cons_size = int(size * rate)
    var_size = size - cons_size

    var_list = ["x{}".format(i) for i in range(1, var_size+1)]
    cons_list = [str(i) for i in range(1, cons_size+1)]

    # set the first node and the last node
    first = cons_list.pop(0)
    last = cons_list.pop()
    
    # shuffle the variable nodes and constant node except the first and last constant nodes
    node_list = var_list + cons_list
    random.shuffle(node_list)

    # insert the first and last constant nodes back to node list
    node_list.insert(0, first)
    node_list.append(last)
    
    # generate pairwise path list for physical path
    forward_path = []
    overlay_nodes = [] # store the constant nodes in physical path order
    for i in range(size-1):
        forward_path.append((node_list[i], node_list[i+1]))
        if type(node_list[i]) is int or node_list[i].isdigit():
            overlay_nodes.append(node_list[i])
    if type(node_list[size-1]) is int or node_list[size-1].isdigit():
        overlay_nodes.append(node_list[size-1])

    # generate pairwise path list for overlay path
    overlay_path = []
    for i in range(cons_size-1):
        overlay_path.append((overlay_nodes[i], overlay_nodes[i+1]))

    # print(node_list)
    # print(forward_path)
    # print(overlay_nodes)
    # print(overlay_path)
    return forward_path, node_list, overlay_path, overlay_nodes

def gen_chain_even_group(size=10, rate=0.5):
    cons_size = int(size * rate)

    node_list = []
    if cons_size < 2:
        var_size = size - 2
        cons_size = 2
        var_list = ["x{}".format(i) for i in range(1, var_size+1)]
        node_list = ["1"] + var_list + ["2"]
    else:
        var_size = size - cons_size
        # print("var_size", var_size)
        group_num = cons_size - 1
        # print("group_num", group_num)
        avg_group_size = int(var_size / group_num)
        # print("avg_group_size", avg_group_size)

        j = 1 
        for i in range(group_num-1):
            lower = avg_group_size-1 if avg_group_size-1 >= 0 else 0
            upper = avg_group_size+2
            # print(lower, upper)
            size_per_group = random.choice(range(lower, upper))
            # print(size_per_group)
            node_list.append(str(i+1))
            s = 0
            while s < size_per_group:
                node_list.append("x{}".format(j))
                j += 1
                s += 1
        node_list.append(str(group_num))
        s = 0
        # print("j", j)
        final_group_size = var_size-(j-1)
        # print("final_group", final_group_size)
        while s < final_group_size:
            node_list.append("x{}".format(j))
            j += 1
            s += 1    
        node_list.append(str(group_num+1))
        # print(node_list)

    var_list = ["x{}".format(i) for i in range(1, var_size+1)]
    cons_list = [str(i) for i in range(1, cons_size+1)]
    
    forward_path = []
    for i in range(size-1):
        forward_path.append((node_list[i], node_list[i+1]))

    overlay_path = []
    for i in range(cons_size-1):
        overlay_path.append((cons_list[i], cons_list[i+1]))

    return forward_path, node_list, overlay_path, cons_list

def display(tuples, self_tuples):
    print("\n***********Tableau***********")
    for t in tuples:
        print(t)
    print("-----------")   
    for t in self_tuples:
        print(t)

    print("****************************\n")

def get_max(overlay):
    max_val = 0
    for node in overlay:
        if int(node) > max_val:
            max_val = int(node)
    return max_val

def isIPAddress(opd):
    return len(opd.split(".")) == 4

def convert_tableau_to_sql(tableau, tablename, overlay_nodes):
    """
    Convert tableau to corresponding SQL

    Parameters:
    ------------
    tableau : list 
        The tableau tuples(non self-connected) and self-connected tuples in forwarding order, 
        generated by gen_tableau() function (tuples + self_tuples) or retrieved from database table.
        For example, path 1 -> 2 -> 3, the tableau tuples are [(1, 5, {}), (5, 2, {}), (2, 3, {}), (1, 1, {}), (2, 2, {})], 
        node 2 is split into 2 and 5(interface, calculated by adding 2 and the max value among the virtual nodes, here is 3).

    tablename : string 
        The name of data table in database that stores the tableau

    overlay_nodes : list
        the list of constant nodes in overlay network

    Returns:
    ------------
    sql : string
        The sql string that can directly run in Postgres 
    """
    # cols = []
    tables = []
    constraints = []
    column_names = ['n1', 'n2', 'F'] # TODO: Automate this. Take columns as parameter
    
    last = ""
    last_F = ""
    var_dict = {}
    summary = {}
    summary_nodes = []
    for i in range(len(tableau)):
        tables.append("{} t{}".format(tablename, i))
        n1 = tableau[i][0]
        n2 = tableau[i][1]


        # Extra logic to handle firewalls. Should be automated
        if (len(tableau[i]) > 3): # when conditions occur
            for j, column in enumerate(column_names):
                val = tableau[i][j]
                if val in overlay_nodes and val not in summary:
                    summary[val] = 't{}.{}'.format(i, column)
                    summary_nodes.append('t{}.{}'.format(i, column))
            conditions = tableau[i][3]

            if conditions != "":
                conditionList = conditions.split(",")
                for c in conditionList:
                    c = c.strip()
                    match = re.search('!=|<=|>=|<>|<|>|=', c)
                    left_opd = c[:match.span()[0]].strip()
                    opr = match.group()
                    right_opd = c[match.span()[1]:].strip()
                    constraints.append("t{}.{} {} '{}'".format(i, column_names[2], opr, right_opd))



        if n1.isdigit() or isIPAddress(n1):
            constraints.append("t{}.n1 = '{}'".format(i, n1))
        
        if n2.isdigit() or isIPAddress(n2):
            constraints.append("t{}.n2 = '{}'".format(i, n2))

        if n1 == last and not n1.isdigit():
            constraints.append("t{}.n2 = t{}.n1".format(i-1, i))
            var_dict[n1] = i
            if (len(tableau[i]) > 2): # for firewalls
                constraints.append("t{}.{} = t{}.{}".format(i-1, column_names[2], i, column_names[2]))

        if not n1.isdigit() and not n2.isdigit() and n1 == n2:
            constraints.append("t{}.n1 = t{}.n2".format(i, i))
            if n1 in var_dict.keys():
                constraints.append("t{}.n1 = t{}.n2".format(var_dict[n1], i))


        last = n2

    sql = "select " + ", ".join(summary_nodes) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    print(sql)
    return sql

# def convert_closure_group_to_sql(tableau, tablename, overlay_nodes):
#     """
#     Convert closure group to corresponding SQL

#     Parameters:
#     ------------
#     tableau : list 
#         The closure group tableau tuples(non self-connected) and self-connected tuples in forwarding order, 
#         generated by gen_tableau() function (tuples + self_tuples) or retrieved from database table.
#         For example, path 1 -> 2 -> 3, the tableau tuples are [(1, 5, {}), (5, 2, {}), (2, 3, {}), (1, 1, {}), (2, 2, {})], 
#         node 2 is split into 2 and 5(interface, calculated by adding 2 and the max value among the virtual nodes, here is 3).

#     tablename : string 
#         The name of data table in database that stores the tableau

#     overlay_nodes : list
#         the list of constant nodes in overlay network

#     Returns:
#     ------------
#     sql : string
#         The sql string that can directly run in Postgres 
#     """
#     max_val = get_max(overlay_nodes)
#     constant_cols = overlay_nodes.copy()
#     for i in range(len(overlay_nodes)):
#         if i == 0 or i == (len(overlay_nodes) - 1):
#             continue
#         constant_cols.append(str(int(overlay_nodes[i]) + max_val))
    
#     cols = []
#     tables = []
#     constraints = []
    
#     last = ""
#     var_dict = {}
    
#     for i in range(len(tableau)):
#         tables.append("{} t{}".format(tablename, i))
#         # (n1, n2, _) = tableau[i]
#         n1 = tableau[i][0]
#         n2 = tableau[i][1]

#         if n1 in constant_cols:
#             constraints.append("t{}.n1 = '{}'".format(i, n1))
#             if n1 != n2 and n1 != last:
#                 cols.append("t{}.n1".format(i))
#                 constant_cols.remove(n1)
            
#         if n2 in constant_cols:
#             if n1 != n2:
#                 cols.append("t{}.n2".format(i))
#                 constant_cols.remove(n2)
#             constraints.append("t{}.n2 = '{}'".format(i, n2))

#         if n1 == last and not n1.isdigit():
#             constraints.append("t{}.n2 = t{}.n1".format(i-1, i))
#             var_dict[n1] = i

#         if not n1.isdigit() and not n2.isdigit() and n1 == n2:
#             constraints.append("t{}.n1 = t{}.n2".format(i, i))
#             if n1 in var_dict.keys():
#                 constraints.append("t{}.n1 = t{}.n2".format(var_dict[n1], i))

#         last = n2
#     # print(cols)
#     # print(tables)
#     # print(constraints)
#     constant_col_sql = ", ".join(["{}".format(c) for c in constant_cols])
#     sql = "select " + constant_col_sql + ", " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
#     print(sql)
#     return sql



if __name__ == '__main__':
    size = 10 # the number of nodes in physical network path
    rate = 0.3 # the percentage of constant nodes in physical network path (the number of nodes in overlay path)

    physical_path, physical_nodes, overlay_path, overlay_nodes = gen_large_chain(size=size, rate=rate)

    physical_tuples, phy_self_tuples = gen_tableau(path=physical_path, overlay=overlay_nodes)

    display(physical_tuples, phy_self_tuples)

    overlay_tuples, ove_self_tuples = gen_tableau(path=overlay_path, overlay=overlay_nodes)

    display(overlay_tuples, ove_self_tuples)

    sql = convert_tableau_to_sql(phy_self_tuples+phy_self_tuples, "T_v", overlay_nodes)
    print(sql)