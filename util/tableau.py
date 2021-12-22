import random
import psycopg2

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
    self_tuples = []
    tuples = []
    i = 0
    while i < len(path) - 1:
        (n1, n2) = path[i]
        (n3, n4) = path[i+1]
        
        self_tuples.append((n1, n1, '{}'))

        if n2 in overlay:
            tuples.append((n1, "i_{}".format(n2), '{}'))
            tuples.append(("i_{}".format(n2), n3, '{}'))
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
    cons_list = [i for i in range(1, cons_size+1)]

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

    print(node_list)
    print(forward_path)
    print(overlay_nodes)
    print(overlay_path)
    return forward_path, node_list, overlay_path, overlay_nodes

def display(tuples, self_tuples):
    print("\n***********Tableau***********")
    for t in tuples:
        print(t)
    print("-----------")   
    for t in self_tuples:
        print(t)

    print("****************************\n")

def convert_tableau_to_sql(tableau, tablename, overlay_nodes):
    """
    Convert tableau to cosrresponding SQL

    Parameters:
    ------------
    tableau : list 
        The tableau tuples(non self-connected) and self-connected tuples in forwarding order, 
        generated by gen_tableau() function (tuples + self_tuples) or retrieved from database table.
        For example, path 1 -> 2 -> 3, the tableau tuples are [(1, i_2, {}), (i_2, 2, {}), (2, 3, {}), (1, 1, {}), (2, 2, {})]

    tablename : string 
        The name of data table in database that stores the tableau

    overlay_nodes : list
        the list of constant nodes in overlay network

    Returns:
    ------------
    sql : string
        The sql string that can directly run in Postgres 
    """
    cols = []
    tables = []
    constraints = []

    last = ""
    var_dict = {}
    for i in range(len(tableau)):
        tables.append("{} t{}".format(tablename, i))
        (n1, n2, _) = tableau[i]
        if n1 in overlay_nodes:
            constraints.append("t{}.n1 = '{}'".format(i, n1))
            if n1 != n2 and n1 != last:
                cols.append("t{}.n1".format(i))
        if n2 in overlay_nodes:
            constraints.append("t{}.n2 = '{}'".format(i, n2))
            if n1 != n2:
                cols.append("t{}.n2".format(i))
        
        if n1 == last and n1 not in overlay_nodes:
            constraints.append("t{}.n2 = t{}.n1".format(i-1, i))
            var_dict[n1] = i
        
        if n1 not in overlay_nodes and n2 not in overlay_nodes and n1 == n2:
            constraints.append("t{}.n1 = t{}.n2".format(i, i))
            if n1 in var_dict.keys():
                constraints.append("t{}.n1 = t{}.n2".format(var_dict[n1], i))
        last = n2

    sql = "select " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    return sql

if __name__ == '__main__':
    size = 100 # the number of nodes in physical network path
    rate = 0.3 # the percentage of constant nodes in physical network path (the number of nodes in overlay path)

    physical_path, physical_nodes, overlay_path, overlay_nodes = gen_large_chain(size=size, rate=rate)

    physical_tuples, phy_self_tuples = gen_tableau(path=physical_path, overlay=overlay_nodes)

    display(physical_tuples, phy_self_tuples)

    overlay_tuples, ove_self_tuples = gen_tableau(path=overlay_path, overlay=overlay_nodes)

    display(overlay_tuples, ove_self_tuples)