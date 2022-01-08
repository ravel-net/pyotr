import psycopg2
import random
import time
import json
import databaseconfig as cfg

conn = psycopg2.connect(host=cfg.postgres["host"], database=cfg.postgres["db"], user=cfg.postgres["user"], password=cfg.postgres["password"])
cursor = conn.cursor()

"""
Overlay network example:
topology: X - Y - Z

Physical network example:
topology: 
 /- u -\
X       Y - w - Z
 \_ v _/  

 /- 2 -\
1       4 - 5 - 6
 \_ 3 _/ 
"""
def gen_network(edges, tablename):
    cursor.execute("DROP TABLE IF EXISTS {}".format(tablename))
    cursor.execute("CREATE TABLE {} (n1 text, n2 text)".format(tablename))

    cursor.executemany("INSERT INTO {} VALUES (%s, %s) ".format(tablename), edges)

    conn.commit()

def dfs(u, d, visited, path, path_list):
    # Mark the current node as visited and store in path
    visited[int(u)-1]= True
    path.append(u)

    # If current vertex is same as destination, then print
    # current path[]
    if u == d:
        path_list.append(path.copy())
    else:
        # If current vertex is not destination
        # Recur for all the vertices adjacent to this vertex
        cursor.execute("select n2 from toy_physical where n1 = '{}'".format(u))
        nodes = cursor.fetchall()
        # print(nodes)
        for n in nodes:
            i = n[0]
            if visited[int(i)-1]== False:
                dfs(i, d, visited, path, path_list)
                    
    # Remove current vertex from path[] and mark it as unvisited
    path.pop()
    visited[int(u)-1]= False

def gen_all_path(v, src, dst):
    # Mark all the vertices as not visited
    visited =[False]*(v)

    # Create an array to store paths
    path = []
    path_list = []

    # Call the recursive helper function to print all paths
    dfs(src, dst, visited, path, path_list)
    return path_list

"""
 /- u -\
1       2 - w - 3
 \_ v _/ 
"""
def gen_tableau(path, overlay):
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

def gen_large_chain(size=10, rate=0.5):
    cons_size = int(size * rate)
    var_size = size - cons_size
    if cons_size < 2:
        var_size = size - 2
        cons_size = 2

    var_list = ["x{}".format(i) for i in range(1, var_size+1)]
    cons_list = [str(i) for i in range(1, cons_size+1)]

    first = cons_list.pop(0)
    last = cons_list.pop()
    
    node_list = var_list + cons_list
    random.shuffle(node_list)
    node_list.insert(0, first)
    node_list.append(last)
    
    forward_path = []
    overlay_list = []
    for i in range(size-1):
        forward_path.append((node_list[i], node_list[i+1]))
        if node_list[i].isdigit():
            overlay_list.append(node_list[i])
    if node_list[size-1].isdigit():
        overlay_list.append(node_list[size-1])

    overlay_path = []
    for i in range(cons_size-1):
        overlay_path.append((overlay_list[i], overlay_list[i+1]))

    # print(node_list)
    # print(forward_path)
    # print(overlay_list)
    # print(overlay_path)
    return forward_path, node_list, overlay_path, overlay_list

def gen_sql_p_to_v(physical_table, overlay_table, overlay_nodes):
    tables = []
    constraints = []
    cols = []

    cursor.execute("select * from {}".format(physical_table))
    count = cursor.rowcount
    last = ""
    for i in range(1, count+1):
        tables.append("{} t{}".format(overlay_table, i))
        row = cursor.fetchone()
        if row[0] in overlay_nodes:
            constraints.append("t{}.n1 = '{}'".format(i, row[0]))
            if row[0] != row[1] and row[0] != last:
                cols.append("t{}.n1".format(i))
        if row[1] in overlay_nodes:
            constraints.append("t{}.n2 = '{}'".format(i, row[1]))
            if row[0] != row[1]:
                cols.append("t{}.n2".format(i))
        
        if row[0] == last and row[0] not in overlay_nodes:
            constraints.append("t{}.n2 = t{}.n1".format(i-1, i))
        
        if row[0] not in overlay_nodes and row[1] not in overlay_nodes and row[0] == row[1]:
            constraints.append("t{}.n1 = t{}.n2".format(i, i))

        last = row[1]
    # print(cols)
    # print(tables)
    # print(constraints)
    sql = "select " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    print(sql)
    return sql

def gen_sql_v_to_p(physical_table, overlay_table, overlay_nodes):
    cols = []
    tables = []
    constraints = []

    cursor.execute("select * from {}".format(overlay_table))

    last = ""
    count = cursor.rowcount
    for i in range(1, count+1):
        tables.append("{} t{}".format(physical_table, i))
        row = cursor.fetchone()
        if row[0] in overlay_nodes and row[0] != last and row[0] and row[0] != row[1]:
            constraints.append("t{}.n1 = '{}'".format(i, row[0]))
            # if row[0] != row[1]:
            cols.append("t{}.n1".format(i))
        if row[1] in overlay_nodes and row[1] != row[0]:
            constraints.append("t{}.n2 = '{}'".format(i, row[1]))
            cols.append("t{}.n2".format(i))

        if row[0] == row[1]:
            constraints.append("t{}.n1 = '{}'".format(i, row[0]))
            constraints.append("t{}.n2 = '{}'".format(i, row[1]))
        
    
    # print(cols)
    # print(tables)
    # print(constraints)
    sql = "select " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    print(sql)
    return sql

def unvar(node):
    if node.startswith("i_"):
        return node[2:]
    else:
        return node

def convert_tableau_to_sql(tableau, tablename, overlay_nodes):
    cols = []
    tables = []
    constraints = []

    last = ""
    var_dict = {}
    for i in range(len(tableau)):
        tables.append("{} t{}".format(tablename, i))
        # (n1, n2, _) = tableau[i]
        n1 = tableau[i][0]
        n2 = tableau[i][1]
        if unvar(n1) in overlay_nodes:
            constraints.append("t{}.n1 = '{}'".format(i, n1))
            if n1 != n2 and n1 != last:
                cols.append("t{}.n1".format(i))
        if unvar(n2) in overlay_nodes:
            constraints.append("t{}.n2 = '{}'".format(i, n2))
            if n1 != n2:
                cols.append("t{}.n2".format(i))
        
        if n1 == last and unvar(n1) not in overlay_nodes:
            constraints.append("t{}.n2 = t{}.n1".format(i-1, i))
            var_dict[n1] = i
        
        if unvar(n1) not in overlay_nodes and unvar(n2) not in overlay_nodes and n1 == n2:
            constraints.append("t{}.n1 = t{}.n2".format(i, i))
            if n1 in var_dict.keys():
                constraints.append("t{}.n1 = t{}.n2".format(var_dict[n1], i))
        last = n2
    # print(cols)
    # print(tables)
    # print(constraints)
    sql = "select " + ", ".join(cols) + " from " + ", ".join(tables) + " where " + " and ".join(constraints)
    print(sql)
    return sql

            
if __name__ == "__main__":
    # gen_sql_p_to_v("tp", "tv", ['1', '2'])
    # print("\n--------------------------------")
    # gen_sql_v_to_p("tp", "tv", ['1', '2'])

    # gen_sql_p_to_v("t_10", "t_10_o", ['1', '3', '4', '2', '5'])
    # print("\n--------------------------------")
    # gen_sql_v_to_p("t_10", "t_10_o", ['1', '3', '4', '2', '5'])
    # size = [10]
    # rate = 0.5
    # for s in size:
    #     data = {}
    #     begin = time.time()
    #     physical_path, physical_nodes, overlay_path, overlay_nodes = gen_large_chain(s, rate)
    #     data['physical_path'] = physical_path
    #     data['physical_nodes'] = physical_nodes
    #     data['overlay_path'] = overlay_path
    #     data['overlay_nodes'] = overlay_nodes
    #     with open('data/chain{}.json'.format(s), 'w') as outfile:
    #         json.dump(data, outfile)

        
    #     print("Generate chain with {} nodes".format(s), time.time() - begin)

    overlay = ['1', '2']
    path = [('1', 'u'), ('u', 'w'),('w', '2')]

    # # overlay = ['x', 'y', 'z']
    # # path = [('x', 'u'), ('u', 'y'), ('y', 'w'), ('w', 'z')]

    # path = [('1', 'x3'), ('x3', '3'), ('3', 'x4'), ('x4', '4'), ('4', 'x1'), ('x1', 'x5'), ('x5', '2'), ('2', 'x2'), ('x2', '5')]
    # overlay = ['1', '3', '4', '2', '5']
    # overlay_path = [('1', '3'), ('3', '4'), ('4', '2'), ('2', '5')]
    # path = [('1', 'x5'), ('x5', 'x4'), ('x4', 'x8'), ('x8', 'x6'), ('x6', 'x1'), ('x1', 'x2'), ('x2', 'x3'), ('x3', 'x7'), ('x7', '2')]
    # overlay = ['1', '2']
    # overlay_path = [('1', '2')]
    # path = [('1', 'x5'), ('x5', 'x4'), ('x4', 'x3'), ('x3', '2'), ('2', 'x6'), ('x6', 'x1'), ('x1', 'x2'), ('x2', 'x7'), ('x7', '3')]
    # overlay = ['1', '2', '3']
    # overlay_path = [('1', '2'), ('2', '3')]

    # path = [('1', 'x4'), ('x4', 'x3'), ('x3', 'x2'), ('x2', 'x5'), ('x5', 'x1'), ('x1', 'x6'), ('x6', '2')]
    # overlay = ['1', '2']
    # overlay_path = [('1', '2')]

    # path = [('1', 'x2'), ('x2', 'x1'), ('x1', 'x4'), ('x4', 'x3'), ('x3', '2'), ('2', 'x5'), ('x5', '3')]
    # overlay = ['1', '2', '3']
    # overlay_path = [('1', '2'), ('2', '3')]
    tuples, self_tuples = gen_tableau(path, overlay)

    convert_tableau_to_sql(tuples+self_tuples, "tp", overlay)

    tablename = "tp"
    cursor.execute("drop table if exists {}".format(tablename))
    cursor.execute("create table {} (n1 int4_faure, n2 int4_faure, condition text[])".format(tablename))
    cursor.executemany("insert into {} values(%s, %s, %s)".format(tablename), tuples+self_tuples)
    conn.commit()
    
    # print("\n*****T_p1******")   
    # for t in tuples:
    #     # if int(t[0]) // num == 1 and int(t[0]) != num:
    #     #     print("{}_{}".format(int(t[0]) % num, t[0]), end="\t")
    #     # else:
    #     #     print(t[0], end="\t")

    #     # if int(t[1]) // num == 1 and int(t[1]) != num:
    #     #     print("{}_{}".format(int(t[1]) % num, t[1]), end='\t')
    #     # else:
    #     #     print(t[1], end="\t")
    #     print(t)
    # print("-----------")   
    # for t in self_tuples:
    #     # if int(t[0]) // num == 1 and int(t[0]) != num:
    #     #     print("{}_{}".format(int(t[0]) % num, t[0]), end="\t")
    #     # else:
    #     #     print(t[0], end="\t")

    #     # if int(t[1]) // num == 1 and int(t[1]) != num:
    #     #     print("{}_{}".format(int(t[1]) % num, t[1]), end="\t")
    #     # else:
    #     #     print(t[1], end="\t")
    #     print(t)
    
