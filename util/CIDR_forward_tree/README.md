# CIDR forward tree

## Topology

There are 4 sizes of AS topology in the `/topo` folder: AS4755, AS3356, AS2914 and AS7018. The size: AS4755 < AS3356 < AS2914 < AS7018.

## Generate forward tree script

`gen_forward_table_with_backup.py` shows the script that generates the forward tree with backup links

### Usage:

- Step 1: load topo into database by calling `load_topo()`.
- Step 2: find the largest connected component in the topology(the topology may be unconnected) by calling `get_largest_connected_network()`, returns the links and nodes of the largest connected component. Then store the links into database.
- Step 3: generate the one spanning tree by calling `gen_spanning_tree()`, returns the spanning tree links and the root of this tree. The root will be the destination of the forward tree.
- Step 4: stores the spanning tree into database by calling `load_tree_in_f()`. This step will reverse the spanning tree generated in step 3 and treat the root as the destination. This is a base forward table in the database.
- Step 5: add backup links for the base forward table by calling `add_link()`. You can set the rate of the nodes who will be added backup link.
- Step 6: add filter for the forward table by calling `add_filter()`. You can set the rate of the nodes who will be added the filter.

### Notes

- The forward table is used **integer** datatype for links, so that if uses translator_pyotr or translator(Faure), you need to transform the datatype.

- `gen_sql.py` provides the transform function. The function looks like `gen_{datatype}_table{_reg}()`, the {datatype} represents the datatype used in the target table, {_reg} means the target table is a regular table that is without condition column.

### Example of generating forward tree

```python
as_num = 2914 #determine the AS number
as_tablename = "as{}".format(as_num) # the table name stores AS topology

'''
Step 1: load AS topology into database
'''
load_topo("/topo/{}_edges.txt".format(as_num), as_tablename)

'''
Step 2: get the largest connected component of AS topology
'''
cursor.execute("select * from {}".format(as_tablename))
all_links = cursor.fetchall()
print("all links:", len(all_links))
connected_links, connected_nodes = get_largest_connected_network(all_links)
print("largest component: edges:", len(connected_links), "nodes:", len(connected_nodes))

topo_tablename = "topo_{}".format(as_num) # the table name stores largest connnected component topology
fwd_tablename = "fwd_{}".format(as_num) # the table name stores the forward tree

'''
Store the largest component into database
'''
cursor.execute("drop table if exists {}".format(topo_tablename))
cursor.execute("create table {}(n1 integer, n2 integer)".format(topo_tablename))
cursor.executemany("insert into {} values(%s, %s)".format(topo_tablename), connected_links)
conn.commit()

'''
Step 3: generate the spanning tree 
'''
spanning_links, root = gen_spanning_tree(connected_links)
print("root", root)
print("spanning tree links:", len(spanning_links))

'''
Step 4: store the spanning tree into database
'''
load_tree_in_f(spanning_links, fwd_tablename)

'''
Step 5: add backup links
'''
add_link(root, topo_tablename, fwd_tablename, 0.2) # 0.2 is the percentage of nodes to set up backup link

'''
Step 6: add filter
'''
add_filter(connected_nodes, root, 0.5, fwd_tablename) # 0.5 is the percentage of nodes to set up filter
```