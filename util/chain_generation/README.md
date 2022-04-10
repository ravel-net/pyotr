# Chain with loops

`gen_chain_with_loop(size, rate_summary, size_single_loop)`: Generate chain topology with loops. Configure size of chain topology, size of summary nodes and the number of variable nodes in a single loop.

## Input: 

- size: integer
  - The number of nodes in the topology
- rate_summary: float
  - the percentage of nodes that appears in the summary; ranges [0, 1]
- size_single_loop:integer
  - the number of variable nodes in a single loop; It is the upper bound of a single loop.

## output: 

- path: list
  - the forward path for chain with loops
- summary_nodes: list
  - the list of summary nodes(constant nodes)
- variable_nodes: list
  - the list of variable nodes
- picked_nodes: list
  - the list of constant nodes which connect to loops.

`gen_chain_with_loop_control_position(size, rate_summary, rate_loops)`: Generate chain topology with loops. Configure size of chain topology, size of summary nodes and the number of summary nodes who are connected to loops.

## Input: 

- size: integer
  - The number of nodes in the topology
- rate_summary: float
  - the percentage of nodes that appears in the summary; ranges [0, 1]
- rate_loops:float
  - the percentage of summay nodes that contains the loop; ranges [0, 1]
  
## output:

Same as the above.

# generate the corresponding tableau for chain with loops

`gen_tableau(path, picked_nodes)`:

## input:

- path: list, generated by `gen_chain_with_loop()`
  - the forwarding path of chain with loops
- picked nodes: list, generated by `gen_chain_with_loop()`
  - the constant nodes who connect to loops.