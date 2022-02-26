# Generate chain with loops

## gen_chain.py

This is for generating chain topology with loops. The parameters of generating function are:

- size: the total number of nodes(variables/constants) in chain topology
- rate_summary: the percentage of nodes that appears in the summary; ranges [0, 1]
- rate_loops: the percentage of summary nodes which contain the loop; ranges [0, 1]

```python
path, summary_nodes, loop_nodes, picked_nodes = gen_chain_with_loop(size=15, rate_summary=0.5, rate_loops=0.5)
tuples = gen_tableau(path, picked_nodes)
print(tuples)
```