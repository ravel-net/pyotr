# Instruction for tableau.py

## Usage

```python
# the number of nodes in physical network path
size = 10 
# the percentage of constant nodes in physical network path (the number of nodes in overlay path)
rate = 0.3 

# call gen_large_chain() to generate physical path and  virtual path
physical_path, physical_nodes, overlay_path, overlay_nodes = gen_large_chain(size=size, rate=rate)

# call gen_tableau() to generate tableau for physical path
physical_tuples, phy_self_tuples = gen_tableau(path=physical_path, overlay=overlay_nodes)

# call gen_tableau() to generate tableau for virtual path
overlay_tuples, ove_self_tuples = gen_tableau(path=overlay_path, overlay=overlay_nodes)

physical_tableau = physical_tuples + phy_self_tuples

virtual_tableau = overlay_tuples + ove_self_tuples

"""
Then store physical_tableau and virtual tableau into database.
...
"""

```