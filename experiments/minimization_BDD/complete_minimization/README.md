# Scripts for minimization

`script_minimization.py` contains  
- `exp_minimization_chain_Z3(size, rate_summary, size_single_loop)`: one is used to run z3 version of minimization;
- `exp_minimization_chain_BDD(size, rate_summary, size_single_loop)`: one is used to run BDD version of minimization;
- `exp_minimization_chain_naive(size, rate_summary, size_single_loop)`: one is used to run naive version of minimization which uses multiple joins.

## input:

- size: integer 
  - the number of nodes in chain topology with loops
- rate_summary: float
  - the percentage of summary nodes, range is [0, 1]
- size_single_loop: integer
  - the number of nodes in a single loop

## output:

- running_time: seconds
  - the running time of minimization