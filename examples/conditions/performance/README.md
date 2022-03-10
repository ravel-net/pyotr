# Z3 performance of checking condition

Files `z3_contrd.txt`, `z3_sat.txt`, `z3_tauto.txt` store the z3 running time. These files in that order refer to conditions in `contradiction.txt`, `satisfiable.txt`, `tautology.txt`. The running time for each line in those files is the time that reasoning one condition.

## The content of z3_*.txt

The header of the content in `z3_*.txt` is `case`, `variable_time`, `solving_time`, `total_time` and `condition`.

- `case` determines the condition case. `0` indicates contradiction, `1` indicates tautology and `2` indicates satisfiable.
- `variable_time` is z3 variable initialization time.
- `solving_time` is z3 solving time
- `total_time` is total z3 running time including variable initialization and solving.
- `condition` is the condition to be checked. 

## Note: `z3_part.py` is the python script to time z3 reasoning time.

The idea for checking one condition in the script is:

1. checking whether the negation of the condition is a tautology;
2. if answer in 1 is unsat, then the condition is a tautology, stop;
3. otherwise, checking whether the condition is contradiction;
4. if answer in 3 is unsat, then the condition is a contradiction, stop;
5. otherwise, the condition is satisfiable, stop.

The `total_time` for one condition records the running time of above steps.

### Usage

```python
"""
time the z3 reasoning time for a file of conditions

record the running time for each condition stored in the output file
return the total running time of all conditions
"""
path = "../"
filename = "contradiction.txt"
output = "./z3_contrad.txt"

domain_condition, domain_time = get_domain_conditions(['1', '2'], ['x1', 'x2', 'x3'], "Int")

total_running_time = time_list_condition(path+"contradiction.txt", "./z3_contrad.txt", domain_condition)

"""
time the z3 reasoning time for a single condition

return the running time for the input condition
"""
condition = "And(x3 == 1, 2 == x3, x3 == 2)"

single_time = time_one_condition(condition, domain_condition)
```