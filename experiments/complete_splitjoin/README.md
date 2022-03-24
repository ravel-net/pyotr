# Minimization experiment

## Dataset

The dataset uses overlay network encoding. The chain topologies are stored under `variable/data` folder. The number in the filename represents the total nodes(constant and variable nodes) in the chain topology.

## Split-merge 

The scripts of experiments which run by split-merge function are named `group_query_splitjoin_tauto#.py` where `#` repsented a number and its number is correspond to its size of dataset(i.e. the number of total nodes in the chain topology). 

The file `chain#_complete_split_tauto.txt` records the running time using split-merge algorithm in seconds for each step. 

- `data`: running time on data portion; 
- `condition`: running time on updating condition 
- `#input_contrd`: the number of input tuples to check whether condition is contradiction 
- `contradiction`: running time on checking contradiction 
- `#input_redun`: the number of input tuples to check whether condition is redundancy and tautology 
- `redundancy`: running time on checking redundancy 
- `join`: total running time of `data`, `condition`, `contradiction` and `redundancy` 
- `merge`: running time on merging tuples 
- `output_rows`: the number of tuples after merging tuples.

Some records may missing.

## Naive

The scripts of experiments which run using naive function are named `group_query_splitjoin#.py` where `#` is same meaning with the above.

The file `chain#_complete_split.txt` records the running time using naive method in seconds for each step. The attributes in the files refer to the file in *Split-merge*. Some records may missing.

## Note

We can run to completion on 5 node chain topology, then failed in the following number: 10, 15, 20 and 50. They always reports memory issue on the last several joins and **they may need to spend hours running to the last several joins**. 