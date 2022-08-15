# Homomorphism
homomorphism.py provides the main function `homomorphism` that takes two tableux as input and returns whether or not homomorphism exists between them. If homomorphism does not exist and the data instance has variables, the function provides a counter example. The details of this function are given as comments in the code. The example can be run as:

`python homomorphism.py`

### Requirements:
1. Make sure that postgresql is installed.
2. Make sure that the [databaseconfig](https://github.com/ravel-net/pyotr/blob/cleanup/databaseconfig.py) has correct information. The default usename and password is usually `postgres`. If a database does not exist, create one using:
```
sudo -u postgres -i # where postgres is the user associated with postgres
psql
CREATE DATABASE [DB_NAME],
```
3. Make sure `int4_faure` is installed in the given database (e.g. in DB_name). The instructions to install are given [here](https://github.com/ravel-net/pyotr/blob/cleanup/Backend/storage/dataypes/int_faure/README.md) 

## Minimization Example
Function `main` in homomorphism.py shows how to use the function for network minimization. Consider the network below:
![minimization_mubashir](https://user-images.githubusercontent.com/61048625/180695608-45a47a19-2883-465e-b190-153b9833d4f1.jpeg)
Both diagrams show the same network but in the first diagram we use variables instead of constants. Note that for reachability between 1 and 4, the loop is redundant and thus the network can be minimized.
The query is:
```
T_query = [
	("1", "2"),
	("2", "x"),
	("x", "y"),
	("y", "x"),
	("x", "3"),
	("3", "z"),
	("z", "4"),
]
query_summary=["1","4"] 
```
For the first diagram, the tableau becomes:
```
column_names=["n1","n2", "condition"]
T_data = [
	("1", "2", ""),
	("2", "x", ""),
	("x", "y", ""), # Homomorphism exists even after commenting this out (removing this tuple)
	("y", "x", ""), # Homomorphism exists even after commenting this out (removing this tuple)
	("x", "3", ""),
	("3", "z", ""), 
	("z", "4", ""),

	# self loops
	("x", "x", ""),
	("y", "y", ""),
	("z", "z", ""),
]	
data_summary=["1","4"]
domain={"x":["1","2","3","4"], "y":["1","2","3","4"], "z":["1","2","3","4"]}
```
To test homomorphism, we run:

`homomorphism_test(query=T_query, query_summary=query_summary, data_instance=T_data, data_summary=data_summary, domain=domain, data_instance_table="T_data", column_names=column_names, storage_types=["int4_faure", "int4_faure"])`

Note that we can comment out the loop from the data instance and homomorphism should still hold. However, if we try to comment out any other tuple (such as the first tuple, (1,2)), homomorphism does not hold - implying that the tuple cannot be removed.

## Link Failure Example
This example is commented out under `main`. The summaries here are technically incorrect (not implied from the tableau) but the example showcases homomorphism with more than two columns. Consider two networks with backup paths, `T_data_1` and `T_data_2`:
![link_failure_mubashir](https://user-images.githubusercontent.com/61048625/180696588-18a9a44b-b0d7-4491-b1f3-92c19aa8009f.jpeg)
T_data_1 has backup paths correctly configured while T_data_2 does not. We want to see if reachability along with waypointing along the firewall is ensured. We represent link failures with variables `x` and `y` where the value 0 represents failure and 1 represents that the link is active. To test if the backup links are correctly configured, we come with the following setup:
```
T_query = [
	("a","b","x","y",""),
	("b","c","x","y",""),
	("c","d","x","y",""),
	("d","e","x","y",""),
]
query_summary=["a","c","e"]
```
For T_data_2 the data instance becomes:
```
column_names=["n1","n2", "x_link_status", "y_link_status", "condition"]
T_data_2 = [
	("1","2","1","y", ""),
	("2","3","x","y",""),
	("1","4","0","y",""),
	("3","4","x","1",""),
	("4","5","x","y",""),
	("3","5","x","0",""),

	("1","1","x","y",""),
	("2","2","x","y",""),
	("3","3","x","y",""),
	("4","4","x","y",""),
	("5","5","x","y",""),
]
data_summary=["1","3","5"]
domain={"x":["0","1"], "y":["0","1"]}
```
To test homomorphism, we run:

`homomorphism_test(query=T_query, query_summary=query_summary, data_instance=T_data_2, data_summary=data_summary, domain=domain, data_instance_table="T_data", column_names=column_names, storage_types=["int4_faure", "int4_faure"])`

The result would be unsatisfiable and the counter-example obtained would be `x=0,y=0` or `x=0,y=1`, denoting that the two networks are not equivalent when link x has failed
