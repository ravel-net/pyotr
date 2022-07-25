# Homomorphism
homomorphism.py provides the main function `homomorphism` that takes two tableux as input and returns whether or not there exists a homomorphism between them. If homomorphism does not exists and the data instance has variables, the function provides a counter example. The details of this function are given as comments in the code
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
