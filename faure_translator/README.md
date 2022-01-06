# Translator

This translator is the baseline of old faure but supports multiple joins and batch process on z3 step. This translator file is a python script that help do the expeiment conveniently and cannot use in the Ravel terminal.

## Database configuration

Create a `.py` file named `databaseconfig.py`. Then copy the following config to this file. Replace your database information.

```python
postgres = {
    "host": "your host",
    "user": "your username",
    "password": "your password",
    "db": "your database"
}
```

Put `databaseconfig.py` under the `/faure_translator` folder. Or you can put this file to other folder, then please add the folder path to the environment.

## translator usage

- step 1: create a SQL query. For example, using tableau.py
- step 2: call `generate_tree()` to analyse SQL, then return a `tree` dict object.
- step 3: call `data()` to run data content step, then return the execution time of data content step.
- step 4: call `upd_condition()` to run updating condition step, then return the execution time of updating condition step.
- step 5: call `normalization()` to run normalization step(z3 step), then return the execution time of removing contradiction and redundancy respectively, and the input of process of removing contradiction and redundancy. 
    The returns format 
    ```python
    {  
        "contradiction":[
            contrad_count, # the input of process of removing contradiction
            contr_end-contrd_begin # the execution time of removing contradiction
            ], 
        "redundancy":[
            redun_count, # the input of process of removing redundancy
            redun_end-redun_begin # the execution time of removing redundancy
            ]
    }
    ```

Example:

```python
sql = tableau.convert_tableau_to_sql(group, "T_v", overlay_nodes)
tree = generate_tree(sql)
count_data_time = 0 # record the 10 times execution time of data content step
count_upd_time = 0
count_contrad_time = 0
count_redun_time = 0
tuples_contrad = 0 # record the number of input for the process of removing contradiction
tuples_redun = 0

# run 10 times of three steps
for i in range(10):
    data_time = data(tree)
    count_data_time += data_time

    upd_time = upd_condition(tree)
    count_upd_time += upd_time

    nor_time = normalization()
    count_contrad_time += nor_time["contradiction"][1]
    tuples_contrad = nor_time["contradiction"][0]
    count_redun_time += nor_time["redundancy"][1]
    tuples_redun = nor_time["redundancy"][0]

total_time = count_data_time/10 + count_upd_time/10 + count_contrad_time/10 + count_redun_time/10

z3_time = count_contrad_time/10+count_redun_time/10


```