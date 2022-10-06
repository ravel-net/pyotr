# Faure Evaluation

This folder provides the implementation of faure evaluation. The main file is `faure_evaluation.py` and two tool files `parser.py` and `attribute.py` 

## Parameters

- `conn`: an instance of psycopg2.connect
- `sql`: SQL
- `additional_condition`: string. An string additional condition that would be appended to output table
- `output_table`: string. The tablename for output
- `databases`: dict. Default is {}. The format is {'tablename': {'types': ['datatype1', 'datatype2', ...], 'names': ['attr1', 'attr2', ...]}, ...}. **If datatype does not be set, FaureEvaluation will learn from database. Only works when the corresponding tables exist in the database.**
- `domains`: dict. Default is {}. The format is {'var1': ['val1', 'val2', ...], ...}. **Domain cannot be empty when using BDD engine!**
- `reasoning_engine`: `z3` or `bdd`. Default `z3`. Lettercase insensitive.
- `reasoning_sort`: `Int` or `BitVec`. Default `Int`. We use `Int` as a flag to use integer data and `BitVec` as a flag to use IP data for BDD.
- `simplification_on`: Boolean. Default `True`. A siwtch to decide if doing simplification for output conditions. **Only works when using z3 engine!**
- `information_on`: Boolean. Default `False`. It is a siwtch for printing progress information such as the steps, running sqls.

## Usage exmaple
We can use z3 and BDD in `FaureEvaluation`.

```python
conn = psycopg2.connect(
    host=cfg.postgres["host"], 
    database=cfg.postgres["db"], 
    user=cfg.postgres["user"], 
    password=cfg.postgres["password"])

domains = {
    'd1':['1', '2'],
    'd2':['1', '2'],
    'd':['1', '2']
}

sql = "select t3.a1 as a1, t1.a2 as a2 from R t1, R t2, L t3, L t4 where t1.a1 = t3.a2 and t2.a1 = t4.a2 and t3.a1 = t4.a1 and t1.a2 = '1';"
additional_condition = "d != 2"
output_table = "output"

databases = {
    'R':{
        'types':['integer', 'int4_faure', 'text[]'], 
        'names':['a1', 'a2', 'condition']
    }, 
    'l':{
        'types':['integer', 'integer', 'text[]'], 
        'names':['a1', 'a2', 'condition']
    }}

# example for z3 engine and Int reasoning type, has an assignment for databases parameter, simplification is off, printing information is on
FaureEvaluation(
    conn, 
    sql, 
    additional_condition=additional_condition, 
    output_table=output_table,
    databases=databases, 
    domains=domains, 
    reasoning_engine='z3', 
    reasoning_sort='Int', 
    simplication_on=False, 
    information_on=True)

# example for BDD engine and for IP data(using BitVec as a flag for BDD engine), no assignment for databases parameter, printing information is on
# FaureEvaluation(
#     conn, 
#     sql, 
#     additional_condition=additional_condition, 
#     output_table=output_table,
#     databases={}, 
#     domains=domains, 
#     reasoning_engine='bdd', 
#     reasoning_sort='BitVec', 
#     information_on=True)
```

example SQL script for above tables:
```sql
drop table if EXISTS R;
create table R(
    a1 integer,
    a2 int4_faure,
    condition text[]
);
insert into R  values( 3, 'd', '{"Or(d == 1, d == 2)"}');

drop table if EXISTS L;
create table L(
    a1 integer, 
    a2 integer,
    condition text[]
);
insert into L values(4, 3, '{}');
```