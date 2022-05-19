# Homomorphism for toy backup link failures

It is **hard-coded** for the SQL queries of each tableau.

q1 = (T1, u1)

q2 = (T2, u2)

q3 = (T3, u3)

## Results

q3 $\subset$ q1 (i.e.q1(T3)) doesn't hold

q2 $\subset$ q1 (i.e.q1(T2)) doesn't hold

q3 $\subset$ q2 (i.e.q2(T3)) holds

## Running code

`run.py` is the script to run homo for link failure.

```python
domain = [1, 2]
variables = ['v', 'w']

begin = time.time()
run_program_T2("T_3",domain, variables) # q2(T3)
print(time.time() - begin)

run_program_T1("T_3", domain, variables) # q1(T3)
```