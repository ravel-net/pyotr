# Benchmark

There are two folders, one is `naive` folder which stores the conditions who are not simplified, another one is `simp` folder which stores the conditions who are simplified but do not remove the contradictory conditions.

- `r1_2.sql`: contains conditions who are satisfiable and contradictory.
- `r3_4.sql`: contains conditions who are satisfiable and tautological.
- The SQL for joining two tables is: `select t1.n1 as n1, t2.n2 as n2 from r1_2 t1, r3_4 t2 where t1.n1 = '1' and t1.n2 = t2.n1;`.

