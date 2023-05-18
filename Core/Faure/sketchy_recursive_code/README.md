# Sketchy Recursive Faure_evaluation 

Note: in fact, implement it iteratively.

```SQL
WITH RECURSIVE temp_R(n1, n2) AS (
    SELECT * from L   -- non-recursive item
    UNION 
    SELECT t1.n1 as n1, t2.n2 as n2  --recursive item
    FROM temp_R t1, L t2
    WHERE t1.n2 = t2.n1
)
SELECT * from temp_R; -- parent query
```

**`faure_evaluation_copy.py` adds a new parameter `is_recursive`.** When we run recursive WITH query, please set `is_recursive` True. Default False.

**the sketchy recursive Faure_Evaluation only implement non-recursive item and recursive item**. That is, the final results will output irrelevant to the parent query. It will stores in `output` table. 

