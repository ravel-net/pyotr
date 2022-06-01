
-- Step 1: create table F
DROP TABLE IF EXISTS F CASCADE;
CREATE TABLE F (
    n1 integer,
    n2 integer,
    s integer[],
    condition TEXT[]
);

INSERT INTO F(n1, n2, s, condition) VALUES 
(1, 2, ARRAY[1], ARRAY['l1 == 2']),
(1, 3, ARRAY[1], ARRAY['l1 == 3']),
(1, 5, ARRAY[1], ARRAY['l1 == 5']),
(2, 1, ARRAY[]::integer[], ARRAY['l2 == 1']),
(2, 3, ARRAY[]::integer[], ARRAY['l2 == 3']),
(2, 4, ARRAY[2], ARRAY['l2 == 4']),
(3, 1, ARRAY[]::integer[], ARRAY['l3 == 1']),
(3, 2, ARRAY[3], ARRAY['l3 == 2']),
(4, 2, ARRAY[]::integer[], ARRAY['l4 == 2']),
(4, 5, ARRAY[4], ARRAY['l4 == 5']);

-- Step 2: create R table
-- 2.1: R1 <- F
DROP TABLE IF EXISTS R1 CASCADE;
CREATE TABLE R1 AS
SELECT 
n1, n2, s, ARRAY[n1, n2] as path, condition
FROM F;

-- 2.2: R(n) <- R(n-1) JOIN F 
DROP TABLE IF EXISTS R2 CASCADE;
CREATE TABLE R2 AS
SELECT
R1.n1 as n1, F.n2 as n2,
array_cat(F.s, R1.s) as s,
array_cat(R1.path, ARRAY[F.n2]) as path,
array_cat(R1.condition, F.condition) as condition
FROM R1, F
WHERE R1.n2 = F.n1 and R1.n1 != F.n2 and not F.s[1] = ANY(R1.s) and not F.n2 = ANY(R1.path);

DROP TABLE IF EXISTS R3 CASCADE;
CREATE TABLE R3 AS
SELECT
R2.n1 as n1, F.n2 as n2,
array_cat(F.s, R2.s) as s,
array_cat(R2.path, ARRAY[F.n2]) as path,
array_cat(R2.condition, F.condition) as condition
FROM R2, F
WHERE R2.n2 = F.n1 and R2.n1 != F.n2 and not F.s[1] = ANY(R2.s) and not F.n2 = ANY(R2.path);

DROP TABLE IF EXISTS R4 CASCADE;
CREATE TABLE R4 AS
SELECT
R3.n1 as n1, F.n2 as n2,
array_cat(F.s, R3.s) as s,
array_cat(R3.path, ARRAY[F.n2]) as path,
array_cat(R3.condition, F.condition) as condition
FROM R3, F
WHERE R3.n2 = F.n1 and R3.n1 != F.n2 and not F.s[1] = ANY(R3.s) and not F.n2 = ANY(R3.path);

DROP TABLE IF EXISTS R5 CASCADE;
CREATE TABLE R5 AS
SELECT
R4.n1 as n1, F.n2 as n2,
array_cat(F.s, R4.s) as s,
array_cat(R4.path, ARRAY[F.n2]) as path,
array_cat(R4.condition, F.condition) as condition
FROM R4, F
WHERE R4.n2 = F.n1 and R4.n1 != F.n2 and not F.s[1] = ANY(R4.s) and not F.n2 = ANY(R4.path);

DROP TABLE IF EXISTS R6 CASCADE;
CREATE TABLE R6 AS
SELECT
R5.n1 as n1, F.n2 as n2,
array_cat(F.s, R5.s) as s,
array_cat(R5.path, ARRAY[F.n2]) as path,
array_cat(R5.condition, F.condition) as condition
FROM R5, F
WHERE R5.n2 = F.n1 and R5.n1 != F.n2 and not F.s[1] = ANY(R5.s) and not F.n2 = ANY(R5.path);

DROP TABLE IF EXISTS R7 CASCADE;
CREATE TABLE R7 AS
SELECT
R6.n1 as n1, F.n2 as n2,
array_cat(F.s, R6.s) as s,
array_cat(R6.path, ARRAY[F.n2]) as path,
array_cat(R6.condition, F.condition) as condition
FROM R6, F
WHERE R6.n2 = F.n1 and R6.n1 != F.n2 and not F.s[1] = ANY(R6.s) and not F.n2 = ANY(R6.path);

DROP TABLE IF EXISTS R8 CASCADE;
CREATE TABLE R8 AS
SELECT
R7.n1 as n1, F.n2 as n2,
array_cat(F.s, R7.s) as s,
array_cat(R7.path, ARRAY[F.n2]) as path,
array_cat(R7.condition, F.condition) as condition
FROM R7, F
WHERE R7.n2 = F.n1 and R7.n1 != F.n2 and not F.s[1] = ANY(R7.s) and not F.n2 = ANY(R7.path);

DROP TABLE IF EXISTS R9 CASCADE;
CREATE TABLE R9 AS
SELECT
R8.n1 as n1, F.n2 as n2,
array_cat(F.s, R8.s) as s,
array_cat(R8.path, ARRAY[F.n2]) as path,
array_cat(R8.condition, F.condition) as condition
FROM R8, F
WHERE R8.n2 = F.n1 and R8.n1 != F.n2 and not F.s[1] = ANY(R8.s) and not F.n2 = ANY(R8.path);

DROP TABLE IF EXISTS R10 CASCADE;
CREATE TABLE R10 AS
SELECT
R9.n1 as n1, F.n2 as n2,
array_cat(F.s, R9.s) as s,
array_cat(R9.path, ARRAY[F.n2]) as path,
array_cat(R9.condition, F.condition) as condition
FROM R9, F
WHERE R9.n2 = F.n1 and R9.n1 != F.n2 and not F.s[1] = ANY(R9.s) and not F.n2 = ANY(R9.path);

DROP TABLE IF EXISTS R11 CASCADE;
CREATE TABLE R11 AS
SELECT
R10.n1 as n1, F.n2 as n2,
array_cat(F.s, R10.s) as s,
array_cat(R10.path, ARRAY[F.n2]) as path,
array_cat(R10.condition, F.condition) as condition
FROM R10, F
WHERE R10.n2 = F.n1 and R10.n1 != F.n2 and not F.s[1] = ANY(R10.s) and not F.n2 = ANY(R10.path);

DROP TABLE IF EXISTS R12 CASCADE;
CREATE TABLE R12 AS
SELECT
R11.n1 as n1, F.n2 as n2,
array_cat(F.s, R11.s) as s,
array_cat(R11.path, ARRAY[F.n2]) as path,
array_cat(R11.condition, F.condition) as condition
FROM R11, F
WHERE R11.n2 = F.n1 and R11.n1 != F.n2 and not F.s[1] = ANY(R11.s) and not F.n2 = ANY(R11.path);

DROP TABLE IF EXISTS R13 CASCADE;
CREATE TABLE R13 AS
SELECT
R12.n1 as n1, F.n2 as n2,
array_cat(F.s, R12.s) as s,
array_cat(R12.path, ARRAY[F.n2]) as path,
array_cat(R12.condition, F.condition) as condition
FROM R12, F
WHERE R12.n2 = F.n1 and R12.n1 != F.n2 and not F.s[1] = ANY(R12.s) and not F.n2 = ANY(R12.path);

DROP TABLE IF EXISTS R14 CASCADE;
CREATE TABLE R14 AS
SELECT
R13.n1 as n1, F.n2 as n2,
array_cat(F.s, R13.s) as s,
array_cat(R13.path, ARRAY[F.n2]) as path,
array_cat(R13.condition, F.condition) as condition
FROM R13, F
WHERE R13.n2 = F.n1 and R13.n1 != F.n2 and not F.s[1] = ANY(R13.s) and not F.n2 = ANY(R13.path);

DROP TABLE IF EXISTS R15 CASCADE;
CREATE TABLE R15 AS
SELECT
R14.n1 as n1, F.n2 as n2,
array_cat(F.s, R14.s) as s,
array_cat(R14.path, ARRAY[F.n2]) as path,
array_cat(R14.condition, F.condition) as condition
FROM R14, F
WHERE R14.n2 = F.n1 and R14.n1 != F.n2 and not F.s[1] = ANY(R14.s) and not F.n2 = ANY(R14.path);


-- 2.3: (reachability) R <- R1 union R2
DROP TABLE IF EXISTS R CASCADE;
CREATE TABLE R AS
SELECT n1, n2, s, condition FROM R1 union
SELECT n1, n2, s, condition FROM R2 union
SELECT n1, n2, s, condition FROM R3 union
SELECT n1, n2, s, condition FROM R4 union
SELECT n1, n2, s, condition FROM R5 union
SELECT n1, n2, s, condition FROM R6 union
SELECT n1, n2, s, condition FROM R7 union
SELECT n1, n2, s, condition FROM R8 union
SELECT n1, n2, s, condition FROM R9 union
SELECT n1, n2, s, condition FROM R10 union
SELECT n1, n2, s, condition FROM R11 union
SELECT n1, n2, s, condition FROM R12;


-- Step 3: Queries
-- 3.1: lower-bound query
-- ? <- R(1, 5, s), not (3 belongs to s)
SELECT * FROM R 
WHERE n2 = 7121
and not 3 = ANY(s);

-- 3.2 upper-bound query
SELECT * FROM R
WHERE n1 = 1
and n2 = 5 
and 1 = ANY(s)
and 2 = ANY(s)
and 4 = ANY(s);


select a.n1, b.n1 as b_n1, a.n2, b.n2 as b_n2, a.s, b.s as b_s, array_cat(a.condition, b.condition) as condition from R as a, R as b
where a.n1 = b.n1
and a.n2 = b.n2
and a.n1 = 5428 and b.n1 = 5428
and a.n2 = 7121 and b.n2 = 7121
and 129 = ANY(a.s) and 129 = ANY(b.s);
and '{"l5428 == 7121"}' = ANY(a.condition)
and '{"l5428 == 7120"}' = ANY(b.condition);

-- 3.3 Query5
-- avoid(n,5) :- R(n,5,a), 𝑙2 ≠ 3.
DROP TABLE IF EXISTS output;

SELECT * FROM r, f
WHERE r.n1 = f.n1 and r.n2 = f.n2
and n1 = 1 and n2 = 5
and 1 = ANY(r.s)
and 2 = ANY(r.s)
and 4 = ANY(r.s)




