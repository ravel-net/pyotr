
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
n1, n2, s, condition
FROM F;

-- 2.2: R(n) <- R(n-1) JOIN F 
DROP TABLE IF EXISTS R2 CASCADE;
CREATE TABLE R2 AS
SELECT
F.n1 as n1, R1.n2 as n2,
array_cat(F.s, R1.s) as s,
array_cat(F.condition, R1.condition) as condition
FROM R1, F
WHERE F.n2 = R1.n1 and F.n1 != R1.n2 and F.s[1] != ANY(R1.s);

DROP TABLE IF EXISTS R3 CASCADE;
CREATE TABLE R3 AS
SELECT
F.n1 as n1, R2.n2 as n2,
array_cat(F.s, R2.s) as s,
array_cat(F.condition, R2.condition) as condition
FROM R2, F
WHERE F.n2 = R2.n1 and F.n1 != R2.n2 and F.s[1] != ANY(R2.s);

DROP TABLE IF EXISTS R4 CASCADE;
CREATE TABLE R4 AS
SELECT
F.n1 as n1, R3.n2 as n2,
array_cat(F.s, R3.s) as s,
array_cat(F.condition, R3.condition) as condition
FROM R3, F
WHERE F.n2 = R3.n1 and F.n1 != R3.n2 and F.s[1] != ANY(R3.s);

SELECT
F.n1 as n1, R4.n2 as n2,
array_cat(F.s, R4.s) as s,
array_cat(F.condition, R4.condition) as condition
FROM R4, F
WHERE F.n2 = R4.n1 and F.n1 != R4.n2 and F.s[1] != ANY(R4.s);

-- 2.3: (reachability) R <- R1 union R2
DROP TABLE IF EXISTS R CASCADE;
CREATE TABLE R AS
SELECT * FROM R1 union
SELECT * FROM R2 union
SELECT * FROM R3 union
SELECT * FROM R4;


-- Step 3: Queries
-- 3.1: lower-bound query
-- ? <- R(1, 5, s), not (3 belongs to s)
SELECT * FROM R 
WHERE n1 = 1 
and n2 = 5
and not 3 = ANY(s);

-- 3.2 upper-bound query
SELECT * FROM R
WHERE n1 = 1
and n2 = 5 
and 1 = ANY(s)
and 2 = ANY(s)
and 4 = ANY(s);

