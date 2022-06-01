
-- Step 1: create table F
DROP TABLE IF EXISTS F CASCADE;
CREATE TABLE F (
    n1 TEXT,
    n2 TEXT,
    s integer[],
    condition TEXT[]
);

INSERT INTO F(n1, n2, s, condition) VALUES 
('1', 'x1', ARRAY[1], ARRAY['l1 == x1', 'Or(x1 == 2, x1 == 3, x1 == 5)']),
('2', 'x2', ARRAY[]::integer[], ARRAY['l2 == x2', 'Or(x2 == 1, x2 == 3)']),
('2', 'x2', ARRAY[2], ARRAY['l2 == x2', 'Or(x2 == 4)']),
('3', 'x3', ARRAY[]::integer[], ARRAY['l3 == x3', 'Or(x3 == 1)']),
('3', 'x3', ARRAY[3], ARRAY['l3 == x3', 'Or(x3 == 2)']),
('4', 'x4', ARRAY[]::integer[], ARRAY['l4 == x4', 'Or(x4 == 2)']),
('4', 'x4', ARRAY[4], ARRAY['l4 == x4', 'Or(x4 == 5)']);

-- Step 2: create R table
-- 2.1: R1 <- F
DROP TABLE IF EXISTS R1 CASCADE;
CREATE TABLE R1 AS
SELECT 
n1, n2 as n3, s, condition
FROM F;

-- 2.2: R(n) <- R(n-1) JOIN F 
-- create data content
DROP TABLE IF EXISTS R2;
CREATE TABLE R2 AS 
SELECT r1.n1, r1.n3 as n2, f.n1 AS f_n2, f.n2 AS n3,
array_cat(r1.s, f.s) AS s,
array_cat(r1.condition, f.condition) AS condition 
FROM r1, f 
WHERE equal(f.n2, r1.n1) 
AND not_equal(f.n1, r1.n3) 
AND not F.s[1] = ANY(R1.s); 

-- 2.3 Update Condition
-- join condition
UPDATE R2 SET condition = array_append(condition, n2 || ' == ' || f_n2);
UPDATE R2 SET condition = array_append(condition, n1 || ' != ' || n3);

-- projection condition
-- UPDATE R2 SET n2 = f_n2 WHERE not is_var(n2);

-- UPDATE output SET s = f_s WHERE not is_var(s);
-- UPDATE output SET condition = f_condition WHERE not is_var(condition);
ALTER TABLE R2 DROP COLUMN n2, DROP COLUMN f_n2; 

-- Normalization
DELETE FROM R2 WHERE is_contradiction(condition);
UPDATE R2 SET condition = '{}' WHERE is_tauto(condition);
UPDATE R2 SET condition = remove_redundant(condition) where has_redundant(condition);

-- create R3
-- create data content
DROP TABLE IF EXISTS R3;
CREATE TABLE R3 AS 
SELECT r2.n1, r2.n3 AS n2, f.n1 AS f_n2, f.n2 AS n3,
array_cat(r2.s, f.s) AS s,
array_cat(r2.condition, f.condition) AS condition 
FROM r2, f 
WHERE equal(f.n2, r2.n1) 
AND not_equal(f.n1, r2.n3) 
AND not F.s[1] = ANY(R2.s); 

-- join condition
UPDATE R3 SET condition = array_append(condition, n2 || ' == ' || f_n2);
UPDATE R3 SET condition = array_append(condition, n1 || ' != ' || n3);

-- projection condition
ALTER TABLE R3 DROP COLUMN n2, DROP COLUMN f_n2; 

-- Normalization
DELETE FROM R3 WHERE is_contradiction(condition);
UPDATE R3 SET condition = '{}' WHERE is_tauto(condition);
UPDATE R3 SET condition = remove_redundant(condition) where has_redundant(condition);

-- create R4
-- create data content
DROP TABLE IF EXISTS R4;
CREATE TABLE R4 AS 
SELECT r3.n1, r3.n3 AS n2, f.n1 AS f_n2, f.n2 AS n3,
array_cat(r3.s, f.s) AS s,
array_cat(r3.condition, f.condition) AS condition 
FROM r3, f 
WHERE equal(f.n2, r3.n1) 
AND not_equal(f.n1, r3.n3) 
AND not F.s[1] = ANY(r3.s); 

-- join condition
UPDATE R4 SET condition = array_append(condition, n2 || ' == ' || f_n2);
UPDATE R4 SET condition = array_append(condition, n1 || ' != ' || n3);

-- projection condition
ALTER TABLE R4 DROP COLUMN n2, DROP COLUMN f_n2; 

-- Normalization
DELETE FROM R4 WHERE is_contradiction(condition);
UPDATE R4 SET condition = '{}' WHERE is_tauto(condition);
UPDATE R4 SET condition = remove_redundant(condition) where has_redundant(condition);

-- Step 3: R <- R1 union R2 union R3 union ...
DROP TABLE IF EXISTS R CASCADE;
CREATE TABLE R AS
SELECT * FROM R1 union
SELECT * FROM R2 union
SELECT * FROM R3 union
SELECT * FROM R4;

ALTER TABLE R RENAME COLUMN n3 TO n2;

-- lower-bound query
-- ? <- R(1, 5, s), not (3 belongs to s)
-- regular SQL query
SELECT * FROM R 
WHERE n1 = 1 
and n2 = 5
and not 3 = ANY(s);

-- ctable SQL
-- Step 1: create data content
DROP TABLE IF EXISTS output; 
CREATE TABLE output AS 
select * from r  
where  equal(n1, '1') 
and equal(n2, '5')
and not 3 = ANY(s);

-- update select condtions
UPDATE output SET condition = array_append(condition, n1 ||' == '|| '1') ;
UPDATE output SET condition = array_append(condition, n2 ||' == '|| '5') ;

-- Normalization
DELETE FROM output WHERE is_contradiction(output.condition);
UPDATE output SET condition = '{}' WHERE is_tauto(output.condition);
UPDATE output SET condition = remove_redundant(condition) where has_redundant(condition);

-- upper-bound query









