drop table if EXISTS T;
create table T ( n1 int4_faure, n2 int4_faure, status int4_faure, condition text[]);
insert into T values('1', '2', 'x', '{"x == 1"}');
insert into T values('1', '3', 'x', '{"x == 0"}');
insert into T values('2', '3', 'y', '{"y == 1"}');
insert into T values('2', '4', 'y', '{"y == 0"}');
insert into T values('3', '4', 'v', '{}');
insert into T values('5', '4', 'z', '{"z == 1"}');

drop table if EXISTS T_prime;
create table T_prime ( n1 int4_faure, n2 int4_faure, status int4_faure, condition text[]);
insert into T_prime values('1', '2', 'x', '{"x == 1"}');
insert into T_prime values('1', '4', 'x', '{"x == 0"}');
insert into T_prime values('2', '3', 'y', '{"y == 1"}');
insert into T_prime values('2', '4', 'y', '{"y == 0"}');
insert into T_prime values('3', '4', 'v', '{}');
insert into T_prime values('5', '4', 'z', '{"z == 1"}');

select 1, 4 from (select * from T where status='1') t1,
                 (select * from T where status='0') t2,
                 (select * from T where status='1') t3,
                 (select * from T where status='0') t4,
                 T t5,
                 (select * from T where status='1') t6
            where t1.n1 = '1' and t1.n2 = '2' AND
                  t2.n1 = '1' and t2.n2 = '3' AND
                  t3.n1 = '2' and t3.n2 = '3' AND
                  t4.n1 = '2' and t4.n2 = '4' AND
                  t5.n1 = '3' and t5.n2 = '4' AND
                  t6.n1 = '5' and t6.n2 = '4';

select * from T_prime t1,
                T_prime t2,
                T_prime t3,
                T_prime t4,
                T_prime t5,
                T_prime t6
        where t1.n1 = '1' and t1.n2 = '2' AND t1.status='1' AND
                t2.n1 = '1' and t2.n2 = '3' AND t2.status='0' AND
                t3.n1 = '2' and t3.n2 = '3' AND t3.status='1' AND
                t4.n1 = '2' and t4.n2 = '4' AND t4.status='0' AND
                t5.n1 = '3' and t5.n2 = '4' AND 
                t6.n1 = '5' and t6.n2 = '4' AND t6.status='1';

select * from T t1,
                T t2,
                T t3,
                T t4
        where t1.n1 = '1' and t1.n2 = t2.n1 AND
                t2.n2 = t3.n1 AND
                t3.n2 = t4.n1 AND
                t4. n2 = '4';


drop table if EXISTS T_1;
create table T_1 ( n1 int4_faure, n2 int4_faure, condition text[]);
insert into T_1 values('1', 'u', '{"x == 1"}');
insert into T_1 values('u', '2', '{}');
insert into T_1 values('1', '2', '{"x == 0"}');
insert into T_1 values('2', 'v', '{"y == 1"}');
insert into T_1 values('v', 'w', '{}');
insert into T_1 values('2', 'w', '{"y == 0"}');

drop table if EXISTS T_2;
create table T_2 ( n1 int4_faure, n2 int4_faure, condition text[]);
insert into T_2 values('1', 'u', '{"x == 1"}');
insert into T_2 values('u', '2', '{}');
insert into T_2 values('1', 'v', '{"x == 0"}');
insert into T_2 values('2', 'v', '{"y == 1"}');
insert into T_2 values('v', 'w', '{}');
insert into T_2 values('2', 'w', '{"y == 0"}');

drop table if EXISTS T_3;
create table T_3 ( n1 int4_faure, n2 int4_faure, condition text[]);
insert into T_3 values('1', '2', '{"x == 1"}');
insert into T_3 values('1', 'v', '{"x == 0"}');
insert into T_3 values('2', 'v', '{"y == 1"}');
insert into T_3 values('v', 'w', '{}');
insert into T_3 values('2', 'w', '{"y == 0"}');

-- program T_3
select 1, 2, 'w' from T_2 t1, 
                        T_2 t2,
                        T_2 t3
                where t1.n1 = '1' AND t1.n2 = '2' AND
                        t2.n1 = t1.n2 AND t2.n2 = t3.n1
UNION
SELECT 1, 2, 'w' from T_2 t1,
                        T_2 t2
                where t1.n1 = '1' AND t1.n2 = '2' AND
                        t2.n1 = '2'
UNION
SELECT 1, 'w' from T_2 t1,
                T_2 t2
                where t1.n1 = '1' AND t2.n1 = t1.n2 ;

-- program T_2
select 1, 2, 'w' from TABLE t1, 
                        TABLE t2,
                        TABLE t3, 
                        TABLE t4
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND 
                        t2.n2 = '2'AND t3.n1 = '2' AND t3.n2 = t4.n1
UNION
SELECT 1, 2, 'w' from TABLE t1,
                        TABLE t2,
                        TABLE t3
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND
                        t2.n2 = '2' AND
                        t3.n1 = '2'
UNION
SELECT 1, 'w' from TABLE t1,
                TABLE t2
                where t1.n1 = '1' AND t2.n1 = t1.n2 ;

-- program T_1
select 1, 2, 'w' from TABLE t1, 
                        TABLE t2,
                        TABLE t3, 
                        TABLE t4
                where t1.n1 = '1' AND t2.n1 = t1.n2 AND 
                        t2.n2 = '2'AND 
                        t3.n1 = '2' AND t3.n2 = t4.n1
UNION
SELECT 1, 2, 'w' from TABLE t1,
                        TABLE t2,
                        TABLE t3
                where t1.n1 = '1' AND t1.n2 = '2' AND
                        t2.n1 = '2' AND  t2.n2 = t3.n1 
UNION
SELECT 1, 2, 'w' from TABLE t1,
                        TABLE t2,
                        TABLE t3
                where t1.n1 = '1' AND t1.n2 = t2.n1 AND
                        t2.n2 = '2' AND 
                        t3.n1 = '2'
UNION
SELECT 1, 2, 'w' from TABLE t1,
                TABLE t2
                where t1.n1 = '1' AND t1.n2 = '2' AND t2.n1 = '2';
