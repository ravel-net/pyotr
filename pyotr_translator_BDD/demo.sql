/* DEMOs - ctables
 * Policy1: Static Routes, Filter
 * dest: IP prefix
 * path:
 * condition:
 */
DROP TABLE IF EXISTS policy1 CASCADE;
CREATE UNLOGGED TABLE policy1(
       dest int4_faure,
       path int4_faure,
       condition integer
);
INSERT INTO Policy1 (dest, path, condition) VALUES 
('4','x', 1), -- '{"x == 123"}'
('y','z', 2); -- '{"y != 5", "y != 4"}'
-- ('1.2.3.4','x','{"x == [ABC]"}'),
-- ('y','z','{"y != 1.2.3.5", "y != 1.2.3.4"}');

/* DEMOs - ctables
 * Policy2: Traffic Balancer
 * dest: IP prefix
 * path:
 * condition:
 */
DROP TABLE IF EXISTS Policy2 CASCADE;
create table Policy2 ( 
       dest int4_faure, 
       path int4_faure, 
       flag int4_faure, 
       condition integer
);
INSERT INTO Policy2 (dest, path, flag, condition) VALUES 
('4','123', 'u', 3), -- '{"u == 1"}'
('8','123', 'u', 4), -- '{"u != 1"}'
('4','13', 'v', 5), -- '{"v == 1"}'
('8','13', 'v', 6); -- '{"v != 1"}'
-- ('1.2.3.4','[ABC]', 'u', '{"u == 1"}'),
-- ('5.6.7.8','[ABC]', 'u', '{"u != 1"}'),
-- ('1.2.3.4','[AC]', 'v', '{"v == 1"}'),
-- ('5.6.7.8','[AC]', 'v', '{"v != 1"}');