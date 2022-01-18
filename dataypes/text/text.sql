---------------------------------------------------------------------------
--
-- inet_faure.sql-
--    This file shows how to create a new user-defined type and how to
--    use this new type.
--
--
-- Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
-- Portions Copyright (c) 1994, Regents of the University of California
--
-- src/tutorial/inet_faure.source
--
---------------------------------------------------------------------------
-- TODO: Not specifiying alignment and internal length

CREATE TABLE test_inet_text (
	a	TEXT,
	b	TEXT
);

-- data for user-defined types are just strings in the proper textual
-- representation.
INSERT INTO test_inet_text VALUES ('asd','225.242.0.0/24');
INSERT INTO test_inet_text VALUES ('asd','192.168.2.1/32');
INSERT INTO test_inet_text VALUES ('asd','1.0.0.0/24');
INSERT INTO test_inet_text VALUES ('asd','3.8.0.0/14');

INSERT INTO test_inet_text VALUES ('225.242.0.0/24', '192.168.2.1/24');
INSERT INTO test_inet_text VALUES ('x', '192.168.2.1/16');

SELECT * FROM test_inet_text;

CREATE FUNCTION text_or(TEXT, TEXT) RETURNS TEXT
   AS '/home/manwar/pyotr/dataypes/text/text' LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION text_and(TEXT, TEXT) RETURNS TEXT
   AS '/home/manwar/pyotr/dataypes/text/text' LANGUAGE C IMMUTABLE STRICT;

CREATE OPERATOR | (
   leftarg = TEXT, rightarg = TEXT, procedure = text_or,
   commutator = | --, negator = <= ,
   -- restrict = scalargtsel, join = scalargtjoinsel
);

CREATE OPERATOR & (
   leftarg = TEXT, rightarg = TEXT, procedure = text_and,
   commutator = & --, negator = <= ,
   -- restrict = scalargtsel, join = scalargtjoinsel
);
-- the table. Note that postgres needs many more tuples to start using the
-- btree index during selects.
INSERT INTO test_inet_text VALUES ('192.168.100.1/22', '192.168.100.1/22');
INSERT INTO test_inet_text VALUES ('y', 'x');

-- CREATE INDEX test_cplx_ind ON test_inet_faure
--    USING btree(a inet_faure_abs_ops);

SELECT * from test_inet_text;
SELECT * from test_inet_text where b = '192.168.100.1/24';
SELECT * from test_inet_text where b = '1.0.0.0/24';
SELECT a | b from test_inet_text;
SELECT a & b from test_inet_text;
-- SELECT * from test_inet_faure where a < '192.168.100.20';
-- SELECT * from test_inet_faure where a < '192.168.99.20';
-- SELECT * from test_inet_faure where a > '192.168.99.20';
-- SELECT * from test_inet_faure where a > '192.168.100.0';
-- SELECT * from test_inet_faure where a > '192.168.100.0';
-- SELECT * from test_inet_faure where NOT (a = '192.168.100.0');


-- clean up the example
DROP TABLE test_inet_text;
-- DROP TYPE inet_faure CASCADE;