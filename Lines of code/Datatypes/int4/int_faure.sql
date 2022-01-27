---------------------------------------------------------------------------
--
-- int4_faure.sql-
--    This file shows how to create a new user-defined type and how to
--    use this new type.
--
--
-- Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
-- Portions Copyright (c) 1994, Regents of the University of California
--
-- src/tutorial/int4_faure.source
--
---------------------------------------------------------------------------

-----------------------------
-- Creating a new type:
--	We are going to create a new type called 'int4_faure' which represents
--	int4_faure numbers.
--	A user-defined type must have an input and an output function, and
--	optionally can have binary input and output functions.  All of these
--	are usually user-defined C functions.
-----------------------------

-- Assume the user defined functions are in _OBJWD_/int_faure$DLSUFFIX
-- (we do not want to assume this is in the dynamic loader search path).
-- Look at $PWD/int4_faure.c for the source.  Note that we declare all of
-- them as STRICT, so we do not need to cope with NULL inputs in the
-- C code.  We also mark them IMMUTABLE, since they always return the
-- same outputs given the same inputs.

-- the input function 'int4_faure_in' takes a null-terminated string (the
-- textual representation of the type) and turns it into the internal
-- (in memory) representation. You will get a message telling you 'int4_faure'
-- does not exist yet but that's okay.

CREATE FUNCTION int4_faurein(cstring)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

-- the output function 'inet_faure_out' takes the internal representation and
-- converts it into the textual representation.

CREATE FUNCTION int4_faureout(int4_faure)
   RETURNS cstring
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;

CREATE FUNCTION bool_int4_faure(bool)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION int4_faure_bool(int4_faure)
   RETURNS bool
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

-- the binary input function 'inet_faure_recv' takes a StringInfo buffer
-- and turns its contents into the internal representation.

--CREATE FUNCTION inet_faure_recv(internal)
--   RETURNS inet_faure
--   AS '_OBJWD_/inet_faure'
--   LANGUAGE C IMMUTABLE STRICT;

-- the binary output function 'inet_faure_send' takes the internal representation
-- and converts it into a (hopefully) platform-independent bytea string.

--CREATE FUNCTION inet_faure_send(inet_faure)
--   RETURNS bytea
--   AS '_OBJWD_/inet_faure'
--   LANGUAGE C IMMUTABLE STRICT;


-- now, we can create the type. The internallength specifies the size of the
-- memory block required to hold the type (we need two 8-byte doubles).

-- TODO: Not specifiying alignment and internal length
CREATE TYPE int4_faure (
   internallength = 24,
   input = int4_faurein,
   output = int4_faureout
   -- receive = inet_faure_recv,
   -- send = inet_faure_send,
   -- alignment = double
);


-----------------------------
-- Creating an operator for the new type:
--	Let's define an add operator for int4_faure types. Since POSTGRES
--	supports function overloading, we'll use + as the add operator.
--	(Operator names can be reused with different numbers and types of
--	arguments.)
-----------------------------

-- first, define a function int4_faure_add (also in int4_faure.c)

CREATE FUNCTION int4_faure_um(int4_faure)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION int4_faure_pl(int4_faure, int4_faure)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION int4_faure_mul(int4_faure, int4_faure)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION int4_faure_div(int4_faure, int4_faure)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

CREATE FUNCTION int4_faure_mi(int4_faure, int4_faure)
   RETURNS int4_faure
   AS '_OBJWD_/int_faure'
   LANGUAGE C IMMUTABLE STRICT;

-- we can now define the operator. We show a binary operator here but you
-- can also define a prefix operator by omitting the leftarg.

--   oprname => '-', oprkind => 'l', oprleft => '0', oprright => 'int4',
--   oprresult => 'int4', oprcode => 'int4um' },
CREATE OPERATOR - (
   rightarg = int4_faure,
   procedure = int4_faure_um
);

CREATE OPERATOR + (
   leftarg = int4_faure,
   rightarg = int4_faure,
   procedure = int4_faure_pl,
   commutator = + 
);

CREATE OPERATOR * (
   leftarg = int4_faure,
   rightarg = int4_faure,
   procedure = int4_faure_mul,
   commutator = * 
);

CREATE OPERATOR - (
   leftarg = int4_faure,
   rightarg = int4_faure,
   procedure = int4_faure_mi
);

CREATE OPERATOR / (
   leftarg = int4_faure,
   rightarg = int4_faure,
   procedure = int4_faure_div
);


CREATE FUNCTION int4_faure_lt(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION int4_faure_le(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION int4_faure_eq(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION int4_faure_ge(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION int4_faure_gt(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION int4_faure_ne(int4_faure, int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT PARALLEL SAFE;
CREATE FUNCTION is_var(int4_faure) RETURNS bool
   AS '_OBJWD_/int_faure' LANGUAGE C IMMUTABLE STRICT;

CREATE OPERATOR < (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_lt,
   -- commutator = > , negator = >= ,
   restrict = scalarltsel, join = scalarltjoinsel
);
CREATE OPERATOR <= (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_le,
   -- commutator = >= , negator = > ,
   restrict = scalarlesel, join = scalarlejoinsel
);
CREATE OPERATOR = (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_eq,
   commutator = = ,
   -- negator = <> ,
   restrict = eqsel, join = eqjoinsel
);

CREATE OPERATOR >= (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_ge,
   -- commutator = <= , negator = < ,
   restrict = scalargesel, join = scalargejoinsel
);

CREATE OPERATOR <> (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_ne,
   -- commutator = <= , negator = < ,
   restrict = neqsel, join = neqjoinsel
);

CREATE OPERATOR > (
   leftarg = int4_faure, rightarg = int4_faure, procedure = int4_faure_gt,
   -- commutator = < , negator = <= ,
   restrict = scalargtsel, join = scalargtjoinsel
);