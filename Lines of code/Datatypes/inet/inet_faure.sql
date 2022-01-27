CREATE FUNCTION inet_faure_in(cstring)
   RETURNS inet_faure
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure'
   LANGUAGE C IMMUTABLE STRICT;

-- the output function 'inet_faure_out' takes the internal representation and
-- converts it into the textual representation.

CREATE FUNCTION inet_faure_out(inet_faure)
   RETURNS cstring
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure'
   LANGUAGE C IMMUTABLE STRICT;

-- TODO: Not specifiying alignment and internal length
CREATE TYPE inet_faure (
   input = inet_faure_in,
   output = inet_faure_out
   -- receive = inet_faure_recv,
   -- send = inet_faure_send,
   -- alignment = double
);


-----------------------------
-- Using the new type:
--	user-defined types can be used like ordinary built-in types.
-----------------------------

-- first, define the required operators

CREATE FUNCTION c_less(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION c_leq(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION c_equal(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION c_geq(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION c_greater(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION c_not_equal(inet_faure, inet_faure) RETURNS bool
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION inet_faureor(inet_faure, inet_faure) RETURNS inet_faure
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;
CREATE FUNCTION inet_faureand(inet_faure, inet_faure) RETURNS inet_faure
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;

CREATE OPERATOR < (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_less,
   -- commutator = > , negator = >= ,
   restrict = scalarltsel, join = scalarltjoinsel
);
CREATE OPERATOR <= (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_leq,
   -- commutator = >= , negator = > ,
   restrict = scalarlesel, join = scalarlejoinsel
);
CREATE OPERATOR = (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_equal,
   commutator = = ,
   -- leave out negator since we didn't create <> operator
   -- negator = <> ,
   restrict = eqsel, join = eqjoinsel, MERGES
);

CREATE OPERATOR >= (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_geq,
   -- commutator = <= , negator = < ,
   restrict = scalargesel, join = scalargejoinsel
);

CREATE OPERATOR <> (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_not_equal,
   -- commutator = <= , negator = < ,
   restrict = neqsel, join = neqjoinsel
);

CREATE OPERATOR > (
   leftarg = inet_faure, rightarg = inet_faure, procedure = c_greater,
   -- commutator = < , negator = <= ,
   restrict = scalargtsel, join = scalargtjoinsel
);

CREATE OPERATOR | (
   leftarg = inet_faure, rightarg = inet_faure, procedure = inet_faureor,
   commutator = | --, negator = <= ,
   -- restrict = scalargtsel, join = scalargtjoinsel
);

CREATE OPERATOR & (
   leftarg = inet_faure, rightarg = inet_faure, procedure = inet_faureand,
   commutator = & --, negator = <= ,
   -- restrict = scalargtsel, join = scalargtjoinsel
);
-- create the support function too
CREATE FUNCTION network_cmp(inet_faure, inet_faure) RETURNS int4
   AS '/home/mudbri/Documents/GitHub/pyotr/dataypes/inet_faure/inet_faure' LANGUAGE C IMMUTABLE STRICT;

-- now we can make the operator class