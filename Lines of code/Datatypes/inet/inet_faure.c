/*
 *	PostgreSQL type definitions for the INET and CIDR types.
 *
 *	src/backend/utils/adt/network.c
 *
 *	Jon Postel RIP 16 Oct 1998
 */

#include "postgres.h"

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "access/stratnum.h"
#include <ctype.h>
#include "catalog/pg_opfamily.h"
#include "catalog/pg_type.h"
#include "common/hashfn.h"
#include "common/ip.h"
#include "lib/hyperloglog.h"
// #include "libpq/libpq-be.h"
#include "libpq/pqformat.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/supportnodes.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "inet_faure.h"
#include "utils/lsyscache.h"
#include "utils/sortsupport.h"


PG_MODULE_MAGIC;

/*
 * Common INET/CIDR input routine
 */
static inet_faure *
network_in(char *src, bool is_cidr)
{
	int			bits = 0;
	inet_faure	   *dst;

	dst = (inet_faure *) palloc0(sizeof(inet_faure));

    // TODO: Not assigning default value to the header right now. Think what the default value should be
	strcpy(c_variables(dst), "0"); // denotes a lack of value. TODO: Add a boolean flag instead of this
	// if it is a c-variable
	if (isalpha(src[0]))  // TODO: Find another format for this
		strcpy(c_variables(dst), src);
	
	/*
	 * First, check to see if this is an IPv6 or IPv4 address.  IPv6 addresses
	 * will have a : somewhere in them (several, in fact) so if there is one
	 * present, assume it's V6, otherwise assume it's V4.
	 */
    else {
        if (strchr(src, ':') != NULL)
            ip_family(dst) = PGSQL_AF_INET6;
        else
            ip_family(dst) = PGSQL_AF_INET;

        bits = pg_inet_net_pton(ip_family(dst), src, ip_addr(dst),
                                is_cidr ? ip_addrsize(dst) : -1);
        if ((bits < 0) || (bits > ip_maxbits(dst)))
            ereport(ERROR,
                    (errcode(ERRCODE_INVALID_TEXT_REPRESENTATION),
            /* translator: first %s is inet or cidr */
                    errmsg("invalid input syntax for type %s: \"%s\"",
                            is_cidr ? "cidr" : "inet", src)));

		// if (is_cidr)
		// {
		// 	if (!addressOK(ip_addr(dst), bits, ip_family(dst)))
		// 		ereport(ERROR,
		// 				(errcode(ERRCODE_INVALID_TEXT_REPRESENTATION),
		// 				errmsg("invalid cidr value: \"%s\"", src),
		// 				errdetail("Value has bits set to right of mask.")));
		// }
	}
	ip_bits(dst) = bits;
	SET_INET_VARSIZE(dst);

	return dst;
}

PG_FUNCTION_INFO_V1(inet_faure_in);

Datum
inet_faure_in(PG_FUNCTION_ARGS)
{
	char	   *src = PG_GETARG_CSTRING(0);

	PG_RETURN_INET_P(network_in(src, false));
}


/*
 * Common INET/CIDR output routine
 */
static char *
network_out(inet_faure *src, bool is_cidr)
{
	char		tmp[sizeof("xxxx:xxxx:xxxx:xxxx:xxxx:xxxx:255.255.255.255/128")];
	char	   *dst;

    // c-variable
    if (strcmp(c_variables(src),"0") != 0) {
        dst = psprintf("%s", c_variables(src));
		PG_RETURN_CSTRING(dst);
    }
    else {
        dst = pg_inet_net_ntop(ip_family(src), ip_addr(src), ip_bits(src),
                            tmp, sizeof(tmp));
        if (dst == NULL)
            ereport(ERROR,
                    (errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
                    errmsg("could not format inet value: %m")));

        return pstrdup(tmp);
    }
}

PG_FUNCTION_INFO_V1(inet_faure_out);

Datum
inet_faure_out(PG_FUNCTION_ARGS)
{
	inet_faure 	   *src = PG_GETARG_INET_PP(0);

	PG_RETURN_CSTRING(network_out(src, false));
}


static int32
network_cmp_internal(inet_faure *a1, inet_faure *a2)
{
    // TODO: Decide what to do in case of c-variables. Currently we return 2 and default to true whenever 2 is returned (to preserve tuples that contain c-vars). But this approach does not work if we have something like NOT (condition)
    if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
		return 0;

	if (ip_family(a1) == ip_family(a2))
	{
		int			order;

		order = bitncmp(ip_addr(a1), ip_addr(a2),
						Min(ip_bits(a1), ip_bits(a2)));
		// fprintf(stderr, "order: %d\n", order);
		// fprintf(stderr, "order: %d\n", order);
		if (order != 0)
			return order;
		order = ((int) ip_bits(a1)) - ((int) ip_bits(a2));
		if (order != 0)
			return order;
		return bitncmp(ip_addr(a1), ip_addr(a2), ip_maxbits(a1));
	}

	return ip_family(a1) - ip_family(a2);
}

PG_FUNCTION_INFO_V1(network_cmp);

// FIXME: This function would not work correctly in case of c-variables. Need to think of a fix. Return 0 in case of c variables for now
Datum
network_cmp(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);
    
	PG_RETURN_INT32(network_cmp_internal(a1,a2));
}

/*
 *	Boolean ordering tests.
 */
PG_FUNCTION_INFO_V1(c_less);

Datum
c_less(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0)
        PG_RETURN_BOOL(true);
    

	PG_RETURN_BOOL(network_cmp_internal(a1,a2) < 0);
}

PG_FUNCTION_INFO_V1(c_leq);

Datum
c_leq(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);

	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);
    

	PG_RETURN_BOOL(network_cmp_internal(a1,a2) <= 0);
}

PG_FUNCTION_INFO_V1(c_equal);

Datum
c_equal(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);
    

	PG_RETURN_BOOL(network_cmp_internal(a1,a2) == 0);
}

PG_FUNCTION_INFO_V1(c_geq);

Datum
c_geq(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(network_cmp_internal(a1,a2) >= 0);
}

PG_FUNCTION_INFO_V1(c_greater);

Datum
c_greater(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);
    

	PG_RETURN_BOOL(network_cmp_internal(a1,a2) > 0);
}

PG_FUNCTION_INFO_V1(c_not_equal);

Datum
c_not_equal(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);
	inet_faure	   *a2 = PG_GETARG_INET_PP(1);
	if (strcmp(c_variables(a1),"0") != 0 || strcmp(c_variables(a2),"0") != 0) 
        PG_RETURN_BOOL(true);

	PG_RETURN_BOOL( network_cmp_internal(a1,a2) != 0);
}


PG_FUNCTION_INFO_V1(inet_faureand);

Datum
inet_faureand(PG_FUNCTION_ARGS)
{
	inet_faure	   *ip = PG_GETARG_INET_PP(0);
	inet_faure	   *ip2 = PG_GETARG_INET_PP(1);
	inet_faure	   *dst;

	dst = (inet_faure *) palloc0(sizeof(inet_faure));


	if (strcmp(c_variables(ip),"0") != 0 || strcmp(c_variables(ip2),"0") != 0) {
        // c_variables(dst) = "or-ed";
		strcpy(c_variables(dst), "or-ed");

		PG_RETURN_INET_P(dst);
    }

	if (ip_family(ip) != ip_family(ip2))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("cannot AND inet values of different sizes")));
	else
	{
		int			nb = ip_addrsize(ip);
		unsigned char *pip = ip_addr(ip);
		unsigned char *pip2 = ip_addr(ip2);
		unsigned char *pdst = ip_addr(dst);

		while (nb-- > 0)
			pdst[nb] = pip[nb] & pip2[nb];
	}
	ip_bits(dst) = Max(ip_bits(ip), ip_bits(ip2));

	strcpy(c_variables(dst), "0");
	ip_family(dst) = ip_family(ip);
	SET_INET_VARSIZE(dst);

	PG_RETURN_INET_P(dst);
}

PG_FUNCTION_INFO_V1(inet_faureor);

Datum
inet_faureor(PG_FUNCTION_ARGS)
{
	inet_faure	   *ip = PG_GETARG_INET_PP(0);
	inet_faure	   *ip2 = PG_GETARG_INET_PP(1);
	inet_faure	   *dst;

	dst = (inet_faure *) palloc0(sizeof(inet_faure));


	if (strcmp(c_variables(ip),"0") != 0 || strcmp(c_variables(ip2),"0") != 0) {
        // c_variables(dst) = "or-ed";
		strcpy(c_variables(dst), "or-ed");
		PG_RETURN_INET_P(dst);
    }

	if (ip_family(ip) != ip_family(ip2))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("cannot OR inet values of different sizes")));
	else
	{
		int			nb = ip_addrsize(ip);
		unsigned char *pip = ip_addr(ip);
		unsigned char *pip2 = ip_addr(ip2);
		unsigned char *pdst = ip_addr(dst);

		while (nb-- > 0)
			pdst[nb] = pip[nb] | pip2[nb];
	}
	ip_bits(dst) = Max(ip_bits(ip), ip_bits(ip2));

	strcpy(c_variables(dst), "0");
	ip_family(dst) = ip_family(ip);
	SET_INET_VARSIZE(dst);
	PG_RETURN_INET_P(dst);
}

PG_FUNCTION_INFO_V1(is_var);

Datum
is_var(PG_FUNCTION_ARGS)
{
	inet_faure	   *a1 = PG_GETARG_INET_PP(0);

	// PG_RETURN_BOOL(a1->inet_data.c_var != "0");
	PG_RETURN_BOOL(strcmp(c_variables(a1),"0") != 0);
}