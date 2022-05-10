#include "postgres.h"

#include "fmgr.h"
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include "access/stratnum.h"
#include "catalog/pg_opfamily.h"
#include "catalog/pg_type.h"
#include "common/hashfn.h"
#include "common/ip.h"
#include "lib/hyperloglog.h"
#include "libpq/pqformat.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/supportnodes.h"
#include "utils/builtins.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "utils/inet.h"
#include "utils/lsyscache.h"
#include "utils/sortsupport.h"

PG_MODULE_MAGIC;

typedef struct inet_faure
{
	char		vl_len_[4];		/* Convention for variable length */
	inet		header;
	char		c_var;
}			inet_faure;

static char *
network_out(inet src, bool is_cidr)
{
	char		tmp[sizeof("xxxx:xxxx:xxxx:xxxx:xxxx:xxxx:255.255.255.255/128")];
	char	   *dst;
	int			len;

	dst = pg_inet_net_ntop(ip_family(&src), ip_addr(&src), ip_bits(&src),
						   tmp, sizeof(tmp));
	if (dst == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
				 errmsg("could not format inet value: %m")));

	return pstrdup(tmp);
}

// Add one byte for the extra char
#define SET_INET_C_VARSIZE(dst) \
	SET_VARSIZE(dst, VARHDRSZ + offsetof(inet_struct, ipaddr) + \
				ip_addrsize(dst) + sizeof(char))

static inet *
network_in(char *src, bool is_cidr)
{
	int			bits;
	inet	   *dst;

	dst = (inet *) palloc0(sizeof(inet));

	/*
	 * First, check to see if this is an IPv6 or IPv4 address.  IPv6 addresses
	 * will have a : somewhere in them (several, in fact) so if there is one
	 * present, assume it's V6, otherwise assume it's V4.
	 */

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

	SET_INET_C_VARSIZE(dst);
	ip_bits(dst) = bits;

	return dst;
}

static inet *
network_recv(StringInfo buf, bool is_cidr)
{
	inet	   *addr;
	char	   *addrptr;
	int			bits;
	int			nb,
				i;

	/* make sure any unused bits in a CIDR value are zeroed */
	addr = (inet *) palloc0(sizeof(inet));

	ip_family(addr) = pq_getmsgbyte(buf);
	if (ip_family(addr) != PGSQL_AF_INET &&
		ip_family(addr) != PGSQL_AF_INET6)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
		/* translator: %s is inet or cidr */
				 errmsg("invalid address family in external \"%s\" value",
						is_cidr ? "cidr" : "inet")));
	bits = pq_getmsgbyte(buf);
	if (bits < 0 || bits > ip_maxbits(addr))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
		/* translator: %s is inet or cidr */
				 errmsg("invalid bits in external \"%s\" value",
						is_cidr ? "cidr" : "inet")));
	ip_bits(addr) = bits;
	i = pq_getmsgbyte(buf);		/* ignore is_cidr */
	nb = pq_getmsgbyte(buf);
	if (nb != ip_addrsize(addr))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_BINARY_REPRESENTATION),
		/* translator: %s is inet or cidr */
				 errmsg("invalid length in external \"%s\" value",
						is_cidr ? "cidr" : "inet")));

	addrptr = (char *) ip_addr(addr);
	for (i = 0; i < nb; i++)
		addrptr[i] = pq_getmsgbyte(buf);

	SET_INET_C_VARSIZE(addr);

	return addr;
}

static bytea *
network_send(inet *addr, bool is_cidr)
{
	StringInfoData buf;
	char	   *addrptr;
	int			nb,
				i;

	pq_begintypsend(&buf);
	pq_sendbyte(&buf, ip_family(addr));
	pq_sendbyte(&buf, ip_bits(addr));
	pq_sendbyte(&buf, is_cidr);
	nb = ip_addrsize(addr);
	if (nb < 0)
		nb = 0;
	pq_sendbyte(&buf, nb);
	addrptr = (char *) ip_addr(addr);
	for (i = 0; i < nb; i++)
		pq_sendbyte(&buf, addrptr[i]);
	return pq_endtypsend(&buf);
}

static int32
network_cmp_internal(inet *a1, inet *a2)
{
	if (ip_family(a1) == ip_family(a2))
	{
		int			order;

		order = bitncmp(ip_addr(a1), ip_addr(a2),
						Min(ip_bits(a1), ip_bits(a2)));
		if (order != 0)
			return order;
		order = ((int) ip_bits(a1)) - ((int) ip_bits(a2));
		if (order != 0)
			return order;
		return bitncmp(ip_addr(a1), ip_addr(a2), ip_maxbits(a1));
	}

	return ip_family(a1) - ip_family(a2);
}


// /*****************************************************************************
//  * Input/Output functions
//  ********************************************s*********************************/

PG_FUNCTION_INFO_V1(inet_faure_in);

Datum
inet_faure_in(PG_FUNCTION_ARGS)
{
	inet		header;
	char		c_var;
	inet_faure    *result;

	char	   *src = PG_GETARG_CSTRING(0); //

	// TODO: Not assigning default value to the header right now. Think what the default value should be
	c_var = '0'; // denotes a lack of value. TODO: Add a boolean flag instead of this
	// if it is a c-variable
	if (src[0] == 'x' || src[0] == 'y') {
		c_var = src[0];
	}
	else {
		header = *network_in(src, false);
	}

	result = (inet_faure *) palloc(sizeof(inet_faure));
	result->header = header;
	result->c_var = c_var;
	PG_RETURN_POINTER(result);
}

PG_FUNCTION_INFO_V1(inet_faure_out);

Datum
inet_faure_out(PG_FUNCTION_ARGS)
{
	inet_faure    *inet_out = (inet_faure *) PG_GETARG_POINTER(0);
	char	   *result;

	// TODO: Replace this hacky check with a function is_conditional
	if (inet_out->c_var != '0') {
		result = psprintf("%c", inet_out->c_var);
		PG_RETURN_CSTRING(result);
	}
	else {
		inet	   src = inet_out->header; // FIXME: Passing by memory reference, might be dangerous
		PG_RETURN_CSTRING(network_out(src, false));
	}
}

// /*****************************************************************************
//  * Binary Input/Output functions
//  *
//  * These are optional.
//  *****************************************************************************/

PG_FUNCTION_INFO_V1(inet_faure_recv);

Datum
inet_faure_recv(PG_FUNCTION_ARGS)
{
	StringInfo	buf = (StringInfo) PG_GETARG_POINTER(0);
	inet_faure    *result;

	result = (inet_faure *) palloc(sizeof(inet_faure));
	result->header = *network_recv(buf, true); // FIXME: Can we remove the pointer conversion here?
	result->c_var = pq_getmsgbyte(buf); // TODO: Make sure that this is correct. Assuming char is of a single byte
	PG_RETURN_POINTER(result);
}

PG_FUNCTION_INFO_V1(inet_faure_send);

Datum
inet_faure_send(PG_FUNCTION_ARGS)
{
	inet_faure    *inet_send = (inet_faure *) PG_GETARG_POINTER(0);
	StringInfoData buf;

	pq_begintypsend(&buf);
	bytea* inet_bytes = network_send(&inet_send->header, false);
	pq_sendbyte(&buf, inet_send->c_var); // TODO: Make sure that this is correct. Assuming char is of a single byte
	PG_RETURN_BYTEA_P(pq_endtypsend(&buf)); // TODO: Not sure if this is correct. Don't know what we are supposed to return. Copied this line from examples
}

// /*****************************************************************************
//  * New Operators
//  *
//  * A practical Complex datatype would provide much more than this, of course.
//  *****************************************************************************/

// PG_FUNCTION_INFO_V1(complex_add);

// Datum
// complex_add(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);
// 	Complex    *result;

// 	result = (Complex *) palloc(sizeof(Complex));
// 	result->x = a->x + b->x;
// 	result->y = a->y + b->y;
// 	PG_RETURN_POINTER(result);
// }


// /*****************************************************************************
//  * Operator class for defining B-tree index
//  *
//  * It's essential that the comparison operators and support function for a
//  * B-tree index opclass always agree on the relative ordering of any two
//  * data values.  Experience has shown that it's depressingly easy to write
//  * unintentionally inconsistent functions.  One way to reduce the odds of
//  * making a mistake is to make all the functions simple wrappers around
//  * an internal three-way-comparison function, as we do here.
//  *****************************************************************************/

// #define Mag(c)	((c)->x*(c)->x + (c)->y*(c)->y)

static int
inet_faure_cmp_internal(inet_faure * a, inet_faure * b)
{
	char		a_c_var = a->c_var,
				b_c_var = b->c_var;
	
	// If either of them are c-variables, return true
	if (a_c_var == '0' || b_c_var == '0') {
		return 0; // 
	}

	inet		a_header = a->header,
				b_header = b->header;

	return(network_cmp_internal(&a_header, &b_header));
}


// PG_FUNCTION_INFO_V1(complex_abs_lt);

// Datum
// complex_abs_lt(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);

// 	PG_RETURN_BOOL(complex_abs_cmp_internal(a, b) < 0);
// }

// PG_FUNCTION_INFO_V1(complex_abs_le);

// Datum
// complex_abs_le(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);

// 	PG_RETURN_BOOL(complex_abs_cmp_internal(a, b) <= 0);
// }

PG_FUNCTION_INFO_V1(inet_faure_eq);

Datum
inet_faure_eq(PG_FUNCTION_ARGS)
{
	inet_faure    *a = (inet_faure *) PG_GETARG_POINTER(0);
	inet_faure    *b = (inet_faure *) PG_GETARG_POINTER(1);

	PG_RETURN_BOOL(inet_faure_cmp_internal(a, b) == 0);
}

PG_FUNCTION_INFO_V1(inet_faure_cmp);
Datum
inet_faure_cmp(PG_FUNCTION_ARGS)
{
	inet_faure    *a = (inet_faure *) PG_GETARG_POINTER(0);
	inet_faure    *b = (inet_faure *) PG_GETARG_POINTER(1);

	PG_RETURN_INT32(inet_faure_cmp_internal(a, b));
}

// PG_FUNCTION_INFO_V1(complex_abs_ge);

// Datum
// complex_abs_ge(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);

// 	PG_RETURN_BOOL(complex_abs_cmp_internal(a, b) >= 0);
// }

// PG_FUNCTION_INFO_V1(complex_abs_gt);

// Datum
// complex_abs_gt(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);

// 	PG_RETURN_BOOL(complex_abs_cmp_internal(a, b) > 0);
// }

// PG_FUNCTION_INFO_V1(complex_abs_cmp);

// Datum
// complex_abs_cmp(PG_FUNCTION_ARGS)
// {
// 	Complex    *a = (Complex *) PG_GETARG_POINTER(0);
// 	Complex    *b = (Complex *) PG_GETARG_POINTER(1);

// 	PG_RETURN_INT32(complex_abs_cmp_internal(a, b));
// }
