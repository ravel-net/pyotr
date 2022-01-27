/*-------------------------------------------------------------------------
 *
 * int.c
 *	  Functions for the built-in integer types (except int8).
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/int.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * OLD COMMENTS
 *		I/O routines:
 *		 int2in, int2out, int2recv, int2send
 *		 int4in, int4out, int4recv, int4send
 *		 int2vectorin, int2vectorout, int2vectorrecv, int2vectorsend
 *		Boolean operators:
 *		 inteq, intne, intlt, intle, intgt, intge
 *		Arithmetic operators:
 *		 intpl, intmi, int4mul, intdiv
 *
 *		Arithmetic operators:
 *		 intmod
 */
#include "postgres.h"

#include <ctype.h>
#include <limits.h>
#include <math.h>

#include "fmgr.h"
#include "common/hashfn.h"
// #include "catalog/pg_type.h"
// #include "common/int.h"
#include "int_faure.h"
// #include "funcapi.h"
#include "libpq/pqformat.h"
// #include "nodes/nodeFuncs.h"
// #include "nodes/supportnodes.h"
// #include "optimizer/optimizer.h"
// #include "utils/array.h"
#include "utils/builtins.h"

PG_MODULE_MAGIC;


int4_faure* int4_faure_new(int32 i, char* c_var) { 
  int4_faure * p = (int4_faure *) palloc(sizeof(int4_faure));
  p->integer = i;
  strncpy(p->c_var, c_var, C_LEN);
  return p;
}

bool is_cvar(int4_faure* c) {
	return (strcmp(C_VAR(c),"0") != 0);
	// return (strcmp(C_VAR(c),"0") != 0 && C_VAR(c)[0] != 'i');
}

/*
 *		int4in			- converts "src" to int4
 */
PG_FUNCTION_INFO_V1(int4_faurein);

Datum
int4_faurein(PG_FUNCTION_ARGS)
{
	char	   *num = PG_GETARG_CSTRING(0);
	int4_faure * result = (int4_faure *) palloc(sizeof(int4_faure));

    // TODO: Not assigning default value to the header right now. Think what the default value should be
	strncpy(result->c_var, "0", C_LEN); // denotes a lack of value. TODO: Add a boolean flag instead of this if it is a c-variable
	result->integer = 0; // By default, the integer component is set to 0
	if (isalpha(num[0]))  // TODO: Find another format for this
		strncpy(result->c_var, num, C_LEN);
	else 
		result->integer = pg_strtoint32(num);
	// if(num[0] == 'i')
	// 	result->integer = get_interface_num(num);

	PG_RETURN_POINTER(result);
}

PG_FUNCTION_INFO_V1(int4_faureout);
/*
 *		int4out			- converts int4 to "num"
 */
Datum
int4_faureout(PG_FUNCTION_ARGS)
{
	int4_faure    *src = (int4_faure *) PG_GETARG_POINTER(0);
	char* result;

    if (strcmp(src->c_var,"0") != 0) 
        result = psprintf("%s", src->c_var);
	else {
		result = (char *) palloc(12);	/* sign, 10 digits, '\0' */
		pg_ltoa(src->integer, result);
	}
	PG_RETURN_CSTRING(result);
} 

PG_FUNCTION_INFO_V1(int4_faure_bool);
/* Cast int4_faure -> bool */
Datum
int4_faure_bool(PG_FUNCTION_ARGS)
{
	if (PG_GETARG_INT32_INT_FAURE(0) == 0)
		PG_RETURN_BOOL(false);
	else
		PG_RETURN_BOOL(true);
}

PG_FUNCTION_INFO_V1(bool_int4_faure);
/* Cast bool -> int4_faure */
Datum
bool_int4_faure(PG_FUNCTION_ARGS)
{
	int4_faure* result = int4_faure_new(1, "0");
	if (PG_GETARG_BOOL(0) == false) 
		result->integer = 0;
	PG_RETURN_POINTER(result);
}
 
// /*
//  *		============================
//  *		COMPARISON OPERATOR ROUTINES
//  *		============================
//  */

// /*
//  *		inteq			- returns 1 iff arg1 == arg2
//  *		intne			- returns 1 iff arg1 != arg2
//  *		intlt			- returns 1 iff arg1 < arg2
//  *		intle			- returns 1 iff arg1 <= arg2
//  *		intgt			- returns 1 iff arg1 > arg2
//  *		intge			- returns 1 iff arg1 >= arg2
//  */


PG_FUNCTION_INFO_V1(int4_faure_eq);
Datum
int4_faure_eq(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);
		
	PG_RETURN_BOOL(arg1->integer == arg2->integer);
}

PG_FUNCTION_INFO_V1(int4_faure_ne);
Datum
int4_faure_ne(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(arg1->integer != arg2->integer);
}

PG_FUNCTION_INFO_V1(int4_faure_lt);
Datum
int4_faure_lt(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(arg1->integer < arg2->integer);
} 

PG_FUNCTION_INFO_V1(is_var);
Datum
is_var(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);

	if (is_cvar(arg1))
		PG_RETURN_BOOL(true);
	else
		PG_RETURN_BOOL(false);
}

// PG_FUNCTION_INFO_V1(int4_faure_hash);
// Datum
// int4_faure_hash(PG_FUNCTION_ARGS)
// {
// 	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
// 	Datum		result;

// 	if (is_cvar(arg1))
// 		result = hash_any((unsigned char *) C_VAR(arg1), strlen(C_VAR(arg1)));
// 	else 
// 		result = hash_uint32(DatumGetInt32IntFaure(arg1));

// 	PG_RETURN_DATUM(result);
// }

PG_FUNCTION_INFO_V1(int4_faure_le);
Datum
int4_faure_le(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(arg1->integer <= arg2->integer);
}

PG_FUNCTION_INFO_V1(int4_faure_gt);
Datum
int4_faure_gt(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(arg1->integer > arg2->integer);
}

PG_FUNCTION_INFO_V1(int4_faure_ge);
Datum
int4_faure_ge(PG_FUNCTION_ARGS)
{
	int4_faure		*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure		*arg2 = PG_GETARG_INT32_FAURE(1);

	if (is_cvar(arg1) || is_cvar(arg2))
		PG_RETURN_BOOL(true);

	PG_RETURN_BOOL(arg1->integer >= arg2->integer);
}

void concat(char* prev, char* after, char* result) {
	int prev_len = strlen(prev);
	int after_len = strlen(after);
	if (prev_len+after_len-1 > C_LEN) // extra 1 for the double counting of null
		ereport(ERROR,
		(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
			errmsg("Resultant open form is out-of-range of C_LEN")));
	for (int i = 0; i < prev_len; i++)
		result[i] = prev[i];
	for (int i = 0; i < after_len; i++)
		result[i+prev_len] = after[i];
	result[prev_len+after_len] = '\0'; // add null at the end
} 	

PG_FUNCTION_INFO_V1(int4_faure_um);
Datum
int4_faure_um(PG_FUNCTION_ARGS)
{
	int4_faure		   *arg = PG_GETARG_INT32_FAURE(0);
	int4_faure 		*result = int4_faure_new(0, "0");

	if (is_cvar(arg)) {
		concat("-", C_VAR(arg), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (unlikely(DatumGetInt32IntFaure(arg) == PG_INT32_MIN)) 
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("integer out of range")));
	result->integer = -(arg->integer);
	PG_RETURN_POINTER(result);
}

// Datum
// int4up(PG_FUNCTION_ARGS)
// {
// 	int32		arg = PG_GETARG_INT32(0);

// 	PG_RETURN_INT32(arg);
// }
 
PG_FUNCTION_INFO_V1(int4_faure_pl);
Datum
int4_faure_pl(PG_FUNCTION_ARGS)
{
	int4_faure	*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure	*arg2 = PG_GETARG_INT32_FAURE(1);
 
	int4_faure 		*result = int4_faure_new(0, "0");

	if (is_cvar(arg1) && is_cvar(arg2)) { // TODO: Review this
		concat(C_VAR(arg1), "+", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg1)) {
		// int size_arg2 = (int)((ceil(log10(arg2->integer))+1)*sizeof(char));
		char str_arg2[C_LEN];
		sprintf(str_arg2, "%d", arg2->integer);
		concat(C_VAR(arg1), "+", C_VAR(result));
		concat(C_VAR(result), str_arg2, C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg2)) {
		// int size_arg1= (int)((ceil(log10(arg1->integer))+1)*sizeof(char));
		char str_arg1[C_LEN];
		sprintf(str_arg1, "%d", arg1->integer);
		concat(str_arg1, "+", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (unlikely(pg_add_s32_overflow(arg1->integer, arg2->integer, &(result->integer))))
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("integer out of range")));

	PG_RETURN_INT32(result);
}

PG_FUNCTION_INFO_V1(int4_faure_mi);
Datum
int4_faure_mi(PG_FUNCTION_ARGS)
{
	int4_faure	*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure	*arg2 = PG_GETARG_INT32_FAURE(1);
 
	int4_faure 		*result = int4_faure_new(0, "0");

	if (is_cvar(arg1) && is_cvar(arg2)) { // TODO: Review this
		concat(C_VAR(arg1), "-", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg1)) {
		// int size_arg2 = (int)((ceil(log10(arg2->integer))+1)*sizeof(char));
		char str_arg2[C_LEN];
		sprintf(str_arg2, "%d", arg2->integer);
		concat(C_VAR(arg1), "-", C_VAR(result));
		concat(C_VAR(result), str_arg2, C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg2)) {
		// int size_arg1= (int)((ceil(log10(arg1->integer))+1)*sizeof(char));
		char str_arg1[C_LEN];
		sprintf(str_arg1, "%d", arg1->integer);
		concat(str_arg1, "-", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (unlikely(pg_sub_s32_overflow(arg1->integer, arg2->integer, &(result->integer))))
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("integer out of range")));

	PG_RETURN_INT32(result);
}

PG_FUNCTION_INFO_V1(int4_faure_mul);
Datum
int4_faure_mul(PG_FUNCTION_ARGS)
{
	int4_faure	*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure	*arg2 = PG_GETARG_INT32_FAURE(1);
 
	int4_faure 		*result = int4_faure_new(0, "0");

	if (is_cvar(arg1) && is_cvar(arg2)) { // TODO: Review this
		concat(C_VAR(arg1), "*", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg1)) {
		// int size_arg2 = (int)((ceil(log10(arg2->integer))+1)*sizeof(char));
		char str_arg2[C_LEN];
		sprintf(str_arg2, "%d", arg2->integer);
		concat(C_VAR(arg1), "*", C_VAR(result));
		concat(C_VAR(result), str_arg2, C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg2)) {
		// int size_arg1= (int)((ceil(log10(arg1->integer))+1)*sizeof(char));
		char str_arg1[C_LEN];
		sprintf(str_arg1, "%d", arg1->integer);
		concat(str_arg1, "*", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (unlikely(pg_mul_s32_overflow(arg1->integer, arg2->integer, &(result->integer))))
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("integer out of range")));

	PG_RETURN_INT32(result);
}

PG_FUNCTION_INFO_V1(int4_faure_div);
Datum
int4_faure_div(PG_FUNCTION_ARGS)
{
	int4_faure	*arg1 = PG_GETARG_INT32_FAURE(0);
	int4_faure	*arg2 = PG_GETARG_INT32_FAURE(1);
 
	int4_faure 		*result = int4_faure_new(0, "0");

	if (is_cvar(arg1) && is_cvar(arg2)) { // TODO: Review this
		concat(C_VAR(arg1), "*", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg1)) {
		// int size_arg2 = (int)((ceil(log10(arg2->integer))+1)*sizeof(char));
		char str_arg2[C_LEN];
		sprintf(str_arg2, "%d", arg2->integer);
		concat(C_VAR(arg1), "*", C_VAR(result));
		concat(C_VAR(result), str_arg2, C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	else if (is_cvar(arg2)) {
		// int size_arg1= (int)((ceil(log10(arg1->integer))+1)*sizeof(char));
		char str_arg1[C_LEN];
		sprintf(str_arg1, "%d", arg1->integer);
		concat(str_arg1, "*", C_VAR(result));
		concat(C_VAR(result), C_VAR(arg2), C_VAR(result));
		PG_RETURN_POINTER(result);
	}
	if(arg2->integer == 0) {
		ereport(ERROR,
		(errcode(ERRCODE_DIVISION_BY_ZERO),
			errmsg("division by zero")));
		/* ensure compiler realizes we mustn't reach the division (gcc bug) */
		PG_RETURN_NULL();
	}

		/*
	 * INT_MIN / -1 is problematic, since the result can't be represented on a
	 * two's-complement machine.  Some machines produce INT_MIN, some produce
	 * zero, some throw an exception.  We can dodge the problem by recognizing
	 * that division by -1 is the same as negation.
	 */
	if (arg2->integer == -1)
	{
		if (unlikely(arg1->integer == PG_INT32_MIN))
			ereport(ERROR,
					(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
					 errmsg("integer out of range")));
		result->integer = -(arg1->integer);
		PG_RETURN_INT32(result);
	}
	/* No overflow is possible */

	result->integer = arg1->integer / arg2->integer;

	PG_RETURN_POINTER(result);
}