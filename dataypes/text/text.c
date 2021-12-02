/*-------------------------------------------------------------------------
 *
 * varlena.c
 *	  Functions for the variable-length built-in types.
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/varlena.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <ctype.h>
#include <limits.h>
#include <stdlib.h>

#include "access/detoast.h"
// #include "access/toast_compression.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_type.h"
#include "common/hashfn.h"
#include "common/int.h"
#include "common/unicode_norm.h"
#include "lib/hyperloglog.h"
#include "libpq/pqformat.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "parser/scansup.h"
#include "port/pg_bswap.h"
#include "regex/regex.h"
#include "utils/builtins.h"
#include "utils/bytea.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
// #include "utils/pg_locale.h"
#include "utils/sortsupport.h"
#include "varlena.h"


PG_MODULE_MAGIC;

/*****************************************************************************
 *	 CONVERSION ROUTINES EXPORTED FOR USE BY C CODE							 *
 *****************************************************************************/

/*
 * cstring_to_text_with_len
 *
 * Same as cstring_to_text except the caller specifies the string length;
 * the string need not be null_terminated.
 */
text *
cstring_to_text_with_len(const char *s, int len)
{
	text	   *result = (text *) palloc(len + VARHDRSZ);

	SET_VARSIZE(result, len + VARHDRSZ);
	memcpy(VARDATA(result), s, len);

	return result;
}

/*
 * cstring_to_text
 *
 * Create a text value from a null-terminated C string.
 *
 * The new text value is freshly palloc'd with a full-size VARHDR.
 */
text *
cstring_to_text(const char *s)
{
	return cstring_to_text_with_len(s, strlen(s));
}



/*
 * text_to_cstring
 *
 * Create a palloc'd, null-terminated C string from a text value.
 *
 * We support being passed a compressed or toasted text value.
 * This is a bit bogus since such values shouldn't really be referred to as
 * "text *", but it seems useful for robustness.  If we didn't handle that
 * case here, we'd need another routine that did, anyway.
 */
char *
text_to_cstring(const text *t)
{
	/* must cast away the const, unfortunately */
	text	   *tunpacked = pg_detoast_datum_packed(unconstify(text *, t));
	int			len = VARSIZE_ANY_EXHDR(tunpacked);
	char	   *result;

	result = (char *) palloc(len + 1);
	memcpy(result, VARDATA_ANY(tunpacked), len);
	result[len] = '\0';

	if (tunpacked != t)
		pfree(tunpacked);

	return result;
}

PG_FUNCTION_INFO_V1(text_or);

// Hacky implementation for experiments
Datum
text_or(PG_FUNCTION_ARGS)
{
	text	   *arg1 = PG_GETARG_TEXT_PP(0);
	text	   *arg2 = PG_GETARG_TEXT_PP(1);
	char	   *arg1_cstring = text_to_cstring(arg1);
	char	   *arg2_cstring = text_to_cstring(arg2);
	char	   *result;
	int			len1 = VARSIZE_ANY_EXHDR(arg1);
	int			len2 = VARSIZE_ANY_EXHDR(arg2);

	fprintf(stderr, "initial string arg1: %s\n", arg1_cstring);
	fprintf(stderr, "initial string arg2: %s\n", arg2_cstring);

	if (isalpha(arg1_cstring[0]) || isalpha(arg2_cstring[0])) {
		result = (char *) palloc(5 + 1);
		strcpy(result, "or-ed");
		text* result_text = cstring_to_text(result);
		PG_RETURN_TEXT_P(result_text);
	}

	if (len2 > len1)
		len1 = len2;

	result = (char *) palloc(len1 + 1);

	int global_count  = 0;
	int arg1_count = 0;
	int arg2_count = 0;
	for (int i = 0; i < 4; i++) // four bytes for IPv4
	{
		int arg1_num = 0;
		int arg2_num = 0;
		if (!(arg1_cstring[arg1_count]) || !(arg2_cstring[arg2_count]))
			break;
		if (arg1_cstring[arg1_count] == '/' || arg2_cstring[arg2_count] == '/')
			break;

		int j = 0;
		char tmp1[4];
		while (arg1_cstring[arg1_count] != '.' && j < 3) {
			tmp1[j] = arg1_cstring[arg1_count];
			j++;
			arg1_count++;
		}
		tmp1[j] = '\0';
		arg1_num = atoi(tmp1);
		fprintf(stderr, "arg1_num: %d\n", arg1_num);

		j = 0;
		char tmp2[4];
		while (arg2_cstring[arg2_count] != '.' && j < 3) {
			tmp2[j] = arg2_cstring[arg2_count];
			j++;
			arg2_count++;
		}
		tmp2[j] = '\0';
		arg2_num = atoi(tmp2);
		fprintf(stderr, "arg2_num: %d\n", arg2_num);

		int result_or = arg1_num | arg2_num;
		char str[4];
		sprintf(str, "%d", result_or);
		fprintf(stderr, "result_or: %s\n", str);

		int str_count = 0;
		while (str[str_count]) {
			result[global_count] = str[str_count];
			global_count++;
			str_count++;
		}
		if (i != 3) {
			result[global_count] = '.';
			global_count++;
		} 
		else {
			result[global_count] = '/';
			global_count++;
		}
		fprintf(stderr, "for end result: %s\n", str);
		arg1_count++;
		arg2_count++;

	}

	int loc_of_slash = 0;
	for (int i = 0; i < len2; i++) {
		if (arg2_cstring[i] == '/') {
			loc_of_slash = i;
			break;
		}
	}
	fprintf(stderr, "location: %d\n", loc_of_slash);

	for (int i = loc_of_slash+1; i < len2; i++) {
		result[global_count] = arg2_cstring[i];
		fprintf(stderr, "val subnet: %c\n", arg2_cstring[i]);
		global_count++;
	}
	result[global_count] = '\0';
	fprintf(stderr, "final: %s\n", result);

	text* result_text = cstring_to_text(result);
	PG_RETURN_TEXT_P(result_text);
	// result = (text_cmp(arg1, arg2, PG_GET_COLLATION()) > 0);

	// PG_FREE_IF_COPY(arg1, 0);
	// PG_FREE_IF_COPY(arg2, 1);
}