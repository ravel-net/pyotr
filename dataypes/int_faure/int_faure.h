/*-------------------------------------------------------------------------
 *
 * int.h
 *	  Routines to perform integer math, while checking for overflows.
 *
 * The routines in this file are intended to be well defined C, without
 * relying on compiler flags like -fwrapv.
 *
 * To reduce the overhead of these routines try to use compiler intrinsics
 * where available. That's not that important for the 16, 32 bit cases, but
 * the 64 bit cases can be considerably faster with intrinsics. In case no
 * intrinsics are available 128 bit math is used where available.
 *
 * Copyright (c) 2017-2021, PostgreSQL Global Development Group
 *
 * src/include/common/int.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef INT_FAURE_H
#define INT_FAURE_H

typedef struct int4_faure
{
	int32 	 integer;
	char 	 c_var[20]; 	    /* TODO: Make this dynamic */
} int4_faure;

// Datum int4_faure_new_datum(int32 i, char* c_var) { 
//   int4_faure p = int4_faure_new(i, c_var);
//   return p;
// }

// #define DatumGetInt32Faure(X) (int32) (((int4_faure*) (X))->integer)
#define DatumGetInt32IntFaure(X) ((int32) (((int4_faure*) (X))->integer))
#define DatumGetIntFaure(X) (((int4_faure*) (X)))
#define PG_GETARG_INT32_INT_FAURE(n)	 DatumGetInt32IntFaure(PG_GETARG_DATUM(n))
#define PG_GETARG_INT32_FAURE(n)	 DatumGetIntFaure(PG_GETARG_DATUM(n))

#define C_VAR(n)	((char*) (((int4_faure*) (n))->c_var))


// #define PG_RETURN_INT32(x)	 return Int32GetDatum(x)


// #define PG_GETARG_INT_FAURE_PP(n) ((int4_faure *) PG_GETARG_DATUM(n))
/*---------
 * The following guidelines apply to all the routines:
 * - If a + b overflows, return true, otherwise store the result of a + b
 * into *result. The content of *result is implementation defined in case of
 * overflow.
 * - If a - b overflows, return true, otherwise store the result of a - b
 * into *result. The content of *result is implementation defined in case of
 * overflow.
 * - If a * b overflows, return true, otherwise store the result of a * b
 * into *result. The content of *result is implementation defined in case of
 * overflow.
 *---------
 */

/*------------------------------------------------------------------------
 * Overflow routines for signed integers
 *------------------------------------------------------------------------
 */

/*
 * INT16_FAURE
 */
// static inline bool
// pg_add_s16_overflow(int16 a, int16 b, int16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #else
// 	int32_faure		res = (int32_faure) a + (int32_faure) b;

// 	if (res > PG_INT16_FAURE_MAX || res < PG_INT16_FAURE_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int16) res;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_s16_overflow(int16 a, int16 b, int16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #else
// 	int32_faure		res = (int32_faure) a - (int32_faure) b;

// 	if (res > PG_INT16_FAURE_MAX || res < PG_INT16_FAURE_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int16) res;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_s16_overflow(int16 a, int16 b, int16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #else
// 	int32_faure		res = (int32_faure) a * (int32_faure) b;

// 	if (res > PG_INT16_FAURE_MAX || res < PG_INT16_FAURE_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int16) res;
// 	return false;
// #endif
// }

// /*
//  * INT32
//  */
// static inline bool
// pg_add_s32_overflow(int32_faure a, int32_faure b, int32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #else
// 	int64		res = (int64) a + (int64) b;

// 	if (res > PG_INT32_MAX || res < PG_INT32_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int32_faure) res;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_s32_overflow(int32_faure a, int32_faure b, int32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #else
// 	int64		res = (int64) a - (int64) b;

// 	if (res > PG_INT32_MAX || res < PG_INT32_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int32_faure) res;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_s32_overflow(int32_faure a, int32_faure b, int32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #else
// 	int64		res = (int64) a * (int64) b;

// 	if (res > PG_INT32_MAX || res < PG_INT32_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int32_faure) res;
// 	return false;
// #endif
// }

// /*
//  * INT64
//  */
// static inline bool
// pg_add_s64_overflow(int64 a, int64 b, int64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #elif defined(HAVE_INT128)
// 	int128		res = (int128) a + (int128) b;

// 	if (res > PG_INT64_MAX || res < PG_INT64_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int64) res;
// 	return false;
// #else
// 	if ((a > 0 && b > 0 && a > PG_INT64_MAX - b) ||
// 		(a < 0 && b < 0 && a < PG_INT64_MIN - b))
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a + b;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_s64_overflow(int64 a, int64 b, int64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #elif defined(HAVE_INT128)
// 	int128		res = (int128) a - (int128) b;

// 	if (res > PG_INT64_MAX || res < PG_INT64_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int64) res;
// 	return false;
// #else
// 	if ((a < 0 && b > 0 && a < PG_INT64_MIN + b) ||
// 		(a > 0 && b < 0 && a > PG_INT64_MAX + b))
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a - b;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_s64_overflow(int64 a, int64 b, int64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #elif defined(HAVE_INT128)
// 	int128		res = (int128) a * (int128) b;

// 	if (res > PG_INT64_MAX || res < PG_INT64_MIN)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (int64) res;
// 	return false;
// #else
// 	/*
// 	 * Overflow can only happen if at least one value is outside the range
// 	 * sqrt(min)..sqrt(max) so check that first as the division can be quite a
// 	 * bit more expensive than the multiplication.
// 	 *
// 	 * Multiplying by 0 or 1 can't overflow of course and checking for 0
// 	 * separately avoids any risk of dividing by 0.  Be careful about dividing
// 	 * INT_MIN by -1 also, note reversing the a and b to ensure we're always
// 	 * dividing it by a positive value.
// 	 *
// 	 */
// 	if ((a > PG_INT32_MAX || a < PG_INT32_MIN ||
// 		 b > PG_INT32_MAX || b < PG_INT32_MIN) &&
// 		a != 0 && a != 1 && b != 0 && b != 1 &&
// 		((a > 0 && b > 0 && a > PG_INT64_MAX / b) ||
// 		 (a > 0 && b < 0 && b < PG_INT64_MIN / a) ||
// 		 (a < 0 && b > 0 && a < PG_INT64_MIN / b) ||
// 		 (a < 0 && b < 0 && a < PG_INT64_MAX / b)))
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a * b;
// 	return false;
// #endif
// }

// /*------------------------------------------------------------------------
//  * Overflow routines for unsigned integers
//  *------------------------------------------------------------------------
//  */

// /*
//  * UINT16
//  */
// static inline bool
// pg_add_u16_overflow(uint16 a, uint16 b, uint16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #else
// 	uint16		res = a + b;

// 	if (res < a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = res;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_u16_overflow(uint16 a, uint16 b, uint16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #else
// 	if (b > a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a - b;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_u16_overflow(uint16 a, uint16 b, uint16 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #else
// 	uint32_faure		res = (uint32_faure) a * (uint32_faure) b;

// 	if (res > PG_UINT16_MAX)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (uint16) res;
// 	return false;
// #endif
// }

// /*
//  * INT32
//  */
// static inline bool
// pg_add_u32_overflow(uint32_faure a, uint32_faure b, uint32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #else
// 	uint32_faure		res = a + b;

// 	if (res < a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = res;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_u32_overflow(uint32_faure a, uint32_faure b, uint32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #else
// 	if (b > a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a - b;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_u32_overflow(uint32_faure a, uint32_faure b, uint32_faure *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #else
// 	uint64		res = (uint64) a * (uint64) b;

// 	if (res > PG_UINT32_MAX)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (uint32_faure) res;
// 	return false;
// #endif
// }

// /*
//  * UINT64
//  */
// static inline bool
// pg_add_u64_overflow(uint64 a, uint64 b, uint64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_add_overflow(a, b, result);
// #else
// 	uint64		res = a + b;

// 	if (res < a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = res;
// 	return false;
// #endif
// }

// static inline bool
// pg_sub_u64_overflow(uint64 a, uint64 b, uint64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_sub_overflow(a, b, result);
// #else
// 	if (b > a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = a - b;
// 	return false;
// #endif
// }

// static inline bool
// pg_mul_u64_overflow(uint64 a, uint64 b, uint64 *result)
// {
// #if defined(HAVE__BUILTIN_OP_OVERFLOW)
// 	return __builtin_mul_overflow(a, b, result);
// #elif defined(HAVE_INT128)
// 	uint128		res = (uint128) a * (uint128) b;

// 	if (res > PG_UINT64_MAX)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = (uint64) res;
// 	return false;
// #else
// 	uint64		res = a * b;

// 	if (a != 0 && b != res / a)
// 	{
// 		*result = 0x5EED;		/* to avoid spurious warnings */
// 		return true;
// 	}
// 	*result = res;
// 	return false;
// #endif
// }

#endif							/* COMMON_INT_H */
