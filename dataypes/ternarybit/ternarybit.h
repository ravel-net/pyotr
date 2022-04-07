/*-------------------------------------------------------------------------
 *
 * varbit.h
 *	  Functions for the SQL datatypes BIT() and BIT VARYING().
 *
 * Code originally contributed by Adriaan Joubert.
 *
 * Portions Copyright (c) 1996-2021, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/utils/varbit.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef TERNARY_BITS_H
#define TERNARY_BITS_H

#include <limits.h>

#include "fmgr.h"

/*
 * Modeled on struct varlena from postgres.h, but data type is bits8.
 *
 * Caution: if bit_len is not a multiple of BITS_PER_BYTE, the low-order
 * bits of the last byte of bit_dat[] are unused and MUST be zeroes.
 * (This allows bit_cmp() to not bother masking the last byte.)
 * Also, there should not be any excess bytes counted in the header length.
 */
typedef struct
{
	int32		vl_len_;		/* varlena header (do not touch directly!) */
	int32		bit_len;		/* number of valid bits */
	bits8		bit_dat[FLEXIBLE_ARRAY_MEMBER]; /* bit string, most sig. byte
												 * first */
} TernaryBit;

/*
 * fmgr interface macros
 *
 * BIT and BIT VARYING are toastable varlena types.  They are the same
 * as far as representation goes, so we just have one set of macros.
 */
#define DatumGetTernaryBitP(X)		   ((TernaryBit *) PG_DETOAST_DATUM(X))
#define DatumGetTernaryBitPCopy(X)	   ((TernaryBit *) PG_DETOAST_DATUM_COPY(X))
#define TernaryBitPGetDatum(X)		   PointerGetDatum(X)
#define PG_GETARG_TERNARYBIT_P(n)	   DatumGetTernaryBitP(PG_GETARG_DATUM(n))
#define PG_GETARG_TERNARYBIT_P_COPY(n) DatumGetTernaryBitPCopy(PG_GETARG_DATUM(n))
#define PG_RETURN_TERNARYBIT_P(x)	   return TernaryBitPGetDatum(x)

/* Header overhead *in addition to* VARHDRSZ */
#define TERNARYBITHDRSZ			sizeof(int32)
/* Number of bits in this bit string */
#define TERNARYBITLEN(PTR)		(((TernaryBit *) (PTR))->bit_len)
/* Pointer to the first byte containing bit string data */
#define TERNARYBITS(PTR)		(((TernaryBit *) (PTR))->bit_dat)
/* Number of bytes in the data section of a bit string */
#define TERNARYBITBYTES(PTR)	(VARSIZE(PTR) - VARHDRSZ - TERNARYBITHDRSZ)
/* Padding of the bit string at the end (in bits) */
#define TERNARYBITPAD(PTR)		(TERNARYBITBYTES(PTR)*BITS_PER_BYTE - TERNARYBITLEN(PTR))
/* Number of bytes needed to store a bit string of a given length */
#define TERNARYBITTOTALLEN(BITLEN)	(((BITLEN) + BITS_PER_BYTE-1)/BITS_PER_BYTE + \
								 VARHDRSZ + TERNARYBITHDRSZ)
/*
 * Maximum number of bits.  Several code sites assume no overflow from
 * computing bitlen + X; TERNARYBITTOTALLEN() has the largest such X.
 */
#define TERNARYBITMAXLEN		(INT_MAX - BITS_PER_BYTE + 1)
/* pointer beyond the end of the bit string (like end() in STL containers) */
#define TERNARYBITEND(PTR)		(((bits8 *) (PTR)) + VARSIZE(PTR))
/* Mask that will cover exactly one byte, i.e. BITS_PER_BYTE bits */
#define BITMASK 0xFF

#endif
