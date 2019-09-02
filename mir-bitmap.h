/* This file is a part of MIR project.
  Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_BITMAP_H

#define MIR_BITMAP_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include "mir-varr.h"

#define FALSE 0
#define TRUE 1

#if !defined(BITMAP_ENABLE_CHECKING) && !defined(NDEBUG)
#define BITMAP_ENABLE_CHECKING
#endif

#ifndef BITMAP_ENABLE_CHECKING
#define BITMAP_ASSERT(EXPR, OP) ((void) (EXPR))

#else
static inline void mir_bitmap_assert_fail (const char *op) {
  fprintf (stderr, "wrong %s for a bitmap", op);
  assert (0);
}

#define BITMAP_ASSERT(EXPR, OP) (void) ((EXPR) ? 0 : (mir_bitmap_assert_fail (#OP), 0))

#endif

#define BITMAP_WORD_BITS 64

typedef uint64_t bitmap_el_t;

DEF_VARR (bitmap_el_t);

typedef VARR (bitmap_el_t) * bitmap_t;
typedef const VARR (bitmap_el_t) * const_bitmap_t;

static inline bitmap_t bitmap_create2 (size_t init_bits_num) {
  bitmap_t bm;

  VARR_CREATE (bitmap_el_t, bm, (init_bits_num + BITMAP_WORD_BITS - 1) / BITMAP_WORD_BITS);
  return bm;
}

static inline bitmap_t bitmap_create (void) { return bitmap_create2 (0); }

static inline void bitmap_destroy (bitmap_t bm) { VARR_DESTROY (bitmap_el_t, bm); }

static inline void bitmap_clear (bitmap_t bm) { VARR_TRUNC (bitmap_el_t, bm, 0); }

static inline void bitmap_expand (bitmap_t bm, size_t nb) {
  size_t i, len = VARR_LENGTH (bitmap_el_t, bm);
  size_t new_len = (nb + BITMAP_WORD_BITS - 1) / BITMAP_WORD_BITS;

  for (i = len; i < new_len; i++) VARR_PUSH (bitmap_el_t, bm, (bitmap_el_t) 0);
}

static inline int bitmap_bit_p (const_bitmap_t bm, size_t nb) {
  size_t nw, sh, len = VARR_LENGTH (bitmap_el_t, bm);
  bitmap_el_t *addr = VARR_ADDR (bitmap_el_t, bm);

  if (nb >= BITMAP_WORD_BITS * len) return 0;
  nw = nb / BITMAP_WORD_BITS;
  sh = nb % BITMAP_WORD_BITS;
  return (addr[nw] >> sh) & 1;
}

static inline int bitmap_set_bit_p (bitmap_t bm, size_t nb) {
  size_t nw, sh;
  bitmap_el_t *addr;
  int res;

  bitmap_expand (bm, nb + 1);
  addr = VARR_ADDR (bitmap_el_t, bm);
  nw = nb / BITMAP_WORD_BITS;
  sh = nb % BITMAP_WORD_BITS;
  res = ((addr[nw] >> sh) & 1) == 0;
  addr[nw] |= (bitmap_el_t) 1 << sh;
  return res;
}

static inline int bitmap_clear_bit_p (bitmap_t bm, size_t nb) {
  size_t nw, sh, len = VARR_LENGTH (bitmap_el_t, bm);
  bitmap_el_t *addr = VARR_ADDR (bitmap_el_t, bm);
  int res;

  if (nb >= BITMAP_WORD_BITS * len) return 0;
  nw = nb / BITMAP_WORD_BITS;
  sh = nb % BITMAP_WORD_BITS;
  res = (addr[nw] >> sh) & 1;
  addr[nw] &= ~((bitmap_el_t) 1 << sh);
  return res;
}

static inline void bitmap_copy (bitmap_t dst, const_bitmap_t src) {
  size_t dst_len = VARR_LENGTH (bitmap_el_t, dst);
  size_t src_len = VARR_LENGTH (bitmap_el_t, src);

  if (dst_len >= src_len)
    VARR_TRUNC (bitmap_el_t, dst, src_len);
  else
    bitmap_expand (dst, src_len * BITMAP_WORD_BITS);
  memcpy (VARR_ADDR (bitmap_el_t, dst), VARR_ADDR (bitmap_el_t, src),
          src_len * sizeof (bitmap_el_t));
}

static inline int bitmap_equal_p (const_bitmap_t bm1, const_bitmap_t bm2) {
  const_bitmap_t temp_bm;
  size_t i, temp_len, bm1_len = VARR_LENGTH (bitmap_el_t, bm1);
  size_t bm2_len = VARR_LENGTH (bitmap_el_t, bm2);
  bitmap_el_t *addr1, *addr2;

  if (bm1_len > bm2_len) {
    temp_bm = bm1;
    bm1 = bm2;
    bm2 = temp_bm;
    temp_len = bm1_len;
    bm1_len = bm2_len;
    bm2_len = temp_len;
  }
  addr1 = VARR_ADDR (bitmap_el_t, bm1);
  addr2 = VARR_ADDR (bitmap_el_t, bm2);
  if (memcmp (addr1, addr2, bm1_len * sizeof (bitmap_el_t)) != 0) return FALSE;
  for (i = bm1_len; i < bm2_len; i++)
    if (addr2[i] != 0) return FALSE;
  return TRUE;
}

static inline int bitmap_intersect_p (const_bitmap_t bm1, const_bitmap_t bm2) {
  size_t i, min_len, bm1_len = VARR_LENGTH (bitmap_el_t, bm1);
  size_t bm2_len = VARR_LENGTH (bitmap_el_t, bm2);
  bitmap_el_t *addr1 = VARR_ADDR (bitmap_el_t, bm1);
  bitmap_el_t *addr2 = VARR_ADDR (bitmap_el_t, bm2);

  min_len = bm1_len <= bm2_len ? bm1_len : bm2_len;
  for (i = 0; i < min_len; i++)
    if ((addr1[i] & addr2[i]) != 0) return TRUE;
  return FALSE;
}

static inline int bitmap_empty_p (const_bitmap_t bm) {
  size_t i, len = VARR_LENGTH (bitmap_el_t, bm);
  bitmap_el_t *addr = VARR_ADDR (bitmap_el_t, bm);

  for (i = 0; i < len; i++)
    if (addr[i] != 0) return FALSE;
  return TRUE;
}

static inline bitmap_el_t bitmap_el_max3 (bitmap_el_t el1, bitmap_el_t el2, bitmap_el_t el3) {
  if (el1 <= el2) return el2 < el3 ? el3 : el2;
  return el1 < el3 ? el3 : el1;
}

static inline bitmap_el_t bitmap_el_max4 (bitmap_el_t el1, bitmap_el_t el2, bitmap_el_t el3,
                                          bitmap_el_t el4) {
  if (el1 <= el2) return bitmap_el_max3 (el2, el3, el4);
  return bitmap_el_max3 (el1, el3, el4);
}

/* Return the number of bits set in BM.  */
static inline size_t bitmap_bit_count (const_bitmap_t bm) {
  size_t i, len = VARR_LENGTH (bitmap_el_t, bm);
  bitmap_el_t el, *addr = VARR_ADDR (bitmap_el_t, bm);
  size_t count = 0;

  for (i = 0; i < len; i++) {
    if ((el = addr[i]) != 0) {
      for (; el != 0; el >>= 1)
        if (el & 1) count++;
    }
  }
  return count;
}

static inline int bitmap_op2 (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2,
                              bitmap_el_t (*op) (bitmap_el_t, bitmap_el_t)) {
  size_t i, len, bound, src1_len, src2_len;
  bitmap_el_t old, *dst_addr, *src1_addr, *src2_addr;
  int change_p = FALSE;

  src1_len = VARR_LENGTH (bitmap_el_t, src1);
  src2_len = VARR_LENGTH (bitmap_el_t, src2);
  len = bitmap_el_max3 (VARR_LENGTH (bitmap_el_t, dst), src1_len, src2_len);
  bitmap_expand (dst, len * BITMAP_WORD_BITS);
  dst_addr = VARR_ADDR (bitmap_el_t, dst);
  src1_addr = VARR_ADDR (bitmap_el_t, src1);
  src2_addr = VARR_ADDR (bitmap_el_t, src2);
  for (bound = i = 0; i < len; i++) {
    old = dst_addr[i];
    if ((dst_addr[i] = op (i >= src1_len ? 0 : src1_addr[i], i >= src2_len ? 0 : src2_addr[i]))
        != 0)
      bound = i + 1;
    if (old != dst_addr[i]) change_p = TRUE;
  }
  VARR_TRUNC (bitmap_el_t, dst, bound);
  return change_p;
}

static inline bitmap_el_t bitmap_el_and (bitmap_el_t el1, bitmap_el_t el2) { return el1 & el2; }

static inline int bitmap_and (bitmap_t dst, bitmap_t src1, bitmap_t src2) {
  return bitmap_op2 (dst, src1, src2, bitmap_el_and);
}

static inline bitmap_el_t bitmap_el_and_compl (bitmap_el_t el1, bitmap_el_t el2) {
  return el1 & ~el2;
}

static inline int bitmap_and_compl (bitmap_t dst, bitmap_t src1, bitmap_t src2) {
  return bitmap_op2 (dst, src1, src2, bitmap_el_and_compl);
}

static inline bitmap_el_t bitmap_el_ior (bitmap_el_t el1, bitmap_el_t el2) { return el1 | el2; }

static inline int bitmap_ior (bitmap_t dst, bitmap_t src1, bitmap_t src2) {
  return bitmap_op2 (dst, src1, src2, bitmap_el_ior);
}

static inline int bitmap_op3 (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2,
                              const_bitmap_t src3,
                              bitmap_el_t (*op) (bitmap_el_t, bitmap_el_t, bitmap_el_t)) {
  size_t i, len, bound, src1_len, src2_len, src3_len;
  bitmap_el_t old, *dst_addr, *src1_addr, *src2_addr, *src3_addr;
  int change_p = FALSE;

  src1_len = VARR_LENGTH (bitmap_el_t, src1);
  src2_len = VARR_LENGTH (bitmap_el_t, src2);
  src3_len = VARR_LENGTH (bitmap_el_t, src3);
  len = bitmap_el_max4 (VARR_LENGTH (bitmap_el_t, dst), src1_len, src2_len, src3_len);
  bitmap_expand (dst, len * BITMAP_WORD_BITS);
  dst_addr = VARR_ADDR (bitmap_el_t, dst);
  src1_addr = VARR_ADDR (bitmap_el_t, src1);
  src2_addr = VARR_ADDR (bitmap_el_t, src2);
  src3_addr = VARR_ADDR (bitmap_el_t, src3);
  for (bound = i = 0; i < len; i++) {
    old = dst_addr[i];
    if ((dst_addr[i] = op (i >= src1_len ? 0 : src1_addr[i], i >= src2_len ? 0 : src2_addr[i],
                           i >= src3_len ? 0 : src3_addr[i]))
        != 0)
      bound = i + 1;
    if (old != dst_addr[i]) change_p = TRUE;
  }
  VARR_TRUNC (bitmap_el_t, dst, bound);
  return change_p;
}

static inline bitmap_el_t bitmap_el_ior_and (bitmap_el_t el1, bitmap_el_t el2, bitmap_el_t el3) {
  return el1 | (el2 & el3);
}

/* DST = SRC1 | (SRC2 & SRC3).  Return true if DST changed.  */
static inline int bitmap_ior_and (bitmap_t dst, bitmap_t src1, bitmap_t src2, bitmap_t src3) {
  return bitmap_op3 (dst, src1, src2, src3, bitmap_el_ior_and);
}

static inline bitmap_el_t bitmap_el_ior_and_compl (bitmap_el_t el1, bitmap_el_t el2,
                                                   bitmap_el_t el3) {
  return el1 | (el2 & ~el3);
}

/* DST = SRC1 | (SRC2 & ~SRC3).  Return true if DST changed.  */
static inline int bitmap_ior_and_compl (bitmap_t dst, bitmap_t src1, bitmap_t src2, bitmap_t src3) {
  return bitmap_op3 (dst, src1, src2, src3, bitmap_el_ior_and_compl);
}

static inline void bitmap_for_each (bitmap_t bm, void (*func) (size_t, void *), void *data) {
  size_t i, nb, len = VARR_LENGTH (bitmap_el_t, bm);
  bitmap_el_t el, *addr = VARR_ADDR (bitmap_el_t, bm);

  for (i = 0; i < len; i++) {
    if ((el = addr[i]) != 0) {
      for (nb = 0; el != 0; el >>= 1, nb++)
        if (el & 1) func (i * BITMAP_WORD_BITS + nb, data);
    }
  }
}

#endif /* #ifndef MIR_BITMAP_H */
