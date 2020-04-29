/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Sparse bitmap implementation.  */
#ifndef MIR_BITMAP_H

#define MIR_BITMAP_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <limits.h>
#include "mir-dlist.h"

#define FALSE 0
#define TRUE 1

#if !defined(BITMAP_ENABLE_CHECKING) && !defined(NDEBUG)
#define BITMAP_ENABLE_CHECKING
#endif

#ifndef BITMAP_ENABLE_CHECKING
#define BITMAP_ASSERT(EXPR, OP) ((void) (EXPR))
#else

static inline void mir_bitmap_assert_fail (const char *op) {
  fprintf (stderr, "%s\n", op);
  assert (0);
}

#define BITMAP_ASSERT(EXPR, OP) (void) ((EXPR) ? 0 : (mir_bitmap_assert_fail (OP), 0))
#endif

#ifdef __GNUC__
#define MIR_BITMAP_UNUSED __attribute__ ((unused))
#define MIR_BITMAP_NO_RETURN __attribute__ ((noreturn))
#else
#define MIR_BITMAP_UNUSED
#define MIR_BITMAP_NO_RETURN
#endif

static inline void MIR_BITMAP_NO_RETURN mir_bitmap_error (const char *message) {
#ifdef MIR_BITMAP_ERROR
  MIR_BITMAP_ERROR (message);
  assert (0);
#else
  fprintf (stderr, "%s\n", message);
#endif
  exit (1);
}

typedef struct bitmap_el_s *bitmap_el_t;

DEF_DLIST_LINK (bitmap_el_t);

#define BITMAP_WORD_BITS 64
#define BITMAP_EL_WORDS 2       /* to make 4x64-bit bitmap element */
typedef uint64_t bitmap_word_t; /* should be unsigned */

struct bitmap_el_s {
  size_t index;
  DLIST_LINK (bitmap_el_t) bitmap_el_link;
  bitmap_word_t words[BITMAP_EL_WORDS];
};

DEF_DLIST (bitmap_el_t, bitmap_el_link);

typedef struct bitmap_s *bitmap_t;
typedef struct bitmap_s *const_bitmap_t;

DEF_DLIST_LINK (bitmap_t);

struct bitmap_s {
  DLIST (bitmap_el_t) els;
  bitmap_el_t curr_el; /* last looked element, NULL only for empty els */
  DLIST_LINK (bitmap_t) bitmap_link;
  struct bitmap_group_s *bg;
};

DEF_DLIST (bitmap_t, bitmap_link);

struct bitmap_group_s {
  DLIST (bitmap_el_t) free_els;         /* freed els */
  DLIST (bitmap_t) free_bms, group_bms; /* freed and non-freed bitmaps */
};

typedef struct bitmap_group_s *bitmap_group_t;

static inline bitmap_group_t bitmap_group_create (void) {
  bitmap_group_t bg = malloc (sizeof (struct bitmap_group_s));

  if (bg == NULL) mir_bitmap_error ("bitmap: no memory");
  DLIST_INIT (bitmap_t, bg->free_bms);
  DLIST_INIT (bitmap_t, bg->group_bms);
  DLIST_INIT (bitmap_el_t, bg->free_els);
  return bg;
}

static inline void bitmap_destroy (bitmap_t bm);

/* Free all memory used for the group -- beware about using group bitmaps after that. */
static inline void bitmap_group_destroy (bitmap_group_t bg) {
  bitmap_t bm;
  bitmap_el_t el;

  BITMAP_ASSERT (bg != NULL, "NULL bitmap group in bitmap_group_destroy");
  while ((bm = DLIST_HEAD (bitmap_t, bg->group_bms)) != NULL) {
    DLIST_REMOVE (bitmap_t, bg->group_bms, bm);
    bitmap_destroy (bm);
  }
  while ((bm = DLIST_HEAD (bitmap_t, bg->free_bms)) != NULL) {
    DLIST_REMOVE (bitmap_t, bg->free_bms, bm);
    free (bm);
  }
  while ((el = DLIST_HEAD (bitmap_el_t, bg->free_els)) != NULL) {
    DLIST_REMOVE (bitmap_el_t, bg->free_els, el);
    free (el);
  }
  free (bg);
}

static inline void _bitmap_check (const_bitmap_t bm) {
  bitmap_el_t el, next_el;

  BITMAP_ASSERT (bm != NULL && bm->bg != NULL, "_bitmap_check");
  el = DLIST_HEAD (bitmap_el_t, bm->els);
  BITMAP_ASSERT (el == NULL || bm->curr_el != 0, "_bitmap_check");
#ifdef BITMAP_ENABLE_CHECKING_ALL
  for (; el != NULL; el = next_el) {
    next_el = DLIST_NEXT (bitmap_el_t, el);
    BITMAP_ASSERT (next_el == NULL || el->index < next_el->index, "_bitmap_check");
    bitmap_word_t w = 0;
    for (size_t i = 0; i < BITMAP_EL_WORDS; i++) w |= el->words[i];
    BITMAP_ASSERT (w != 0, "_bitmap_check");
  }
#endif
}

static inline bitmap_t bitmap_create2 (size_t MIR_BITMAP_UNUSED init_bits_num, bitmap_group_t bg) {
  bitmap_t bm = malloc (sizeof (struct bitmap_s));

  DLIST_APPEND (bitmap_t, bg->group_bms, bm);
  DLIST_INIT (bitmap_el_t, bm->els);
  bm->bg = bg;
  bm->curr_el = NULL;
  _bitmap_check (bm);
  return bm;
}

static inline bitmap_t bitmap_create (bitmap_group_t bg) { return bitmap_create2 (0, bg); }

static inline void _bitmap_clear_from (bitmap_t bm, bitmap_el_t from_el) {
  bitmap_el_t el, next_el;
  bitmap_group_t bg = bm->bg;

  for (el = from_el; el != NULL; el = next_el) {
    next_el = DLIST_NEXT (bitmap_el_t, el);
    DLIST_REMOVE (bitmap_el_t, bm->els, el);
    DLIST_APPEND (bitmap_el_t, bg->free_els, el);
  }
}

static inline void bitmap_clear (bitmap_t bm) {
  _bitmap_check (bm);
  _bitmap_clear_from (bm, DLIST_HEAD (bitmap_el_t, bm->els));
  bm->curr_el = NULL;
}

static inline void bitmap_destroy (bitmap_t bm) {
  _bitmap_check (bm);
  bitmap_clear (bm);
  DLIST_REMOVE (bitmap_t, bm->bg->group_bms, bm);
  DLIST_APPEND (bitmap_t, bm->bg->free_bms, bm);
}

/* Find and return bitmap element for NB bit.  Return NULL otherwise.
   Return element in PREV_EL which is previous or should be previous
   for the element (NULL means the element list beggining).  */
static inline bitmap_el_t _bitmap_find_el (bitmap_t bm, size_t nb, bitmap_el_t *prev_el) {
  bitmap_el_t el;
  int backward_p = FALSE;
  size_t curr_index, index = nb / (BITMAP_WORD_BITS * BITMAP_EL_WORDS);

  if ((el = bm->curr_el) == NULL) { /* empty list */
    *prev_el = NULL;
    return NULL;
  } else if ((curr_index = el->index) == index) { /* found element */
    *prev_el = DLIST_PREV (bitmap_el_t, el);
    return el;
  }
  curr_index = bm->curr_el->index;
  /* Search where the element should be: */
  if (curr_index < index) {
    if (index / 2 < curr_index) { /* forward from curr_el */
      el = bm->curr_el;
    } else { /* backward from tail */
      el = DLIST_TAIL (bitmap_el_t, bm->els);
      backward_p = TRUE;
    }
  } else if (curr_index / 2 < index) { /* backward from curr_el */
    el = bm->curr_el;
    backward_p = TRUE;
  } else { /* forward from head: */
    el = DLIST_HEAD (bitmap_el_t, bm->els);
  }
  if (backward_p) { /* prev_el is set up for not found case */
    while (el != NULL && el->index > index) el = DLIST_PREV (bitmap_el_t, el);
    *prev_el = el;
  } else { /* prev_el is set up for not found case */
    while (el != NULL && el->index < index) el = DLIST_NEXT (bitmap_el_t, el);
    *prev_el = el == NULL ? DLIST_TAIL (bitmap_el_t, bm->els) : DLIST_PREV (bitmap_el_t, el);
  }
  if (el == NULL || el->index != index) return NULL; /* not found */
  bm->curr_el = el;
  *prev_el = DLIST_PREV (bitmap_el_t, el);
  return el;
}

static inline bitmap_el_t _bitmap_add_el (bitmap_t bm, bitmap_el_t prev_el) {
  bitmap_el_t el;

  if ((el = DLIST_HEAD (bitmap_el_t, bm->bg->free_els)) == NULL) {
    el = malloc (sizeof (struct bitmap_el_s));
  } else {
    DLIST_REMOVE (bitmap_el_t, bm->bg->free_els, el);
  }
  for (size_t i = 0; i < BITMAP_EL_WORDS; i++) el->words[i] = 0;
  if (prev_el == NULL)
    DLIST_PREPEND (bitmap_el_t, bm->els, el);
  else
    DLIST_INSERT_AFTER (bitmap_el_t, bm->els, prev_el, el);
  return el;
}

static inline int bitmap_bit_p (const_bitmap_t bm, size_t nb) {
  _bitmap_check (bm);
  bitmap_el_t el, prev_el;

  if ((el = _bitmap_find_el (bm, nb, &prev_el)) == NULL) return FALSE;
  return (el->words[nb / BITMAP_WORD_BITS % BITMAP_EL_WORDS] >> (nb % BITMAP_WORD_BITS)) & 1;
}

static inline int bitmap_set_bit_p (bitmap_t bm, size_t nb) {
  _bitmap_check (bm);
  int res;
  bitmap_el_t prev_el, el = _bitmap_find_el (bm, nb, &prev_el);
  size_t nw = nb / BITMAP_WORD_BITS % BITMAP_EL_WORDS;
  bitmap_word_t mask = ((bitmap_word_t) 1) << (nb % BITMAP_WORD_BITS);

  if (el != 0) {
    res = (el->words[nw] & mask) == 0;
    el->words[nw] |= mask;
    return res;
  }
  bm->curr_el = el = _bitmap_add_el (bm, prev_el);
  el->index = nb / (BITMAP_WORD_BITS * BITMAP_EL_WORDS);
  el->words[nw] = mask;
  return 1;
}

static inline int _bitmap_zero_el_p (bitmap_el_t el) {
  for (size_t i = 0; i < BITMAP_EL_WORDS; i++)
    if (el->words[i] != 0) return FALSE;
  return TRUE;
}

static inline int bitmap_clear_bit_p (bitmap_t bm, size_t nb) {
  _bitmap_check (bm);
  bitmap_el_t prev_el, el = _bitmap_find_el (bm, nb, &prev_el);
  size_t nw = nb / BITMAP_WORD_BITS % BITMAP_EL_WORDS;
  bitmap_word_t mask = ((bitmap_word_t) 1) << (nb % BITMAP_WORD_BITS);
  int res;

  if (el == 0) return 0;
  res = (el->words[nw] & mask) != 0;
  el->words[nw] &= ~mask;
  if (_bitmap_zero_el_p (el)) {
    bm->curr_el = prev_el != NULL ? prev_el : DLIST_NEXT (bitmap_el_t, bm->curr_el);
    DLIST_REMOVE (bitmap_el_t, bm->els, el);
    DLIST_APPEND (bitmap_el_t, bm->bg->free_els, el);
  }
  return res;
}

static inline int bitmap_set_bit_range_p (bitmap_t bm, size_t nb, size_t len) {  // ???
  int res = 0;
  for (size_t i = 0; i < len; i++) res |= bitmap_set_bit_p (bm, nb + i);
  return res != 0;
}

static inline int bitmap_clear_bit_range_p (bitmap_t bm, size_t nb, size_t len) {  // ???
  int res = 0;
  for (size_t i = 0; i < len; i++) res |= bitmap_clear_bit_p (bm, nb + i);
  return res != 0;
}

static inline void bitmap_copy (bitmap_t dst, const_bitmap_t src) {
  _bitmap_check (src);
  bitmap_group_t bg = bg = dst->bg;
  bitmap_el_t el, new_el, prev_el = NULL;

  bitmap_clear (dst);
  for (el = DLIST_HEAD (bitmap_el_t, src->els); el != NULL; el = DLIST_NEXT (bitmap_el_t, el)) {
    new_el = _bitmap_add_el (dst, prev_el);
    new_el->index = el->index;
    for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] = el->words[i];
    prev_el = new_el;
  }
  dst->curr_el = DLIST_HEAD (bitmap_el_t, dst->els);
}

static inline int bitmap_equal_p (const_bitmap_t bm1, const_bitmap_t bm2) {
  _bitmap_check (bm1);
  _bitmap_check (bm2);
  bitmap_el_t el1, el2;

  for (el1 = DLIST_HEAD (bitmap_el_t, bm1->els), el2 = DLIST_HEAD (bitmap_el_t, bm2->els);
       el1 != NULL && el2 != NULL;
       el1 = DLIST_NEXT (bitmap_el_t, el1), el2 = DLIST_NEXT (bitmap_el_t, el2)) {
    if (el1->index != el2->index) return FALSE;
    for (size_t i = 0; i < BITMAP_EL_WORDS; i++)
      if (el1->words[i] != el2->words[i]) return FALSE;
  }
  return el1 == NULL && el2 == NULL;
}

static inline int bitmap_intersect_p (const_bitmap_t bm1, const_bitmap_t bm2) {
  _bitmap_check (bm1);
  _bitmap_check (bm2);
  bitmap_el_t el1 = DLIST_HEAD (bitmap_el_t, bm1->els), el2 = DLIST_HEAD (bitmap_el_t, bm2->els);

  while (el1 != NULL && el2 != NULL) {
    if (el1->index < el2->index) {
      el1 = DLIST_NEXT (bitmap_el_t, el1);
    } else if (el1->index > el2->index) {
      el2 = DLIST_NEXT (bitmap_el_t, el2);
    } else {
      for (size_t i = 0; i < BITMAP_EL_WORDS; i++)
        if (el1->words[i] & el2->words[i]) return TRUE;
      el1 = DLIST_NEXT (bitmap_el_t, el1);
      el2 = DLIST_NEXT (bitmap_el_t, el2);
    }
  }
  return FALSE;
}

static inline int bitmap_empty_p (const_bitmap_t bm) {
  _bitmap_check (bm);
  return DLIST_HEAD (bitmap_el_t, bm->els) == NULL;
}

/* Return the number of bits set in BM.  */
static inline size_t bitmap_bit_count (const_bitmap_t bm) {
  _bitmap_check (bm);
  bitmap_el_t el;
  bitmap_word_t w;
  size_t count = 0;

  for (el = DLIST_HEAD (bitmap_el_t, bm->els); el != NULL; el = DLIST_NEXT (bitmap_el_t, el))
    for (size_t i = 0; i < BITMAP_EL_WORDS; i++)
      for (w = el->words[i]; w != 0; w >>= 1)
        if (w & 1) count++;
  return count;
}

static inline int bitmap_el_eq_p (bitmap_el_t el1, bitmap_el_t el2) {
  if (el1->index != el2->index) return FALSE;
  for (size_t i = 0; i < BITMAP_EL_WORDS; i++)
    if (el1->words[i] != el2->words[i]) return FALSE;
  return TRUE;
}

static inline int _bitmap_op2 (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2, int ior_p,
                               int compl_p) {
  _bitmap_check (dst);
  _bitmap_check (src1);
  _bitmap_check (src2);
  bitmap_el_t dst_el = DLIST_HEAD (bitmap_el_t, dst->els), first_dst_el = dst_el;
  bitmap_el_t el1 = DLIST_HEAD (bitmap_el_t, src1->els);
  bitmap_el_t el2 = DLIST_HEAD (bitmap_el_t, src2->els);
  bitmap_el_t prev_new_el = NULL, new_el = NULL;
  size_t curr_index = dst_el == NULL ? 0 : dst_el->index;
  int change_p = FALSE, update_p;

  dst->curr_el = NULL;
  while ((el1 != NULL && (ior_p || compl_p || el2 != NULL)) || (ior_p && el2 != NULL)) {
    update_p = FALSE;
    if (new_el == NULL) new_el = _bitmap_add_el (dst, prev_new_el);
    if (el2 == NULL || (el1 != NULL && el1->index < el2->index)) {
      if (ior_p || compl_p) {
        new_el->index = el1->index;
        for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] = el1->words[i];
        update_p = TRUE;
      }
      el1 = DLIST_NEXT (bitmap_el_t, el1);
    } else if ((ior_p && el1 == NULL) || el1->index > el2->index) {
      if (ior_p) {
        new_el->index = el2->index;
        for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] = el2->words[i];
        update_p = TRUE;
      }
      el2 = DLIST_NEXT (bitmap_el_t, el2);
    } else {
      bitmap_word_t w = 0;

      BITMAP_ASSERT (el1 != NULL && el2 != NULL && el1->index == el2->index, "_bitmap_or2");
      new_el->index = el1->index;
      for (size_t i = 0; i < BITMAP_EL_WORDS; i++) {
        if (ior_p)
          new_el->words[i] = el1->words[i] | el2->words[i];
        else
          new_el->words[i] = el1->words[i] & (compl_p ? ~el2->words[i] : el2->words[i]);
        if (!ior_p) w |= new_el->words[i];
      }
      if (ior_p || w != 0) update_p = TRUE;
      el1 = DLIST_NEXT (bitmap_el_t, el1);
      el2 = DLIST_NEXT (bitmap_el_t, el2);
    }
    if (!update_p) continue;
    if (change_p || dst_el == NULL || !bitmap_el_eq_p (dst_el, new_el)) {
      change_p = TRUE;
    } else {
      dst_el = DLIST_NEXT (bitmap_el_t, dst_el);
    }
    if (new_el->index <= curr_index || dst->curr_el == NULL) dst->curr_el = new_el;
    prev_new_el = new_el;
    new_el = NULL;
  }
  if (dst_el != NULL) change_p = TRUE;
  _bitmap_clear_from (dst, first_dst_el);
  if (new_el != NULL) {
    BITMAP_ASSERT (!ior_p, "bitmap_ior wrong result");
    DLIST_REMOVE (bitmap_el_t, dst->els, new_el);
    DLIST_APPEND (bitmap_el_t, dst->bg->free_els, new_el);
  }
  return change_p;
}

static inline int bitmap_ior (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2) {
  return _bitmap_op2 (dst, src1, src2, TRUE, FALSE);
}

static inline int bitmap_and (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2) {
  return _bitmap_op2 (dst, src1, src2, FALSE, FALSE);
}

static inline int bitmap_and_compl (bitmap_t dst, const_bitmap_t src1, const_bitmap_t src2) {
  return _bitmap_op2 (dst, src1, src2, FALSE, TRUE);
}

/* DST = SRC1 | (SRC2 & SRC3) or DST = SRC1 | (SRC2 & ~SRC3).  Return true if DST changed.  */
static inline int _bitmap_op3 (bitmap_t dst, bitmap_t src1, bitmap_t src2, bitmap_t src3,
                               int compl_p) {
  _bitmap_check (dst);
  _bitmap_check (src1);
  _bitmap_check (src2);
  _bitmap_check (src3);
  bitmap_el_t dst_el = DLIST_HEAD (bitmap_el_t, dst->els), first_dst_el = dst_el;
  bitmap_el_t el1 = DLIST_HEAD (bitmap_el_t, src1->els);
  bitmap_el_t el2 = DLIST_HEAD (bitmap_el_t, src2->els);
  bitmap_el_t el3 = DLIST_HEAD (bitmap_el_t, src3->els);
  bitmap_el_t prev_new_el = NULL, new_el = NULL;
  size_t curr_index = dst_el == NULL ? 0 : dst_el->index;
  int change_p = FALSE, update_p;

  dst->curr_el = NULL;
  while (el1 != NULL || (el2 != NULL && (compl_p || el3 != NULL))) {
    update_p = FALSE;
    if (new_el == NULL) new_el = _bitmap_add_el (dst, prev_new_el);
    if (el2 == NULL || (!compl_p && el3 == NULL)
        || (el1 != NULL && el1->index < el2->index
            && ((compl_p && el3 == NULL) || el1->index < el3->index))) {
      new_el->index = el1->index;
      for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] = el1->words[i];
      el1 = DLIST_NEXT (bitmap_el_t, el1);
      update_p = TRUE;
    } else if ((compl_p && el3 == NULL) || el2->index < el3->index) {
      if (compl_p) {
        new_el->index = el2->index;
        for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] = el2->words[i];
        update_p = TRUE;
        if (el1 != NULL && el1->index == el2->index) {
          for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] |= el1->words[i];
          el1 = DLIST_NEXT (bitmap_el_t, el1);
        }
      }
      el2 = DLIST_NEXT (bitmap_el_t, el2);
    } else if (el2->index > el3->index) {
      el3 = DLIST_NEXT (bitmap_el_t, el3);
    } else {
      bitmap_word_t w = 0;

      new_el->index = el2->index;
      for (size_t i = 0; i < BITMAP_EL_WORDS; i++) {
        new_el->words[i] = el2->words[i] & (compl_p ? ~el3->words[i] : el3->words[i]);
        w |= new_el->words[i];
      }
      if (el1 != NULL && el1->index == el2->index) {
        w = 1;
        for (size_t i = 0; i < BITMAP_EL_WORDS; i++) new_el->words[i] |= el1->words[i];
        el1 = DLIST_NEXT (bitmap_el_t, el1);
      }
      if (w != 0) update_p = TRUE;
      el2 = DLIST_NEXT (bitmap_el_t, el2);
      el3 = DLIST_NEXT (bitmap_el_t, el3);
    }
    if (!update_p) continue;
    if (change_p || dst_el == NULL || !bitmap_el_eq_p (dst_el, new_el)) {
      change_p = TRUE;
    } else {
      dst_el = DLIST_NEXT (bitmap_el_t, dst_el);
    }
    if (new_el->index <= curr_index || dst->curr_el == NULL) dst->curr_el = new_el;
    prev_new_el = new_el;
    new_el = NULL;
  }
  if (dst_el != NULL) change_p = TRUE;
  _bitmap_clear_from (dst, first_dst_el);
  if (new_el != NULL) {
    DLIST_REMOVE (bitmap_el_t, dst->els, new_el);
    DLIST_APPEND (bitmap_el_t, dst->bg->free_els, new_el);
  }
  return change_p;
}

/* DST = SRC1 | (SRC2 & SRC3).  Return true if DST changed.  */
static inline int bitmap_ior_and (bitmap_t dst, bitmap_t src1, bitmap_t src2, bitmap_t src3) {
  return _bitmap_op3 (dst, src1, src2, src3, FALSE);
}

/* DST = SRC1 | (SRC2 & ~SRC3).  Return true if DST changed.  */
static inline int bitmap_ior_and_compl (bitmap_t dst, bitmap_t src1, bitmap_t src2, bitmap_t src3) {
  return _bitmap_op3 (dst, src1, src2, src3, TRUE);
}

typedef struct {
  bitmap_el_t curr_el;
  size_t nw, nb; /* nb is always in range [0..BITMAP_WORD_BITS) */
} bitmap_iterator_t;

static inline void _bitmap_iterator_init (bitmap_iterator_t *iter, bitmap_t bm) {
  _bitmap_check (bm);
  iter->curr_el = DLIST_HEAD (bitmap_el_t, bm->els);
  iter->nw = iter->nb = 0;
}

static inline int _bitmap_iterator_next (bitmap_iterator_t *iter, size_t *nbit) {
  bitmap_el_t el;
  size_t w, nw = iter->nw, nb = iter->nb;
  bitmap_word_t rest_mask, bit_mask, zero = 0, one = 1;

  for (el = iter->curr_el; el != NULL; el = DLIST_NEXT (bitmap_el_t, el), nb = nw = 0) {
    for (; nw < BITMAP_EL_WORDS; nw++, nb = 0)
      if ((w = el->words[nw]) != 0) {
        for (rest_mask = ~zero << nb, bit_mask = one << nb;
             nb < BITMAP_WORD_BITS && (w & rest_mask) != 0; nb++, rest_mask <<= 1, bit_mask <<= 1)
          if ((w & bit_mask) != 0) {
            *nbit = (el->index * BITMAP_EL_WORDS + nw) * BITMAP_WORD_BITS + nb;
            iter->curr_el = el;
            iter->nw = nw;
            if ((iter->nb = nb + 1) >= BITMAP_WORD_BITS) {
              iter->nb = 0;
              iter->nw = nw + 1;
            }
            return TRUE;
          }
      }
  }
  iter->curr_el = NULL;
  return FALSE;
}

/* Bitmap should not be change in the loop! */
#define FOREACH_BITMAP_BIT(iter, bitmap, nbit) \
  for (_bitmap_iterator_init (&iter, bitmap); _bitmap_iterator_next (&iter, &nbit);)

#endif /* #ifndef MIR_BITMAP_H */
