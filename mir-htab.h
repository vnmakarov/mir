/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_HTAB_H
#define MIR_HTAB_H

#include "mir-varr.h"

#define FALSE 0
#define TRUE 1

#if !defined(VARR_ENABLE_CHECKING) && !defined(NDEBUG)
#define VARR_ENABLE_CHECKING
#endif

#ifndef HTAB_ENABLE_CHECKING
#define HTAB_ASSERT(EXPR, OP, T) ((void) (EXPR))

#else
static inline void mir_htab_assert_fail (const char *op, const char *var) {
  fprintf (stderr, "wrong %s for %s\n", op, var);
  assert (0);
}

#define HTAB_ASSERT(EXPR, OP, T) (void) ((EXPR) ? 0 : (mir_htab_assert_fail (OP, #T), 0))

#endif

#ifdef __GNUC__
#define MIR_HTAB_UNUSED __attribute__ ((unused))
#define MIR_HTAB_NO_RETURN __attribute__ ((noreturn))
#else
#define MIR_HTAB_UNUSED
#define MIR_HTAB_NO_RETURN
#endif

static inline void MIR_HTAB_NO_RETURN mir_htab_error (const char *message) {
#ifdef MIR_HTAB_ERROR
  MIR_HTAB_ERROR (message);
  assert (FALSE);
#else
  fprintf (stderr, "%s\n", message);
#endif
  exit (1);
}

/*---------------- Typed hash table -----------------------------*/
typedef unsigned htab_ind_t;
typedef unsigned htab_size_t;
typedef unsigned htab_hash_t;

#define HTAB_EMPTY_IND (~(htab_ind_t) 0)
#define HTAB_DELETED_IND (HTAB_EMPTY_IND - 1)
#define HTAB_DELETED_HASH 0

enum htab_action { HTAB_FIND, HTAB_INSERT, HTAB_REPLACE, HTAB_DELETE };

#define HTAB(T) HTAB_##T
#define HTAB_OP(T, OP) HTAB_##T##_##OP
#define HTAB_OP_DEF(T, OP) MIR_HTAB_UNUSED HTAB_OP (T, OP)

DEF_VARR (htab_ind_t)

#define HTAB_EL(T) HTAB_EL_##T

#define HTAB_T(T)                                          \
  typedef struct HTAB_EL (T) {                             \
    htab_hash_t hash;                                      \
    T el;                                                  \
  } HTAB_EL (T);                                           \
  DEF_VARR (HTAB_EL (T))                                   \
  typedef struct {                                         \
    htab_size_t els_num, els_start, els_bound, collisions; \
    htab_hash_t (*hash_func) (T el);                       \
    int (*eq_func) (T el1, T el2);                         \
    void (*free_func) (T el);                              \
    VARR (HTAB_EL (T)) * els;                              \
    VARR (htab_ind_t) * entries;                           \
  } HTAB (T);

#define DEF_HTAB(T)                                                                               \
  HTAB_T (T)                                                                                      \
                                                                                                  \
  static inline void HTAB_OP_DEF (T, create) (HTAB (T) * *htab, htab_size_t min_size,             \
                                              htab_hash_t (*hash_func) (T el),                    \
                                              int (*eq_func) (T el1, T el2),                      \
                                              void (*free_func) (T el)) {                         \
    HTAB (T) * ht;                                                                                \
    htab_size_t i, size;                                                                          \
                                                                                                  \
    for (size = 2; min_size > size; size *= 2)                                                    \
      ;                                                                                           \
    ht = malloc (sizeof (*ht));                                                                   \
    if (ht == NULL) mir_htab_error ("htab: no memory");                                           \
    VARR_CREATE (HTAB_EL (T), ht->els, size);                                                     \
    VARR_TAILOR (HTAB_EL (T), ht->els, size);                                                     \
    VARR_CREATE (htab_ind_t, ht->entries, 2 * size);                                              \
    ht->hash_func = hash_func;                                                                    \
    ht->eq_func = eq_func;                                                                        \
    ht->free_func = free_func;                                                                    \
    ht->els_num = ht->els_start = ht->els_bound = ht->collisions = 0;                             \
    for (i = 0; i < 2 * size; i++) VARR_PUSH (htab_ind_t, ht->entries, HTAB_EMPTY_IND);           \
    *htab = ht;                                                                                   \
  }                                                                                               \
                                                                                                  \
  static inline void HTAB_OP_DEF (T, clear) (HTAB (T) * htab) {                                   \
    htab_ind_t *addr;                                                                             \
    htab_size_t i, size;                                                                          \
    HTAB_EL (T) * els_addr;                                                                       \
                                                                                                  \
    HTAB_ASSERT (htab != NULL, "clear", T);                                                       \
    if (htab->free_func != NULL) {                                                                \
      els_addr = VARR_ADDR (HTAB_EL (T), htab->els);                                              \
      size = VARR_LENGTH (HTAB_EL (T), htab->els);                                                \
      for (i = 0; i < htab->els_bound; i++)                                                       \
        if (els_addr[i].hash != HTAB_DELETED_HASH) htab->free_func (els_addr[i].el);              \
    }                                                                                             \
    htab->els_num = htab->els_start = htab->els_bound = 0;                                        \
    addr = VARR_ADDR (htab_ind_t, htab->entries);                                                 \
    size = VARR_LENGTH (htab_ind_t, htab->entries);                                               \
    for (i = 0; i < size; i++) addr[i] = HTAB_EMPTY_IND;                                          \
  }                                                                                               \
                                                                                                  \
  static inline void HTAB_OP_DEF (T, destroy) (HTAB (T) * *htab) {                                \
    HTAB_ASSERT (*htab != NULL, "destroy", T);                                                    \
    if ((*htab)->free_func != NULL) HTAB_OP (T, clear) (*htab);                                   \
    VARR_DESTROY (HTAB_EL (T), (*htab)->els);                                                     \
    VARR_DESTROY (htab_ind_t, (*htab)->entries);                                                  \
    free (*htab);                                                                                 \
    *htab = NULL;                                                                                 \
  }                                                                                               \
                                                                                                  \
  static inline int HTAB_OP_DEF (T, do) (HTAB (T) * htab, T el, enum htab_action action,          \
                                         T * res) {                                               \
    htab_ind_t ind, el_ind, *entry, *first_deleted_entry = NULL;                                  \
    htab_hash_t hash, peterb;                                                                     \
    htab_size_t els_size, size, mask, start, bound, i;                                            \
    htab_ind_t *addr;                                                                             \
    HTAB_EL (T) * els_addr;                                                                       \
                                                                                                  \
    HTAB_ASSERT (htab != NULL, "do htab", T);                                                     \
    size = VARR_LENGTH (htab_ind_t, htab->entries);                                               \
    els_size = VARR_LENGTH (HTAB_EL (T), htab->els);                                              \
    HTAB_ASSERT (els_size * 2 == size, "do size", T);                                             \
    if ((action == HTAB_INSERT || action == HTAB_REPLACE) && htab->els_bound == els_size) {       \
      size *= 2;                                                                                  \
      VARR_TAILOR (htab_ind_t, htab->entries, size);                                              \
      addr = VARR_ADDR (htab_ind_t, htab->entries);                                               \
      for (i = 0; i < size; i++) addr[i] = HTAB_EMPTY_IND;                                        \
      VARR_TAILOR (HTAB_EL (T), htab->els, els_size * 2);                                         \
      els_addr = VARR_ADDR (HTAB_EL (T), htab->els);                                              \
      start = htab->els_start;                                                                    \
      bound = htab->els_bound;                                                                    \
      htab->els_start = htab->els_bound = htab->els_num = 0;                                      \
      for (i = start; i < bound; i++)                                                             \
        if (els_addr[i].hash != HTAB_DELETED_HASH) {                                              \
          HTAB_OP (T, do) (htab, els_addr[i].el, HTAB_INSERT, res);                               \
          HTAB_ASSERT ((*htab->eq_func) (*res, els_addr[i].el), "do expand", T);                  \
        }                                                                                         \
      HTAB_ASSERT (bound - start >= htab->els_bound, "do bound", T);                              \
    }                                                                                             \
    mask = size - 1;                                                                              \
    hash = (*htab->hash_func) (el);                                                               \
    if (hash == HTAB_DELETED_HASH) hash += 1;                                                     \
    peterb = hash;                                                                                \
    ind = hash & mask;                                                                            \
    addr = VARR_ADDR (htab_ind_t, htab->entries);                                                 \
    els_addr = VARR_ADDR (HTAB_EL (T), htab->els);                                                \
    for (;; htab->collisions++) {                                                                 \
      entry = addr + ind;                                                                         \
      el_ind = *entry;                                                                            \
      if (el_ind != HTAB_EMPTY_IND) {                                                             \
        if (el_ind == HTAB_DELETED_IND) {                                                         \
          first_deleted_entry = entry;                                                            \
        } else if (els_addr[el_ind].hash == hash && (*htab->eq_func) (els_addr[el_ind].el, el)) { \
          if (action == HTAB_REPLACE) {                                                           \
            if (htab->free_func != NULL) htab->free_func (els_addr[el_ind].el);                   \
            els_addr[el_ind].el = el;                                                             \
          }                                                                                       \
          if (action != HTAB_DELETE) {                                                            \
            *res = els_addr[el_ind].el;                                                           \
          } else {                                                                                \
            htab->els_num--;                                                                      \
            *entry = HTAB_DELETED_IND;                                                            \
            if (htab->free_func != NULL) htab->free_func (els_addr[el_ind].el);                   \
            els_addr[el_ind].hash = HTAB_DELETED_HASH;                                            \
          }                                                                                       \
          return TRUE;                                                                            \
        }                                                                                         \
      } else {                                                                                    \
        if (action == HTAB_INSERT || action == HTAB_REPLACE) {                                    \
          htab->els_num++;                                                                        \
          if (first_deleted_entry != NULL) entry = first_deleted_entry;                           \
          els_addr[htab->els_bound].hash = hash;                                                  \
          els_addr[htab->els_bound].el = el;                                                      \
          *entry = htab->els_bound++;                                                             \
          *res = el;                                                                              \
        }                                                                                         \
        return FALSE;                                                                             \
      }                                                                                           \
      peterb >>= 11;                                                                              \
      ind = (5 * ind + peterb + 1) & mask;                                                        \
    }                                                                                             \
  }                                                                                               \
                                                                                                  \
  static inline htab_size_t HTAB_OP_DEF (T, els_num) (HTAB (T) * htab) {                          \
    HTAB_ASSERT (htab != NULL, "els_num", T);                                                     \
    return htab->els_num;                                                                         \
  }                                                                                               \
  static inline htab_size_t HTAB_OP_DEF (T, collisions) (HTAB (T) * htab) {                       \
    HTAB_ASSERT (htab != NULL, "collisions", T);                                                  \
    return htab->collisions;                                                                      \
  }

#define HTAB_CREATE(T, V, S, H, EQ) (HTAB_OP (T, create) (&(V), S, H, EQ, NULL))
#define HTAB_CREATE_WITH_FREE_FUNC(T, V, S, H, EQ, F) (HTAB_OP (T, create) (&(V), S, H, EQ, F))
#define HTAB_CLEAR(T, V) (HTAB_OP (T, clear) (V))
#define HTAB_DESTROY(T, V) (HTAB_OP (T, destroy) (&(V)))
/* It returns TRUE if the element existed in the table.  */
#define HTAB_DO(T, V, EL, A, TAB_EL) (HTAB_OP (T, do) (V, EL, A, &(TAB_EL)))
#define HTAB_ELS_NUM(T, V) (HTAB_OP (T, els_num) (V))
#define HTAB_COLLISIONS(T, V) (HTAB_OP (T, collisions) (V))

#endif /* #ifndef MIR_HTAB_H */
