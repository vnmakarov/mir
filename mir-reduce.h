/* Data compression.  Major goals are simplicity, fast decompression
   speed, moderate compression speed.  The algorithm is tuned for
   binary MIR compression and close to LZ4.  Only we use a bit
   different format and offsets in symbol numbers instead of just
   offsets.

   Functions reduce_do/reduce_undo are the only interface functions.

   Format:
    o 8 bits tag
      (N bits for symbol length; 0 means no sym, 2^N -1 means symbol length as uint present;
      (8-N) bits for reference length; 0 means no ref, 2^(8-N) - 1 means length as uint present)
    o [uint for symbol lenght]*, symbol string,
    o [uint for ref len]*, symbol number as uint */

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "mir-hash.h"

#define FALSE 0
#define TRUE 1
#define REDUCE_SYMB_TAG_LEN 3
#define REDUCE_SYMB_TAG_LONG ((1 << REDUCE_SYMB_TAG_LEN) - 1) /* should be not changed */
#define REDUCE_REF_TAG_LEN (8 - REDUCE_SYMB_TAG_LEN)
#define REDUCE_REF_TAG_LONG ((1 << REDUCE_REF_TAG_LEN) - 1) /* should be not changed */
#define REDUCE_START_LEN 4
#define REDUCE_BUF_LEN (1 << 20) /* should be power of two */
#define REDUCE_TABLE_SIZE (2 * REDUCE_BUF_LEN)
#define REDUCE_MAX_SYMB_LEN (2047)

typedef size_t (*reader_t) (void *start, size_t len);
typedef size_t (*writer_t) (const void *start, size_t len);

struct reduce_el {
  uint32_t pos, num, next, head;
};

struct reduce_data {
  reader_t reader;
  writer_t writer;
  int err_p;
  uint32_t curr_num, buf_bound, curr_symb_len;
  uint8_t curr_symb[REDUCE_MAX_SYMB_LEN];
  uint8_t buf[REDUCE_BUF_LEN];
  struct reduce_el table[REDUCE_TABLE_SIZE]; /* hash -> {pos, num} */
  uint32_t el_free;
};

static inline uint32_t reduce_min (uint32_t a, uint32_t b) { return a < b ? a : b; }

static inline uint32_t reduce_get_new_el (struct reduce_data *data) {
  uint32_t res = data->el_free;

  if (res != UINT32_MAX) data->el_free = data->table[res].next;
  return res;
}

static inline void reduce_put (struct reduce_data *data, int byte) {
  uint8_t u = byte;

  if (data->writer (&u, 1) != 1) data->err_p = TRUE;
}

static inline int reduce_get (reader_t reader) {
  uint8_t u;

  if (reader (&u, 1) != 1) return -1;
  return u;
}

static inline uint32_t reduce_ref_offset_size (uint32_t offset) {
  return offset < (1 << 7) ? 1 : offset < (1 << 14) ? 2 : offset < (1 << 21) ? 3 : 4;
}

static inline uint32_t reduce_ref_size (uint32_t len, uint32_t offset) {
  assert (len >= REDUCE_START_LEN);
  len -= REDUCE_START_LEN - 1;
  return ((len < REDUCE_REF_TAG_LONG ? 0 : reduce_ref_offset_size (len))
          + reduce_ref_offset_size (offset));
}

static inline void reduce_uint_write (struct reduce_data *data, uint32_t u) {
  int n;

  assert (u < (1 << 7 * 4));
  for (n = 1; n <= 4 && u >= (1 << 7 * n); n++)
    ;
  reduce_put (data, (1 << (8 - n)) | (u >> (n - 1) * 8) & 0xff); /* tag */
  for (int i = 2; i <= n; i++) reduce_put (data, (u >> (n - i) * 8) & 0xff);
}

static inline int64_t reduce_uint_read (reader_t reader) {
  int i, n, r = reduce_get (reader);
  uint32_t u, v;

  if (r < 0) return -1;
  for (u = (uint32_t) r, n = 1; n <= 4 && (u >> (8 - n)) != 1; n++)
    ;
  assert ((u >> (8 - n)) == 1);
  v = u & (0xff >> n);
  for (i = 1; i < n; i++) {
    if ((r = reduce_get (reader)) < 0) return -1;
    v = v * 256 + (uint32_t) r;
  }
  return v;
}

static inline int reduce_symb_flush (struct reduce_data *data, int ref_tag) {
  uint8_t u;
  uint32_t len = data->curr_symb_len;

  if (len == 0 && ref_tag == 0) return FALSE;
  u = ((len < REDUCE_SYMB_TAG_LONG ? len : REDUCE_SYMB_TAG_LONG) << REDUCE_REF_TAG_LEN) | ref_tag;
  data->writer (&u, 1);
  if (len >= REDUCE_SYMB_TAG_LONG) reduce_uint_write (data, len);
  data->writer (data->curr_symb, len);
  data->curr_symb_len = 0;
  return TRUE;
}

static inline void reduce_output_byte (struct reduce_data *data, uint32_t pos) {
  if (data->curr_symb_len + 1 > REDUCE_MAX_SYMB_LEN) {
    reduce_symb_flush (data, 0);
    data->curr_symb_len = 0;
  }
  data->curr_symb[data->curr_symb_len++] = data->buf[pos];
}

static inline void reduce_output_ref (struct reduce_data *data, uint32_t offset, uint32_t len) {
  uint32_t ref_tag;

  assert (len >= REDUCE_START_LEN);
  len -= REDUCE_START_LEN - 1;
  ref_tag = len < REDUCE_REF_TAG_LONG ? len : REDUCE_REF_TAG_LONG;
  reduce_symb_flush (data, ref_tag);
  if (len >= REDUCE_REF_TAG_LONG) reduce_uint_write (data, len);
  reduce_uint_write (data, offset);
}

static inline uint32_t reduce_dict_find_longest (struct reduce_data *data, uint32_t pos,
                                                 uint32_t *dict_pos) {
  uint32_t len, best_len, len_bound;
  uint64_t hash;
  uint32_t off, best_off, ref_size, best_ref_size;
  uint32_t curr, prev, next;
  const char *s1, *s2;
  struct reduce_el *el, *best_el = NULL;

  if (pos + REDUCE_START_LEN > data->buf_bound) return 0;
  hash = mir_hash (&data->buf[pos], REDUCE_START_LEN, 42) % REDUCE_TABLE_SIZE;
  for (curr = data->table[hash].head, prev = UINT32_MAX; curr != UINT32_MAX;
       prev = curr, curr = next) {
    next = data->table[curr].next;
    el = &data->table[curr];
    len_bound = reduce_min (data->buf_bound - pos, pos - el->pos);
    if (len_bound < REDUCE_START_LEN) continue;
    s1 = &data->buf[el->pos];
    s2 = &data->buf[pos];
#if MIR_HASH_UNALIGNED_ACCESS
    assert (REDUCE_START_LEN >= 4);
    if (*(uint32_t *) &s1[0] != *(uint32_t *) &s2[0]) continue;
    len = 4;
#else
    len = 0;
#endif
    for (; len < len_bound; len++)
      if (s1[len] != s2[len]) break;
#if !MIR_HASH_UNALIGNED_ACCESS
    if (len < REDUCE_START_LEN) continue;
#endif
    if (best_el == NULL) {
      best_len = len;
      best_el = el;
      best_ref_size = reduce_ref_size (best_len, best_off);
      continue;
    }
    off = data->curr_num - el->num;
    best_off = data->curr_num - best_el->num;
    ref_size = reduce_ref_size (len, off);
    if (best_len + ref_size < len + best_ref_size) {
      best_len = len;
      best_el = el;
      best_ref_size = ref_size;
    }
  }
  if (best_el == NULL) return 0;
  *dict_pos = best_el->num;
  return best_len;
}

static inline void reduce_dict_add (struct reduce_data *data, uint32_t pos) {
  uint64_t hash;
  struct reduce_el *el;
  uint32_t curr;

  if (pos + REDUCE_START_LEN > data->buf_bound) return;
  hash = mir_hash (&data->buf[pos], REDUCE_START_LEN, 42) % REDUCE_TABLE_SIZE;
  if ((curr = reduce_get_new_el (data)) == UINT32_MAX) { /* rare case: use last if any */
    for (curr = data->table[hash].head; curr != UINT32_MAX && data->table[curr].next != UINT32_MAX;
         curr = data->table[curr].next)
      ;
    if (curr == UINT32_MAX) return; /* no more free els */
  }
  data->table[curr].pos = pos;
  data->table[curr].num = data->curr_num++;
  data->table[curr].next = data->table[hash].head;
  data->table[hash].head = curr;
}

static void reduce_reset_next (struct reduce_data *data) {
  for (uint32_t i = 0; i < REDUCE_TABLE_SIZE; i++) {
    data->table[i].next = i + 1;
    data->table[i].head = UINT32_MAX;
  }
  data->table[REDUCE_TABLE_SIZE - 1].next = UINT32_MAX;
  data->el_free = 0;
}

static inline int reduce_do (reader_t reader, writer_t writer) {
  int err_p;
  uint32_t dict_len, dict_pos, base;
  struct reduce_data *data = malloc (sizeof (struct reduce_data));

  data->reader = reader;
  data->writer = writer;
  data->err_p = FALSE;
  for (;;) {
    data->buf_bound = reader (&data->buf, REDUCE_BUF_LEN);
    if (data->buf_bound == 0) break;
    data->curr_num = data->curr_symb_len = 0;
    reduce_reset_next (data);
    for (uint32_t pos = 0; pos < data->buf_bound;) {
      dict_len = reduce_dict_find_longest (data, pos, &dict_pos);
      base = data->curr_num;
      if (dict_len == 0) {
        reduce_output_byte (data, pos);
        reduce_dict_add (data, pos);
        pos++;
        continue;
      }
      reduce_output_ref (data, base - dict_pos, dict_len);
      reduce_dict_add (data, pos); /* replace */
      pos += dict_len;
    }
    reduce_symb_flush (data, 0);
  }
  err_p = data->err_p;
  free (data);
  return !err_p;
}

static inline int reduce_undo (reader_t reader, writer_t writer) {
  uint8_t tag;
  uint32_t sym_len, ref_len, ref_ind, sym_pos, pos = 0, curr_ind = 0;
  uint64_t r;
  int ret = FALSE;
  struct reduce_data *data = malloc (sizeof (struct reduce_data));

  data->reader = reader;
  data->writer = writer;
  for (;;) {
    if (reader (&tag, 1) == 0) {
      if (pos != 0) writer (&data->buf[0], pos);
      ret = TRUE;
      break;
    }
    sym_len = tag >> REDUCE_REF_TAG_LEN;
    if (sym_len != 0) {
      if (sym_len == REDUCE_SYMB_TAG_LONG) {
        if ((r = reduce_uint_read (reader)) < 0) break;
        sym_len = r;
      }
      if (sym_len > REDUCE_MAX_SYMB_LEN || pos + sym_len > REDUCE_BUF_LEN) break;
      if (reader (&data->buf[pos], sym_len) != sym_len) break;
      for (uint32_t i = 0; i < sym_len; i++, pos++, curr_ind++) data->table[curr_ind].pos = pos;
    }
    ref_len = tag & REDUCE_REF_TAG_LONG;
    if (ref_len != 0) {
      if (ref_len == REDUCE_REF_TAG_LONG) {
        if ((r = reduce_uint_read (reader)) < 0) break;
        ref_len = r;
      }
      ref_len += REDUCE_START_LEN - 1;
      if ((r = reduce_uint_read (reader)) < 0) break;
      ref_ind = r;
      if (curr_ind < ref_ind) break;
      sym_pos = data->table[curr_ind - ref_ind].pos;
      if (sym_pos + ref_len > REDUCE_BUF_LEN) break;
      memcpy (&data->buf[pos], &data->buf[sym_pos], ref_len);
      data->table[curr_ind++].pos = pos;
      pos += ref_len;
    }
    if (pos >= REDUCE_BUF_LEN) {
      if (pos != REDUCE_BUF_LEN) break;
      writer (&data->buf[0], pos);
      pos = curr_ind = 0;
    }
  }
  free (data);
  return ret;
}
