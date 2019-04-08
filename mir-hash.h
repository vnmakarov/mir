/* This file is a part of MIR project.

   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Simple high-quality multiplicative hash passing demerphq-smhsher.
   Hash for the same key can be different on different
   architectures. */                                                                                                                                   
#ifndef __MIR_HASH__
#define __MIR_HASH__

#include <stddef.h>
#include <stdint.h>

static inline uint64_t mir_get_key_part (const uint8_t *v, size_t len) {
  uint64_t tail = 0;
  
#if defined(__x86_64__) || defined(__i386__) || defined(__PPC64__) || defined(__s390__)  \
    || defined(__m32c__) || defined(cris) || defined(__CR16__) || defined(__vax__)       \
    || defined(__m68k__) || defined(__aarch64__) || defined(_M_AMD64) || defined(_M_IX86)
  if (len == sizeof (uint64_t)) return *(uint64_t *) v;
  else if (len == sizeof (uint32_t)) return *(uint32_t *) v;
  else if (len == sizeof (uint16_t)) return *(uint16_t *) v;
#endif
  for (size_t i = 0; i < len; i++)
    ((uint8_t *) &tail)[i] = v[i];
  return tail;
}

static inline uint64_t mir_mum (uint64_t v) {
  uint64_t c = 0X65862b62bdf5ef4d;
#if defined (__SIZEOF_INT128__)
  __uint128_t r = (__uint128_t) v * (__uint128_t) c;
  return (uint64_t) (r >> 64) + (uint64_t) r;
#else
  uint64_t v1 = v >> 32, v2 = (uint32_t) v, c1 = c >> 32, c2 = (uint32_t) c, rm = v2 * c1 + v1 * c2;
  return v1 * c1 + (rm >> 32) + v2 * c2 + (rm << 32);
#endif
}

static inline uint64_t mir_round (uint64_t state, uint64_t v) {
  state ^= mir_mum (v);
  return state ^ mir_mum (state);
}

static inline uint64_t mir_hash (const void *key, size_t len, uint64_t seed) {
  const uint8_t *v = (const uint8_t *)key;
  uint64_t r = seed + len;
  
  for (; len >= 8; len -= 8, v += 8)
    r = mir_round (r, mir_get_key_part (v, 8));
  if (len != 0)
    r ^= mir_mum (mir_get_key_part (v, len));
  return mir_round (r, r);
}

static inline uint64_t mir_hash_init (uint64_t seed) { return seed; }
static inline uint64_t mir_hash_step (uint64_t h, uint64_t key) { return mir_round (h, key); }
static inline uint64_t mir_hash_finish (uint64_t h) { return mir_round (h, h); }

static inline uint64_t mir_hash64 (uint64_t key, uint64_t seed) {
  return mir_hash_finish (mir_hash_step (mir_hash_init (seed), key));
}

#endif
