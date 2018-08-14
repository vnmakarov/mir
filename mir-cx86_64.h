#include <stdint.h>

#define MIR_CHAR_BIT 8

typedef int8_t mir_schar;
typedef int16_t mir_short;
typedef int32_t mir_int;
typedef int64_t mir_long;
typedef int64_t mir_long_long;

#define MIR_SCHAR_MIN INT8_MIN
#define MIR_SCHAR_MAX INT8_MAX
#define MIR_SHORT_MIN INT16_MIN
#define MIR_SHORT_MAX INT16_MAX
#define MIR_INT_MIN INT32_MIN
#define MIR_INT_MAX INT32_MAX
#define MIR_LONG_MIN INT64_MIN
#define MIR_LONG_MAX INT32_MAX
#define MIR_LLONG_MIN INT64_MIN
#define MIR_LLONG_MAX INT64_MAX

typedef uint8_t mir_uchar;
typedef uint16_t mir_ushort;
typedef uint32_t mir_uint;
typedef uint64_t mir_ulong;
typedef uint64_t mir_ulong_long;

#define MIR_UCHAR_MAX UINT8_MAX
#define MIR_USHORT_MAX UINT16_MAX
#define MIR_UINT_MAX UINT32_MAX
#define MIR_ULONG_MAX UINT32_MAX
#define MIR_ULLONG_MAX UINT64_MAX

typedef mir_schar mir_char;
#define MIR_CHAR_MIN MIR_SCHAR_MIN
#define MIR_CHAR_MAX MIR_SCHAR_MAX

typedef float mir_float;
typedef double mir_double;
typedef mir_double mir_long_double;

typedef uint8_t mir_bool;
typedef int64_t mir_ptrdiff_t;
typedef uint64_t mir_size_t;

static const char *standard_includes[] = {
  "include/mirc/mirc.h",
  "include/mirc/x86-64/mirc-x86_64-linux.h"
};

static const char *standard_include_dirs[] = {
  "include/mirc/",
  "include/mirc/x86-64/"
};

#define ADJUST_TYPE_ALIGNMENT(align, type) x86_adjust_type_alignment (align, type)

static int x86_adjust_type_alignment (int align, struct type *type) {
  /* see https://www.uclibc.org/docs/psABI-x86_64.pdf */
  if (type->mode != TM_ARR || raw_type_size (type) < 16) return align;
  return 16;
}

static int invalid_alignment (mir_long_long align) {
  return align != 0 && align != 1 && align != 2 && align != 4 && align != 8 && align != 16;
}

/* Update BYTE_OFFSET and BIT_OFFSET for a bit field of length BIT_LEN.
   Return storage unit size to use.  */
static int get_bit_field_info (int bit_len, unsigned long long *byte_offset, int *bit_offset) {
  int unit_size;
  unsigned long long start_byte, finish_byte, start_unit_byte;
  
  assert (bit_len <= 8 * 8);
  for (;;) {
    for (unit_size = 1; unit_size <= 8; unit_size *= 2) {
      if (bit_len > unit_size * 8) continue;
      start_byte = *byte_offset; finish_byte = (start_byte * 8 + *bit_offset + bit_len - 1) / 8;
      start_unit_byte = (start_byte / unit_size) * unit_size;
      if (finish_byte < start_unit_byte + unit_size)
	break;
    }
    if (unit_size <= 8)
      break;
    (*byte_offset)++;
    *bit_offset = 0;
  }
  return unit_size;
}
