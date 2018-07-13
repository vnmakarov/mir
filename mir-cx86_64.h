#include <stdint.h>

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
#define MIR_LONG_LONG_MIN INT64_MIN
#define MIR_LONG_LONG_MAX INT64_MAX

typedef uint8_t mir_uchar;
typedef uint16_t mir_ushort;
typedef uint32_t mir_uint;
typedef uint64_t mir_ulong;
typedef uint64_t mir_ulong_long;

#define MIR_UCHAR_MAX UINT8_MAX
#define MIR_USHORT_MAX UINT16_MAX
#define MIR_UINT_MAX UINT32_MAX
#define MIR_ULONG_MAX UINT32_MAX
#define MIR_ULONG_LONG_MAX UINT64_MAX

typedef mir_schar mir_char;
#define MIR_CHAR_MIN MIR_SCHAR_MIN
#define MIR_CHAR_MAX MIR_SCHAR_MAX

typedef float mir_float;
typedef double mir_double;
typedef mir_double mir_long_double;

typedef uint8_t mir_bool; // ???
typedef int64_t mir_ptrdiff_t;
typedef uint64_t mir_size_t;
