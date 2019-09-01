/* See 5.2.4.2 */
#ifndef __LIMITS_H
#define __LIMITS_H

#define CHAR_BIT 8

#define SCHAR_MIN (-SCHAR_MAX - 1)
#define SCHAR_MAX 127
#define UCHAR_MAX (SCHAR_MAX * 2 + 1)

#define MB_LEN_MAX 1

#define SHRT_MIN (-SHRT_MAX - 1)
#define SHRT_MAX 32767
#define USHRT_MAX (SHRT_MAX * 2 + 1)

#define INT_MIN (-INT_MAX - 1)
#define INT_MAX 2147483647
#define UINT_MAX (INT_MAX * 2u + 1u)

#define LONG_MIN (-LONG_MAX - 1l)
#define LONG_MAX 9223372036854775807l
#define ULONG_MAX (LONG_MAX * 2ul + 1ul)

#define LLONG_MIN LONG_MIN
#define LLONG_MAX LONG_MAX
#define ULLONG_MAX ULONG_MAX

/* signed char by default */
#define CHAR_MIN SCHAR_MIN
#define CHAR_MAX SCHAR_MAX

#endif /* #ifndef __LIMITS_H */
