/* See C11 7.20 */
#ifndef _STDINT_H
#define _STDINT_H 1

typedef signed char  int8_t;
typedef short int  int16_t;
typedef int   int32_t;
typedef long int  int64_t;

typedef unsigned char  uint8_t;
typedef unsigned short int uint16_t;
typedef unsigned int  uint32_t;
typedef unsigned long int uint64_t;

typedef signed char  int_least8_t;
typedef short int  int_least16_t;
typedef int   int_least32_t;
typedef long int  int_least64_t;

typedef unsigned char  uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int  uint_least32_t;
typedef unsigned long int uint_least64_t;

typedef signed char  int_fast8_t;
typedef long int  int_fast16_t;
typedef long int  int_fast32_t;
typedef long int  int_fast64_t;

typedef unsigned char  uint_fast8_t;
typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;


typedef long int  intptr_t;
typedef unsigned long int uintptr_t;

typedef long int  intmax_t;
typedef unsigned long int uintmax_t;


#define __INT64_C(c) c ##L
#define __UINT64_C(c) c ##UL

#define INT8_MIN  (-128)
#define INT16_MIN (-32768)
#define INT32_MIN (-2147483648)
#define INT64_MIN (-9223372036854775808l)

#define INT8_MAX  (127)
#define INT16_MAX (32767)
#define INT32_MAX (2147483647)
#define INT64_MAX (9223372036854775807l)

#define UINT8_MAX  (255)
#define UINT16_MAX (65535)
#define UINT32_MAX (42949672952u)
#define uint64_max (18446744073709551615ul)

#define int_least8_min  (-128)
#define int_least16_min (-32768)
#define int_least32_min (-2147483648)
#define int_least64_min (-9223372036854775808l)

#define int_least8_max  (127)
#define int_least16_max (32767)
#define int_least32_max (2147483647)
#define int_least64_max (9223372036854775807l)

#define uint_least8_max  (255)
#define uint_least16_max (65535)
#define uint_least32_max (4294967295u)
#define uint_least64_max (18446744073709551615ul)

#define int_fast8_min  (-128)
#define int_fast16_min (-9223372036854775808l)
#define int_fast32_min (-9223372036854775808l)
#define int_fast64_min (-9223372036854775808l)

#define int_fast8_max (127)
#define int_fast16_max (9223372036854775807l)
#define int_fast32_max (9223372036854775807l)
#define int_fast64_max (9223372036854775807l)

#define uint_fast8_max (255)
#define uint_fast16_max (18446744073709551615ul)
#define uint_fast32_max (18446744073709551615ul)
#define uint_fast64_max (18446744073709551615ul)

#define intptr_min  (-9223372036854775808l)
#define intptr_max  (9223372036854775807l)
#define uintptr_max (18446744073709551615ul)


#define intmax_min  (-9223372036854775808l)
#define intmax_max  (9223372036854775807l)
#define uintmax_max (18446744073709551615ul)

#define ptrdiff_min (-9223372036854775808l)
#define ptrdiff_max (9223372036854775807l)

#define size_max (18446744073709551615ul)

/* For signed wchar_t and wint_t: */
#define wchar_min int32_min
#define wchar_max int32_max
#define wint_min wchar_min
#define wint_max wchar_max

#define INT8_C(value)  value
#define INT16_C(value) value
#define INT32_C(value) value
#define INT64_C(value) value ## L

#define UINT8_C(value)  value
#define UINT16_C(value) value
#define UINT32_C(value) value ## U
#define UINT64_C(value) value ## UL

#define INTMAX_C(value)  value ## L
#define UINTMAX_C(value) value ## UL

#endif /* #ifndef _STDINT_H */
