/* See C11 7.20 */
#ifndef _STDINT_H
#define _STDINT_H 1

typedef signed char int8_t;
typedef short int int16_t;
typedef int int32_t;
typedef long int int64_t;

typedef unsigned char uint8_t;
typedef unsigned short int uint16_t;
typedef unsigned int uint32_t;
typedef unsigned long int uint64_t;

typedef signed char int_least8_t;
typedef short int int_least16_t;
typedef int int_least32_t;
typedef long int int_least64_t;

typedef unsigned char uint_least8_t;
typedef unsigned short int uint_least16_t;
typedef unsigned int uint_least32_t;
typedef unsigned long int uint_least64_t;

typedef signed char int_fast8_t;
typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;

typedef unsigned char uint_fast8_t;
typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;

#define __intptr_t_defined
typedef long int intptr_t;
typedef unsigned long int uintptr_t;

typedef long int intmax_t;
typedef unsigned long int uintmax_t;

#define __INT64_C(c) c##L
#define __UINT64_C(c) c##UL

#define INT8_MIN (-128)
#define INT16_MIN (-32768)
#define INT32_MIN (-2147483648)
#define INT64_MIN (-9223372036854775808l)

#define INT8_MAX (127)
#define INT16_MAX (32767)
#define INT32_MAX (2147483647)
#define INT64_MAX (9223372036854775807l)

#define UINT8_MAX (255)
#define UINT16_MAX (65535)
#define UINT32_MAX (4294967295u)
#define UINT64_MAX (18446744073709551615ul)

#define INT_LEAST8_MIN (-128)
#define INT_LEAST16_MIN (-32768)
#define INT_LEAST32_MIN (-2147483648)
#define INT_LEAST64_MIN (-9223372036854775808L)

#define INT_LEAST8_MAX (127)
#define INT_LEAST16_MAX (32767)
#define INT_LEAST32_MAX (2147483647)
#define INT_LEAST64_MAX (9223372036854775807L)

#define UINT_LEAST8_MAX (255)
#define UINT_LEAST16_MAX (65535)
#define UINT_LEAST32_MAX (4294967295U)
#define UINT_LEAST64_MAX (18446744073709551615UL)

#define INT_FAST8_MIN (-128)
#define INT_FAST16_MIN (-9223372036854775808L)
#define INT_FAST32_MIN (-9223372036854775808L)
#define INT_FAST64_MIN (-9223372036854775808L)

#define INT_FAST8_MAX (127)
#define INT_FAST16_MAX (9223372036854775807L)
#define INT_FAST32_MAX (9223372036854775807L)
#define INT_FAST64_MAX (9223372036854775807L)

#define UINT_FAST8_MAX (255)
#define UINT_FAST16_MAX (18446744073709551615UL)
#define UINT_FAST32_MAX (18446744073709551615UL)
#define UINT_FAST64_MAX (18446744073709551615UL)

#define INTPTR_MIN (-9223372036854775808L)
#define INTPTR_MAX (9223372036854775807L)
#define UINTPTR_MAX (18446744073709551615UL)

#define INTMAX_MIN (-9223372036854775808L)
#define INTMAX_MAX (9223372036854775807L)
#define UINTMAX_MAX (18446744073709551615UL)

#define PTRDIFF_MIN (-9223372036854775808L)
#define PTRDIFF_MAX (9223372036854775807L)

#define SIZE_MAX (18446744073709551615UL)

/* For signed wchar_t and wint_t: */
#define WCHAR_MIN INT32_MIN
#define WCHAR_MAX INT32_MAX
#define WINT_MIN WCHAR_MIN
#define WINT_MAX WCHAR_MAX

#define INT8_C(value) value
#define INT16_C(value) value
#define INT32_C(value) value
#define INT64_C(value) value##L

#define UINT8_C(value) value
#define UINT16_C(value) value
#define UINT32_C(value) value##U
#define UINT64_C(value) value##UL

#define INTMAX_C(value) value##L
#define UINTMAX_C(value) value##UL

#endif /* #ifndef _STDINT_H */
