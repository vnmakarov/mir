#define __amd64 1
#define __amd64__ 1
#define _LP64 1
#define __LP64__ 1
#define __x86_64 1
#define __x86_64__ 1

#define __SIZEOF_DOUBLE__ 8
#define __SIZEOF_FLOAT__ 4
#define __SIZEOF_INT__ 4
#define __SIZEOF_LONG_DOUBLE__ 8
#define __SIZEOF_LONG_LONG__ 8
#define __SIZEOF_LONG__ 8
#define __SIZEOF_POINTER__ 8
#define __SIZEOF_PTRDIFF_T__ 8
#define __SIZEOF_SHORT__ 2
#define __SIZEOF_SIZE_T__ 8

#define __BYTE_ORDER__ 1234
#define __ORDER_LITTLE_ENDIAN__ 1234
#define __ORDER_BIG_ENDIAN__ 4321

/* Some GCC predefined macros: */
#define __SIZE_TYPE__ unsigned long
#define __PTRDIFF_TYPE__ long
#define __INTMAX_TYPE__ long
#define __UINTMAX_TYPE__ unsigned long
#define __INT8_TYPE__ signed char
#define __INT16_TYPE__ short
#define __INT32_TYPE__ int
#define __INT64_TYPE__ long
#define __UINT8_TYPE__ unsigned char
#define __UINT16_TYPE__ unsigned short
#define __UINT32_TYPE__ unsigned int
#define __UINT64_TYPE__ unsigned long
#define __INTPTR_TYPE__ long
#define __UINTPTR_TYPE__ unsigned long

#define __CHAR_BIT__ 8
#define __INT8_MAX__ 127
#define __INT16_MAX__ 32767
#define __INT32_MAX__ 2147483647
#define __INT64_MAX__ 9223372036854775807l
#define __UINT8_MAX__ (__INT8_MAX__ * 2u + 1u)
#define __UINT16_MAX__ (__INT16_MAX__ * 2u + 1u)
#define __UINT32_MAX__ (__INT32_MAX__ * 2u + 1u)
#define __UINT64_MAX__ (__INT64_MAX__ * 2u + 1u)
#define __SCHAR_MAX__ __INT8_MAX__
#define __SHRT_MAX__ __INT16_MAX__
#define __INT_MAX__ __INT32_MAX__
#define __LONG_MAX__ __INT64_MAX__
#define __LONG_LONG_MAX__ __INT64_MAX__
#define __SIZE_MAX__ __UINT64_MAX__
#define __PTRDIFF_MAX__ __INT64_MAX__
#define __INTMAX_MAX__ __INT64_MAX__
#define __UINTMAX_MAX__ __UINT64_MAX__
#define __INTPTR_MAX__ __INT64_MAX__
#define __UINTPTR_MAX__ __UINT64_MAX__

#define __FLT_MIN_EXP__ (-125)
#define __FLT_MAX_EXP__ 128
#define __FLT_DIG__ 6
#define __FLT_DECIMAL_DIG__ 9
#define __FLT_MANT_DIG__ 24
#define __FLT_MIN__ 1.17549435082228750796873653722224568e-38F
#define __FLT_MAX__ 3.40282346638528859811704183484516925e+38F
#define __FLT_EPSILON__ 1.19209289550781250000000000000000000e-7F

#define __DBL_MIN_EXP__ (-1021)
#define __DBL_MAX_EXP__ 1024
#define __DBL_DIG__ 15
#define __DBL_DECIMAL_DIG__ 17
#define __DBL_MANT_DIG__ 53
#define __DBL_MAX__ ((double) 1.79769313486231570814527423731704357e+308L)
#define __DBL_MIN__ ((double) 2.22507385850720138309023271733240406e-308L)
#define __DBL_EPSILON__ ((double) 2.22044604925031308084726333618164062e-16L)

typedef unsigned short char16_t;
typedef unsigned int char32_t;

#define __gnu_linux__ 1
#define __linux 1
#define __linux__ 1
#define __unix 1
#define __unix__ 1
#define linux 1

void *alloca (unsigned long);
