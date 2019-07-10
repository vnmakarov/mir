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

/* Some GCC predefined macros: */
#define __INT8_MAX__      127
#define __INT16_MAX__     32767
#define __INT32_MAX__     2147483647
#define __INT64_MAX__     9223372036854775807l
#define __UINT8_MAX__     (__INT8_MAX__ * 2u + 1u)
#define __UINT16_MAX__    (__INT16_MAX__ * 2u + 1u)
#define __UINT32_MAX__    (__INT32_MAX__ * 2u + 1u)
#define __UINT64_MAX__    (__INT64_MAX__ * 2u + 1u)
#define __SCHAR_MAX__     __INT8_MAX__
#define __SHRT_MAX__      __INT16_MAX__
#define __INT_MAX__       __INT32_MAX__
#define __LONG_MAX__      __INT64_MAX__
#define __LONG_LONG_MAX__ __INT64_MAX__
#define __SIZE_MAX__      __UINT64_MAX__
#define __PTRDIFF_MAX__   __INT64_MAX__
#define __INTMAX_MAX__    __INT64_MAX__
#define __UINTMAX_MAX__   __UINT64_MAX__
#define __INTPTR_MAX__    __INT64_MAX__
#define __UINTPTR_MAX__   __UINT64_MAX__

typedef unsigned short char16_t;
typedef unsigned int char32_t;

#define __gnu_linux__ 1
#define __linux 1
#define __linux__ 1
#define __unix 1
#define __unix__ 1
#define linux 1
