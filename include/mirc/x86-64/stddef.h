/* See C11 7.19 */
#ifndef __STDDEF_H
#define __STDDEF_H

typedef long ptrdiff_t;
typedef unsigned long size_t;
typedef long double max_align_t;
typedef unsigned int wchar_t;

#define NULL ((void *)0)
#define offsetof(type, member_designator) ((size_t) & ((type *) 0)->member_designator)

#endif /* #ifndef __STDDEF_H */
