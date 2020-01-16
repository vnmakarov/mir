/* This file is a part of MIR project.
   Copyright (C) 2019-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* See C11 7.19 */
#ifndef __STDDEF_H
#define __STDDEF_H

typedef long ptrdiff_t;
typedef unsigned long size_t;
typedef long double max_align_t;
#ifdef __APPLE__
typedef int wchar_t;
#else
typedef unsigned int wchar_t;
#endif

#ifndef __APPLE__
#define NULL ((void *) 0)
#endif

#define offsetof(type, member_designator) ((size_t) & ((type *) 0)->member_designator)

#endif /* #ifndef __STDDEF_H */
