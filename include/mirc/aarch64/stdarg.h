/* This file is a part of MIR project.
   Copyright (C) 2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef __STDARG_H
#define __STDARG_H

typedef struct {
  void *__stack;
  void *__gr_top;
  void *__vr_top;
  int __gr_offs;
  int __vr_offs;
} va_list;

#define va_start(ap, param) __builtin_va_start (ap)
#define va_arg(ap, type) __builtin_va_arg(ap, (type *) 0)
#define va_end(ap) 0
#define va_copy(dest, src) ((dest)[0] = (src)[0])

/* For standard headers of a GNU system: */
#ifndef __GNUC_VA_LIST
#define __GNUC_VA_LIST 1
#endif
typedef va_list __gnuc_va_list;
#endif /* #ifndef __STDARG_H */
