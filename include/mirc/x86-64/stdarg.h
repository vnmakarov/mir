/* See C11 7.16 and https://www.uclibc.org/docs/psABI-x86_64.pdf */
#ifndef __STDARG_H
#define __STDARG_H

typedef struct {
  unsigned int gp_offset;
  unsigned int fp_offset;
  void *overflow_arg_area;
  void *reg_save_area;
} va_list[1];

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
