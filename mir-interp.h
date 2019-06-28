/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_INTERP_H

#define MIR_INTERP_H

#include "mir.h"

typedef union {
  MIR_insn_code_t ic;
  void *a;
  int64_t i;
  uint64_t u;
  float f;
  double d;
  long double ld;
} MIR_val_t;

extern void MIR_interp_init (void);
extern void MIR_interp (MIR_item_t func_item, MIR_val_t *results, size_t nargs, ...);
extern void MIR_interp_arr (MIR_item_t func_item, MIR_val_t *results, size_t nargs, MIR_val_t *vals);
extern void MIR_interp_arr_varg (MIR_item_t func_item, MIR_val_t *results, size_t nargs, MIR_val_t *vals, va_list va);
extern void MIR_interp_finish (void);
extern void MIR_set_interp_interface (MIR_item_t func_item);

#endif /* #ifndef MIR_INTERP_H */
