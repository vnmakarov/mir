#ifndef MIR_INTERP_H

#define MIR_INTERP_H

#include "mir.h"

typedef union {MIR_insn_code_t ic; void *a; int64_t i; uint64_t u; float f; double d;} MIR_val_t;

extern void MIR_interp_init (void);
extern MIR_val_t MIR_interp (MIR_item_t func_item, size_t nargs, ...);
extern MIR_val_t MIR_interp_arr (MIR_item_t func_item, size_t nargs, MIR_val_t *vals);
extern void MIR_interp_finish (void);
extern void MIR_set_C_interp_interface (MIR_item_t func_item);

#endif /* #ifndef MIR_INTERP_H */
