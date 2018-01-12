#ifndef MIR_INTERP_H

#define MIR_INTERP_H

#include "mir.h"

typedef union {MIR_insn_code_t ic; void *a; int64_t i; uint64_t u; float f; double d;} MIR_val_t;

extern void MIR_interp_init (void);
extern MIR_val_t MIR_interp (MIR_item_t func_item, void (*resolver) (const char *name), size_t nargs, ...);
extern void MIR_interp_finish (void);


#endif /* #ifndef MIR_INTERP_H */
