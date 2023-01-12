/* This file is a part of MIR project.
   Copyright (C) 2018-2023 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_GEN_H

#define MIR_GEN_H

#include "mir.h"

#ifndef MIR_NO_GEN_DEBUG
#define MIR_NO_GEN_DEBUG 0
#endif

#ifdef __cplusplus
extern "C" {
#endif

extern void MIR_gen_init (MIR_context_t ctx, int gens_num);
extern void MIR_gen_set_debug_file (MIR_context_t ctx, int gen_num, FILE *f);
extern void MIR_gen_set_debug_level (MIR_context_t ctx, int gen_num, int debug_level);
extern void MIR_gen_set_optimize_level (MIR_context_t ctx, int gen_num, unsigned int level);
extern void *MIR_gen (MIR_context_t ctx, int gen_num, MIR_item_t func_item);
extern void MIR_set_gen_interface (MIR_context_t ctx, MIR_item_t func_item);
extern void MIR_set_parallel_gen_interface (MIR_context_t ctx, MIR_item_t func_item);
extern void MIR_set_lazy_gen_interface (MIR_context_t ctx, MIR_item_t func_item);
extern void MIR_gen_finish (MIR_context_t ctx);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef MIR_GEN_H */
