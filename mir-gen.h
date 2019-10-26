/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_GEN_H

#define MIR_GEN_H

#include "mir.h"

#ifndef MIR_GEN_DEBUG
#define MIR_GEN_DEBUG 0
#endif

extern void MIR_gen_init (MIR_context_t context);
extern void MIR_gen_set_debug_file (MIR_context_t context, FILE *f);
extern void *MIR_gen (MIR_context_t context, MIR_item_t func_item);
extern void MIR_set_gen_interface (MIR_context_t context, MIR_item_t func_item);
extern void MIR_set_lazy_gen_interface (MIR_context_t context, MIR_item_t func_item);
extern void MIR_gen_finish (MIR_context_t context);

#endif /* #ifndef MIR_GEN_H */
