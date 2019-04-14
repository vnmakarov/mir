/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_GEN_H

#define MIR_GEN_H

#include "mir.h"

#ifndef MIR_GEN_DEBUG
#define MIR_GEN_DEBUG 0
#endif

extern void MIR_gen_init (void);
#if MIR_GEN_DEBUG
extern void MIR_gen_set_debug_file (FILE *f);
#endif
extern void *MIR_gen (MIR_item_t func_item);
extern void MIR_gen_finish (void);


#endif /* #ifndef MIR_GEN_H */
