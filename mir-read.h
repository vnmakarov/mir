#ifndef MIR_READ_H
#define MIR_READ_H

#include "mir.h"

extern void MIR_read_init (void);
extern void MIR_read_finish (void);

extern MIR_item_t MIR_read_string (const char *str);

#endif /* #ifndef MIR_READ_H */
