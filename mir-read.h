#ifndef MIR_READ_H
#define MIR_READ_H

#include "mir.h"

typedef void (*MIR_read_error_func_t) (MIR_error_type_t error_type, const char *message);

extern void MIR_read_init (void);
extern void MIR_read_finish (void);

extern MIR_read_error_func_t MIR_get_read_error_func (void);
extern void MIR_set_read_error_func (MIR_read_error_func_t func);

extern MIR_item_t MIR_read_string (const char *str);

#endif /* #ifndef MIR_READ_H */
