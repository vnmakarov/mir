#include "mir.h"
#include "mir-gen.h"

MIR_module_t MIR_get_last_module (MIR_context_t ctx) {
  return DLIST_TAIL (MIR_module_t, *MIR_get_module_list (ctx));
}

static const char *ir_add
  = "m_add: module\n\
export add\n\
add: func i32, i32: a0, i32: a1\n\
local i64: r0\n\
add r0, a0, a1\n\
ret r0\n\
endfunc\n\
endmodule\n\
";

static const char *ir_main
  = "m_main: module\n\
import add\n\
proto_add: proto i32, i32: ax, i32: ay\n\
export main\n\
main: func i32\n\
local i64: r1\n\
inlay proto_add, add, r1, 3, 4\n\
ret r1\n\
endfunc\n\
endmodule\n\
";

int main (void) {
  MIR_context_t ctx = MIR_init ();
  MIR_gen_init (ctx);

  MIR_scan_string (ctx, ir_add);
  MIR_module_t m_add = MIR_get_last_module (ctx);
  MIR_load_module (ctx, m_add);

  MIR_scan_string (ctx, ir_main);
  MIR_module_t m_main = MIR_get_last_module (ctx);
  MIR_load_module (ctx, m_main);

  MIR_link (ctx, MIR_set_gen_interface, NULL);

  MIR_item_t main_func = DLIST_TAIL (MIR_item_t, m_main->items);
  typedef int (*main_t) (void);
  main_t f = (main_t) main_func->addr;
  int result = f ();

  MIR_gen_finish (ctx);
  MIR_finish (ctx);

  return result != 7;
}
