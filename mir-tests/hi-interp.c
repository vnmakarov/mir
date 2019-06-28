#include "../mir-interp.h"
#include "scan-hi.h"

static int32_t print (int32_t c) {
  fputc (c, stderr);
  return 1;
}

int main (void) {
  MIR_module_t m;
  MIR_item_t func;
  MIR_val_t val;
    
  MIR_init ();
  MIR_load_external ("print", print);
  m = create_hi_module ();
  func = DLIST_TAIL (MIR_item_t, m->items);
#if MIR_INTERP_DEBUG 
  fprintf (stderr, "\n++++++ Hi func before simplification:\n");
  MIR_output (stderr);
#endif
  MIR_simplify_func (func, TRUE);
#if MIR_INTERP_DEBUG 
  fprintf (stderr, "++++++ Hi func after simplification:\n");
  MIR_output (stderr);
#endif
  MIR_load_module (m);
  MIR_link (MIR_set_interp_interface, NULL);
  MIR_interp_init ();
  MIR_interp (func, &val, 0);
  fprintf (stderr, "func hi returns %ld\n", (long) val.i);
  MIR_interp_finish ();
  MIR_finish ();
  return 0;
}
