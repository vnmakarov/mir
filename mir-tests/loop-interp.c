#include "../mir-interp.h"
#include "api-loop.h"
#include "real-time.h"

#include <inttypes.h>

int main (void) {
  MIR_module_t m;
  MIR_item_t func;
  MIR_val_t val;
  double start_time;
  const int64_t n_iter = 1000000000;
    
  MIR_init ();
  func = create_mir_func_with_loop (&m);
#if MIR_INTERP_DEBUG 
  fprintf (stderr, "++++++ Loop before simplification:\n");
  MIR_output (stderr);
#endif
  MIR_simplify_func (func, TRUE);
#if MIR_INTERP_DEBUG 
  fprintf (stderr, "++++++ Loop after simplification:\n");
  MIR_output (stderr);
#endif
  MIR_load_module (m);
  MIR_link ();
  MIR_interp_init ();
  start_time = real_sec_time ();
  val.i = n_iter;
#if MIR_C_INTERFACE
  typedef int64_t (*loop_func) (int64_t);
  MIR_set_C_interp_interface (func);
  int64_t res = ((loop_func) func->addr) (n_iter);
  fprintf (stderr, "C interface test (%"PRId64 ") -> %"PRId64 ": %.3f sec\n", n_iter, res, real_sec_time () - start_time);
#else
  val = MIR_interp (func, 1, val);
  fprintf (stderr, "test (%"PRId64 ") -> %"PRId64 ": %.3f sec\n", n_iter, val.i, real_sec_time () - start_time);
#endif
  MIR_interp_finish ();
  MIR_finish ();
  return 0;
}
