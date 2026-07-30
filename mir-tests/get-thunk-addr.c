#include "../mir-gen.h"
#include "scan-sieve.h"

#include <inttypes.h>

int main (void) {
  MIR_context_t ctx;
  MIR_module_t m;
  MIR_item_t func;
  uint64_t (*fun) (void);
  uint64_t res;
  ctx = MIR_init ();
  func = create_mir_func_sieve (ctx, NULL, &m);
  MIR_load_module (ctx, func->module);
  MIR_gen_init (ctx);
  MIR_link (ctx, MIR_set_gen_interface, NULL);
  fun = MIR_gen (ctx, func);
  fun = _MIR_get_thunk_addr (ctx, fun);
  res = fun ();
  fprintf (stderr, "sieve () -> %ld\n", (long) res);
  MIR_gen_finish (ctx);
  MIR_finish (ctx);
  return 0;
}
