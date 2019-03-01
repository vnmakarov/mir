#include "../mir.h"

#include "api-loop.h"
#include "api-memop.h"

int main (void) {
  MIR_module_t m;
  MIR_item_t func1, func2;
  
  MIR_init ();
  func1 = create_mir_func_with_loop (&m);
  func2 = create_mir_example2 (&m);
  MIR_simplify_func (func1);
  MIR_simplify_func (func2);
  fprintf (stderr, "Simplified code:\n");
  MIR_output (stderr);
  MIR_finish ();
  return 0;
}
