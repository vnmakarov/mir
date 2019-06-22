#include <stdio.h>
#include "../mir-gen.h"
#include "test-read.h"

int main (int argc, char *argv[]) {
  MIR_item_t func;
  MIR_module_t m;

  if (argc != 2) {
    fprintf (stderr, "Usage: %s <mir file name>\n", argv[0]);
    exit (1);
  }
  MIR_init ();
  MIR_scan_string (read_file (argv[1]));
  m = DLIST_TAIL (MIR_module_t, MIR_modules);
  func = DLIST_TAIL (MIR_item_t, m->items);
  MIR_load_module (m);
  MIR_link (NULL, NULL);
  MIR_gen_init ();
#if MIR_GEN_DEBUG
  fprintf (stderr, "\n==============================%s============================\n", argv[1]);
  MIR_gen_set_debug_file (stderr);
#endif
  MIR_gen (func);
  MIR_gen_finish ();
  MIR_finish ();
  exit (0);
}
