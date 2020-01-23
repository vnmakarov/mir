#include <stdio.h>
#include "../mir-gen.h"
#include "test-read.h"

int main (int argc, char *argv[]) {
  MIR_item_t func;
  MIR_module_t m;
  MIR_context_t ctx;
  char *str;

  if (argc != 2) {
    fprintf (stderr, "Usage: %s <mir file name>\n", argv[0]);
    exit (1);
  }
  ctx = MIR_init ();
  str = read_file (argv[1]);
  MIR_scan_string (ctx, str);
  m = DLIST_TAIL (MIR_module_t, *MIR_get_module_list (ctx));
  func = DLIST_TAIL (MIR_item_t, m->items);
  MIR_load_module (ctx, m);
  MIR_link (ctx, NULL, NULL);
  MIR_gen_init (ctx);
#if MIR_GEN_DEBUG
  fprintf (stderr, "\n==============================%s============================\n", argv[1]);
  MIR_gen_set_debug_file (ctx, stderr);
#endif
  MIR_gen (ctx, func);
  MIR_gen_finish (ctx);
  MIR_finish (ctx);
  free (str);
  exit (0);
}
