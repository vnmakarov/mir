#include <string.h>
#include "../mir.h"
#include "../mir-interp.h"
#include "../mir-gen.h"
#include "test-read.h"

int main (int argc, char *argv[]) {
  const char *mir_fname = NULL;
  MIR_module_t mir_module;
  MIR_item_t f, main_func;
  MIR_val_t val;
  int interpr_p, gen_p;
  int res;
  uint64_t (*fun_addr) (void);
  
  if (argc != 2 && argc != 3) {
    fprintf (stderr, "%s: [-i|-g] <input mir file>\n", argv[0]);
    exit (1);
  }
  interpr_p = gen_p = FALSE;
  if (strcmp (argv[1], "-i") == 0) {
    interpr_p = TRUE;
  } else if (strcmp (argv[1], "-g") == 0) {
    gen_p = TRUE;
  } else if (argc == 3) {
    fprintf (stderr, "%s: unknown option %s\n", argv[0], argv[1]);
    exit (1);
  }
  mir_fname = argv[argc - 1];
  MIR_init ();
  MIR_scan_string (read_file (mir_fname));
  mir_module = DLIST_HEAD (MIR_module_t, MIR_modules);
  if (DLIST_NEXT (MIR_module_t, mir_module) != NULL) {
    fprintf (stderr, "%s: there should be one module in the file %s\n", argv[0], mir_fname);
    exit (1);
  }
  if (! gen_p && ! interpr_p)
    MIR_output (stderr);
  main_func = NULL;
  for (f = DLIST_HEAD (MIR_item_t, mir_module->items); f != NULL; f =  DLIST_NEXT (MIR_item_t, f))
    if (f->item_type == MIR_func_item) {
      MIR_simplify_func (f, TRUE);
      if (strcmp (f->u.func->name, "main") == 0)
	main_func = f;
    }
  if (! gen_p && ! interpr_p) {
    fprintf (stderr, "+++++++++++++++++++After simplification:+++++++++++++++\n");
    MIR_output (stderr);
  }
  if (main_func == NULL) {
    fprintf (stderr, "%s: cannot execute program w/o main function\n", argv[0]);
    exit (1);
  }
  MIR_load_module (mir_module);
  MIR_load_external ("abort", abort);
  MIR_load_external ("exit", exit);
  MIR_load_external ("printf", printf);
  MIR_inline (main_func);
  if (! gen_p && ! interpr_p) {
    fprintf (stderr, "+++++++++++++++++++After inlining:+++++++++++++++\n");
    MIR_output (stderr);
  }
  if (interpr_p) {
    MIR_interp_init ();
    MIR_link (MIR_set_interp_interface);
    val = MIR_interp (main_func, 0);
    fprintf (stderr, "%s: %lu\n", mir_fname, val.i);
    MIR_interp_finish ();
  } else if (gen_p) {
    MIR_gen_init ();
#if MIR_GEN_DEBUG
    MIR_gen_set_debug_file (stderr);
#endif
    MIR_link (MIR_set_gen_interface);
    fun_addr = MIR_gen (main_func);
    res = fun_addr ();
    fprintf (stderr, "%s: %d\n", mir_fname, res);
    MIR_gen_finish ();
  }
  MIR_finish ();
  exit (0);
}
