#include <stdio.h>
#include "../mir-gen.h"

static char *read_file (const char *name) {
  FILE *f;
  size_t len;
  char *str;
  
  if ((f = fopen (name, "r")) == NULL) {
    perror (name);
    exit (1);
  }
  fseek (f, 0, SEEK_END);
  len = ftell (f);
  rewind (f);
  str = (char *) malloc (len + 1);
  if (fread (str, 1, len, f) != len) {
    fprintf (stderr, "file %s was changed\n", name);
    exit (1);
  }
  str[len] = 0;
  return str;
}

void main (int argc, char *argv[]) {
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
