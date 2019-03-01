#include "../mir.h"

#include "scan-sieve.h"

int main (void) {
  FILE *f;
  const char *fname = "/tmp/__tmp.mirb";
  
  MIR_init ();
  create_mir_func_sieve (NULL, NULL);
  MIR_output (stderr);
  f = fopen (fname, "wb");
  mir_assert (f != NULL);
  MIR_write (f);
  fclose (f);
  f = fopen (fname, "rb");
  mir_assert (f != NULL);
  MIR_read (f);
  fclose (f);
  fprintf (stderr, "+++++++++++++After reading:\n");
  MIR_output (stderr);
  remove (fname);
  MIR_finish ();
  return 0;
}
