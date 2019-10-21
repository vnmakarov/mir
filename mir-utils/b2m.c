/* Transform mir binary form from stdin into mir text to stdout.  */

#include "mir.h"
int main (int argc, char *argv[]) {
  MIR_context_t ctx = MIR_init ();

  if (argc != 1) {
    fprintf (stderr, "Usage: %s < mir-binary-file  > mir-text-file\n", argv[1]);
    return 1;
  }
  MIR_read (ctx, stdin);
  MIR_output (ctx, stdout);
  MIR_finish (ctx);
  return 0;
}
