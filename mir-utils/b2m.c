/* Transform mir binary form from stdin into mir text to stdout.  */

#include "mir.h"

#ifdef _WIN32
/* <stdio.h> provides _fileno */
#include <fcntl.h> /* provides _O_BINARY */
#include <io.h>    /* provides _setmode */
#endif

int main (int argc, char *argv[]) {
  MIR_context_t ctx = MIR_init ();

#ifdef _WIN32
  if (_setmode (_fileno (stdin), _O_BINARY) == -1) return 1;
#endif

  if (argc != 1) {
    fprintf (stderr, "Usage: %s < mir-binary-file  > mir-text-file\n", argv[1]);
    return 1;
  }
  MIR_read (ctx, stdin);
  MIR_output (ctx, stdout);
  MIR_finish (ctx);
  return 0;
}
