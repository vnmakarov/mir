/* Transform mir textual form from stdin into mir binary to
   stdout.  */

#include "mir.h"

#ifdef _WIN32
/* <stdio.h> provides _fileno */
#include <fcntl.h> /* provides _O_BINARY */
#include <io.h>    /* provides _setmode */
#endif

DEF_VARR (char);

int main (int argc, char *argv[]) {
  MIR_context_t ctx = MIR_init ();
  VARR (char) * str;
  int c;

#ifdef _WIN32
  if (_setmode (_fileno (stdout), _O_BINARY) == -1) return 1;
#endif

  if (argc != 1) {
    fprintf (stderr, "Usage: %s < mir-text-file > mir-binary-file\n", argv[1]);
    return 1;
  }
  VARR_CREATE (char, str, 1024 * 1024);
  while ((c = getchar ()) != EOF) VARR_PUSH (char, str, c);
  VARR_PUSH (char, str, 0);
  MIR_scan_string (ctx, VARR_ADDR (char, str));
  MIR_write (ctx, stdout);
  MIR_finish (ctx);
  VARR_DESTROY (char, str);
  return 0;
}
