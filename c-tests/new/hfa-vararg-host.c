/* aarch64: homogeneous floating-point aggregates passed to a host (natively
   compiled) variadic function go in FP registers like named ones (Linux), or
   by value on the stack (Apple), where the callee's va_arg finds them. */
#include <stdio.h>
#include <string.h>

typedef struct {
  double d;
} d1;
typedef struct {
  double a, b;
} d2;
typedef struct {
  double a, b, c, d;
} d4;

int main (void) {
#if defined(__aarch64__)
  char buf[256];
  d1 x = {1.5}, y = {-2.25};
  d2 z = {3.125, 4.0};
  d4 w = {5, 6, 7, 8};

  /* the last d4 no longer fits in v0-v7 and goes to the stack */
  snprintf (buf, sizeof (buf), "%g %g %g %g %g %g %g %g %g %g %g %g", x, y, z, w, w);
  if (strcmp (buf, "1.5 -2.25 3.125 4 5 6 7 8 5 6 7 8") != 0) {
    printf ("got \"%s\"\n", buf);
    return 1;
  }
#endif
  return 0;
}
