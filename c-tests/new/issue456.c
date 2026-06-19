/* PR #456: mixed-class (SSE+INTEGER) struct varargs must not read a stale
   SSE slot -- each {double,long} struct after the first. */
#include <stdarg.h>
struct DL { double d; long i; };
static int check (int n, ...) {
  va_list ap; va_start (ap, n);
  double td = 0; long ti = 0;
  for (int k = 0; k < n; k++) { struct DL s = va_arg (ap, struct DL); td += s.d; ti += s.i; }
  va_end (ap);
  return (td == 6.0 && ti == 60) ? 0 : 1;
}
int main (void) {
  struct DL a = {1,10}, b = {2,20}, c = {3,30};
  return check (3, a, b, c);
}
