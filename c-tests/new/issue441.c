/* PR #441: a struct/union va_arg used directly as an rvalue must get real
   storage (it was written to NULL), and two va_block_arg insns must not be
   CSE'd by GVN (op 0 is an input address, not a def). */
#include <stdarg.h>
struct S { char c[999]; };
static int f (int i, ...) {
  va_list ap;
  va_start (ap, i);
  int a = va_arg (ap, struct S).c[0];
  int b = va_arg (ap, struct S).c[1];
  va_end (ap);
  return a + b;
}
int main (void) {
  struct S s = {{21, 21}};
  return f (1, s, s) == 42 ? 0 : 1;
}
