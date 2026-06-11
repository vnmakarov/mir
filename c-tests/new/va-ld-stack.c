/* Long double passed on the stack: with binary128 long double (e.g.
   aarch64), FP args past the 8 v-registers go to the stack 16-aligned.
   Exercises va_arg_builtin (varargs) and the ff interface (fixed args)
   stack paths, which used "% 16" where round-up-to-16 was intended.  */
#include <stdarg.h>

long double vsum (int n, ...) {
  va_list ap;
  long double s = 0;

  va_start (ap, n);
  while (n--) s += va_arg (ap, long double);
  va_end (ap);
  return s;
}

long double fsum (long double a1, long double a2, long double a3, long double a4, long double a5,
                  long double a6, long double a7, long double a8, long double a9,
                  long double a10) {
  return a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10;
}

int main (void) {
  if (vsum (9, 1.L, 2.L, 3.L, 4.L, 5.L, 6.L, 7.L, 8.L, 9.L) != 45.L) return 1;
  if (fsum (1.L, 2.L, 3.L, 4.L, 5.L, 6.L, 7.L, 8.L, 9.L, 10.L) != 55.L) return 2;
  return 0;
}
