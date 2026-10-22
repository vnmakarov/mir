/* A va_list field read before and after va_arg must be loaded again: the
   va_* insns update the va_list in memory, so GVN may not reuse a value
   loaded, or forward one stored, before them. */
#include <stdarg.h>

#if defined(__aarch64__) && !defined(__APPLE__)
#define OFFS_WORD 6 /* int __gr_offs, at byte 24 */
#elif defined(__x86_64__) && !defined(_WIN32)
#define OFFS_WORD 0 /* unsigned gp_offset */
#endif

#ifdef OFFS_WORD
static int f (int n, ...) {
  va_list ap;
  int *w, before, after, a, b;

  va_start (ap, n);
  w = (int *) (void *) &ap;
  before = w[OFFS_WORD];
  a = va_arg (ap, int);
  after = w[OFFS_WORD];
  w[OFFS_WORD] = before; /* rewind: the next va_arg reads the same int again */
  b = va_arg (ap, int);
  va_end (ap);
  return before != after && a == 42 && b == 42 && w[OFFS_WORD] == after;
}
#endif

int main (void) {
#ifdef OFFS_WORD
  return f (1, 42, 7) ? 0 : 1;
#else
  return 0;
#endif
}
