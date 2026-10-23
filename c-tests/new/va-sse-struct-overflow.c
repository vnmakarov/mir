/* More all-SSE structs through varargs than there are XMM argument
   registers: the rest are in the overflow area, and va_arg must fetch them
   from there rather than past the end of the register save area. */
#include <stdarg.h>

typedef struct {
  double d, f;
} dd;

static double sum (int cnt, ...) {
  va_list ap;
  double ret = 0;

  va_start (ap, cnt);
  for (int i = 0; i < cnt; i++) {
    dd s = va_arg (ap, dd);
    ret += s.d + s.f;
  }
  va_end (ap);
  return ret;
}

int main (void) {
  dd s0 = {2, 3}, s1 = {5, 7}, s2 = {11, 13}, s3 = {17, 19}, s4 = {23, 29};
  dd s5 = {31, 37}, s6 = {41, 43}, s7 = {47, 53}, s8 = {59, 61}, s9 = {67, 71};
  return sum (10, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9) == 639 ? 0 : 1;
}
