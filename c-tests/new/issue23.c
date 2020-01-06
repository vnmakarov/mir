#include <stdio.h>
#include <math.h>
int main (void) {
  printf ("%lf\n", NAN);
  printf ("%lf\n", INFINITY);
  printf ("%lf\n", HUGE_VAL);
  printf ("%f\n", HUGE_VALF);
  printf ("%Lf\n", HUGE_VALL);
  return 0;
}
