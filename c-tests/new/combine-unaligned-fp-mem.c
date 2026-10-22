/* Combining an address computation into a floating-point load/store must
   not produce an offset the target can't encode (aarch64's scaled FP
   load/store offsets must be multiples of the access size). */
#include <string.h>

static void put (char *buf, float f, double d) {
  *(float *) (buf + 2) = f; /* misaligned, as in a packed struct */
  *(double *) (buf + 7) = d;
}

static double get (char *buf) { return *(float *) (buf + 2) + *(double *) (buf + 7); }

int main (void) {
  union {
    double align;
    char b[32];
  } u;

  memset (&u, 0, sizeof (u));
  put (u.b, 1.5f, 2.25);
  return get (u.b) == 3.75 ? 0 : 1;
}
