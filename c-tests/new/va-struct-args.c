/* Named struct parameters before the ellipsis must not break va_arg.
   On x86-64 va_start used to recompute the named args' layout instead of
   using the machinize walk's state: register-passed blocks were neither
   counted into gp_offset/fp_offset nor excluded from the overflow area,
   and memory-passed blocks were counted without 8-byte rounding. */
#include <stdarg.h>

struct IS {
  long a;
};                          /* 1 GPR */
struct FS {
  double d;
};                          /* 1 XMM */
struct MS {
  char c[17];
};                          /* memory, size not a multiple of 8 */

static int reg_int_structs (struct IS s1, struct IS s2, int z, ...) {
  va_list ap;
  va_start (ap, z);
  int v = va_arg (ap, int);
  va_end (ap);
  return v;
}

static double reg_fp_structs (struct FS f1, struct FS f2, double z, ...) {
  va_list ap;
  va_start (ap, z);
  double v = va_arg (ap, double);
  va_end (ap);
  return v;
}

static int mem_structs (struct MS m1, struct MS m2, struct MS m3, struct MS m4, struct MS m5,
                        struct MS m6, struct MS m7, int g1, int g2, int g3, int g4, int g5,
                        int g6, ...) {
  /* All GPRs consumed by g1..g6: the vararg comes from the overflow area,
     right after the seven 24-byte-rounded structs. */
  va_list ap;
  va_start (ap, g6);
  int v = va_arg (ap, int);
  va_end (ap);
  return v;
}

int main (void) {
  struct IS s1 = {111}, s2 = {222};
  struct FS f1 = {1.5}, f2 = {2.5};
  struct MS m = {{0}};

  if (reg_int_structs (s1, s2, 3, 42) != 42) return 1;
  if (reg_fp_structs (f1, f2, 3.0, 43.0) != 43.0) return 2;
  if (mem_structs (m, m, m, m, m, m, m, 1, 2, 3, 4, 5, 6, 44) != 44) return 3;
  return 0;
}
