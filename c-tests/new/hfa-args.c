/* Homogeneous floating-point aggregates (structs of 1-4 floats, doubles or
   long doubles) passed and returned by value: in FP registers while they
   last, then on the stack, and through varargs.  On aarch64 these use the
   HFA block types (MIR_T_BLK + 1..3); elsewhere the target's own rules. */
#include <stdarg.h>

typedef struct { float a; } f1;
typedef struct { float a, b; } f2;
typedef struct { float a[3]; } f3;
typedef struct { float a, b, c, d; } f4;
typedef struct { double a; } d1;
typedef struct { double a, b; } d2;
typedef struct { double a[3]; } d3;
typedef struct { double a, b, c, d; } d4;
typedef struct { long double a, b; } q2;
typedef struct { struct { float x, y; } p; float z; } nf3;
typedef union { float f; float g[2]; } uf2;

#define MK(T, n, v0) static T mk_##T (double s) { T r; float *pf; double *pd; long double *pq; \
  (void) pf; (void) pd; (void) pq; v0; return r; }
MK (f1, 1, r.a = s)
MK (f2, 2, (r.a = s, r.b = s + 1))
MK (f3, 3, (r.a[0] = s, r.a[1] = s + 1, r.a[2] = s + 2))
MK (f4, 4, (r.a = s, r.b = s + 1, r.c = s + 2, r.d = s + 3))
MK (d1, 1, r.a = s)
MK (d2, 2, (r.a = s, r.b = s + 1))
MK (d3, 3, (r.a[0] = s, r.a[1] = s + 1, r.a[2] = s + 2))
MK (d4, 4, (r.a = s, r.b = s + 1, r.c = s + 2, r.d = s + 3))
MK (q2, 2, (r.a = s, r.b = s + 1))
MK (nf3, 3, (r.p.x = s, r.p.y = s + 1, r.z = s + 2))
MK (uf2, 2, (r.g[0] = s, r.g[1] = s + 1))

static double sum_f1 (f1 v) { return v.a; }
static double sum_f2 (f2 v) { return v.a + v.b; }
static double sum_f3 (f3 v) { return v.a[0] + v.a[1] + v.a[2]; }
static double sum_f4 (f4 v) { return v.a + v.b + v.c + v.d; }
static double sum_d1 (d1 v) { return v.a; }
static double sum_d2 (d2 v) { return v.a + v.b; }
static double sum_d3 (d3 v) { return v.a[0] + v.a[1] + v.a[2]; }
static double sum_d4 (d4 v) { return v.a + v.b + v.c + v.d; }
static double sum_q2 (q2 v) { return v.a + v.b; }
static double sum_nf3 (nf3 v) { return v.p.x + v.p.y + v.z; }
static double sum_uf2 (uf2 v) { return v.g[0] + v.g[1]; }

/* expected sum of mk_T (s) with n members: n*s + n*(n-1)/2 */
#define EXP(n, s) ((n) * (s) + (n) * ((n) -1) / 2)

/* Two of them after 6 doubles: the first fits in the FP registers only for
   1-2 members, the second goes to the stack - and the trailing double after
   them must go to the stack too. */
#define MANY(T) \
  static double many_##T (double x0, double x1, double x2, double x3, double x4, double x5, \
                          T v, int i, T w, double x6) { \
    return x0 + x1 + x2 + x3 + x4 + x5 + sum_##T (v) + i + sum_##T (w) + x6; \
  }
MANY (f1) MANY (f2) MANY (f3) MANY (f4) MANY (d1) MANY (d2) MANY (d3) MANY (d4) MANY (q2)
MANY (nf3) MANY (uf2)

#define VA(T) \
  static double va_##T (int n, ...) { \
    va_list ap; \
    double r = 0; \
    va_start (ap, n); \
    for (int k = 0; k < n; k++) r += sum_##T (va_arg (ap, T)) + va_arg (ap, double); \
    va_end (ap); \
    return r; \
  }
VA (f1) VA (f2) VA (f3) VA (f4) VA (d1) VA (d2) VA (d3) VA (d4) VA (q2) VA (nf3) VA (uf2)

static int fails;
#define CHECK(T, n) \
  do { \
    if (sum_##T (mk_##T (3)) != EXP (n, 3)) fails |= 1; \
    if (many_##T (1, 2, 3, 4, 5, 6, mk_##T (10), 7, mk_##T (20), 8) \
        != 36 + EXP (n, 10) + EXP (n, 20)) \
      fails |= 2; \
    if (va_##T (5, mk_##T (1), 0.5, mk_##T (2), 0.5, mk_##T (3), 0.5, mk_##T (4), 0.5, mk_##T (5), \
                0.5) \
        != EXP (n, 1) + EXP (n, 2) + EXP (n, 3) + EXP (n, 4) + EXP (n, 5) + 2.5) \
      fails |= 4; \
  } while (0)

int main (void) {
  CHECK (f1, 1);
  CHECK (f2, 2);
  CHECK (f3, 3);
  CHECK (f4, 4);
  CHECK (d1, 1);
  CHECK (d2, 2);
  CHECK (d3, 3);
  CHECK (d4, 4);
  CHECK (q2, 2);
  CHECK (nf3, 3);
  CHECK (uf2, 2);
  return fails;
}
