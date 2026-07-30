extern int printf (const char *, ...);

__attribute__ ((always_inline)) static int add (int a, int b) { return a + b; }

static __attribute__ ((__always_inline__)) int mul (int a, int b) { return a * b; }

int main (void) {
  printf ("%d %d\n", add (3, 4), mul (5, 6));
  return 0;
}
