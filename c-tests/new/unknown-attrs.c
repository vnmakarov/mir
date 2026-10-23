extern int printf (const char *, ...);
extern void abort (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__)) __attribute__ ((__cold__));
__attribute__((always_inline)) __attribute__((unused)) static int add (int a, int b) { return a + b; }
int main (void) {
  printf ("%d\n", add (3, 4));
  return 0;
}
