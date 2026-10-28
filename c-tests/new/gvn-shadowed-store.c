/* An int is read, then a BB stores through a char pointer and a long
   pointer, then the int is read again.  The char store (alias set 0) may
   alias the int, so the second read must load again, although the long
   store that follows it in the BB does not alias the int.  */
int g;
long h;

int f (int *p, char *c, long *q, int k) {
  int a = *p;
  if (k) a += 1;
  *c = 7;
  *q = 2;
  if (k > 1) a += 2;
  return a + *p;
}

int main (void) {
  g = 0x01010100;
  int r = f (&g, (char *) &g, &h, 1);
  return (r != 0x01010101 + 0x01010107) + 2 * (g != 0x01010107);
}
