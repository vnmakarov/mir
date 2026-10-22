/* Reading an uninitialized narrow auto local must yield a value within the
   type's range: the backing reg may hold stale full-width garbage, so
   without an extension at the declaration `x / 1000` can leave char range
   (cf. gcc.c-torture execute/pr34099-2.c). */

volatile int big_div = 1000;

static long dirty (long a, long b) {
  long v[8];
  for (int i = 0; i < 8; i++) v[i] = a * b + i + 0x7f00ff00abcdL;
  return v[7];
}

static int fchar (void) {
  char x;
  return x / big_div;
}

static int fschar (void) {
  signed char x;
  return x / big_div;
}

static int fuchar (void) {
  unsigned char x;
  return x / big_div;
}

static int fshort (void) {
  short x;
  return x / (big_div * 100);
}

static int fushort (void) {
  unsigned short x;
  return x / (big_div * 100);
}

int main (void) {
  dirty (0x12345678L, 0x9abcdef0L);
  if (fchar () != 0) return 1;
  dirty (0x76543210L, 0x0fedcba9L);
  if (fschar () != 0) return 2;
  dirty (0x55aa55aaL, 0xaa55aa55L);
  if (fuchar () != 0) return 3;
  dirty (0x12345678L, 0x9abcdef0L);
  if (fshort () != 0) return 4;
  dirty (0x76543210L, 0x0fedcba9L);
  if (fushort () != 0) return 5;
  return 0;
}
