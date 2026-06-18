/* PR #450: a zero-length array member must sit at the running offset,
   not 0 (which would alias the preceding member). */
struct S { unsigned char n[1]; char a[0]; };
int main (void) {
  struct S s;
  return ((char *) s.a - (char *) &s) == 1 ? 0 : 1;
}
