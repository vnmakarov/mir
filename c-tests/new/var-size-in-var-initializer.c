void *xmalloc (int size);
static int *f (void) {
  int *new_pair = xmalloc (sizeof (*new_pair));
  return new_pair;
}
int main (void) { return 0; }
