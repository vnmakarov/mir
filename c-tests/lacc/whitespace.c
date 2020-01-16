int puts(const char *);
void abort (void);
 /* form feed, 0x0c */

int main(void) {
#ifdef __APPLE__
  return !(puts("Hello") >= 0);
#else
  return !(puts("Hello") == 6);
#endif
}
