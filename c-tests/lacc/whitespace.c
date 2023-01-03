int puts (const char *);
void abort (void);
/* form feed, 0x0c */
#define puts(s) printf ("%s\n", s)
int main (void) {
  return !(puts ("Hello") == 6);
}
