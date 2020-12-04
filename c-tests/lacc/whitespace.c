int puts (const char *);
void abort (void);
/* form feed, 0x0c */

int main (void) {
#if defined(__APPLE__) || defined(_WIN32) /* different puts return meaning */
  return !(puts ("Hello") >= 0);
#else
  return !(puts ("Hello") == 6);
#endif
}
