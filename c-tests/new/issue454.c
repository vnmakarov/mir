/* PR #454: out-of-SSA lost-copy hazard for a self-loop block -- the
   condition must see this iteration's value, not the next. */
extern void abort (void);
int main (void) {
  int n = 0, i = 5;
  while (i-- > 0) n++;
  return n == 5 ? 0 : 1;
}
