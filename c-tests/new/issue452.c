/* PR #452 (1): a struct statement-expression value must have independent
   storage, not a reused stack slot. */
struct large { int x, y[9]; };
int main (void) {
  int d = ({ struct large t; t.x = 2; t; }).x
        - ({ struct large t; t.x = 1; t; }).x;
  return d == 1 ? 0 : 1;
}
