/* PR #452 (2): a statement-expression ending in x-- must materialize its
   value in value context. */
void g (int i) { (void) i; }
void f (int i) { while ( ({ i--; }) ) g (0); }
int main (void) { f (10); return 0; }
