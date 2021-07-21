typedef struct Boo {
  float x;
} Boo;

typedef struct Foo {
  Boo data[4];
} Foo;

void abort (void);
int main () {
  Foo foo = (Foo){.data[1] = {1}};
  Foo foo2 = (Foo){.data[1] = {1}, {2}};
  if (foo.data[1].x != 1 || foo2.data[1].x != 1 || foo2.data[2].x != 2) abort ();
  return 0;
}
