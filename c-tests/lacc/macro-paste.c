int puts (const char *);

#define FOO(s) s##_f##u##nc
#define STR(s) #s
#define CAT(a, b) STR (a##b)

int foo_func (void) { return puts (CAT (foo, 5)); }

#define glue(a, b) a##b
#define cat(a, b) glue (a, b)
#define HELLOWORLD "hello"
#define WORLD WORLD ", world"

int test (void) { return puts (glue (HELLO, WORLD)) + puts (cat (HELLO, WORLD)); }

int main (void) {
#if defined(__APPLE__) || defined(__WIN32) /* another puts return value meaning */
  return !(FOO (foo) () + test () >= 0);
#else
  return !(FOO (foo) () + test () == 24);
#endif
}
