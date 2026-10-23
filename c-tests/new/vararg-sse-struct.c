/* x86-64: structs of floating-point members passed to a host (natively
   compiled) variadic function travel in XMM registers, and %al must count
   them, or the callee's prologue may skip saving the XMM argument registers
   that va_arg then reads. (Other targets: c2mir doesn't pass such structs
   to host varargs per their ABIs - e.g. aarch64 HFAs - so not tested.) */
#include <stdio.h>
#include <string.h>

typedef struct {
  double d;
} sd;
typedef struct {
  double a, b;
} sdd;

int main (void) {
#if defined(__x86_64__) && !defined(_WIN32)
  char buf[128];
  sd x = {1.5}, y = {-2.25};
  sdd z = {3.125, 4.0};

  snprintf (buf, sizeof (buf), "%g %g %g %g", x, y, z);
  if (strcmp (buf, "1.5 -2.25 3.125 4") != 0) {
    printf ("got \"%s\"\n", buf);
    return 1;
  }
#endif
  return 0;
}
