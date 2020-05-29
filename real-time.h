#include <sys/time.h>

static double __attribute__ ((unused)) real_sec_time (void) {
  struct timeval tv;

  gettimeofday (&tv, NULL);
  return tv.tv_usec / 1000000.0 + tv.tv_sec;
}

static double __attribute__ ((unused)) real_usec_time (void) {
  struct timeval tv;

  gettimeofday (&tv, NULL);
  return tv.tv_usec + tv.tv_sec * 1000000.0;
}
