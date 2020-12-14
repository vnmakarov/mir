#include <stdio.h>
#include "mir-reduce.h"
#include "mir-varr.h"
#include "real-time.h"

DEF_VARR (uint8_t);
static VARR (uint8_t) * orig, *buf1, *buf2;

static FILE *input_file;
static size_t input_length1 = 0;
static size_t reader1 (void *start, size_t len, void *aux_data) {
  size_t n = fread (start, 1, len, input_file);

  for (size_t i = 0; i < n; i++) VARR_PUSH (uint8_t, orig, ((uint8_t *) start)[i]);
  input_length1 += n;
  return n;
}

static size_t output_length1 = 0;
static size_t writer1 (const void *start, size_t len, void *aux_data) {
  output_length1 += len;
  for (size_t i = 0; i < len; i++) VARR_PUSH (uint8_t, buf1, ((uint8_t *) start)[i]);
  return len;
}

static size_t size_min (size_t a, size_t b) { return a < b ? a : b; }

static size_t input_length2 = 0;
static size_t reader2 (void *start, size_t len, void *aux_data) {
  size_t s = size_min (len, VARR_LENGTH (uint8_t, buf1) - input_length2);

  for (size_t i = 0; i < s; i++)
    ((uint8_t *) start)[i] = VARR_GET (uint8_t, buf1, input_length2 + i);
  input_length2 += s;
  return s;
}

static size_t output_length2 = 0;
static size_t writer2 (const void *start, size_t len, void *aux_data) {
  output_length2 += len;
  for (size_t i = 0; i < len; i++) VARR_PUSH (uint8_t, buf2, ((uint8_t *) start)[i]);
  return len;
}

int main (int argc, const char *argv[]) {
  size_t i, n;
  double start = real_usec_time ();

  if (argc != 2 || (input_file = fopen (argv[1], "r")) == NULL) {
    fprintf (stderr, "usage: %s <inputfile>\n", argv[0]);
    return 1;
  }
  VARR_CREATE (uint8_t, orig, 0);
  VARR_CREATE (uint8_t, buf1, 0);
  if (!reduce_encode (reader1, writer1, NULL)) {
    fprintf (stderr, "Error in reducing input file!\n");
    return 1;
  }
  fprintf (stderr, "Compression:   original len = %lu, result = %lu, ration=%.2f, time=%.2fms\n",
           input_length1, output_length1, (input_length1 + 0.0) / output_length1,
           (real_usec_time () - start) / 1000.0);
  VARR_CREATE (uint8_t, buf2, 0);
  start = real_usec_time ();
  if (!reduce_decode (reader2, writer2, NULL)) {
    fprintf (stderr, "Corrupted input file!\n");
    return 1;
  }
  fprintf (stderr, "Decompression: original len = %lu, result = %lu, ration=%.2f, time=%.2fms\n",
           input_length2, output_length2, (input_length2 + 0.0) / output_length2,
           (real_usec_time () - start) / 1000.0);
  if (VARR_LENGTH (uint8_t, orig) != VARR_LENGTH (uint8_t, buf2)) {
    fprintf (stderr, "FAIL: original and reduced/unreduced files are of different length!\n");
    return 1;
  }
  for (i = 0; i < VARR_LENGTH (uint8_t, orig); i++)
    if (VARR_GET (uint8_t, orig, i) != VARR_GET (uint8_t, buf2, i)) break;
  if (i < VARR_LENGTH (uint8_t, orig)) {
    fprintf (stderr,
             "FAIL: original and reduced/unreduced files are different on pos = %lu! Result:\n", i);
    for (n = i; n < i + 40 && n < VARR_LENGTH (uint8_t, buf2); n++)
      fprintf (stderr, "%c", VARR_GET (uint8_t, buf2, n));
    fprintf (stderr, "\n");
    return 1;
  }
  return 0;
}
