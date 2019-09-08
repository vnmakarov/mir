void abort (void);
#define SieveSize 819000
int sieve (int n) {
  int i, k, prime, count, iter;
  char flags[SieveSize];

  for (iter = 0; iter < n; iter++) {
    count = 0;
    for (i = 0; i < SieveSize; i++)
      flags[i] = 1;
    for (i = 0; i < SieveSize; i++)
      if (flags[i]) {
	prime = i + i + 3;
	for (k = i + prime; k < SieveSize; k += prime)
	  flags[k] = 0;
	count++;
      }
  }
  return count;
}

int main (void) {
  if (sieve (10) != 123814)
    abort ();
  return 0;
}
