int printf(const char *, ...);

static int test(long double d) {
	int i, j;
	long double e = 3.14L, f = 0;

	i = d == 1.0L;
	j = d != e;

	if (d < 3) f += 1;
	if (d <= e) f += 2;
	if (d > e) f += 3L;
	if (d >= e) f += 4u;

	return printf("%Lf, %Lf, %Lf, %d, %d\n", d, e, f, i, j);
}

int main(void) {
	double a = -3.3;
	long double b = 22.5f;

	return test(a) + test(b) + test(1.0L) + test(3.14L);
}
