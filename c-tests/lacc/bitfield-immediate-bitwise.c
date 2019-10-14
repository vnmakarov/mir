int printf(const char *, ...);

struct foo {
	long f : 50;
};

int main(void) {
	struct foo p = {0x235709324614};

	long a = p.f & 7610294871096;
	long b = p.f | 7610294871096;
	return printf("%ld, %ld\n", a, b);
}
