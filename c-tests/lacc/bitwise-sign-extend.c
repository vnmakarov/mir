int printf(const char *, ...);

char f = -1L;
long g = 0x9D3BBD11537C3E80L;

int main(void) {
	return printf("%ld, %ld, %ld\n",
		(g & f),
		(g ^ f),
		(g | f));
}
