int printf(const char *, ...);

int main(void) {
	return printf("%lu, %ld, %ld, %u, %ld\n",
		0xF2C889DD98AE1F63,
		0xFFD2086BDu,
		0xFFD2086BD,
		0xFFFFFFFF,
		4294967295);
}
