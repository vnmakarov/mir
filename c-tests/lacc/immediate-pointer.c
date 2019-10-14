int printf(const char *, ...);

struct point {
	long x, y;
} p;

static long offset = (long) &((struct point *) 0x8)->y;

int main(void) {
	int *ptr = &*((int *) 0x601044);
	return printf("%p, %ld\n", ptr, offset);
}
