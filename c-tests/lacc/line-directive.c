int printf(const char *, ...);

#line __LINE__
int i = __LINE__;
char *s = __FILE__;
# line 10 "bar.c"
int j = __LINE__;

int main(void) {
	return printf("%d, %d, %d, %s, %s\n",
		__LINE__, i, j, s, __FILE__);
}
