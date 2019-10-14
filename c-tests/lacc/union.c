union foo {
	int a;
	long b;
};

int main() {
	union foo bar;
	bar.a = 1;
	bar.b = 8;
	return sizeof(bar) + sizeof(union foo) + bar.a + bar.b;
}
