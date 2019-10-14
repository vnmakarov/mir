union value {
	char v;
	long l;
	struct {
		long x, y;
	} point;
};

int main() {
	union value v = {1};
	return v.point.x;
}
