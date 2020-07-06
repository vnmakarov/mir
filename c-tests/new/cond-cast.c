int time_limit;
void func (int average, int simple_average) {
  time_limit = (average < 2.0 * simple_average) ? average : 2.0 * simple_average;
}

int main (void) { return 0; }
