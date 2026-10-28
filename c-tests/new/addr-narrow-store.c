/* A store through a char pointer to an int changes only its low byte, so
   the int's address can not be replaced by the int itself.  */
int main (void) {
  int x = 0x01010100;
  char *c = (char *) &x;
  *c = 7;
  return x != 0x01010107;
}
