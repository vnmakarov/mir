/* Source bytes 0xFF (Latin-1 y-diaeresis) in a comment, a string literal and a
   character constant: a source byte is never the end of the file (C11 5.1.1.2).
   Before: c2m read 0xFF from its line buffer as -1, i.e. EOF ("unfinished
   comment"); gcc and clang compile this and return 0.  cafÿ */
int main (void) {
  const char *s = "ÿxÿ";
  if ((unsigned char) s[0] != 0xFF || s[1] != 'x' || (unsigned char) s[2] != 0xFF || s[3] != 0) return 1;
  if ((unsigned char) 'ÿ' != 0xFF) return 2;
  return 0;
}
