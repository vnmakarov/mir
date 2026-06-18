static void set_uchar (unsigned char *p) { *p = 255; }
static void set_schar (signed char *p) { *p = -3; }
static void set_ushort (unsigned short *p) { *p = 65535; }
static void set_short (short *p) { *p = -2; }

int main (void) {
  unsigned char uc;
  signed char sc;
  unsigned short us;
  short ss;

  set_uchar (&uc);
  set_schar (&sc);
  set_ushort (&us);
  set_short (&ss);

  if (uc != 255) return 1;
  if (sc != -3) return 2;
  if (us != 65535) return 3;
  if (ss != -2) return 4;
  return 0;
}
