static char *read_file (const char *name) {
  FILE *f;
  size_t len;
  char *str;

  if ((f = fopen (name, "r")) == NULL) {
    perror (name);
    exit (1);
  }
  fseek (f, 0, SEEK_END);
  len = ftell (f);
  rewind (f);
  str = (char *) malloc (len + 1);
  if (fread (str, 1, len, f) != len) {
    fprintf (stderr, "file %s was changed\n", name);
    exit (1);
  }
  str[len] = 0;
  return str;
}
