/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

static const char *standard_includes[] = {
  "include/mirc/mirc.h",
  "include/mirc/x86-64/mirc-x86_64-linux.h"
};

static const char *standard_include_dirs[] = {
  "include/mirc/",
  "include/mirc/x86-64/"
};

#define MAX_ALIGNMENT 16

#define ADJUST_TYPE_ALIGNMENT(align, type) x86_adjust_type_alignment (align, type)

static int x86_adjust_type_alignment (int align, struct type *type) {
  /* see https://www.uclibc.org/docs/psABI-x86_64.pdf */
  if (type->mode != TM_ARR || raw_type_size (type) < 16)
    return align;
  return 16;
}

static int invalid_alignment (mir_llong align) {
  return align != 0 && align != 1 && align != 2 && align != 4 && align != 8 && align != 16;
}
