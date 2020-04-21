/* This file is a part of MIR project.
   Copyright (C) 2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#include "../mirc.h"
#include "mirc-s390x-linux.h"

static const char *standard_includes[] = {mirc, s390x_mirc};

static const char *standard_include_dirs[] = {"include/mirc/", "include/mirc/s390x/"};

#define MAX_ALIGNMENT 16

#define ADJUST_VAR_ALIGNMENT(c2m_ctx, align, type) \
  s390x_adjust_var_alignment (c2m_ctx, align, type)

static int s390x_adjust_var_alignment (c2m_ctx_t c2m_ctx, int align, struct type *type) {
  return align;
}

static int invalid_alignment (mir_llong align) {
  return align != 0 && align != 1 && align != 2 && align != 4 && align != 8 && align != 16;
}
