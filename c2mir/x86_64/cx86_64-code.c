/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#include "../mirc.h"
#include "mirc-x86_64-linux.h"

static const char *standard_includes[] = {mirc, x86_64_mirc};

static const char *standard_include_dirs[] = {"include/mirc/", "include/mirc/x86-64/"};

#define MAX_ALIGNMENT 16

#define ADJUST_VAR_ALIGNMENT(c2m_ctx, align, type) x86_adjust_var_alignment (c2m_ctx, align, type)

static int x86_adjust_var_alignment (c2m_ctx_t c2m_ctx, int align, struct type *type) {
  /* see https://www.uclibc.org/docs/psABI-x86_64.pdf */
  if (type->mode == TM_ARR && raw_type_size (c2m_ctx, type) >= 16) return 16;
  return align;
}

static int invalid_alignment (mir_llong align) {
  return align != 0 && align != 1 && align != 2 && align != 4 && align != 8 && align != 16;
}
