/* This file is a part of MIR project.
   Copyright (C) 2020-2021 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#include "../mirc.h"
#include "mirc_armv7_linux.h"

#include "mirc_armv7_float.h"
#include "mirc_armv7_limits.h"
#include "mirc_armv7_stdarg.h"
#include "mirc_armv7_stdint.h"
#include "mirc_armv7_stddef.h"

static string_include_t standard_includes[]
  = {{NULL, mirc}, {NULL, armv7_mirc}, TARGET_STD_INCLUDES};

#define MAX_ALIGNMENT 16

#define ADJUST_VAR_ALIGNMENT(c2m_ctx, align, type) \
  armv7_adjust_var_alignment (c2m_ctx, align, type)

static int armv7_adjust_var_alignment (c2m_ctx_t c2m_ctx, int align, struct type *type) {
  return align;
}

static int invalid_alignment (mir_llong align) {
  return align != 0 && align != 1 && align != 2 && align != 4 && align != 8 && align != 16;
}
