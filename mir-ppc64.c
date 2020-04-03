/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

// _MIR_get_thunk, _MIR_redirect_thunk, _MIR_get_interp_shim, _MIR_get_ff_call, _MIR_get_wrapper
#define VA_LIST_IS_ARRAY_P 1 /* one element which is a pointer to args */

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define PPC64_STACK_HEADER_SIZE 32
#define PPC64_TOC_OFFSET 24
#define PPC64_FUNC_DESC_LEN 0
#else
#define PPC64_STACK_HEADER_SIZE 48
#define PPC64_TOC_OFFSET 40
#define PPC64_FUNC_DESC_LEN 24
#endif

static void ppc64_push_func_desc (MIR_context_t ctx);
void (*ppc64_func_desc) (MIR_context_t ctx) = ppc64_push_func_desc;

static void ppc64_push_func_desc (MIR_context_t ctx) {
  VARR_TRUNC (uint8_t, machine_insns, 0);
  for (int i = 0; i < PPC64_FUNC_DESC_LEN; i++)
    VARR_PUSH (uint8_t, machine_insns, ((uint8_t *) ppc64_func_desc)[i]);
}

#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
static void ppc64_redirect_func_desc (MIR_context_t ctx, void *desc, void *to) {
  mir_assert (((uint64_t) desc & 0x3) == 0 && ((uint64_t) to & 0x3) == 0); /* alignment */
  _MIR_change_code (ctx, desc, (uint8_t *) &to, sizeof (to));
}
#endif

static void *ppc64_publish_func_and_redirect (MIR_context_t ctx) {
  void *res = _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                                 VARR_LENGTH (uint8_t, machine_insns));
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  ppc64_redirect_func_desc (ctx, res, (uint8_t *) res + PPC64_FUNC_DESC_LEN);
#endif
  return res;
}

static void push_insn (MIR_context_t ctx, uint32_t insn) {
  uint8_t *p = (uint8_t *) &insn;
  for (size_t i = 0; i < 4; i++) VARR_PUSH (uint8_t, machine_insns, p[i]);
}

static void push_insns (MIR_context_t ctx, const uint32_t *pat, size_t pat_len) {
  uint8_t *p = (uint8_t *) pat;
  for (size_t i = 0; i < pat_len; i++) VARR_PUSH (uint8_t, machine_insns, p[i]);
}

static void ppc64_gen_mov (MIR_context_t ctx, unsigned to, unsigned from) {
  /* or to,from,from: */
  push_insn (ctx, (31 << 26) | (444 << 1) | (from << 21) | (to << 16) | (from << 11));
}

static void ppc64_gen_addi (MIR_context_t ctx, unsigned rt_reg, unsigned ra_reg, int disp) {
  push_insn (ctx, (14 << 26) | (rt_reg << 21) | (ra_reg << 16) | (disp & 0xffff));
}

static void ppc64_gen_ld (MIR_context_t ctx, unsigned to, unsigned base, int disp,
                          MIR_type_t type) {
  int single_p = type == MIR_T_F;
  int double_p = type == MIR_T_D || type == MIR_T_LD;
  /* (ld | lf[sd]) to, disp(base): */
  assert (base != 0 && base < 32 && to < 32 && (single_p || double_p || (disp & 0x3) == 0));
  push_insn (ctx, ((single_p ? 48 : double_p ? 50 : 58) << 26) | (to << 21) | (base << 16)
                    | (disp & 0xffff));
}

static void ppc64_gen_st (MIR_context_t ctx, unsigned from, unsigned base, int disp,
                          MIR_type_t type) {
  int single_p = type == MIR_T_F;
  int double_p = type == MIR_T_D || type == MIR_T_LD;
  /* std|stf[sd] from, disp(base): */
  assert (base != 0 && base < 32 && from < 32 && (single_p || double_p || (disp & 0x3) == 0));
  push_insn (ctx, ((single_p ? 52 : double_p ? 54 : 62) << 26) | (from << 21) | (base << 16)
                    | (disp & 0xffff));
}

static void ppc64_gen_stdu (MIR_context_t ctx, int disp) {
  assert ((disp & 0x3) == 0);
  push_insn (ctx, 0xf8210001 | disp & 0xfffc); /* stdu 1, disp (1) */
}

static void ppc64_gen_address (MIR_context_t ctx, unsigned int reg, void *p) {
  uint64_t a = (uint64_t) p;
  if ((a >> 32) == 0) {
    if (((a >> 31) & 1) == 0) { /* lis r,0,Z2 */
      push_insn (ctx, (15 << 26) | (reg << 21) | (0 << 16) | (a >> 16) & 0xffff);
    } else { /* xor r,r,r; oris r,r,Z2 */
      push_insn (ctx, (31 << 26) | (316 << 1) | (reg << 21) | (reg << 16) | (reg << 11));
      push_insn (ctx, (25 << 26) | (reg << 21) | (reg << 16) | (a >> 16) & 0xffff);
    }
  } else {
    /* lis r,0,Z0; ori r,r,Z1; rldicr r,r,32,31; oris r,r,Z2; ori r,r,Z3: */
    push_insn (ctx, (15 << 26) | (reg << 21) | (0 << 16) | (a >> 48));
    push_insn (ctx, (24 << 26) | (reg << 21) | (reg << 16) | (a >> 32) & 0xffff);
    push_insn (ctx, (30 << 26) | (reg << 21) | (reg << 16) | 0x07c6);
    push_insn (ctx, (25 << 26) | (reg << 21) | (reg << 16) | (a >> 16) & 0xffff);
  }
  push_insn (ctx, (24 << 26) | (reg << 21) | (reg << 16) | a & 0xffff);
}

static void ppc64_gen_jump (MIR_context_t ctx, unsigned int reg, int call_p) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  assert (reg != 0);
  ppc64_gen_ld (ctx, 0, reg, 0, MIR_T_I64);                         /* 0 = func addr */
  ppc64_gen_ld (ctx, 2, reg, 8, MIR_T_I64);                         /* r2 = TOC */
  push_insn (ctx, (31 << 26) | (467 << 1) | (0 << 21) | (9 << 16)); /* mctr 0 */
#else
  if (reg != 12) ppc64_gen_mov (ctx, 12, reg);                       /* 12 = func addr */
  push_insn (ctx, (31 << 26) | (467 << 1) | (12 << 21) | (9 << 16)); /* mctr 12 */
#endif
  push_insn (ctx, (19 << 26) | (528 << 1) | (20 << 21) | (call_p ? 1 : 0)); /* bcctr[l] */
}

void *_MIR_get_bstart_builtin (MIR_context_t ctx) {
  static const uint32_t bstart_code[] = {
    0x7c230b78, /* mr 3,1 */
    0x4e800020, /* blr */
  };
  ppc64_push_func_desc (ctx);
  push_insns (ctx, bstart_code, sizeof (bstart_code));
  return ppc64_publish_func_and_redirect (ctx);
}

void *_MIR_get_bend_builtin (MIR_context_t ctx) {
  static const uint32_t bend_finish_code[] = {
    0x7c611b78, /* mr      r1,r3 */
    0x4e800020, /* blr */
  };
  ppc64_push_func_desc (ctx);
  ppc64_gen_ld (ctx, 0, 1, 0, MIR_T_I64);                /* r0 = 0(r1) */
  ppc64_gen_st (ctx, 0, 3, 0, MIR_T_I64);                /* 0(r3) = r0 */
  ppc64_gen_ld (ctx, 0, 1, PPC64_TOC_OFFSET, MIR_T_I64); /* r0 = toc_offset(r1) */
  ppc64_gen_st (ctx, 0, 3, PPC64_TOC_OFFSET, MIR_T_I64); /* toc_offset(r3) = r0 */
  push_insns (ctx, bend_finish_code, sizeof (bend_finish_code));
  return ppc64_publish_func_and_redirect (ctx);
}

void *_MIR_get_thunk (MIR_context_t ctx) { /* emit 3 doublewords for func descriptor: */
  ppc64_push_func_desc (ctx);
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return ppc64_publish_func_and_redirect (ctx);
#else
  const uint32_t nop_insn = 24 << (32 - 6);                          /* ori 0,0,0 */
  const int max_thunk_len = (7 * 8);
  VARR_TRUNC (uint8_t, machine_insns, 0);
  for (int i = 0; i < max_thunk_len; i++) push_insn (ctx, nop_insn);
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
#endif
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  ppc64_redirect_func_desc (ctx, thunk, to);
#else
  static const uint32_t global_entry_end[] = {
    0x7d8903a6, /* mtctr r12 */
    0x4e800420, /* bctr */
  };
  VARR_TRUNC (uint8_t, machine_insns, 0);
  ppc64_gen_address (ctx, 12, to);
  push_insns (ctx, global_entry_end, sizeof (global_entry_end));
  _MIR_change_code (ctx, thunk, VARR_ADDR (uint8_t, machine_insns),
                    VARR_LENGTH (uint8_t, machine_insns));
#endif
}

struct ppc64_va_list {
  uint64_t *arg_area;
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct ppc64_va_list *va = p;
  MIR_type_t type = t;
  int fp_p = type == MIR_T_F || type == MIR_T_D;
  void *a = va->arg_area;

  if (type == MIR_T_LD) {
    va->arg_area += 2;
  } else {
    va->arg_area++;
  }
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  if (type == MIR_T_F || type == MIR_T_I32) a = (char *) a + 4; /* 2nd word of doubleword */
#endif
  return a;
}

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct ppc64_va_list **va = p;
  va_list *vap = a;

  assert (sizeof (struct ppc64_va_list) == sizeof (va_list));
  *va = (struct ppc64_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

/* Generation: fun (fun_addr, res_arg_addresses):
   save lr (r1 + 16); allocate and form minimal stack frame (with necessary param area); save r14;
   r12=fun_addr (r3); r14 = res_arg_addresses (r4);
   r0=mem[r14,<args_offset>]; (arg_reg=mem[r0] or r0=mem[r0];mem[r1,r1_offset]=r0) ...
   if func is vararg: put fp args also in gp regs
   call *r12;
   r0=mem[r14,<offset>]; res_reg=mem[r0]; ...
   restore r14, r1, lr; return. */
void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres, MIR_type_t *res_types, size_t nargs,
                        MIR_type_t *arg_types, int vararg_p) {
  static uint32_t start_pattern[] = {
    0x7c0802a6, /* mflr r0 */
    0xf8010010, /* std  r0,16(r1) */
  };
  static uint32_t finish_pattern[] = {
    0xe8010010, /* ld   r0,16(r1) */
    0x7c0803a6, /* mtlr r0 */
    0x4e800020, /* blr */
  };
  MIR_type_t type;
  int n_gpregs = 0, n_fpregs = 0, res_reg = 14, frame_size, disp, param_offset, param_size = 0;

  ppc64_push_func_desc (ctx);
  for (uint32_t i = 0; i < nargs; i++) param_size += arg_types[i] == MIR_T_LD ? 16 : 8;
  if (param_size < 64) param_size = 64;
  frame_size = PPC64_STACK_HEADER_SIZE + param_size + 8; /* +local var to save res_reg */
  if (frame_size % 16 != 0) frame_size += 8;             /* align */
  ppc64_gen_st (ctx, 2, 1, PPC64_TOC_OFFSET, MIR_T_I64);
  push_insns (ctx, start_pattern, sizeof (start_pattern));
  ppc64_gen_stdu (ctx, -frame_size);
  ppc64_gen_st (ctx, res_reg, 1, PPC64_STACK_HEADER_SIZE + param_size,
                MIR_T_I64); /* save res_reg */
  mir_assert (sizeof (long double) == 16);
  ppc64_gen_mov (ctx, res_reg, 4); /* results & args */
  ppc64_gen_mov (ctx, 12, 3);      /* func addr */
  n_gpregs = n_fpregs = 0;
  param_offset = nres * 16;              /* args start */
  disp = PPC64_STACK_HEADER_SIZE;        /* param area start */
  for (uint32_t i = 0; i < nargs; i++) { /* load args: */
    type = arg_types[i];
    if ((type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) && n_fpregs < 13) {
      ppc64_gen_ld (ctx, 1 + n_fpregs, res_reg, param_offset, type);
      if (vararg_p) {
        if (n_gpregs >= 8) {
          ppc64_gen_st (ctx, 1 + n_fpregs, 1, disp, MIR_T_D);
        } else { /* load into gp reg too */
          ppc64_gen_st (ctx, 1 + n_fpregs, 1, -8, MIR_T_D);
          ppc64_gen_ld (ctx, 3 + n_gpregs, 1, -8, MIR_T_I64);
        }
      }
      n_fpregs++;
      if (type == MIR_T_LD) {
        if (n_fpregs < 13) {
          ppc64_gen_ld (ctx, 1 + n_fpregs, res_reg, param_offset + 8, type);
          if (vararg_p) {
            if (n_gpregs + 1 >= 8) {
              ppc64_gen_st (ctx, 1 + n_fpregs, 1, disp + 8, MIR_T_D);
            } else { /* load gp reg to */
              ppc64_gen_st (ctx, 1 + n_fpregs, 1, -8, MIR_T_D);
              ppc64_gen_ld (ctx, 4 + n_gpregs, 1, -8, MIR_T_I64);
            }
          }
          n_fpregs++;
        } else {
          ppc64_gen_ld (ctx, 0, res_reg, param_offset + 8, type);
          ppc64_gen_st (ctx, 0, 1, disp + 8, MIR_T_D);
        }
      }
    } else if (type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) {
      ppc64_gen_ld (ctx, 0, res_reg, param_offset, type);
      ppc64_gen_st (ctx, 0, 1, disp, MIR_T_D);
      if (type == MIR_T_LD) {
        ppc64_gen_ld (ctx, 0, res_reg, param_offset + 8, type);
        ppc64_gen_st (ctx, 0, 1, disp + 8, MIR_T_D);
      }
    } else if (n_gpregs < 8) {
      ppc64_gen_ld (ctx, n_gpregs + 3, res_reg, param_offset, MIR_T_I64);
    } else {
      ppc64_gen_ld (ctx, 0, res_reg, param_offset, MIR_T_I64);
      ppc64_gen_st (ctx, 0, 1, disp, MIR_T_I64);
    }
    disp += type == MIR_T_LD ? 16 : 8;
    param_offset += 16;
    n_gpregs += type == MIR_T_LD ? 2 : 1;
  }
  ppc64_gen_jump (ctx, 12, TRUE); /* call func_addr */
  n_gpregs = n_fpregs = 0;
  disp = 0;
  for (uint32_t i = 0; i < nres; i++) {
    type = res_types[i];
    if ((type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) && n_fpregs < 4) {
      ppc64_gen_st (ctx, n_fpregs + 1, res_reg, disp, type);
      n_fpregs++;
      if (type == MIR_T_LD) {
        if (n_fpregs >= 4)
          (*error_func) (MIR_ret_error, "ppc64 can not handle this combination of return values");
        ppc64_gen_st (ctx, n_fpregs + 1, res_reg, disp + 8, type);
        n_fpregs++;
      }
    } else if (n_gpregs < 1) {  // just one gp reg
      ppc64_gen_st (ctx, n_gpregs + 3, res_reg, disp, MIR_T_I64);
      n_gpregs++;
    } else {
      (*error_func) (MIR_ret_error, "ppc64 can not handle this combination of return values");
    }
    disp += 16;
  }
  ppc64_gen_ld (ctx, res_reg, 1, PPC64_STACK_HEADER_SIZE + param_size,
                MIR_T_I64); /* restore res_reg */
  ppc64_gen_addi (ctx, 1, 1, frame_size);
  push_insns (ctx, finish_pattern, sizeof (finish_pattern));
  return ppc64_publish_func_and_redirect (ctx);
}

/* Transform C call to call of void handler (MIR_context_t ctx, MIR_item_t func_item,
                                             va_list va, MIR_val_t *results):
   Brief: put all C call args to local vars (or if va_arg do nothing); save lr (r1+16), r14;
          allocate and form minimal shim stack frame (param area = 8 * 8);
          call handler with args; move results(r14) to return regs; restore lr,r14,r1; return */
void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t func_item, void *handler) {
  MIR_func_t func = func_item->u.func;
  uint32_t nres = func->nres, nargs = func->nargs;
  int vararg_p = func->vararg_p;
  MIR_type_t type, *res_types = func->res_types;
  MIR_var_t *arg_vars = VARR_ADDR (MIR_var_t, func->vars);
  int disp, size, frame_size, local_var_size, param_offset, va_reg = 11, caller_r1 = 12,
                                                            res_reg = 14;
  int n_gpregs, n_fpregs;
  static uint32_t start_pattern[] = {
    0x7c0802a6, /* mflr r0 */
    0xf8010010, /* std  r0,16(r1) */
  };
  static uint32_t finish_pattern[] = {
    0xe8010010, /* ld   r0,16(r1) */
    0x7c0803a6, /* mtlr r0 */
    0x4e800020, /* blr */
  };

  VARR_TRUNC (uint8_t, machine_insns, 0);
  frame_size = PPC64_STACK_HEADER_SIZE + 64; /* header + 8(param area) */
  local_var_size = nres * 16 + 8;            /* saved r14, results */
  if (vararg_p) {
    for (unsigned reg = 3; reg <= 10; reg++) /* std rn,dispn(r1) : */
      ppc64_gen_st (ctx, reg, 1, PPC64_STACK_HEADER_SIZE + (reg - 3) * 8, MIR_T_I64);
    ppc64_gen_addi (ctx, va_reg, 1, PPC64_STACK_HEADER_SIZE);
  } else {
    ppc64_gen_mov (ctx, caller_r1, 1); /* caller frame r1 */
    for (uint32_t i = 0; i < nargs; i++) {
      type = arg_vars[i].type;
      local_var_size += type == MIR_T_LD ? 16 : 8;
    }
  }
  frame_size += local_var_size;
  if (frame_size % 16 != 0) frame_size += 8; /* align */
  push_insns (ctx, start_pattern, sizeof (start_pattern));
  ppc64_gen_stdu (ctx, -frame_size);
  ppc64_gen_st (ctx, res_reg, 1, PPC64_STACK_HEADER_SIZE + 64, MIR_T_I64); /* save res_reg */
  if (!vararg_p) { /* save args in local vars: */
    /* header_size + 64 + nres * 16 + 8 -- start of stack memory to keep args: */
    disp = PPC64_STACK_HEADER_SIZE + 64 + nres * 16 + 8;
    ppc64_gen_addi (ctx, va_reg, 1, disp);
    param_offset = PPC64_STACK_HEADER_SIZE;
    n_gpregs = n_fpregs = 0;
    for (uint32_t i = 0; i < nargs; i++) {
      type = arg_vars[i].type;
      if ((type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) && n_fpregs < 13) {
        ppc64_gen_st (ctx, n_fpregs + 1, 1, disp, MIR_T_D);
        n_fpregs++;
        if (type == MIR_T_LD) {
          if (n_fpregs < 13) {
            ppc64_gen_st (ctx, n_fpregs + 1, 1, disp + 8, MIR_T_D);
            n_fpregs++;
          } else {
            ppc64_gen_ld (ctx, 0, caller_r1, param_offset + 8, MIR_T_D);
            ppc64_gen_st (ctx, 0, 1, disp + 8, MIR_T_D);
          }
        }
      } else if (n_gpregs < 8) {
        ppc64_gen_st (ctx, n_gpregs + 3, 1, disp, MIR_T_I64);
      } else if (type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) {
        ppc64_gen_ld (ctx, 0, caller_r1, param_offset + (type == MIR_T_F ? 4 : 0), type);
        ppc64_gen_st (ctx, 0, 1, disp, MIR_T_D);
        if (type == MIR_T_LD) {
          ppc64_gen_ld (ctx, 0, caller_r1, param_offset + 8, MIR_T_D);
          ppc64_gen_st (ctx, 0, 1, disp + 8, MIR_T_D);
        }
      } else {
        ppc64_gen_ld (ctx, 0, caller_r1, param_offset, MIR_T_I64);
        ppc64_gen_st (ctx, 0, 1, disp, MIR_T_I64);
      }
      size = type == MIR_T_LD ? 16 : 8;
      disp += size;
      param_offset += size;
      n_gpregs += type == MIR_T_LD ? 2 : 1;
    }
  }
  ppc64_gen_addi (ctx, res_reg, 1, 64 + PPC64_STACK_HEADER_SIZE + 8);
  ppc64_gen_address (ctx, 3, ctx);
  ppc64_gen_address (ctx, 4, func_item);
  ppc64_gen_mov (ctx, 5, va_reg);
  ppc64_gen_mov (ctx, 6, res_reg);
  ppc64_gen_address (ctx, 12, handler);
  ppc64_gen_jump (ctx, 12, TRUE);
  disp = n_gpregs = n_fpregs = 0;
  for (uint32_t i = 0; i < nres; i++) {
    type = res_types[i];
    if ((type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) && n_fpregs < 4) {
      ppc64_gen_ld (ctx, n_fpregs + 1, res_reg, disp, type);
      n_fpregs++;
      if (type == MIR_T_LD) {
        if (n_fpregs >= 4)
          (*error_func) (MIR_ret_error, "ppc64 can not handle this combination of return values");
        ppc64_gen_ld (ctx, n_fpregs + 1, res_reg, disp + 8, type);
        n_fpregs++;
      }
    } else if (n_gpregs < 1) {  // just one gp reg
      ppc64_gen_ld (ctx, n_gpregs + 3, res_reg, disp, MIR_T_I64);
      n_gpregs++;
    } else {
      (*error_func) (MIR_ret_error, "ppc64 can not handle this combination of return values");
    }
    disp += 16;
  }
  ppc64_gen_ld (ctx, res_reg, 1, PPC64_STACK_HEADER_SIZE + 64, MIR_T_I64); /* restore res_reg */
  ppc64_gen_addi (ctx, 1, 1, frame_size);
  push_insns (ctx, finish_pattern, sizeof (finish_pattern));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Brief: save lr (r1+16); update r1, save all param regs (r1+header+64);
          allocate and form minimal wrapper stack frame (param area = 8*8);
          r3 = call hook_address (ctx, called_func); r12=r3
          restore params regs (r1+header+64),  r1, lr (r1+16); ctr=r12; b *ctr */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  static uint32_t prologue[] = {
    0x7c0802a6, /* mflr r0 */
    0xf8010010, /* std  r0,16(r1) */
  };
  static uint32_t epilogue[] = {
    0xe8010010, /* ld   r0,16(r1) */
    0x7c0803a6, /* mtlr r0 */
  };
  int frame_size = PPC64_STACK_HEADER_SIZE + 8 * 8 + 13 * 8 + 8 * 8;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, prologue, sizeof (prologue));
  /* stdu r1,n(r1): header + 8(gp args) + 13(fp args) + 8(param area): */
  if (frame_size % 16 != 0) frame_size += 8;
  ppc64_gen_stdu (ctx, -frame_size);
  for (unsigned reg = 3; reg <= 10; reg++) /* std rn,dispn(r1) : */
    ppc64_gen_st (ctx, reg, 1, PPC64_STACK_HEADER_SIZE + (reg - 3) * 8 + 64, MIR_T_I64);
  for (unsigned reg = 1; reg <= 13; reg++) /* stfd fn,dispn(r1) : */
    ppc64_gen_st (ctx, reg, 1, PPC64_STACK_HEADER_SIZE + (reg - 1 + 8) * 8 + 64, MIR_T_D);
  ppc64_gen_address (ctx, 3, ctx);
  ppc64_gen_address (ctx, 4, called_func);
  ppc64_gen_address (ctx, 12, hook_address);
  ppc64_gen_jump (ctx, 12, TRUE);
  ppc64_gen_mov (ctx, 12, 3);
  for (unsigned reg = 3; reg <= 10; reg++) /* ld rn,dispn(r1) : */
    ppc64_gen_ld (ctx, reg, 1, PPC64_STACK_HEADER_SIZE + (reg - 3) * 8 + 64, MIR_T_I64);
  for (unsigned reg = 1; reg <= 13; reg++) /* lfd fn,dispn(r1) : */
    ppc64_gen_ld (ctx, reg, 1, PPC64_STACK_HEADER_SIZE + (reg - 1 + 8) * 8 + 64, MIR_T_D);
  ppc64_gen_addi (ctx, 1, 1, frame_size);
  push_insns (ctx, epilogue, sizeof (epilogue));
  push_insn (ctx, (31 << 26) | (467 << 1) | (12 << 21) | (9 << 16)); /* mctr 12 */
  push_insn (ctx, (19 << 26) | (528 << 1) | (20 << 21));             /* bcctr */
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}
