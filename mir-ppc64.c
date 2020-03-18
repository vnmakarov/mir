/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

// _MIR_get_thunk, _MIR_redirect_thunk, _MIR_get_interp_shim, _MIR_get_ff_call, _MIR_get_wrapper
#define VA_LIST_IS_ARRAY_P 1 /* one element which is a pointer to args */

#define FUNC_DESC_LEN 24
static void ppc64_push_func_desc (MIR_context_t ctx);
void (*ppc64_func_desc) (MIR_context_t ctx) = ppc64_push_func_desc;

static void ppc64_push_func_desc (MIR_context_t ctx) {
  VARR_TRUNC (uint8_t, machine_insns, 0);
  for (int i = 0; i < FUNC_DESC_LEN; i++)
    VARR_PUSH (uint8_t, machine_insns, ((uint8_t *) ppc64_func_desc)[i]);
}

static void ppc64_redirect_func_desc (MIR_context_t ctx, void *desc, void *to) {
  mir_assert (((uint64_t) desc & 0x3) == 0 && ((uint64_t) to & 0x3) == 0); /* alignment */
  _MIR_change_code (ctx, desc, (uint8_t *) &to, sizeof (to));
}

static void *ppc64_publish_func_and_redirect (MIR_context_t ctx) {
  void *res = _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                                 VARR_LENGTH (uint8_t, machine_insns));
  ppc64_redirect_func_desc (ctx, res, (uint8_t *) res + FUNC_DESC_LEN);
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
  static const uint32_t bend_code[] = {
    0xe8010000, /* ld      r0,0(r1) */
    0xf8030000, /* std     r0,0(r3) */
    0xe8010028, /* ld      r0,40(r1) */
    0xf8030028, /* std     r0,40(r3) */
    0x7c611b78, /* mr      r1,r3 */
    0x4e800020, /* blr */
  };
  ppc64_push_func_desc (ctx);
  push_insns (ctx, bend_code, sizeof (bend_code));
  return ppc64_publish_func_and_redirect (ctx);
}

void *_MIR_get_thunk (MIR_context_t ctx) { /* emit 3 doublewords for func descriptor: */
  ppc64_push_func_desc (ctx);
  return ppc64_publish_func_and_redirect (ctx);
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
  ppc64_redirect_func_desc (ctx, thunk, to);
}

struct ppc64_va_list {
  uint64_t *arg_area;
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct ppc64_va_list *va = p;
  MIR_type_t type = t;
  int fp_p = type == MIR_T_F || type == MIR_T_D;
  void *a = va->arg_area;

  if (type == MIR_T_F || type == MIR_T_I32) {
    a = (char *) a + 4; /* 2nd word of doubleword */
    va->arg_area = (uint64_t *) ((char *) a + 4);
  } else if (type == MIR_T_LD) {
    va->arg_area += 2;
  } else {
    va->arg_area++;
  }
  return a;
}

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct ppc64_va_list **va = p;
  va_list *vap = a;

  assert (sizeof (struct ppc64_va_list) == sizeof (va_list));
  *va = (struct ppc64_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

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
  ppc64_gen_ld (ctx, 0, reg, 0, MIR_T_I64);                                 /* 0 = func addr */
  ppc64_gen_ld (ctx, 2, reg, 8, MIR_T_I64);                                 /* r2 = TOC */
  push_insn (ctx, (31 << 26) | (467 << 1) | (0 << 21) | (9 << 16));         /* mctr 0 */
  push_insn (ctx, (19 << 26) | (528 << 1) | (20 << 21) | (call_p ? 1 : 0)); /* bcctr[l] */
}

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
  frame_size = 48 + param_size + 8;         /* +local var to save res_reg */
  if (frame_size % 8 != 0) frame_size += 8; /* align */
  ppc64_gen_st (ctx, 2, 1, 40, MIR_T_I64);
  push_insns (ctx, start_pattern, sizeof (start_pattern));
  ppc64_gen_stdu (ctx, -frame_size);
  ppc64_gen_st (ctx, res_reg, 1, 48 + param_size, MIR_T_I64); /* save res_reg */
  mir_assert (sizeof (long double) == 16);
  ppc64_gen_mov (ctx, res_reg, 4); /* results & args */
  ppc64_gen_mov (ctx, 12, 3);      /* func addr */
  n_gpregs = n_fpregs = 0;
  param_offset = nres * 16;              /* args start */
  disp = 48;                             /* param area start */
  for (uint32_t i = 0; i < nargs; i++) { /* load args: */
    type = arg_types[i];
    if ((type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) && n_fpregs < 13) {
      ppc64_gen_ld (ctx, 1 + n_fpregs, res_reg, param_offset, type);
      if (vararg_p) {
        if (n_gpregs >= 8) {
          ppc64_gen_st (ctx, 1 + n_fpregs, 1, disp, MIR_T_D);
        } else { /* load gp reg to */
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
    } else if (n_gpregs < 8) {
      ppc64_gen_ld (ctx, n_gpregs + 3, res_reg, param_offset, MIR_T_I64);
    } else if (type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) {
      ppc64_gen_ld (ctx, 0, res_reg, param_offset, type);
      ppc64_gen_st (ctx, 0, 1, disp, MIR_T_D);
      if (type == MIR_T_LD) {
        ppc64_gen_ld (ctx, 0, res_reg, param_offset + 8, type);
        ppc64_gen_st (ctx, 0, 1, disp + 8, MIR_T_D);
      }
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
  ppc64_gen_ld (ctx, res_reg, 1, 48 + param_size, MIR_T_I64); /* restore res_reg */
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
  static uint32_t save_gp_regs_pattern[] = {
    0xf8610030, /* std r3,48(r1) */
    0xf8810038, /* std r4,56(r1) */
    0xf8a10040, /* std r5,64(r1) */
    0xf8c10048, /* std r6,72(r1) */
    0xf8e10050, /* std r7,80(r1) */
    0xf9010058, /* std r8,88(r1) */
    0xf9210060, /* std r9,96(r1) */
    0xf9410068, /* std r10,104(r1) */
  };

  VARR_TRUNC (uint8_t, machine_insns, 0);
  frame_size = 112;               /* 6(frame start) + 8(param area) */
  local_var_size = nres * 16 + 8; /* saved r14, results */
  if (vararg_p) {
    push_insns (ctx, save_gp_regs_pattern, sizeof (save_gp_regs_pattern));
    ppc64_gen_addi (ctx, va_reg, 1, 48);
  } else {
    ppc64_gen_mov (ctx, caller_r1, 1); /* caller frame r1 */
    for (uint32_t i = 0; i < nargs; i++) {
      type = arg_vars[i].type;
      local_var_size += type == MIR_T_LD ? 16 : 8;
    }
  }
  frame_size += local_var_size;
  if (frame_size % 8 != 0) frame_size += 8; /* align */
  push_insns (ctx, start_pattern, sizeof (start_pattern));
  ppc64_gen_stdu (ctx, -frame_size);
  ppc64_gen_st (ctx, res_reg, 1, 48 + 64, MIR_T_I64); /* save res_reg */
  if (!vararg_p) {                                    /* save args in local vars: */
    disp = 112 + nres * 16 + 8; /* 48 + 64 + nres * 16 + 8: start of local vars to keep args */
    ppc64_gen_addi (ctx, va_reg, 1, disp);
    param_offset = 48;
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
  ppc64_gen_addi (ctx, res_reg, 1, 64 + 48 + 8);
  ppc64_gen_address (ctx, 3, ctx);
  ppc64_gen_address (ctx, 4, func_item);
  ppc64_gen_mov (ctx, 5, va_reg);
  ppc64_gen_mov (ctx, 6, res_reg);
  ppc64_gen_address (ctx, 7, handler);
  ppc64_gen_jump (ctx, 7, TRUE);
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
  ppc64_gen_ld (ctx, res_reg, 1, 48 + 64, MIR_T_I64); /* restore res_reg */
  ppc64_gen_addi (ctx, 1, 1, frame_size);
  push_insns (ctx, finish_pattern, sizeof (finish_pattern));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Brief: save lr (r1+16); update r1, save all param regs (r1+112);
          allocate and form minimal wrapper stack frame (param area = 8*8);
          r3 = call hook_address (ctx, called_func);
          restore params regs (r1+112),  r1, lr (r1+16); ctr=r11; b *ctr */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  static uint32_t prologue[] = {
    0x7c0802a6, /* mflr r0 */
    0xf8010010, /* std  r0,16(r1) */
    0xf821fee9, /* stdu r1,-280(r1): 6(frame start) + 8(gp args) + 13(fp args) + 8(param area) */
    0xf8610070, /* std  r3,112(r1) */
    0xf8810078, /* std  r4,120(r1) */
    0xf8a10080, /* std  r5,128(r1) */
    0xf8c10088, /* std  r6,136(r1) */
    0xf8e10090, /* std  r7,144(r1) */
    0xf9010098, /* std  r8,152(r1) */
    0xf92100a0, /* std  r9,160(r1) */
    0xf94100a8, /* std  r10,168(r1) */
    0xd82100b0, /* stfd f1,176(r1) */
    0xd84100b8, /* stfd f2,184(r1) */
    0xd86100c0, /* stfd f3,192(r1) */
    0xd88100c8, /* stfd f4,200(r1) */
    0xd8a100d0, /* stfd f5,208(r1) */
    0xd8c100d8, /* stfd f6,216(r1) */
    0xd8e100e0, /* stfd f7,224(r1) */
    0xd90100e8, /* stfd f8,232(r1) */
    0xd92100f0, /* stfd f9,240(r1) */
    0xd94100f8, /* stfd f10,248(r1) */
    0xd9610100, /* stfd f11,256(r1) */
    0xd9810108, /* stfd f12,264(r1) */
    0xd9a10110, /* stfd f13,272(r1) */
  };
  static uint32_t epilogue[] = {
    0xe8610070, /* ld   r3,112(r1) */
    0xe8810078, /* ld   r4,120(r1) */
    0xe8a10080, /* ld   r5,128(r1) */
    0xe8c10088, /* ld   r6,136(r1) */
    0xe8e10090, /* ld   r7,144(r1) */
    0xe9010098, /* ld   r8,152(r1) */
    0xe92100a0, /* ld   r9,160(r1) */
    0xe94100a8, /* ld   r10,168(r1) */
    0xc82100b0, /* lfd  f1,176(r1) */
    0xc84100b8, /* lfd  f2,184(r1) */
    0xc86100c0, /* lfd  f3,192(r1) */
    0xc88100c8, /* lfd  f4,200(r1) */
    0xc8a100d0, /* lfd  f5,208(r1) */
    0xc8c100d8, /* lfd  f6,216(r1) */
    0xc8e100e0, /* lfd  f7,224(r1) */
    0xc90100e8, /* lfd  f8,232(r1) */
    0xc92100f0, /* lfd  f9,240(r1) */
    0xc94100f8, /* lfd  f10,248(r1) */
    0xc9610100, /* lfd  f11,256(r1) */
    0xc9810108, /* lfd  f12,264(r1) */
    0xc9a10110, /* lfd  f13,272(r1) */
    0x38210118, /* addi r1,r1,280 */
    0xe8010010, /* ld   r0,16(r1) */
    0x7c0803a6, /* mtlr r0 */
  };

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, prologue, sizeof (prologue));
  ppc64_gen_address (ctx, 3, ctx);
  ppc64_gen_address (ctx, 4, called_func);
  ppc64_gen_address (ctx, 5, hook_address);
  ppc64_gen_jump (ctx, 5, TRUE);
  ppc64_gen_mov (ctx, 11, 3);
  push_insns (ctx, epilogue, sizeof (epilogue));
  ppc64_gen_jump (ctx, 11, FALSE);
}
