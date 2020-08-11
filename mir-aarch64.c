/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#define VA_LIST_IS_ARRAY_P 0

// _MIR_get_thunk, _MIR_redirect_thunk, _MIR_get_interp_shim, _MIR_get_ff_call, _MIR_get_wrapper

void *_MIR_get_bstart_builtin (MIR_context_t ctx) {
  static const uint32_t bstart_code[] = {
    0x910003e0, /* r0 = rsp */
    0xd65f03c0, /* ret r30 */
  };
  return _MIR_publish_code (ctx, (uint8_t *) bstart_code, sizeof (bstart_code));
}

void *_MIR_get_bend_builtin (MIR_context_t ctx) {
  static const uint32_t bend_code[] = {
    0x9100001f, /* rsp = r0 */
    0xd65f03c0, /* ret r30 */
  };
  return _MIR_publish_code (ctx, (uint8_t *) bend_code, sizeof (bend_code));
}

struct aarch64_va_list {
  /* address following the last (highest addressed) named incoming
     argument on the stack, rounded upwards to a multiple of 8 bytes,
     or if there are no named arguments on the stack, then the value
     of the stack pointer when the function was entered. */
  void *__stack;
  /* the address of the byte immediately following the general
     register argument save area, the end of the save area being
     aligned to a 16 byte boundary. */
  void *__gr_top;
  /* the address of the byte immediately following the FP/SIMD
     register argument save area, the end of the save area being
     aligned to a 16 byte boundary. */
  void *__vr_top;
  int __gr_offs; /* set to 0 – ((8 – named_gr) * 8) */
  int __vr_offs; /* set to 0 – ((8 – named_vr) * 16) */
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct aarch64_va_list *va = p;
  MIR_type_t type = t;
  int fp_p = type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD;
  void *a;

  if (fp_p && va->__vr_offs < 0) {
    a = (char *) va->__vr_top + va->__vr_offs;
    va->__vr_offs += 16;
  } else if (!fp_p && va->__gr_offs < 0) {
    a = (char *) va->__gr_top + va->__gr_offs;
    va->__gr_offs += 8;
  } else {
    if (type == MIR_T_LD) va->__stack = (void *) (((uint64_t) va->__stack + 15) % 16);
    a = va->__stack;
    va->__stack = (char *) va->__stack + (type == MIR_T_LD ? 16 : 8);
  }
  return a;
}

void *va_stack_arg_builtin (void *p, size_t s) { return *(void **) va_arg_builtin (p, MIR_T_I64); }

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct aarch64_va_list *va = p;
  va_list *vap = a;

  assert (sizeof (struct aarch64_va_list) == sizeof (va_list));
  *va = *(struct aarch64_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

static int setup_imm64_insns (MIR_context_t ctx, uint32_t *to, int reg, uint64_t imm64) {
  /* xd=imm64 */
  static const uint32_t imm64_pat[] = {
    0xd2800000, /*  0: mov xd, xxxx(0-15) */
    0xf2a00000, /*  4: movk xd, xxxx(16-31) */
    0xf2c00000, /*  8: movk xd, xxxx(32-47) */
    0xf2e00000, /* 12: movk xd, xxxx(48-63) */
  };
  uint32_t mask = ~(0xffff << 5);

  mir_assert (0 <= reg && reg <= 31);
  to[0] = (imm64_pat[0] & mask) | ((uint32_t) (imm64 & 0xffff) << 5) | reg;
  to[1] = (imm64_pat[1] & mask) | (((uint32_t) (imm64 >> 16) & 0xffff) << 5) | reg;
  to[2] = (imm64_pat[2] & mask) | (((uint32_t) (imm64 >> 32) & 0xffff) << 5) | reg;
  to[3] = (imm64_pat[3] & mask) | (((uint32_t) (imm64 >> 48) & 0xffff) << 5) | reg;
  return sizeof (imm64_pat) / sizeof (uint32_t);
}

static uint8_t *push_insns (MIR_context_t ctx, const uint32_t *pat, size_t pat_len) {
  uint8_t *p = (uint8_t *) pat;

  for (size_t i = 0; i < pat_len; i++) VARR_PUSH (uint8_t, machine_insns, p[i]);
  return VARR_ADDR (uint8_t, machine_insns) + VARR_LENGTH (uint8_t, machine_insns) - pat_len;
}

static size_t gen_mov_addr (MIR_context_t ctx, int reg, void *addr) {
  uint32_t insns[4];
  int insns_num = setup_imm64_insns (ctx, insns, reg, (uint64_t) addr);

  mir_assert (insns_num == 4 && sizeof (insns) == insns_num * sizeof (uint32_t));
  push_insns (ctx, insns, insns_num * sizeof (uint32_t));
  return insns_num * sizeof (uint32_t);
}

#define BR_OFFSET_BITS 26
#define MAX_BR_OFFSET (1 << (BR_OFFSET_BITS - 1)) /* 1 for sign */
#define BR_OFFSET_MASK (~(-1 << BR_OFFSET_BITS))

static void gen_call_addr (MIR_context_t ctx, void *base_addr, int temp_reg, void *call_addr) {
  static const uint32_t call_pat1 = 0x94000000; /* bl x */
  static const uint32_t call_pat2 = 0xd63f0000; /* blr x */
  uint32_t insn;
  int64_t offset = (uint32_t *) call_addr - (uint32_t *) base_addr;

  mir_assert (0 <= temp_reg && temp_reg <= 31);
  if (base_addr != NULL && -(int64_t) MAX_BR_OFFSET <= offset && offset < (int64_t) MAX_BR_OFFSET) {
    insn = call_pat1 | ((uint32_t) offset & BR_OFFSET_MASK);
  } else {
    gen_mov_addr (ctx, temp_reg, call_addr);
    insn = call_pat2 | (temp_reg << 5);
  }
  push_insns (ctx, &insn, sizeof (insn));
}

#define NOP 0xd503201f

void *_MIR_get_thunk (MIR_context_t ctx) {
  int pat[5] = {NOP, NOP, NOP, NOP, NOP}; /* maximal size thunk -- see _MIR_redirect_thunk */

  return _MIR_publish_code (ctx, (uint8_t *) pat, sizeof (pat));
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
  static const uint32_t branch_pat1 = 0xd61f0120; /* br x9 */
  static const uint32_t branch_pat2 = 0x14000000; /* b x */
  int64_t offset = (uint32_t *) to - (uint32_t *) thunk;
  uint32_t code[5];

  mir_assert (((uint64_t) thunk & 0x3) == 0 && ((uint64_t) to & 0x3) == 0); /* alignment */
  if (-(int64_t) MAX_BR_OFFSET <= offset && offset < (int64_t) MAX_BR_OFFSET) {
    code[0] = branch_pat2 | ((uint32_t) offset & BR_OFFSET_MASK);
    _MIR_change_code (ctx, thunk, (uint8_t *) &code[0], sizeof (code[0]));
  } else {
    int n = setup_imm64_insns (ctx, code, 9, (uint64_t) to);

    mir_assert (n == 4);
    code[4] = branch_pat1;
    _MIR_change_code (ctx, thunk, (uint8_t *) code, sizeof (code));
  }
}

static void gen_blk_mov (MIR_context_t ctx, uint32_t offset, uint32_t addr_offset, uint32_t qwords,
			 uint32_t addr_reg) {
  static const uint32_t blk_mov_pat[] = {
    /* 0:*/	0xf940026c, /* ldr x12, [x19,<addr_offset>]*/
    /* 4:*/	0x910003e0, /* add <addr_reg>, sp, <offset>*/
    /* 8:*/	0xd280000b, /* mov x11, 0*/
    /* c:*/	0xd280000e, /* mov x14, <qwords>*/
    /* 10:*/	0xf86c696a, /* ldr x10, [x11,x12]*/
    /* 14:*/	0xd10005ce, /* sub x14, x14, #0x1*/
    /* 18:*/	0xf820696a, /* str x10, [x11,<addr_reg>x13]*/
    /* 1c:*/	0xf10001df, /* cmp x14, 0*/
    /* 20:*/	0x9100216b, /* add x11, x11, 8*/
    /* 24:*/	0x54ffff61, /* b.ne 10 */
  };
  if (qwords == 0) {
    uint32_t pat = 0x910003e0 | addr_reg | (offset << 10); /* add <add_reg>, sp, <offset>*/
    push_insns (ctx, &pat, sizeof (pat));
  } else {
    uint32_t *addr = (uint32_t *) push_insns (ctx, blk_mov_pat, sizeof (blk_mov_pat));
    mir_assert (offset < (1 << 12) && addr_offset % 8 == 0 && (addr_offset >> 3) < (1 << 12));
    mir_assert (addr_reg < 32 && qwords < (1 << 16));
    addr[0] |= (addr_offset >> 3) << 10;
    addr[1] |= addr_reg | (offset << 10);
    addr[3] |= qwords << 5;
    addr[6] |= addr_reg << 16;
  }
}

/* save r0-r7, v0-v7 */
static const uint32_t save_insns[] = {
  0xa9bf1fe6, /* stp R6, R7, [SP, #-16]! */
  0xa9bf17e4, /* stp R4, R5, [SP, #-16]! */
  0xa9bf0fe2, /* stp R2, R3, [SP, #-16]! */
  0xa9bf07e0, /* stp R0, R1, [SP, #-16]! */
  0xadbf1fe6, /* stp Q6, Q7, [SP, #-32]! */
  0xadbf17e4, /* stp Q4, Q5, [SP, #-32]! */
  0xadbf0fe2, /* stp Q2, Q3, [SP, #-32]! */
  0xadbf07e0, /* stp Q0, Q1, [SP, #-32]! */
};

static const uint32_t restore_insns[] = {
  0xacc107e0, /* ldp Q0, Q1, SP, #32 */
  0xacc10fe2, /* ldp Q2, Q3, SP, #32 */
  0xacc117e4, /* ldp Q4, Q5, SP, #32 */
  0xacc11fe6, /* ldp Q6, Q7, SP, #32 */
  0xa8c107e0, /* ldp R0, R1, SP, #16 */
  0xa8c10fe2, /* ldp R2, R3, SP, #16 */
  0xa8c117e4, /* ldp R4, R5, SP, #16 */
  0xa8c11fe6, /* ldp R6, R7, SP, #16 */
};

static const uint32_t ld_pat = 0xf9400260;   /* ldr x, [x19], offset */
static const uint32_t lds_pat = 0xbd400260;  /* ldr s, [x19], offset */
static const uint32_t ldd_pat = 0xfd400260;  /* ldr d, [x19], offset */
static const uint32_t ldld_pat = 0x3dc00260; /* ldr q, [x19], offset */

/* Generation: fun (fun_addr, res_arg_addresses):
   push x19, x30; sp-=sp_offset; x9=fun_addr; x19=res/arg_addrs
   x8=mem[x19,<offset>]; (arg_reg=mem[x8](or addr of blk copy on the stack)
                          or x8=mem[x8] or x13=addr of blk copy on the stack;
                             mem[sp,sp_offset]=x8|x13) ...
   call fun_addr; sp+=offset
   x8=mem[x19,<offset>]; res_reg=mem[x8]; ...
   pop x19, x30; ret x30. */
void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres, MIR_type_t *res_types, size_t nargs,
                        _MIR_arg_desc_t *arg_descs, int vararg_p) {
  static const uint32_t prolog[] = {
    0xa9bf7bf3, /* stp x19,x30,[sp, -16]! */
    0xd10003ff, /* sub sp,sp,<sp_offset> */
    0xaa0003e9, /* mov x9,x0   # fun addr */
    0xaa0103f3, /* mov x19, x1 # result/arg addresses */
  };
  static const uint32_t call_end[] = {
    0xd63f0120, /* blr  x9	   */
    0x910003ff, /* add sp,sp,<sp_offset> */
  };
  static const uint32_t epilog[] = {
    0xa8c17bf3, /* ldp x19,x30,[sp],16 */
    0xd65f03c0, /* ret x30 */
  };
  static const uint32_t st_pat = 0xf9000000;   /* str x, [xn|sp], offset */
  static const uint32_t sts_pat = 0xbd000000;  /* str s, [xn|sp], offset */
  static const uint32_t std_pat = 0xfd000000;  /* str d, [xn|sp], offset */
  static const uint32_t stld_pat = 0x3d800000; /* str q, [xn|sp], offset */
  MIR_type_t type;
  uint32_t n_xregs = 0, n_vregs = 0, sp_offset = 0, blk_offset = 0, pat, offset_imm, scale;
  uint32_t sp = 31, addr_reg, qwords;
  uint32_t *addr;
  const uint32_t temp_reg = 8; /* x8 or v9 */

  mir_assert (sizeof (long double) == 16);
  for (size_t i = 0; i < nargs; i++) { /* caclulate offset for blk params */
    type = arg_descs[i].type;
    if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P || type == MIR_T_BLK) {
      if (n_xregs++ >= 8) blk_offset += 8;
    } else if (type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) {
      if (n_vregs++ >= 8) blk_offset += type == MIR_T_LD ? 16 : 8;
    } else {
      (*error_func) (MIR_call_op_error, "wrong type of arg value");
    }
  }
  blk_offset = (blk_offset + 15) / 16 * 16;
  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, prolog, sizeof (prolog));
  n_xregs = n_vregs = 0;
  for (size_t i = 0; i < nargs; i++) { /* args */
    type = arg_descs[i].type;
    scale = type == MIR_T_F ? 2 : type == MIR_T_LD ? 4 : 3;
    offset_imm = (((i + nres) * sizeof (long double) << 10)) >> scale;
    if (type == MIR_T_BLK) {
      qwords = (arg_descs[i].size + 7) / 8;
      addr_reg = n_xregs < 8 ? n_xregs : 13;
      gen_blk_mov (ctx, blk_offset, (i + nres) * sizeof (long double), qwords, addr_reg);
      blk_offset += qwords * 8;
      if (n_xregs++ >= 8) {
        pat = st_pat | ((sp_offset >> scale) << 10) | addr_reg | (sp << 5);
	push_insns (ctx, &pat, sizeof (pat));
        sp_offset += 8;
      }
    } else if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P) {
      if (n_xregs < 8) {
        pat = ld_pat | offset_imm | n_xregs++;
      } else {
        pat = ld_pat | offset_imm | temp_reg;
        push_insns (ctx, &pat, sizeof (pat));
        pat = st_pat | ((sp_offset >> scale) << 10) | temp_reg | (sp << 5);
        sp_offset += 8;
      }
      push_insns (ctx, &pat, sizeof (pat));
    } else if (type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD) {
      pat = type == MIR_T_F ? lds_pat : type == MIR_T_D ? ldd_pat : ldld_pat;
      if (n_vregs < 8) {
        pat |= offset_imm | n_vregs++;
      } else {
        if (type == MIR_T_LD) sp_offset = (sp_offset + 15) % 16;
        pat |= offset_imm | temp_reg;
        push_insns (ctx, &pat, sizeof (pat));
        pat = type == MIR_T_F ? sts_pat : type == MIR_T_D ? std_pat : stld_pat;
        pat |= ((sp_offset >> scale) << 10) | temp_reg | (sp << 5);
        sp_offset += type == MIR_T_LD ? 16 : 8;
      }
      push_insns (ctx, &pat, sizeof (pat));
    }
  }
  sp_offset = (sp_offset + 15) / 16 * 16;
  blk_offset = (blk_offset + 15) / 16 * 16;
  if (blk_offset != 0) sp_offset = blk_offset;
  mir_assert (sp_offset < (1 << 12));
  ((uint32_t *) VARR_ADDR (uint8_t, machine_insns))[1] |= sp_offset << 10; /* sub sp,sp,<offset> */
  push_insns (ctx, call_end, sizeof (call_end));
  ((uint32_t *) (VARR_ADDR (uint8_t, machine_insns) + VARR_LENGTH (uint8_t, machine_insns)))[-1]
    |= sp_offset << 10;
  n_xregs = n_vregs = 0;
  for (size_t i = 0; i < nres; i++) { /* results */
    offset_imm = i * sizeof (long double) << 10;
    offset_imm >>= res_types[i] == MIR_T_F ? 2 : res_types[i] == MIR_T_D ? 3 : 4;
    if (((MIR_T_I8 <= res_types[i] && res_types[i] <= MIR_T_U64) || res_types[i] == MIR_T_P)
        && n_xregs < 8) {
      pat = st_pat | offset_imm | n_xregs++ | (19 << 5);
      push_insns (ctx, &pat, sizeof (pat));
    } else if ((res_types[i] == MIR_T_F || res_types[i] == MIR_T_D || res_types[i] == MIR_T_LD)
               && n_vregs < 8) {
      pat = res_types[i] == MIR_T_F ? sts_pat : res_types[i] == MIR_T_D ? std_pat : stld_pat;
      pat |= offset_imm | n_vregs++ | (19 << 5);
      push_insns (ctx, &pat, sizeof (pat));
    } else {
      (*error_func) (MIR_ret_error, "x86-64 can not handle this combination of return values");
    }
  }
  push_insns (ctx, epilog, sizeof (epilog));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Transform C call to call of void handler (MIR_context_t ctx, MIR_item_t func_item,
                                             va_list va, MIR_val_t *results) */
void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t func_item, void *handler) {
  static const uint32_t save_x19_pat = 0xf81f0ff3; /* str x19, [sp,-16]! */
  static const uint32_t prepare_pat[] = {
    0xd10083ff, /* sub sp, sp, 32 # allocate va_list */
    0x910003e8, /* mov x8, sp # va_list addr         */
    0x128007e9, /* mov w9, #-64 # gr_offs */
    0xb9001909, /* str w9,[x8, 24] # va_list.gr_offs */
    0x12800fe9, /* mov w9, #-128 # vr_offs */
    0xb9001d09, /* str w9,[x8, 28]  #va_list.vr_offs */
    0x910383e9, /* add x9, sp, #224 # gr_top */
    0xf9000509, /* str x9,[x8, 8] # va_list.gr_top */
    0x91004129, /* add x9, x9, #16 # stack */
    0xf9000109, /* str x9,[x8] # valist.stack */
    0x910283e9, /* add x9, sp, #160 # vr_top*/
    0xf9000909, /* str x9,[x8, 16] # va_list.vr_top */
    0xaa0803e2, /* mov x2, x8 # va arg  */
    0xd2800009, /* mov x9, <(nres+1)*16> */
    0xcb2963ff, /* sub sp, sp, x9 */
    0x910043e3, /* add x3, sp, 16 # results arg */
    0xaa0303f3, /* mov x19, x3 # results */
    0xf90003fe, /* str x30, [sp] # save lr */
  };
  static const uint32_t shim_end[] = {
    0xf94003fe, /* ldr x30, [sp] */
    0xd2800009, /* mov x9, 224+(nres+1)*16 */
    0x8b2963ff, /* add sp, sp, x9 */
    0xf84107f3, /* ldr x19, sp, 16 */
    0xd65f03c0, /* ret x30 */
  };
  uint32_t pat, imm, n_xregs, n_vregs, offset, offset_imm;
  uint32_t nres = func_item->u.func->nres;
  MIR_type_t *results = func_item->u.func->res_types;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, &save_x19_pat, sizeof (save_x19_pat));
  push_insns (ctx, save_insns, sizeof (save_insns));
  push_insns (ctx, prepare_pat, sizeof (prepare_pat));
  imm = (nres + 1) * 16;
  mir_assert (imm < (1 << 16));
  ((uint32_t *) (VARR_ADDR (uint8_t, machine_insns) + VARR_LENGTH (uint8_t, machine_insns)))[-5]
    |= imm << 5;
  gen_mov_addr (ctx, 0, ctx);       /* mov x0, ctx */
  gen_mov_addr (ctx, 1, func_item); /* mov x1, func_item */
  gen_call_addr (ctx, NULL, 9, handler);
  /* move results: */
  n_xregs = n_vregs = offset = 0;
  mir_assert (sizeof (long double) == 16);
  for (uint32_t i = 0; i < nres; i++) {
    if ((results[i] == MIR_T_F || results[i] == MIR_T_D || results[i] == MIR_T_LD) && n_vregs < 8) {
      pat = results[i] == MIR_T_F ? lds_pat : results[i] == MIR_T_D ? ldd_pat : ldld_pat;
      pat |= n_vregs;
      n_vregs++;
    } else if (n_xregs < 8) {  // ??? ltp use
      pat = ld_pat | n_xregs;
      n_xregs++;
    } else {
      (*error_func) (MIR_ret_error, "aarch64 can not handle this combination of return values");
    }
    offset_imm = offset >> (results[i] == MIR_T_F ? 2 : results[i] == MIR_T_LD ? 4 : 3);
    mir_assert (offset_imm < (1 << 12));
    pat |= offset_imm << 10;
    push_insns (ctx, &pat, sizeof (pat));
    offset += 16;
  }
  push_insns (ctx, shim_end, sizeof (shim_end));
  imm = 224 + (nres + 1) * 16;
  mir_assert (imm < (1 << 16));
  ((uint32_t *) (VARR_ADDR (uint8_t, machine_insns) + VARR_LENGTH (uint8_t, machine_insns)))[-4]
    |= imm << 5;
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Save regs x0-x7, q0-q7; x9 = call hook_address (ctx, called_func); restore regs; br x9 */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  static const uint32_t jmp_insn = 0xd61f0120;     /* br x9 */
  static const uint32_t move_insn = 0xaa0003e9;    /* mov x9, x0 */
  static const uint32_t save_fplr = 0xa9bf7bfd;    /* stp R29, R30, [SP, #-16]! */
  static const uint32_t restore_fplr = 0xa8c17bfd; /* ldp R29, R30, SP, #16 */
  uint8_t *base_addr, *curr_addr, *code;
  size_t len = sizeof (save_insns) + sizeof (restore_insns); /* initial code length */

  for (;;) {
    curr_addr = base_addr = _MIR_get_new_code_addr (ctx, len);
    if (curr_addr == NULL) return NULL;
    VARR_TRUNC (uint8_t, machine_insns, 0);
    push_insns (ctx, &save_fplr, sizeof (save_fplr));
    curr_addr += 4;
    push_insns (ctx, save_insns, sizeof (save_insns));
    curr_addr += sizeof (save_insns);
    curr_addr += gen_mov_addr (ctx, 0, ctx);          /*mov x0,ctx  	   */
    curr_addr += gen_mov_addr (ctx, 1, called_func);  /*mov x1,called_func */
    gen_call_addr (ctx, curr_addr, 10, hook_address); /*call <hook_address>, use x10 as temp   */
    push_insns (ctx, &move_insn, sizeof (move_insn));
    push_insns (ctx, restore_insns, sizeof (restore_insns));
    push_insns (ctx, &restore_fplr, sizeof (restore_fplr));
    push_insns (ctx, &jmp_insn, sizeof (jmp_insn));
    len = VARR_LENGTH (uint8_t, machine_insns);
    code = _MIR_publish_code_by_addr (ctx, base_addr, VARR_ADDR (uint8_t, machine_insns), len);
    if (code != NULL) return code;
  }
}
