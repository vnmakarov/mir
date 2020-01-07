/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

void *_MIR_get_bstart_builtin (MIR_context_t ctx) {
  static const uint8_t bstart_code[] = {
    0x48, 0x8d, 0x44, 0x24, 0x08, /* rax = rsp + 8 (lea) */
    0xc3,                         /* ret */
  };
  return _MIR_publish_code (ctx, bstart_code, sizeof (bstart_code));
}
void *_MIR_get_bend_builtin (MIR_context_t ctx) {
  static const uint8_t bend_code[] = {
    0x48, 0x8b, 0x04, 0x24, /* rax = (rsp) */
    0x48, 0x89, 0xfc,       /* rsp = rdi */
    0xff, 0xe0,             /* jmp *rax */
  };
  return _MIR_publish_code (ctx, bend_code, sizeof (bend_code));
}

struct x86_64_va_list {
  uint32_t gp_offset, fp_offset;
  uint64_t *overflow_arg_area, *reg_save_area;
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct x86_64_va_list *va = p;
  MIR_type_t type = t;
  int fp_p = type == MIR_T_F || type == MIR_T_D;
  void *a;

  if (fp_p && va->fp_offset <= 160) {
    a = (char *) va->reg_save_area + va->fp_offset;
    va->fp_offset += 16;
  } else if (!fp_p && type != MIR_T_LD && va->gp_offset <= 40) {
    a = (char *) va->reg_save_area + va->gp_offset;
    va->gp_offset += 8;
  } else {
    a = va->overflow_arg_area;
    va->overflow_arg_area += type == MIR_T_LD ? 2 : 1;
  }
  return a;
}

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct x86_64_va_list *va = p;
  va_list *vap = a;

  assert (sizeof (struct x86_64_va_list) == sizeof (va_list));
  *va = *(struct x86_64_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

/* r11=<address to go to>; jump *r11  */
void *_MIR_get_thunk (MIR_context_t ctx) {
  void *res;
  static const uint8_t pattern[] = {
    0x49, 0xbb, 0,    0, 0, 0, 0, 0, 0, 0, /* 0x0: movabsq 0, r11 */
    0x41, 0xff, 0xe3,                      /* 0x14: jmpq   *%r11 */
  };
  res = _MIR_publish_code (ctx, pattern, sizeof (pattern));
  return res;
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
  _MIR_update_code (ctx, thunk, 1, 2, to);
}

static const uint8_t save_pat[] = {
  0x48, 0x81, 0xec, 0x80, 0,    0,    0, /*sub    $0x80,%rsp		   */
  0xf3, 0x0f, 0x7f, 0x04, 0x24,          /*movdqu %xmm0,(%rsp)		   */
  0xf3, 0x0f, 0x7f, 0x4c, 0x24, 0x10,    /*movdqu %xmm1,0x10(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x54, 0x24, 0x20,    /*movdqu %xmm2,0x20(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x5c, 0x24, 0x30,    /*movdqu %xmm3,0x30(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x64, 0x24, 0x40,    /*movdqu %xmm4,0x40(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x6c, 0x24, 0x50,    /*movdqu %xmm5,0x50(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x74, 0x24, 0x60,    /*movdqu %xmm6,0x60(%rsp)	   */
  0xf3, 0x0f, 0x7f, 0x7c, 0x24, 0x70,    /*movdqu %xmm7,0x70(%rsp)	   */
  0x41, 0x51,                            /*push   %r9			   */
  0x41, 0x50,                            /*push   %r8			   */
  0x51,                                  /*push   %rcx			   */
  0x52,                                  /*push   %rdx			   */
  0x56,                                  /*push   %rsi			   */
  0x57,                                  /*push   %rdi			   */
};

static const uint8_t restore_pat[] = {
  0x5f,                                  /*pop    %rdi			   */
  0x5e,                                  /*pop    %rsi			   */
  0x5a,                                  /*pop    %rdx			   */
  0x59,                                  /*pop    %rcx			   */
  0x41, 0x58,                            /*pop    %r8			   */
  0x41, 0x59,                            /*pop    %r9			   */
  0xf3, 0x0f, 0x6f, 0x04, 0x24,          /*movdqu (%rsp),%xmm0		   */
  0xf3, 0x0f, 0x6f, 0x4c, 0x24, 0x10,    /*movdqu 0x10(%rsp),%xmm1	   */
  0xf3, 0x0f, 0x6f, 0x54, 0x24, 0x20,    /*movdqu 0x20(%rsp),%xmm2	   */
  0xf3, 0x0f, 0x6f, 0x5c, 0x24, 0x30,    /*movdqu 0x30(%rsp),%xmm3	   */
  0xf3, 0x0f, 0x6f, 0x64, 0x24, 0x40,    /*movdqu 0x40(%rsp),%xmm4	   */
  0xf3, 0x0f, 0x6f, 0x6c, 0x24, 0x50,    /*movdqu 0x50(%rsp),%xmm5	   */
  0xf3, 0x0f, 0x6f, 0x74, 0x24, 0x60,    /*movdqu 0x60(%rsp),%xmm6	   */
  0xf3, 0x0f, 0x6f, 0x7c, 0x24, 0x70,    /*movdqu 0x70(%rsp),%xmm7	   */
  0x48, 0x81, 0xc4, 0x80, 0,    0,    0, /*add    $0x80,%rsp		   */
};

static uint8_t *push_insns (MIR_context_t ctx, const uint8_t *pat, size_t pat_len) {
  for (size_t i = 0; i < pat_len; i++) VARR_PUSH (uint8_t, machine_insns, pat[i]);
  return VARR_ADDR (uint8_t, machine_insns) + VARR_LENGTH (uint8_t, machine_insns) - pat_len;
}

static void gen_mov (MIR_context_t ctx, uint32_t offset, uint32_t reg, int ld_p) {
  static const uint8_t ld_gp_reg[] = {0x48, 0x8b, 0x83, 0, 0, 0, 0 /* mov <offset>(%rbx),%reg */};
  static const uint8_t st_gp_reg[] = {0x48, 0x89, 0x83, 0, 0, 0, 0 /* mov %reg,<offset>(%rbx) */};
  uint8_t *addr = push_insns (ctx, ld_p ? ld_gp_reg : st_gp_reg,
                              ld_p ? sizeof (ld_gp_reg) : sizeof (st_gp_reg));
  memcpy (addr + 3, &offset, sizeof (uint32_t));
  assert (reg <= 15);
  addr[0] |= (reg >> 1) & 4;
  addr[2] |= (reg & 7) << 3;
}

static void gen_movxmm (MIR_context_t ctx, uint32_t offset, uint32_t reg, int b32_p, int ld_p) {
  static const uint8_t ld_xmm_reg_pat[] = {
    0xf2, 0x0f, 0x10, 0x83, 0, 0, 0, 0 /* movs[sd] <offset>(%rbx),%xmm */
  };
  static const uint8_t st_xmm_reg_pat[] = {
    0xf2, 0x0f, 0x11, 0x83, 0, 0, 0, 0 /* movs[sd] %xmm, <offset>(%rbx) */
  };
  uint8_t *addr = push_insns (ctx, ld_p ? ld_xmm_reg_pat : st_xmm_reg_pat,
                              ld_p ? sizeof (ld_xmm_reg_pat) : sizeof (st_xmm_reg_pat));
  memcpy (addr + 4, &offset, sizeof (uint32_t));
  assert (reg <= 7);
  addr[3] |= reg << 3;
  if (b32_p) addr[0] |= 1;
}

static void gen_ldst (MIR_context_t ctx, uint32_t sp_offset, uint32_t src_offset, int b64_p) {
  static const uint8_t ldst_pat[] = {
    0x44, 0x8b, 0x93, 0,    0, 0, 0,    /* mov    <src_offset>(%rbx),%r10 */
    0x44, 0x89, 0x94, 0x24, 0, 0, 0, 0, /* mov    %r10,<sp_offset>(%sp) */
  };
  uint8_t *addr = push_insns (ctx, ldst_pat, sizeof (ldst_pat));
  memcpy (addr + 3, &src_offset, sizeof (uint32_t));
  memcpy (addr + 11, &sp_offset, sizeof (uint32_t));
  if (b64_p) {
    addr[0] |= 8;
    addr[7] |= 8;
  }
}

static void gen_ldst80 (MIR_context_t ctx, uint32_t sp_offset, uint32_t src_offset) {
  static uint8_t const ldst80_pat[] = {
    0xdb, 0xab, 0,    0, 0, 0,    /* fldt   <src_offset>(%rbx) */
    0xdb, 0xbc, 0x24, 0, 0, 0, 0, /* fstpt  <sp_offset>(%sp) */
  };
  uint8_t *addr = push_insns (ctx, ldst80_pat, sizeof (ldst80_pat));
  memcpy (addr + 2, &src_offset, sizeof (uint32_t));
  memcpy (addr + 9, &sp_offset, sizeof (uint32_t));
}

static void gen_st80 (MIR_context_t ctx, uint32_t src_offset) {
  static const uint8_t st80_pat[] = {0xdb, 0xbb, 0, 0, 0, 0 /* fstpt   <src_offset>(%rbx) */};
  memcpy (push_insns (ctx, st80_pat, sizeof (st80_pat)) + 2, &src_offset, sizeof (uint32_t));
}

/* Generation: fun (fun_addr, res_arg_addresses):
   push rbx; sp-=sp_offset; r11=fun_addr; rbx=res/arg_addrs
   r10=mem[rbx,<offset>]; (arg_reg=mem[r10] or r10=mem[r10];mem[sp,sp_offset]=r10) ...
   rax=8; call *r11; sp+=offset
   r10=mem[rbx,<offset>]; res_reg=mem[r10]; ...
   pop rbx; ret. */
void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres, MIR_type_t *res_types, size_t nargs,
                        MIR_type_t *arg_types) {
  static const uint8_t prolog[] = {
    0x53,                         /* pushq %rbx */
    0x48, 0x81, 0xec, 0, 0, 0, 0, /* subq <sp_offset>, %rsp */
    0x49, 0x89, 0xfb,             /* mov $rdi, $r11 -- fun addr */
    0x48, 0x89, 0xf3,             /* mov $rsi, $rbx -- result/arg addresses */
  };
  static const uint8_t call_end[] = {
    0x48, 0xc7, 0xc0, 0x08, 0, 0, 0, /* mov $8, rax -- to save xmm varargs */
    0x41, 0xff, 0xd3,                /* callq  *%r11	   */
    0x48, 0x81, 0xc4, 0,    0, 0, 0, /* addq <sp_offset>, %rsp */
  };
  static const uint8_t epilog[] = {
    0x5b, /* pop %rbx */
    0xc3, /* ret */
  };
  static const uint8_t iregs[] = {7, 6, 2, 1, 8, 9}; /* rdi, rsi, rdx, rcx, r8, r9 */
  uint32_t n_iregs = 0, n_xregs = 0, n_fregs, sp_offset = 0;
  uint8_t *addr;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, prolog, sizeof (prolog));
  for (size_t i = 0; i < nargs; i++) {
    if ((MIR_T_I8 <= arg_types[i] && arg_types[i] <= MIR_T_U64) || arg_types[i] == MIR_T_P) {
      if (n_iregs < 6) {
        gen_mov (ctx, (i + nres) * sizeof (long double), iregs[n_iregs++], TRUE);
      } else {
        gen_ldst (ctx, sp_offset, (i + nres) * sizeof (long double), TRUE);
        sp_offset += 8;
      }
    } else if (arg_types[i] == MIR_T_F || arg_types[i] == MIR_T_D) {
      if (n_xregs < 8) {
        gen_movxmm (ctx, (i + nres) * sizeof (long double), n_xregs++, arg_types[i] == MIR_T_F,
                    TRUE);
      } else {
        gen_ldst (ctx, sp_offset, (i + nres) * sizeof (long double), arg_types[i] == MIR_T_D);
        sp_offset += 8;
      }
    } else if (arg_types[i] == MIR_T_LD) {
      gen_ldst80 (ctx, sp_offset, (i + nres) * sizeof (long double));
      sp_offset += 16;
    } else {
      (*error_func) (MIR_call_op_error, "wrong type of arg value");
    }
  }
  sp_offset = (sp_offset + 15) / 16 * 16;
  addr = VARR_ADDR (uint8_t, machine_insns);
  memcpy (addr + 4, &sp_offset, sizeof (uint32_t));
  addr = push_insns (ctx, call_end, sizeof (call_end));
  memcpy (addr + 13, &sp_offset, sizeof (uint32_t));
  n_iregs = n_xregs = n_fregs = 0;
  for (size_t i = 0; i < nres; i++) {
    if (((MIR_T_I8 <= res_types[i] && res_types[i] <= MIR_T_U64) || res_types[i] == MIR_T_P)
        && n_iregs < 2) {
      gen_mov (ctx, i * sizeof (long double), n_iregs++ == 0 ? 0 : 2, FALSE); /* rax or rdx */
    } else if ((res_types[i] == MIR_T_F || res_types[i] == MIR_T_D) && n_xregs < 2) {
      gen_movxmm (ctx, i * sizeof (long double), n_xregs++, res_types[i] == MIR_T_F, FALSE);
    } else if (res_types[i] == MIR_T_LD && n_fregs < 2) {
      gen_st80 (ctx, i * sizeof (long double));
    } else {
      (*error_func) (MIR_ret_error, "x86-64 can not handle this combination of return values");
    }
  }
  push_insns (ctx, epilog, sizeof (epilog));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t func_item, void *handler) {
  static const uint8_t push_rbx[] = {0x53, /*push   %rbx  */};
  static const uint8_t prepare_pat[] = {
    /*  0: */ 0x48, 0x83, 0xec, 0x20,                      /* sub    32,%rsp	     */
    /*  4: */ 0x48, 0x89, 0xe2,                            /* mov    %rsp,%rdx	     */
    /*  7: */ 0xc7, 0x02, 0,    0,    0,    0,             /* movl   0,(%rdx)	     */
    /*  d: */ 0xc7, 0x42, 0x04, 0x30, 0,    0, 0,          /* movl   48, 4(%rdx)	     */
    /* 14: */ 0x48, 0x8d, 0x44, 0x24, 0x20,                /* lea    32(%rsp),%rax   */
    /* 19: */ 0x48, 0x89, 0x42, 0x10,                      /* mov    %rax,16(%rdx)     */
    /* 1d: */ 0x48, 0x8d, 0x84, 0x24, 0xe0, 0, 0, 0,       /* lea    224(%rsp),%rax   */
    /* 25: */ 0x48, 0x89, 0x42, 0x08,                      /* mov    %rax,8(%rdx)    */
    /* 29: */ 0x48, 0x81, 0xec, 0,    0,    0, 0,          /* sub    <n>,%rsp	     */
    /* 30: */ 0x48, 0x89, 0xe3,                            /* mov    %rsp,%rbx	     */
    /* 33: */ 0x48, 0x89, 0xe1,                            /* mov    %rsp,%rcx	     */
    /* 36: */ 0x48, 0xbf, 0,    0,    0,    0, 0, 0, 0, 0, /* movabs <ctx>,%rdi */
    /* 40: */ 0x48, 0xbe, 0,    0,    0,    0, 0, 0, 0, 0, /* movabs <func_item>,%rsi */
    /* 4a: */ 0x48, 0xb8, 0,    0,    0,    0, 0, 0, 0, 0, /* movabs <handler>,%rax    */
    /* 54: */ 0xff, 0xd0,                                  /* callq  *%rax            */
  };
  static const uint8_t shim_end[] = {
    /* 0: */ 0x48, 0x81, 0xc4, 0, 0, 0, 0, /*add    208+n,%rsp*/
    /* 7: */ 0x5b,                         /*pop          %rbx*/
    /* 8: */ 0xc3,                         /*retq             */
  };
  static const uint8_t ld_pat[]
    = {0x48, 0x8b, 0x83, 0, 0, 0, 0}; /* movss <offset>(%rbx), %xmm[01] */
  static const uint8_t movss_pat[]
    = {0xf3, 0x0f, 0x10, 0x83, 0, 0, 0, 0}; /* movss <offset>(%rbx), %xmm[01] */
  static const uint8_t movsd_pat[]
    = {0xf2, 0x0f, 0x10, 0x83, 0, 0, 0, 0};                   /* movsd <offset>(%rbx), %xmm[01] */
  static const uint8_t fldt_pat[] = {0xdb, 0xab, 0, 0, 0, 0}; /* fldt <offset>(%rbx) */
  static const uint8_t fxch_pat[] = {0xd9, 0xc9};             /* fxch */
  uint8_t *addr;
  uint32_t imm, n_iregs, n_xregs, n_fregs, offset;
  uint32_t nres = func_item->u.func->nres;
  MIR_type_t *results = func_item->u.func->res_types;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, push_rbx, sizeof (push_rbx));
  push_insns (ctx, save_pat, sizeof (save_pat));
  addr = push_insns (ctx, prepare_pat, sizeof (prepare_pat));
  imm = nres * 16;
  memcpy (addr + 0x2c, &imm, sizeof (uint32_t));
  memcpy (addr + 0x38, &ctx, sizeof (void *));
  memcpy (addr + 0x42, &func_item, sizeof (void *));
  memcpy (addr + 0x4c, &handler, sizeof (void *));
  /* move results: */
  n_iregs = n_xregs = n_fregs = offset = 0;
  for (uint32_t i = 0; i < nres; i++) {
    if (results[i] == MIR_T_F && n_xregs < 2) {
      addr = push_insns (ctx, movss_pat, sizeof (movss_pat));
      addr[3] |= n_xregs << 3;
      memcpy (addr + 4, &offset, sizeof (uint32_t));
      n_xregs++;
    } else if (results[i] == MIR_T_D && n_xregs < 2) {
      addr = push_insns (ctx, movsd_pat, sizeof (movsd_pat));
      addr[3] |= n_xregs << 3;
      memcpy (addr + 4, &offset, sizeof (uint32_t));
      n_xregs++;
    } else if (results[i] == MIR_T_LD && n_fregs < 2) {
      addr = push_insns (ctx, fldt_pat, sizeof (fldt_pat));
      memcpy (addr + 2, &offset, sizeof (uint32_t));
      if (n_fregs == 1) push_insns (ctx, fxch_pat, sizeof (fxch_pat));
      n_fregs++;
    } else if (n_iregs < 2) {
      addr = push_insns (ctx, ld_pat, sizeof (ld_pat));
      addr[2] |= n_iregs << 4;
      memcpy (addr + 3, &offset, sizeof (uint32_t));
      n_iregs++;
    } else {
      (*error_func) (MIR_ret_error, "x86-64 can not handle this combination of return values");
    }
    offset += 16;
  }
  addr = push_insns (ctx, shim_end, sizeof (shim_end));
  imm = 208 + nres * 16;
  memcpy (addr + 3, &imm, sizeof (uint32_t));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* save regs; r10 = call hook_address (ctx, called_func); restore regs; jmp *r10
 */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  static const uint8_t push_rax[] = {0x50, /*push   %rax */};
  static const uint8_t wrap_end[] = {
    0x58,             /*pop   %rax */
    0x41, 0xff, 0xe2, /*jmpq   *%r10			   */
  };
  static const uint8_t call_pat[] = {
    0x48, 0xbe, 0,    0, 0, 0, 0, 0, 0, 0, /*movabs called_func,%rsi  	   */
    0x48, 0xbf, 0,    0, 0, 0, 0, 0, 0, 0, /*movabs ctx,%rdi  	   */
    0x49, 0xba, 0,    0, 0, 0, 0, 0, 0, 0, /*movabs <hook_address>,%r10  	   */
    0x41, 0xff, 0xd2,                      /*callq  *%r10			   */
    0x49, 0x89, 0xc2,                      /*mov    %rax,%r10		   */
  };
  uint8_t *addr;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  push_insns (ctx, push_rax, sizeof (push_rax));
  push_insns (ctx, save_pat, sizeof (save_pat));
  addr = push_insns (ctx, call_pat, sizeof (call_pat));
  memcpy (addr + 2, &called_func, sizeof (void *));
  memcpy (addr + 12, &ctx, sizeof (void *));
  memcpy (addr + 22, &hook_address, sizeof (void *));
  push_insns (ctx, restore_pat, sizeof (restore_pat));
  push_insns (ctx, wrap_end, sizeof (wrap_end));
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

static void machine_init (MIR_context_t ctx) { VARR_CREATE (uint8_t, machine_insns, 1024); }

static void machine_finish (MIR_context_t ctx) { VARR_DESTROY (uint8_t, machine_insns); }
