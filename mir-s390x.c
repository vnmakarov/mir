/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Long doubles (-mlong-double=128) are always passed by its address (for args and results) */

#if 0 && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#error "s390x works only in BE mode"
#endif

#define VA_LIST_IS_ARRAY_P 1 /* one element array of struct s390x_va_list */

#define S390X_STACK_HEADER_SIZE 160

static void push_insns (MIR_context_t ctx, const uint8_t *pat, size_t pat_len) {
  for (size_t i = 0; i < pat_len; i++) VARR_PUSH (uint8_t, machine_insns, pat[i]);
}

static void s390x_gen_mov (MIR_context_t ctx, unsigned to, unsigned from) {
  uint32_t lgr = (0xb904 << 16) | (to << 4) | from; /* lgr to,from: */
  assert (to < 16 && from < 16);
  push_insns (ctx, (uint8_t *) &lgr, 4);
}

static void s390x_gen_mvi (MIR_context_t ctx, int val, unsigned base, int disp) {
  uint64_t mvghi /* mvghi disp(base), val: */
    = ((0xe548l << 32) | ((uint64_t) base << 28) | ((disp & 0xfff) << 16) | (val & 0xffff)) << 16;
  assert (base < 16 && 0 <= disp && disp < (1 << 12) && -(1 << 15) < val && val < (1 << 15));
  push_insns (ctx, (uint8_t *) &mvghi, 6);
}

static void s390x_gen_ld_st (MIR_context_t ctx, unsigned reg, unsigned base, int disp,
                             MIR_type_t type, int ld_p) {
  int single_p = type == MIR_T_F;
  int double_p = type == MIR_T_D;
  uint64_t dl = disp & 0xfff, dh = (disp >> 12) & 0xff;
  uint64_t common = ((uint64_t) reg << 36) | ((uint64_t) base << 28) | (dl << 16) | (dh << 8);
  uint64_t lgopcode
    = (type == MIR_T_I8
         ? (ld_p ? 0x77 : 0x72)
         : type == MIR_T_U8 ? (ld_p ? 0x90 : 0x72)
                            : type == MIR_T_I16
                                ? (ld_p ? 0x78 : 0x70)
                                : type == MIR_T_U16
                                    ? (ld_p ? 0x91 : 0x70)
                                    : type == MIR_T_I32 ? (ld_p ? 0x14 : 0x50)
                                                        : type == MIR_T_U32 ? (ld_p ? 0x16 : 0x50)
                                                                            : (ld_p ? 0x04 : 0x24));
  uint64_t g = ((0xe3l << 40) | common | lgopcode) << 16;
  uint64_t ey = ((0xedl << 40) | common | (ld_p ? 0x64 : 0x66)) << 16;
  uint64_t dy = ((0xedl << 40) | common | (ld_p ? 0x65 : 0x67)) << 16;
  /* (lg|lgf|llgf|lgb|llgc|lhy|llgh|ley|ldy|stg|sty|sthy|stcy|stey|stdy) reg, disp(base): */
  assert (type != MIR_T_LD && reg < 16 && base < 16 && -(1 << 19) < disp && disp < (1 << 19));
  push_insns (ctx, (uint8_t *) (single_p ? &ey : double_p ? &dy : &g), 6);
}

static void s390x_gen_ld (MIR_context_t ctx, unsigned to, unsigned base, int disp,
                          MIR_type_t type) {
  s390x_gen_ld_st (ctx, to, base, disp, type, TRUE);
}

static void s390x_gen_st (MIR_context_t ctx, unsigned from, unsigned base, int disp,
                          MIR_type_t type) {
  s390x_gen_ld_st (ctx, from, base, disp, type, FALSE);
}

static void s390x_gen_ldstm (MIR_context_t ctx, unsigned from, unsigned to, unsigned base, int disp,
                             int ld_p) {
  uint64_t dl = disp & 0xfff, dh = (disp >> 12) & 0xff;
  uint64_t common = ((uint64_t) from << 36) | ((uint64_t) to << 32) | ((uint64_t) base << 28)
                    | (dl << 16) | (dh << 8);
  uint64_t g = ((0xebl << 40) | common | (ld_p ? 0x4 : 0x24)) << 16;
  /* (lmg|stmg) from,to,disp(base): */
  assert (from < 16 && to < 16 && base < 16 && -(1 << 19) < disp && disp < (1 << 19));
  push_insns (ctx, (uint8_t *) &g, 6);
}

static void s390x_gen_jump (MIR_context_t ctx, unsigned int reg, int call_p) {
  uint16_t bcr = (0x7 << 8) | (15 << 4) | reg;  /* bcr 15,reg: */
  uint16_t balr = (0x5 << 8) | (14 << 4) | reg; /* balr 14,reg: */
  assert (reg < 16);
  push_insns (ctx, (uint8_t *) (call_p ? &balr : &bcr), 2);
}

static void s390x_gen_addi (MIR_context_t ctx, unsigned dst, unsigned src, int disp) {
  uint64_t dl = disp & 0xfff, dh = (disp >> 12) & 0xff;
  uint64_t ops = ((uint64_t) dst << 36) | ((uint64_t) src << 28) | (dl << 16) | (dh << 8);
  uint64_t lay = ((0xe3l << 40) | ops | 0x71) << 16; /* lay dst,disp(src) */
  assert (dst < 16 && src < 16 && -(1 << 19) < disp && disp < (1 << 19));
  push_insns (ctx, (uint8_t *) &lay, 6);
}

static void s390x_gen_3addrs (MIR_context_t ctx, unsigned int r1, void *a1, unsigned int r2,
                              void *a2, unsigned int r3, void *a3) {
  /* 6b:lalr r3,22+align;6b:lg r1,0(r3);6b:lg r2,8(r3);6b:lg r3,16(r3);4b:bc m15,28;align;a1-a3 */
  size_t rem = (VARR_LENGTH (uint8_t, machine_insns) + 28) % 8;
  size_t padding = rem == 0 ? 0 : 8 - rem;
  uint64_t lalr = ((0xc0l << 40) | ((uint64_t) r1 << 36) | (28 + padding) / 2) << 16;
  uint32_t brc = (0xa7 << 24) | (15 << 20) | (4 << 16) | (28 + padding) / 2; /* brc m15,28: */
  assert (r1 != 0);
  push_insns (ctx, (uint8_t *) &lalr, 6);
  s390x_gen_ld (ctx, r3, r1, 16, MIR_T_I64); /* lg r3,16(r1) */
  s390x_gen_ld (ctx, r2, r1, 8, MIR_T_I64);  /* lg r2,8(r1) */
  s390x_gen_ld (ctx, r1, r1, 0, MIR_T_I64);  /* lg r1,0(r1) */
  push_insns (ctx, (uint8_t *) &brc, 4);
  for (size_t i = 0; i < padding; i++) VARR_PUSH (uint8_t, machine_insns, 0);
  push_insns (ctx, (uint8_t *) &a1, 8);
  push_insns (ctx, (uint8_t *) &a2, 8);
  push_insns (ctx, (uint8_t *) &a3, 8);
}

void *_MIR_get_bstart_builtin (MIR_context_t ctx) {
  VARR_TRUNC (uint8_t, machine_insns, 0);
  s390x_gen_mov (ctx, 2, 15);      /* lgr r2,15 */
  s390x_gen_jump (ctx, 14, FALSE); /* bcr m15,r14 */
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

void *_MIR_get_bend_builtin (MIR_context_t ctx) {
  VARR_TRUNC (uint8_t, machine_insns, 0);
  s390x_gen_ld (ctx, 0, 15, 0, MIR_T_I64); /* r0 = 0(r15) */
  s390x_gen_st (ctx, 0, 2, 0, MIR_T_I64);  /* 0(r2) = r0 */
  s390x_gen_mov (ctx, 15, 2);              /* lgr r15,2 */
  s390x_gen_jump (ctx, 14, FALSE);         /* bcr m15,r14 */
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

void *_MIR_get_thunk (MIR_context_t ctx) {
  const int max_thunk_len = (4 * 8); /* see _MIR_redirect_thunk */
  VARR_TRUNC (uint8_t, machine_insns, 0);
  for (int i = 0; i < max_thunk_len; i++) VARR_PUSH (uint8_t, machine_insns, 0);
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
  int64_t offset = (uint8_t *) to - (uint8_t *) thunk;
  VARR_TRUNC (uint8_t, machine_insns, 0);
  assert (offset % 2 == 0);
  offset /= 2;
  if (-(1l << 31) < offset && offset < (1l << 31)) { /* brcl m15,offset: */
    uint64_t brcl = ((0xc0l << 40) | (15l << 36) | (4l << 32) | offset & 0xffffffff) << 16;
    push_insns (ctx, (uint8_t *) &brcl, 6);
  } else { /* 6b:lalr r1,8+padding; 6b:lg r1,0(r1); 2b:bcr m15,r1;padding; 64-bit address: */
    size_t rem = (VARR_LENGTH (uint8_t, machine_insns) + 14) % 8;
    size_t padding = rem == 0 ? 0 : 8 - rem;
    uint64_t lalr = ((0xc0l << 40) | (1l << 36) | (14 + padding) / 2) << 16;
    uint64_t lg = ((0xe3l << 40) | (1l << 36) | (1l << 28) | 0x4) << 16;
    uint16_t bcr = (0x7 << 8) | (15 << 4) | 1; /* bcr 15,r1: */
    push_insns (ctx, (uint8_t *) &lalr, 6);
    push_insns (ctx, (uint8_t *) &lg, 6);
    push_insns (ctx, (uint8_t *) &bcr, 2);
    for (size_t i = 0; i < padding; i++) VARR_PUSH (uint8_t, machine_insns, 0);
    push_insns (ctx, (uint8_t *) &to, 8);
  }
  _MIR_change_code (ctx, thunk, VARR_ADDR (uint8_t, machine_insns),
                    VARR_LENGTH (uint8_t, machine_insns));
}

struct s390x_va_list {
  long __gpr, __fpr;         /* number of args read until now */
  void *__overflow_arg_area; /* argument on the stack to read next */
  void *__reg_save_area;     /* curr func frame start */
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct s390x_va_list *va = p;
  MIR_type_t type = t;
  int fp_p = type == MIR_T_F || type == MIR_T_D;
  void *a;

  if (!fp_p) {
    if (va->__gpr < 5) {
      a = (char *) va->__reg_save_area + 16 + 8 * va->__gpr;
    } else {
      a = va->__overflow_arg_area;
      va->__overflow_arg_area = (char *) va->__overflow_arg_area + 8;
    }
    va->__gpr++;
    if (type == MIR_T_LD) a = *(void **) a; /* always passed by address */
  } else {
    if (va->__fpr < 4) {
      a = (char *) va->__reg_save_area + 128 + 8 * va->__fpr;
    } else {
      a = va->__overflow_arg_area;
      va->__overflow_arg_area = (char *) va->__overflow_arg_area + 8;
    }
    va->__fpr++;
  }
  if (type == MIR_T_F || type == MIR_T_I32) a = (char *) a + 4; /* 2nd word of doubleword */
  return a;
}

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct s390x_va_list *va = p;
  va_list *vap = a;

  assert (sizeof (struct s390x_va_list) == sizeof (va_list));
  *va = *(struct s390x_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

/* Generation: fun (fun_addr, res_arg_addresses):
   save r6, r7, r14 (r15 + 48,112);
   allocate and stack frame (S390X_STACK_HEADER_SIZE + param area size + ld arg values size);
   r1=r2 (fun_addr);
   r7=r3 (res_arg_addresses);
   (arg_reg=mem[r7,arg_offset] or (f1,r0)=mem[r7,arg_offset];mem[r15,S390X_STACK_HEADER_SIZE+offset]=(f1,r0)) ...
   call *r1;
   r0=mem[r7,<res_offset>]; res_reg=mem[r0]; ...
   restore r15; restore r6, r7, r14; return. */
void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres, MIR_type_t *res_types, size_t nargs,
                        MIR_type_t *arg_types, int vararg_p) {
  MIR_type_t type;
  int n_gpregs = 0, n_fpregs = 0, res_reg = 7, frame_size, disp, param_offset, param_size = 0;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  frame_size = S390X_STACK_HEADER_SIZE;
  if (nres > 0 && res_types[0] == MIR_T_LD) n_gpregs++; /* ld address */
  for (uint32_t i = 0; i < nargs; i++) {                /* calculate param area size: */
    type = arg_types[i];
    if (type == MIR_T_LD) frame_size += 16; /* address for ld value */
    if ((type == MIR_T_F || type == MIR_T_D) && n_fpregs < 4) {
      n_fpregs++;
    } else if (type != MIR_T_F && type != MIR_T_D && n_gpregs < 5) {
      n_gpregs++;
    } else {
      frame_size += 8;
      param_size += 8;
    }
  }
  s390x_gen_ldstm (ctx, 6, 7, 15, 48, FALSE); /* stmg 6,7,48(r15) : */
  s390x_gen_st (ctx, 14, 15, 112, MIR_T_I64); /* stg r14,112(r15) */
  s390x_gen_addi (ctx, 15, 15, -frame_size);  /* lay r15,-frame_size(r15) */
  s390x_gen_mov (ctx, 1, 2);                  /* fun_addr */
  s390x_gen_mov (ctx, res_reg, 3);            /* results & args */
  n_gpregs = n_fpregs = 0;
  param_offset = nres * 16;                   /* args start */
  disp = S390X_STACK_HEADER_SIZE;             /* param area start */
  if (nres > 0 && res_types[0] == MIR_T_LD) { /* ld address: */
    s390x_gen_mov (ctx, 2, res_reg);          /* lgr r2,r7 */
    n_gpregs++;
  }
  for (uint32_t i = 0; i < nargs; i++) { /* load args: */
    type = arg_types[i];
    if ((type == MIR_T_F || type == MIR_T_D) && n_fpregs < 4) {
      /* (le,ld) (f0,f2,f4,f6),param_ofset(r7) */
      s390x_gen_ld (ctx, n_fpregs * 2, res_reg, param_offset, type);
      n_fpregs++;
    } else if (type == MIR_T_F || type == MIR_T_D) {
      s390x_gen_ld (ctx, 1, res_reg, param_offset, type);        /* (le,ld) f1,param_offset(r7) */
      s390x_gen_st (ctx, 1, 15, disp, type);                     /* (ste,std) f1,disp(r15) */
      disp += 8;
    } else if (type == MIR_T_LD && n_gpregs < 5) {               /* ld address */
      s390x_gen_addi (ctx, n_gpregs + 2, res_reg, param_offset); /* lay rn,param_offset(r7) */
      n_gpregs++;
    } else if (type == MIR_T_LD) {                    /* pass address of location in the result: */
      s390x_gen_addi (ctx, 0, res_reg, param_offset); /* lay r0,param_offset(r7) */
      s390x_gen_st (ctx, 0, 15, disp, MIR_T_I64);     /* stg r0,disp(r15) */
      disp += 8;
    } else if (n_gpregs < 5) {
      s390x_gen_ld (ctx, n_gpregs + 2, res_reg, param_offset, MIR_T_I64); /* lg* rn,param_offset(r7) */
      n_gpregs++;
    } else {
      s390x_gen_ld (ctx, 0, res_reg, param_offset, MIR_T_I64); /* lg* r0,param_offset(r7) */
      s390x_gen_st (ctx, 0, 15, disp, MIR_T_I64);         /* stg* r0,disp(r15) */
      disp += 8;
    }
    param_offset += 16;
  }
  s390x_gen_jump (ctx, 1, TRUE); /* call *r1 */
  n_gpregs = n_fpregs = 0;
  disp = 0;
  for (uint32_t i = 0; i < nres; i++) {
    type = res_types[i];
    if (type == MIR_T_LD) continue; /* do nothing: the result value is already in results */
    if ((type == MIR_T_F || type == MIR_T_D) && n_fpregs < 4) {
      s390x_gen_st (ctx, n_fpregs * 2, res_reg, disp, type);
      n_fpregs++;
    } else if (type != MIR_T_F && type != MIR_T_D && n_gpregs < 1) {  // just one gp reg
      s390x_gen_st (ctx, n_gpregs + 2, res_reg, disp, MIR_T_I64);
      n_gpregs++;
    } else {
      (*error_func) (MIR_ret_error, "s390x can not handle this combination of return values");
    }
    disp += 16;
  }
  s390x_gen_addi (ctx, 15, 15, frame_size);   /* lay 15,frame_size(15) */
  s390x_gen_ldstm (ctx, 6, 7, 15, 48, TRUE);  /* lmg 6,7,48(r15) : */
  s390x_gen_ld (ctx, 14, 15, 112, MIR_T_I64); /* lg 14,112(r15) */
  s390x_gen_jump (ctx, 14, FALSE);            /* bcr m15,r14 */
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Transform C call to call of void handler (MIR_context_t ctx, MIR_item_t func_item,
                                             va_list va, MIR_val_t *results):
   Brief: save all C call args to register save area; save r7, r14;
          allocate shim stack frame (S390X_STACK_HEADER_SIZE + space for results and va);
          call handler with args; move results to return regs; restore r7,r14,r15; return */
void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t func_item, void *handler) {
  MIR_func_t func = func_item->u.func;
  uint32_t nres = func->nres, nargs = func->nargs;
  MIR_type_t type, *res_types = func->res_types;
  int disp, frame_size, local_var_size, n_gpregs, n_fpregs, va_list_disp, results_disp;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  frame_size = S390X_STACK_HEADER_SIZE;       /* register save area */
  s390x_gen_st (ctx, 14, 15, 112, MIR_T_I64); /* stg 14,112(r15) */
  s390x_gen_ldstm (ctx, 2, 6, 15, 16, FALSE); /* stmg 2,6,16(r15) : */
  for (unsigned reg = 0; reg <= 6; reg += 2)  /* stdy f0,f2,f4,f6,128(r15) : */
    s390x_gen_st (ctx, reg, 15, reg * 4 + 128, MIR_T_D);
  local_var_size = sizeof (struct s390x_va_list) + nres * 16; /* allocate va and results */
  va_list_disp = frame_size;
  results_disp = va_list_disp + sizeof (struct s390x_va_list);
  frame_size += local_var_size;
  assert (frame_size % 8 == 0);
  s390x_gen_addi (ctx, 15, 15, -frame_size);
  /* setup va: mvghi va(15),(0,1): __gpr */
  s390x_gen_mvi (ctx, nres > 0 && res_types[0] == MIR_T_LD ? 1 : 0, 15, va_list_disp);
  s390x_gen_mvi (ctx, 0, 15, va_list_disp + 8);            /* mvghi va+8(15),0: __fpr */
  s390x_gen_addi (ctx, 1, 15, frame_size);                 /* lay 1,frame_size(15) */
  s390x_gen_st (ctx, 1, 15, va_list_disp + 24, MIR_T_I64); /* stg 1,va+24(r15): __reg_save_area */
  s390x_gen_addi (ctx, 1, 1, S390X_STACK_HEADER_SIZE);     /* lay 1,S390X_STACK_HEADER_SIZE(1) */
  /* stg 1,va+16(r15):__overflow_arg_area: */
  s390x_gen_st (ctx, 1, 15, va_list_disp + 16, MIR_T_I64);
  /* call handler: */
  s390x_gen_3addrs (ctx, 2, ctx, 3, func_item, 1, handler);
  s390x_gen_addi (ctx, 4, 15, va_list_disp);
  s390x_gen_addi (ctx, 5, 15, results_disp);
  s390x_gen_jump (ctx, 1, TRUE);
  /* setup result regs: */
  disp = results_disp;
  n_gpregs = n_fpregs = 0;
  for (uint32_t i = 0; i < nres; i++) {
    type = res_types[i];
    if ((type == MIR_T_F || type == MIR_T_D) && n_fpregs < 4) {
      s390x_gen_ld (ctx, n_fpregs * 2, 15, disp, type);
      n_fpregs++;
    } else if (type != MIR_T_F && type != MIR_T_D && n_gpregs < 1) {  // just one gp reg
      if (type != MIR_T_LD) {
        s390x_gen_ld (ctx, n_gpregs + 2, 15, disp, MIR_T_I64);
      } else {
        /* ld address: lg r2,16+frame_size(r15)  */
        s390x_gen_ld (ctx, 2, 15, 16 + frame_size, MIR_T_I64);
        s390x_gen_ld (ctx, 0, 15, disp, MIR_T_D);     /* ld f0,disp(r15) */
        s390x_gen_ld (ctx, 2, 15, disp + 8, MIR_T_D); /* ld f2,disp + 8(r15) */
        s390x_gen_st (ctx, 0, 2, 0, MIR_T_D);         /* st f0,0(r2) */
        s390x_gen_st (ctx, 2, 2, 8, MIR_T_D);         /* st f2,8(r2) */
      }
      n_gpregs++;
    } else {
      (*error_func) (MIR_ret_error, "s390x can not handle this combination of return values");
    }
    disp += 16;
  }
  s390x_gen_addi (ctx, 15, 15, frame_size);   /* lay 15,frame_size(15) */
  s390x_gen_ld (ctx, 6, 15, 48, MIR_T_I64);       /* lg 6,48(r15) : */
  s390x_gen_ld (ctx, 14, 15, 112, MIR_T_I64); /* lg 14,112(r15) */
  s390x_gen_jump (ctx, 14, FALSE);            /* bcr m15,r14 */
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}

/* Brief: save r14 (r15+120); save all param regs r2-r6 (r15+16),f0,f2,f4,f6 (r15+128);
   update r15; allocate and form minimal wrapper stack frame (S390X_STACK_HEADER_SIZE);
   r2 = call hook_address (ctx, called_func); r1=r2; restore all params regs, r15, r14; bcr r1 */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  int frame_size = S390X_STACK_HEADER_SIZE;

  VARR_TRUNC (uint8_t, machine_insns, 0);
  s390x_gen_st (ctx, 14, 15, 112, MIR_T_I64); /* stg 14,112(r15) */
  s390x_gen_ldstm (ctx, 2, 6, 15, 16, FALSE); /* stmg 2,6,16(r15) : */
  for (unsigned reg = 0; reg <= 6; reg += 2)  /* stdy f0,f2,f4,f6,128(r15) : */
    s390x_gen_st (ctx, reg, 15, reg * 4 + 128, MIR_T_D);
  /* r15 -= frame_size: */
  s390x_gen_addi (ctx, 15, 15, -frame_size);
  s390x_gen_3addrs (ctx, 2, ctx, 3, called_func, 4, hook_address);
  s390x_gen_jump (ctx, 4, TRUE);
  s390x_gen_mov (ctx, 1, 2);
  s390x_gen_addi (ctx, 15, 15, frame_size);
  for (unsigned reg = 0; reg <= 6; reg += 2) /* ldy fn,disp(r15) : */
    s390x_gen_ld (ctx, reg, 15, reg * 4 + 128, MIR_T_D);
  s390x_gen_ldstm (ctx, 2, 6, 15, 16, TRUE);  /* lmg 2,6,16(r15) : */
  s390x_gen_ld (ctx, 14, 15, 112, MIR_T_I64); /* lg 14,112(r15) */
  s390x_gen_jump (ctx, 1, FALSE);
  return _MIR_publish_code (ctx, VARR_ADDR (uint8_t, machine_insns),
                            VARR_LENGTH (uint8_t, machine_insns));
}
