/* This file is a part of MIR project.
   Copyright (C) 2018-2023 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* x0 (zero) - always zero; x1 (ra) - link reg; x2 (sp) - sp, x3 (gp) - global pointer, x4 (tp) -
   thread pointer; x8 (s0/fp) - fp; x10-x11 (a0-a1), f10-f11 (fa0-fa1) - ret values, x10-x17
   (a0-a7), f10-f17 (fa0-fa7) - arg regs; x8-x9 (s0-s1), x18-x27 (s2-s11) - callee-saved; x1 (ra),
   x5-x7 (t0-t2), x10-x17 (a0-a7), x28-x31 (t3-t6) - temp regs f0-f7 (ft0-ft7), f10-f17 (fa0-fa7),
   f28-f31 (ft8-ft11) - temp regs f8-f9 (fs0-fs1), f18-f27 (fs2-fs11) - callee-saved

   o pc holds address of the current insn
   o stack is 16-byte aligned
   o long double is 128-bit
   o va_list is a pointer
   o 1-16-bytes structs/unions are passed through int regs (or stack) unless they contains only
     float/double values
   o 9 to 16-bytes values are passed in even (least-significant bits) odd
     register pair (one arg reg can be skipped for this)
   o 9 to 16-bytes values can be passed partially in reg and stack
   o 17 or more bytes values are passed by reference (caller allocates memory for this)
   o all fp varargs are passed only through int regs (or stack)
   o 1 to 16-bytes values are returned in int regs (x10-x11) unless they are float or
     struct/union containing only float/double (in this case they are returned through f10-f11)
   o 17 or more bytes values are returned on stack (allocated by caller)
     whose address is passed by x10 (a0)
   o long doubles for passing and returning purposes are integer
   o empty struct args are ignored
*/

static const int a0_num = 10;
static const int fa0_num = 10;

/* Small block types (less or equal to two quadwords) args are passed in
   BLK: int regs and/or on stack (w/o address)
   BLK1: int regs (even-odd for 9-16 bytes) and/or on stack (w/o address)

   Otherwise any BLK is put somewhere on the stack and its address passed instead.
   All RBLK independently of size is always passed by address as an usual argument.  */

void *_MIR_get_bstart_builtin (MIR_context_t ctx) {
#if __riscv_compressed
  static const uint16_t bstart_code[] = {
    0x850a, /* c.mv a0,sp */
    0x8082, /* c.jr ra */
  };
#else
  static const uint32_t bstart_code[] = {
    0x00010513, /* addi a0,sp,0 */
    0x00008067, /* jalr zero,0(ra) */
  };
#endif
  return _MIR_publish_code (ctx, (uint8_t *) bstart_code, sizeof (bstart_code));
}

void *_MIR_get_bend_builtin (MIR_context_t ctx) {
#if __riscv_compressed
  static const uint16_t bend_code[] = {
    0x812a, /* c.mv sp,a0 */
    0x8082, /* c.jr ra */
  };
#else
  static const uint32_t bend_code[] = {
    0x00050113, /* addi sp,a0,0 */
    0x00008067, /* jalr zero,0(ra) */
  };
#endif
  return _MIR_publish_code (ctx, (uint8_t *) bend_code, sizeof (bend_code));
}

#define VA_LIST_IS_ARRAY_P 0
struct riscv64_va_list {
  uint64_t *arg_area;
};

void *va_arg_builtin (void *p, uint64_t t) {
  struct riscv64_va_list *va = p;
  MIR_type_t type = t;
  void *a = va->arg_area;

  if (type == MIR_T_LD && __SIZEOF_LONG_DOUBLE__ == 16) {
    va->arg_area = a = (char *) (((size_t) a + 15) / 16 * 16); /* align */
    va->arg_area += 2;
  } else {
    va->arg_area++;
  }
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  if (type == MIR_T_F || type == MIR_T_I32) a = (char *) a + 4; /* 2nd word of doubleword */
#endif
  return a;
}

void va_block_arg_builtin (void *res, void *p, size_t s, uint64_t ncase) {
  struct riscv64_va_list *va = p;
  void *a = (void *) va->arg_area;
  if (s <= 2 * 8) {
    if (s > 8 && ncase == 1) {                                   /* BLK1: */
      va->arg_area = a = (char *) (((size_t) a + 15) / 16 * 16); /* align */
    }
    va->arg_area += (s + sizeof (uint64_t) - 1) / sizeof (uint64_t);
  } else {
    a = *(void **) a;
    va->arg_area++;
  }
  memcpy (res, a, s);
}

void va_start_interp_builtin (MIR_context_t ctx, void *p, void *a) {
  struct riscv64_va_list *va = p;
  va_list *vap = a;

  assert (sizeof (struct riscv64_va_list) == sizeof (va_list));
  *va = *(struct riscv64_va_list *) vap;
}

void va_end_interp_builtin (MIR_context_t ctx, void *p) {}

static uint8_t *push_insns (VARR (uint8_t) * insn_varr, const void *pat, size_t pat_len) {
  const uint8_t *p = pat;
  for (size_t i = 0; i < pat_len; i++) VARR_PUSH (uint8_t, insn_varr, p[i]);
  return VARR_ADDR (uint8_t, insn_varr) + VARR_LENGTH (uint8_t, insn_varr) - pat_len;
}

void *_MIR_get_thunk (MIR_context_t ctx) {
  static const uint32_t call_pat[] = {
    0x00000297, /* 0:auipc t0,0x0 */
    0x0102b283, /* 4:ld t0,16(t0) */
    0x00028067, /* 8:jr t0 */
    0x00000013, /* nop:addi zero,zero,0 */
    0x00000013, /* nop:addi zero,zero,0 */
    0x00000013, /* nop:addi zero,zero,0 */
  };
  return _MIR_publish_code (ctx, (uint8_t *) call_pat, sizeof (call_pat));
}

void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void *to) {
  _MIR_change_code (ctx, (uint8_t *) thunk + 16, (uint8_t *) &to, sizeof (to));
}

static const uint32_t add_sp_pat = 0x00010113;  /* addi sp,sp,0 */
static const uint32_t ld_arg_pat = 0x0004b003;  /* ld zero,0(s1) */
static const uint32_t flw_arg_pat = 0x0004a007; /* flw f0,0(s1) */
static const uint32_t fld_arg_pat = 0x0004b007; /* fld f0,0(s1) */

static uint32_t get_i_format_imm (int offset) {
  assert (-(1 << 11) <= offset && offset < (1 << 11));
  return offset << 20;
}

static uint32_t get_i_format_rd (int reg) {
  assert (0 <= reg && reg < 32);
  return reg << 7;
}

static uint32_t get_s_format_imm (int offset) {
  assert (-(1 << 11) <= offset && offset < (1 << 11));
  return (offset >> 5) << 25 | (offset & 0x1f) << 7;
}

static uint32_t get_s_format_rs2 (int reg) {
  assert (0 <= reg && reg < 32);
  return reg << 20;
}

static uint32_t get_u_format_imm (int offset) {
  assert (-(1 << 19) <= offset && offset < (1 << 19));
  return offset << 12;
}

static uint32_t get_j_format_imm (int offset) {
  int d = offset >> 1; /* scale */
  assert (-(1 << 19) <= d && d < (1 << 19));
  return ((d & 0x80000) | ((d & 0x3ff) << 9) | (((d >> 10) & 0x1) << 8) | ((d >> 11) & 0xff)) << 12;
}

static uint32_t get_opfp_format_rd (int reg) {
  assert (0 <= reg && reg < 32);
  return reg << 7;
}

static uint32_t get_opfp_format_rs1 (int reg) {
  assert (0 <= reg && reg < 32);
  return reg << 15;
}

/* Move qwords from addr_offset(s1) to offset(sp). offset(sp) will be in t1.  */
static void gen_blk_mov (VARR (uint8_t) * insn_varr, size_t offset, size_t addr_offset,
                         size_t qwords) {
  static const uint32_t blk_mov_pat[] = {
    /*  0: */ 0x00010313, /* addi t1,sp,0 (<offset>) */
    /*  4: */ 0x0004b383, /* ld t2,0(s1) (<addr_offset>(s1)) */
    /*  8: */ 0x00000e13, /* addi t3,zero,0 */
    /*  c: */ 0x00000e93, /* addi t4,zero,0 (qwords) */
    /* 10: */ 0x01c38fb3, /* L:add t6,t2,t3 */
    /* 14: */ 0x000fbf03, /* ld t5,0(t6) */
    /* 18: */ 0xfffe8e93, /* addi t4,t4,-1 */
    /* 1c: */ 0x01c30fb3, /* add t6,t1,t3 */
    /* 20: */ 0x01efb023, /* sd t5,0(t6) */
    /* 24: */ 0x008e0e13, /* addi t3,t3,8 */
    /* 28: */ 0xfe0e94e3, /* bne t4,zero,-28(L) */
  };
  static const uint32_t blk_mov_pat2[] = {
    /*  0: */ 0x00000e17, /* auipc	t3,0x0 */
    /*  4: */ 0x000e3303, /* ld	t1,0(t3) (disp for <offset>(t3)) */
    /*  8: */ 0x00610333, /* add	t1,sp,t1 */
    /*  c: */ 0x000e3383, /* ld	t2,0(t3) (disp for <addr_offset>(t3)) */
    /* 10: */ 0x009383b3, /* add	t2,t2,s1 */
    /* 14: */ 0x0003b383, /* ld	t2,0(t2) */
    /* 18: */ 0x000e3e83, /* ld	t4,0(t3) (disp for qwords(t3)) */
    /* 1c: */ 0x00000e13, /* addi	t3,zero,0 */
    /* 20: */ 0x01c38fb3, /* add	t6,t2,t3 */
    /* 24: */ 0x000fbf03, /* ld	t5,0(t6) */
    /* 28: */ 0xfffe8e93, /* addi	t4,t4,-1 */
    /* 2c: */ 0x01c30fb3, /* add	t6,t1,t3 */
    /* 30: */ 0x01efb023, /* sd	t5,0(t6) */
    /* 34: */ 0x008e0e13, /* addi	t3,t3,8 */
    /* 38: */ 0xfe0e94e3, /* bne	t4,zero,20 <L> */
    /* 3c: */ 0x0000006f, /* jal	zero,0 */
  };
  if (offset < (1 << 11) && addr_offset < (1 << 11) && qwords < (1 < 11)) {
    uint32_t *addr = (uint32_t *) push_insns (insn_varr, blk_mov_pat, sizeof (blk_mov_pat));
    addr[0] |= get_i_format_imm (offset);
    addr[1] |= get_i_format_imm (addr_offset);
    addr[3] |= get_i_format_imm (qwords);
  } else {
    size_t start = VARR_LENGTH (uint8_t, insn_varr), data_start, data_bound;
    push_insns (insn_varr, blk_mov_pat2, sizeof (blk_mov_pat2));
    while (VARR_LENGTH (uint8_t, insn_varr) % 8 != 0) VARR_PUSH (uint8_t, insn_varr, 0); /* align */
    data_start = VARR_LENGTH (uint8_t, insn_varr);
    push_insns (insn_varr, &offset, sizeof (offset));
    push_insns (insn_varr, &addr_offset, sizeof (addr_offset));
    push_insns (insn_varr, &qwords, sizeof (qwords));
    data_bound = VARR_LENGTH (uint8_t, insn_varr);
    uint32_t *addr = (uint32_t *) (VARR_ADDR (uint8_t, insn_varr) + start);
    addr[1] |= get_i_format_imm (data_start - start /* - 4*/);
    addr[3] |= get_i_format_imm (data_start - start + 8 /* - 12 + 8*/);
    addr[6] |= get_i_format_imm (data_start - start + 16 /*- 24 + 16*/);
    addr[15] |= get_j_format_imm (data_bound - start - 15 /* #insns before jal */ * 4);
  }
}

/* Generation: fun (fun_addr, res_arg_addresses):
   push ra, s1; t0=fun_addr; s1=res/arg_addrs; sp-=sp_offset;
   (arg_reg=mem[s1,offset](or addr of blk copy on the stack)
    or t1=mem[s1,offset] (or addr of blk copy on the stack); mem[sp,sp_offset]=t1) ...
   call t0; sp+=offset
   x10=mem[s1,<offset>]; res_reg=mem[x10]; ...
   pop s1, s0; ret ra. */
void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres, MIR_type_t *res_types, size_t nargs,
                        _MIR_arg_desc_t *arg_descs, size_t arg_vars_num) {
#if __riscv_compressed
  static const uint16_t prolog[] = {
    0x1141, /* c.addi sp,-16 */
    0xe406, /* c.sdsp ra,8(sp) */
    0xe026, /* c.sdsp s1,0(sp) */
    0x82aa, /* c.mv t0,a0 */
    0x84ae, /* c.mv s1,a1 */
  };
#else
  static const uint32_t prolog[] = {
    0xff010113, /* addi sp,sp,-16 */
    0x00113423, /* sd ra,8(sp) */
    0x00913023, /* sd s1,0(sp) */
    0x00050293, /* addi t0,a0,0 */
    0x00058493, /* addi s1,a1,0 */
  };
#endif
  static const uint32_t ld_word_pat = 0x0003b003;      /* ld zero,0(t2) */
  static const uint32_t ld_word_temp_pat = 0x0003b303; /* ld t1,0(t2) */
  static const uint32_t ld_temp_pat = 0x0004b303;      /* ld t1,0(s1) */
  static const uint32_t st_temp_pat = 0x00613023;      /* sd t1,0(sp) */
  static const uint32_t st_arg_pat = 0x0004b023;       /* sd x0,0(s1) */
  static const uint32_t fsw_arg_pat = 0x0004a027;      /* fsw f0,0(s1) */
  static const uint32_t fsd_arg_pat = 0x0004b027;      /* fsd f0,0(s1) */
  static const uint32_t flw_temp_pat = 0x0004a087;     /* flw ft1,0(s1) */
  static const uint32_t fld_temp_pat = 0x0004b087;     /* fld ft1,0(s1) */
  static const uint32_t fsw_temp_pat = 0x00112027;     /* fsw ft1,0(sp) */
  static const uint32_t fsd_temp_pat = 0x00113027;     /* fsd ft1,0(sp) */
  static const uint32_t fmvs_arg_pat = 0xe0000053;     /* fmv.x.w x0,f0 */
  static const uint32_t fmvd_arg_pat = 0xe2000053;     /* fmv.x.d x0,f0 */
  static const uint32_t fmvs_temp_pat = 0xe0008353;    /* fmv.x.w t1,ft1 */
  static const uint32_t fmvd_temp_pat = 0xe2008353;    /* fmv.x.d t1,ft1 */
  static const uint32_t mv_t1_pat = 0x00030013;        /* addi zero,t1,0 */
  static const uint32_t long_sp_add_pat[] = {
    0x00000337, /* lui t1,0 */
    0x00030313, /* addi t1,t1,0 */
    0x00610133, /* add sp,sp,t1 */
  };
  static const uint32_t call = 0x000280e7; /* jalr ra,0(t0) */
#if __riscv_compressed
  static const uint16_t epilog[] = {
    0x60a2, /* ld ra,8(sp) */
    0x6482, /* ld s1,0(sp) */
    0x0141, /* addi sp,sp,16 */
    0x8082, /* c.jr ra */
  };
#else
  static const uint32_t epilog[] = {
    0x00813083, /* ld ra,8(sp) */
    0x00013483, /* ld s1,0(sp) */
    0x01010113, /* addi sp,sp,16 */
    0x00008067, /* jalr zero,0(ra) */
  };
#endif
  size_t len, offset;
  MIR_type_t type;
  uint32_t n_xregs = 0, n_fregs = 0, sp_offset = 0, blk_offset = 0, pat;
  uint32_t parts;
  VARR (uint8_t) * code;
  void *res;

  VARR_CREATE (uint8_t, code, 128);
  mir_assert (__SIZEOF_LONG_DOUBLE__ == 16);
  for (size_t i = 0; i < nargs; i++) { /* calculate offset for blk params */
    type = arg_descs[i].type;
    if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P || type == MIR_T_LD
        || MIR_all_blk_type_p (type)) {
      if ((parts = (arg_descs[i].size + 7) / 8) <= 2 && MIR_blk_type_p (type)) {
        if (type == MIR_T_BLK + 1) n_xregs = (n_xregs + 1) / 2 * 2; /* Make even */
        if (n_xregs + parts > 8) blk_offset += (parts - (n_xregs + parts == 9 ? 1 : 0)) * 8;
        n_xregs += parts;
      } else { /* blocks here are passed by address */
        if (type == MIR_T_LD) n_xregs = (n_xregs + 1) / 2 * 2; /* Make even */
        if (n_xregs >= 8) blk_offset += 8 + (type == MIR_T_LD ? 8 : 0);
        n_xregs++;
        if (type == MIR_T_LD) n_xregs++;
      }
    } else if (type == MIR_T_F || type == MIR_T_D) {
      if (i >= arg_vars_num) { /* vararg */
        if (n_xregs >= 8) blk_offset += 8;
        n_xregs++;
      } else {
        if (n_fregs >= 8) blk_offset += 8;
        n_fregs++;
      }
    } else {
      MIR_get_error_func (ctx) (MIR_call_op_error, "wrong type of arg value");
    }
  }
  blk_offset = (blk_offset + 15) / 16 * 16; /* align stack */
  push_insns (code, prolog, sizeof (prolog));
  len = VARR_LENGTH (uint8_t, code);
  push_insns (code, long_sp_add_pat, sizeof (long_sp_add_pat));
  n_xregs = n_fregs = 0;
  for (size_t i = 0; i < nargs; i++) { /* args */
    type = arg_descs[i].type;
    offset = (i + nres) * sizeof (MIR_val_t);
    if (MIR_blk_type_p (type)) {
      parts = (arg_descs[i].size + 7) / 8;
      if (parts <= 2) {
        pat = ld_arg_pat | get_i_format_imm (offset) | get_i_format_rd (7); /* ld t2,offset(s1) */
        push_insns (code, &pat, sizeof (pat));
        if (type == MIR_T_BLK + 1) n_xregs = (n_xregs + 1) / 2 * 2; /* Make even */
        for (int n = 0; n < parts; n++) {
          if (n_xregs < 8) {
            pat = ld_word_pat | get_i_format_imm (n * 8) | get_i_format_rd (n_xregs + a0_num);
            push_insns (code, &pat, sizeof (pat));
            n_xregs++;
          } else {
            pat = ld_word_temp_pat | get_i_format_imm (n * 8);
            push_insns (code, &pat, sizeof (pat));
            pat = st_temp_pat | get_s_format_imm (sp_offset);
            push_insns (code, &pat, sizeof (pat));
            sp_offset += 8;
            n_xregs++;
          }
          offset += sizeof (MIR_val_t);
        }
      } else {
        gen_blk_mov (code, blk_offset, (i + nres) * sizeof (MIR_val_t), parts);
        blk_offset += parts * 8;
        if (n_xregs < 8) {
          pat = mv_t1_pat | get_i_format_rd (n_xregs + a0_num);
        } else {
          pat = st_temp_pat | get_s_format_imm (sp_offset);
          sp_offset += 8;
        }
        push_insns (code, &pat, sizeof (pat));
        n_xregs++;
      }
    } else if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P || type == MIR_T_LD
               || type == MIR_T_RBLK) {
      if (type == MIR_T_LD) n_xregs = (n_xregs + 1) / 2 * 2; /* Make even */
      if (n_xregs < 8) {
        pat = ld_arg_pat | get_i_format_imm (offset) | get_i_format_rd (n_xregs + a0_num);
        n_xregs++;
        if (type == MIR_T_LD) {
          push_insns (code, &pat, sizeof (pat));
          pat = ld_arg_pat | get_i_format_imm (offset + 8) | get_i_format_rd (n_xregs + a0_num);
          n_xregs++;
        }
      } else {
        pat = ld_temp_pat | get_i_format_imm (offset);
        push_insns (code, &pat, sizeof (pat));
        pat = st_temp_pat | get_s_format_imm (sp_offset);
        sp_offset += 8;
        if (type == MIR_T_LD) {
          push_insns (code, &pat, sizeof (pat));
          pat = ld_temp_pat | get_i_format_imm (offset + 8);
          push_insns (code, &pat, sizeof (pat));
          pat = st_temp_pat | get_s_format_imm (sp_offset);
          sp_offset += 8;
        }
      }
      push_insns (code, &pat, sizeof (pat));
    } else if (type == MIR_T_F || type == MIR_T_D) {
      if (i >= arg_vars_num) { /* vararg */
        pat = type == MIR_T_F ? flw_arg_pat : fld_arg_pat;
        pat |= get_i_format_imm (offset) | get_i_format_rd (1); /* fl(w|d) ft1, <offset>(s1) */
        push_insns (code, &pat, sizeof (pat));
        if (n_xregs < 8) {
          pat = type == MIR_T_F ? fmvs_arg_pat : fmvd_arg_pat;
          pat |= get_opfp_format_rs1 (1)
                 | get_opfp_format_rd (n_xregs + a0_num); /* fmv.x.(w|d) arg, ft1 */
          n_xregs++;
        } else {
          pat = type == MIR_T_F ? fmvs_temp_pat : fmvd_temp_pat;
          pat |= get_opfp_format_rd (6); /* fmv.x.(w|d) t1,ft1 */
          push_insns (code, &pat, sizeof (pat));
          pat = st_temp_pat | get_s_format_imm (sp_offset); /* sd t1,<sp_offset>(sp) */
          sp_offset += 8;
        }
      } else if (n_fregs < 8) {
        pat = type == MIR_T_F ? flw_arg_pat : fld_arg_pat;
        pat |= get_i_format_imm (offset) | get_i_format_rd (n_fregs + fa0_num);
        n_fregs++;
      } else {
        pat = type == MIR_T_F ? flw_temp_pat : fld_temp_pat;
        pat |= get_i_format_imm (offset);
        push_insns (code, &pat, sizeof (pat));
        pat = type == MIR_T_F ? fsw_temp_pat : fsd_temp_pat;
        pat |= get_s_format_imm (sp_offset);
        sp_offset += 8;
      }
      push_insns (code, &pat, sizeof (pat));
    } else {
      MIR_get_error_func (ctx) (MIR_call_op_error, "wrong type of arg value");
    }
  }
  sp_offset = (sp_offset + 15) / 16 * 16;
  blk_offset = (blk_offset + 15) / 16 * 16;
  if (blk_offset != 0) sp_offset = blk_offset;
  int imm = -(int) sp_offset, imm12 = (imm << 20) >> 20, imm20 = ((imm - imm12) >> 12) << 12;
  ((uint32_t *) (&VARR_ADDR (uint8_t, code)[len]))[0] |= get_u_format_imm (imm20); /* lui */
  ((uint32_t *) (&VARR_ADDR (uint8_t, code)[len]))[1] |= get_i_format_imm (imm12); /* addi */
  push_insns (code, &call, sizeof (call));
  if (sp_offset < (1 << 11)) {
    pat = add_sp_pat | get_i_format_imm (sp_offset);
    push_insns (code, &pat, sizeof (pat));
  } else {
    len = VARR_LENGTH (uint8_t, code);
    push_insns (code, long_sp_add_pat, sizeof (long_sp_add_pat));
    ((uint32_t *) (&VARR_ADDR (uint8_t, code)[len]))[0] |= get_u_format_imm ((int) sp_offset >> 12);
    ((uint32_t *) (&VARR_ADDR (uint8_t, code)[len]))[1]
      |= get_i_format_imm ((int) sp_offset & 0xfff);
  }
  n_xregs = n_fregs = 0;
  for (size_t i = 0; i < nres; i++) { /* results */
    offset = i * sizeof (long double);
    if (((MIR_T_I8 <= res_types[i] && res_types[i] <= MIR_T_U64) || res_types[i] == MIR_T_P)
        && n_xregs < 2) {
      pat = st_arg_pat | get_s_format_imm (offset) | get_s_format_rs2 (n_xregs + a0_num);
      n_xregs++;
      push_insns (code, &pat, sizeof (pat));
    } else if (res_types[i] == MIR_T_LD && n_fregs + 1 < 2) {
      pat = st_arg_pat | get_s_format_imm (offset) | get_s_format_rs2 (n_xregs + a0_num);
      n_xregs++;
      push_insns (code, &pat, sizeof (pat));
      pat = st_arg_pat | get_s_format_imm (offset + 8) | get_s_format_rs2 (n_xregs + a0_num);
      n_xregs++;
      push_insns (code, &pat, sizeof (pat));
    } else if ((res_types[i] == MIR_T_F || res_types[i] == MIR_T_D) && n_fregs < 2) {
      pat = res_types[i] == MIR_T_F ? fsw_arg_pat : fsd_arg_pat;
      pat |= get_s_format_imm (offset) | get_s_format_rs2 (n_fregs + fa0_num);
      n_fregs++;
      push_insns (code, &pat, sizeof (pat));
    } else {
      MIR_get_error_func (ctx) (MIR_ret_error,
                                "riscv64 can not handle this combination of return values");
    }
  }
  push_insns (code, epilog, sizeof (epilog));
  res = _MIR_publish_code (ctx, VARR_ADDR (uint8_t, code), VARR_LENGTH (uint8_t, code));
#if 0
  if (getenv ("MIR_code_dump") != NULL)
    _MIR_dump_code ("ffi:", 0, VARR_ADDR (uint8_t, code), VARR_LENGTH (uint8_t, code), res);
#endif
  VARR_DESTROY (uint8_t, code);
  return res;
}

/* Transform C call to call of void handler (MIR_context_t ctx, MIR_item_t func_item,
                                             va_list va, MIR_val_t *results) */
void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t func_item, void *handler) {
  static const uint32_t t0_sp = 0x00010293;      /* addi t0,sp,0 */
  static const uint32_t sub_arg_sp = 0x00010113; /* addi sp,sp,0 */
  static const uint32_t set_a2_pat = 0x00010613; /* addi a2,sp,0 */
#if __riscv_compressed
  static const uint16_t prepare_pat[] = {
    0xe026, /* c.sdsp	s1,0(sp) */
    0xe406, /* c.sdsp	ra,8(sp) */
    0x0804, /* c.addi4spn s1,sp,16 */
    0x86a6, /* c.mv a3,s1 */
  };
  static const uint16_t ra_s1_restore[] = {
    0x6482, /* c.ldsp s1,0(sp) */
    0x60a2, /* c.ldsp ra,8(sp) */
  };
  static const uint16_t ret = 0x8082; /* c.jr ra */
#else
  static const uint32_t prepare_pat[] = {
    0x00913023, /* sd	s1,0(sp) */
    0x00113423, /* sd	ra,8(sp) */
    0x01010493, /* addi	s1,sp,16 */
    0x00048693, /* addi a3,s1,0 */
  };
  static const uint32_t ra_s1_restore[] = {
    0x00013483, /* ld s1,0(sp) */
    0x00813083, /* ld ra,8(sp) */
  };
  static const uint32_t ret = 0x00008067; /* jalr zero,0(ra) */
#endif
  static const uint32_t sd_arg_pat = 0x00013023;      /* sd zero,0(sp) */
  static const uint32_t ld_arg_temp_pat = 0x0002b303; /* ld t1,0(t0) */
  static const uint32_t st_arg_temp_pat = 0x00613023; /* sd t1,0(sp) */
  static const uint32_t fsd_arg_pat = 0x00013027;     /* fsd f0,0(sp) */
  static const uint32_t fsw_arg_pat = 0x00012027;     /* fsw f0,0(sp) */
  static const uint32_t call_pat[] = {
    0x00000297, /* auipc t0,0x0 */
    0x0002b503, /* ld a0,0(t0) */
    0x0002b583, /* ld a1,0(t0) */
    0x0002b283, /* ld t0,0(t0) */
    0x000280e7, /* jalr	ra,0(t0) */
  };
  size_t start, args_start, offset, sp_offset, arg_offset, align_pad;
  MIR_func_t func = func_item->u.func;
  uint32_t nargs = func->nargs, nres = func->nres;
  MIR_var_t *args = VARR_ADDR (MIR_var_t, func->vars);
  MIR_type_t type, *results = func->res_types;
  VARR (uint8_t) * code, *code2;
  void *res;
  uint32_t pat, n_xregs, n_fregs, parts;

  assert (__SIZEOF_LONG_DOUBLE__ == 16);
  VARR_CREATE (uint8_t, code, 128);
  VARR_CREATE (uint8_t, code2, 128);
  push_insns (code, &t0_sp, sizeof (t0_sp));           /* t0 = sp */
  push_insns (code, &sub_arg_sp, sizeof (sub_arg_sp)); /* sp -= <sp_offset> */
  sp_offset = 0;
  n_xregs = n_fregs = 0;
  for (size_t i = 0; i < nargs; i++) { /* args */
    type = args[i].type;
    if (MIR_blk_type_p (type) && (parts = (args[i].size + 7) / 8) <= 2) {
      if (type == MIR_T_BLK + 1 && n_xregs % 2 != 0) { /* Make even */
        sp_offset += 8;
        n_xregs = (n_xregs + 1) / 2 * 2;
      }
      for (int n = 0; n < parts; n++) {
        if (n_xregs < 8) {
          n_xregs++;
        }
        sp_offset += 8;
      }
    } else if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P || type == MIR_T_F
               || type == MIR_T_D || type == MIR_T_LD || type == MIR_T_RBLK
               || MIR_blk_type_p (type)) {
      if (type == MIR_T_LD && n_xregs % 2 != 0) { /* Make even */
        sp_offset += 8;
        n_xregs = (n_xregs + 1) / 2 * 2;
      }
      if (type != MIR_T_F && type != MIR_T_D && n_xregs < 8) {
        n_xregs++;
        sp_offset += 8;
        if (type == MIR_T_LD) {
          sp_offset += 8;
          n_xregs++;
        }
      } else if ((type == MIR_T_F || type == MIR_T_D) && n_fregs < 8) {
        sp_offset += 8;
        n_fregs++;
      } else {
        sp_offset += 8;
        if (type == MIR_T_LD) sp_offset += 8;
      }
    } else {
      MIR_get_error_func (ctx) (MIR_call_op_error, "wrong type of arg value");
    }
  }
  if (n_xregs < 8) sp_offset += 8 * (8 - n_xregs); /* saving rest of arg regs */
  align_pad = sp_offset % 16 != 0 ? 8 : 0;
  sp_offset += align_pad; /* align */
  ((uint32_t *) VARR_ADDR (uint8_t, code))[1] |= get_i_format_imm (-sp_offset);
  arg_offset = 0;
  sp_offset = align_pad;
  n_xregs = n_fregs = 0;
  for (size_t i = 0; i < nargs; i++) { /* args */
    type = args[i].type;
    if (MIR_blk_type_p (type) && (parts = (args[i].size + 7) / 8) <= 2) {
      if (type == MIR_T_BLK + 1 && n_xregs % 2 != 0) { /* Make even */
        sp_offset += 8;
        n_xregs = (n_xregs + 1) / 2 * 2;
      }
      for (int n = 0; n < parts; n++) {
        if (n_xregs < 8) {
          pat = sd_arg_pat | get_s_format_imm (sp_offset) | get_s_format_rs2 (n_xregs + a0_num);
          push_insns (code2, &pat, sizeof (pat));
          n_xregs++;
        } else {
          pat = ld_arg_temp_pat | get_i_format_imm (arg_offset);
          push_insns (code, &pat, sizeof (pat));
          arg_offset += 8;
          pat = st_arg_temp_pat | get_s_format_imm (sp_offset);
          push_insns (code, &pat, sizeof (pat));
        }
        sp_offset += 8;
      }
    } else if ((MIR_T_I8 <= type && type <= MIR_T_U64) || type == MIR_T_P || type == MIR_T_F
               || type == MIR_T_D || type == MIR_T_LD || type == MIR_T_RBLK
               || MIR_blk_type_p (type)) {
      if (type == MIR_T_LD && n_xregs % 2 != 0) { /* Make even */
        sp_offset += 8;
        n_xregs = (n_xregs + 1) / 2 * 2;
      }
      if (type != MIR_T_F && type != MIR_T_D && n_xregs < 8) {
        pat = sd_arg_pat | get_s_format_imm (sp_offset) | get_s_format_rs2 (n_xregs + a0_num);
        push_insns (code2, &pat, sizeof (pat));
        n_xregs++;
        sp_offset += 8;
        if (type == MIR_T_LD) {
          pat = sd_arg_pat | get_s_format_imm (sp_offset) | get_s_format_rs2 (n_xregs + a0_num);
          push_insns (code2, &pat, sizeof (pat));
          sp_offset += 8;
          n_xregs++;
        }
      } else if ((type == MIR_T_F || type == MIR_T_D) && n_fregs < 8) {
        pat = type == MIR_T_F ? fsw_arg_pat : fsd_arg_pat;
        pat |= get_s_format_imm (sp_offset) | get_s_format_rs2 (n_fregs + fa0_num);
        push_insns (code2, &pat, sizeof (pat));
        sp_offset += 8;
        n_fregs++;
      } else {
        pat = ld_arg_temp_pat | get_i_format_imm (arg_offset);
        push_insns (code, &pat, sizeof (pat));
        arg_offset += 8;
        pat = st_arg_temp_pat | get_s_format_imm (sp_offset);
        push_insns (code, &pat, sizeof (pat));
        sp_offset += 8;
        if (type == MIR_T_LD) {
          pat = ld_arg_temp_pat | get_i_format_imm (arg_offset);
          push_insns (code, &pat, sizeof (pat));
          arg_offset += 8;
          pat = st_arg_temp_pat | get_s_format_imm (sp_offset);
          push_insns (code, &pat, sizeof (pat));
          sp_offset += 8;
        }
      }
    }
  }
  while (n_xregs < 8) { /* save rest of arg registers (a<n>..a7) */
    pat = sd_arg_pat | get_s_format_imm (sp_offset) | get_s_format_rs2 (n_xregs + a0_num);
    push_insns (code2, &pat, sizeof (pat));
    sp_offset += 8;
    n_xregs++;
  }
  for (size_t i = 0; i < VARR_LENGTH (uint8_t, code2) / 4; i++) {
    push_insns (code, (uint32_t *) VARR_ADDR (uint8_t, code2) + i, sizeof (uint32_t));
  }
  assert (sp_offset % 16 == 0);
  pat = set_a2_pat | get_i_format_imm (align_pad);
  push_insns (code, &pat, sizeof (pat)); /* a2 = sp + align_pad */
  start = VARR_LENGTH (uint8_t, code);
  push_insns (code, &add_sp_pat, sizeof (add_sp_pat)); /* sp -= <nres*16+16(ra&s1)> */
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + start))[0] |= get_i_format_imm (-nres * 16 - 16);
  push_insns (code, prepare_pat, sizeof (prepare_pat));
  args_start = VARR_LENGTH (uint8_t, code);
  push_insns (code, call_pat, sizeof (call_pat));
  /* move results: */
  n_xregs = n_fregs = offset = 0;
  for (uint32_t i = 0; i < nres; i++) {
    if ((results[i] == MIR_T_F || results[i] == MIR_T_D) && n_fregs < 2) {
      pat = results[i] == MIR_T_F ? flw_arg_pat : fld_arg_pat;
      pat |= get_i_format_imm (offset) | get_i_format_rd (n_fregs + fa0_num);
      n_fregs++;
    } else if (results[i] == MIR_T_LD && n_xregs + 1 < 2) {
      pat = ld_arg_pat | get_i_format_imm (offset) | get_i_format_rd (n_xregs + a0_num);
      push_insns (code, &pat, sizeof (pat));
      pat = ld_arg_pat | get_i_format_imm (offset + 8) | get_i_format_rd (n_xregs + 1 + a0_num);
      n_xregs += 2;
    } else if (n_xregs < 2) {
      pat = ld_arg_pat | get_i_format_imm (offset) | get_i_format_rd (n_xregs + a0_num);
      n_xregs++;
    } else {
      MIR_get_error_func (ctx) (MIR_ret_error,
                                "riscv64 can not handle this combination of return values");
    }
    push_insns (code, &pat, sizeof (pat));
    offset += sizeof (MIR_val_t);
  }
  push_insns (code, ra_s1_restore, sizeof (ra_s1_restore)); /* ld ra,8(sp); ld s1,0(sp) */
  start = VARR_LENGTH (uint8_t, code);
  push_insns (code, &add_sp_pat, sizeof (add_sp_pat)); /* sp += <nres * 16 + 16 + sp_offset> */
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + start))[0]
    |= get_i_format_imm ((nres + 1) * 16 + sp_offset);
  push_insns (code, &ret, sizeof (ret));                                     /* jalr ra */
  while (VARR_LENGTH (uint8_t, code) % 8 != 0) VARR_PUSH (uint8_t, code, 0); /* align */
  offset = VARR_LENGTH (uint8_t, code) - args_start;
  push_insns (code, &ctx, sizeof (ctx));
  push_insns (code, &func_item, sizeof (func_item));
  push_insns (code, &handler, sizeof (handler));
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[1] |= get_i_format_imm (offset);
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[2] |= get_i_format_imm (offset + 8);
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[3] |= get_i_format_imm (offset + 16);
  res = _MIR_publish_code (ctx, VARR_ADDR (uint8_t, code), VARR_LENGTH (uint8_t, code));
#if 0
  if (getenv ("MIR_code_dump") != NULL)
    _MIR_dump_code (func->name, 0, VARR_ADDR (uint8_t, code), VARR_LENGTH (uint8_t, code), res);
#endif
  VARR_DESTROY (uint8_t, code);
  VARR_DESTROY (uint8_t, code2);
  return res;
}

/* save a0-a7,fa0-fa7: */
#if __riscv_compressed
static const uint16_t save_insns[] = {
  0xe42a, /* sd a0,8(sp) */
  0xe82e, /* sd a1,16(sp) */
  0xec32, /* sd a2,24(sp) */
  0xf036, /* sd a3,32(sp) */
  0xf43a, /* sd a4,40(sp) */
  0xf83e, /* sd a5,48(sp) */
  0xfc42, /* sd a6,56(sp) */
  0xe0c6, /* sd a7,64(sp) */
  0xa4aa, /* fsd fa0,72(sp) */
  0xa8ae, /* fsd fa1,80(sp) */
  0xacb2, /* fsd fa2,88(sp) */
  0xb0b6, /* fsd fa3,96(sp) */
  0xb4ba, /* fsd fa4,104(sp) */
  0xb8be, /* fsd fa5,112(sp) */
  0xbcc2, /* fsd fa6,120(sp) */
  0xa146, /* fsd fa7,128(sp) */
};
#else
static const uint32_t save_insns[] = {
  0x00a13423, /* sd a0,8(sp) */
  0x00b13823, /* sd a1,16(sp) */
  0x00c13c23, /* sd a2,24(sp) */
  0x02d13023, /* sd a3,32(sp) */
  0x02e13423, /* sd a4,40(sp) */
  0x02f13823, /* sd a5,48(sp) */
  0x03013c23, /* sd a6,56(sp) */
  0x05113023, /* sd a7,64(sp) */
  0x04a13427, /* fsd fa0,72(sp) */
  0x04b13827, /* fsd fa1,80(sp) */
  0x04c13c27, /* fsd fa2,88(sp) */
  0x06d13027, /* fsd fa3,96(sp) */
  0x06e13427, /* fsd fa4,104(sp) */
  0x06f13827, /* fsd fa5,112(sp) */
  0x07013c27, /* fsd fa6,120(sp) */
  0x09113027, /* fsd fa7,128(sp) */
};
#endif
/* restore a0-a7,fa0-fa7: */
#if __riscv_compressed
static const uint16_t restore_insns[] = {
  0x6522, /* ld a0,8(sp) */
  0x65c2, /* ld a1,16(sp) */
  0x6662, /* ld a2,24(sp) */
  0x7682, /* ld a3,32(sp) */
  0x7722, /* ld a4,40(sp) */
  0x77c2, /* ld a5,48(sp) */
  0x7862, /* ld a6,56(sp) */
  0x6886, /* ld a7,64(sp) */
  0x2526, /* fld fa0,72(sp) */
  0x25c6, /* fld fa1,80(sp) */
  0x2666, /* fld fa2,88(sp) */
  0x3686, /* fld fa3,96(sp) */
  0x3726, /* fld fa4,104(sp) */
  0x37c6, /* fld fa5,112(sp) */
  0x3866, /* fld fa6,120(sp) */
  0x288a, /* fld fa7,128(sp) */
};
#else
static const uint32_t restore_insns[] = {
  0x00813503, /* ld a0,8(sp) */
  0x01013583, /* ld a1,16(sp) */
  0x01813603, /* ld a2,24(sp) */
  0x02013683, /* ld a3,32(sp) */
  0x02813703, /* ld a4,40(sp) */
  0x03013783, /* ld a5,48(sp) */
  0x03813803, /* ld a6,56(sp) */
  0x04013883, /* ld a7,64(sp) */
  0x04813507, /* fld fa0,72(sp) */
  0x05013587, /* fld fa1,80(sp) */
  0x05813607, /* fld fa2,88(sp) */
  0x06013687, /* fld fa3,96(sp) */
  0x06813707, /* fld fa4,104(sp) */
  0x07013787, /* fld fa5,112(sp) */
  0x07813807, /* fld fa6,120(sp) */
  0x08013887, /* fld fa7,128(sp) */
};
#endif

/* Save regs ra,a0-a7,fa0-fa7;
   a0 = call hook_address (ctx, called_func); t0=a0; restore regs; br t0 */
void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address) {
  static const uint32_t jmp_insn = 0x00028067; /* jalr zero,0(t0) */
#if __riscv_compressed
  static const uint16_t sub_sp = 0x7175;     /* c.addi16sp sp,-144 */
  static const uint16_t add_sp = 0x6149;     /* c.addi16sp sp,144 */
  static const uint16_t save_ra = 0xe006;    /* sd ra,0(sp) */
  static const uint16_t restore_ra = 0x6082; /* ld ra,0(sp) */
#else
  static const uint32_t sub_sp = 0xf7010113;     /* addi sp,sp,-144 */
  static const uint32_t add_sp = 0x09010113;     /* addi sp,sp,144 */
  static const uint32_t save_ra = 0x00113023;    /* sd ra,0(sp) */
  static const uint32_t restore_ra = 0x00013083; /* ld ra,0(sp) */
#endif
  static const uint32_t call_pat[] = {
    0x00000297, /* auipc t0,0x0 */
    0x0002b503, /* ld a0,0(t0) */
    0x0002b583, /* ld a1,0(t0) */
    0x0002b603, /* ld a2,0(t0) */
    0x000600e7, /* jalr ra,0(a2) */
    0x00050293, /* mv t0,a0 */
  };
  uint8_t *res_code;
  size_t args_start, offset;
  VARR (uint8_t) * code;

  VARR_CREATE (uint8_t, code, 128);
  VARR_TRUNC (uint8_t, code, 0);
  push_insns (code, &sub_sp, sizeof (sub_sp));
  push_insns (code, &save_ra, sizeof (save_ra));
  push_insns (code, save_insns, sizeof (save_insns));
  args_start = VARR_LENGTH (uint8_t, code);
  push_insns (code, call_pat, sizeof (call_pat));
  push_insns (code, &restore_ra, sizeof (restore_ra));
  push_insns (code, restore_insns, sizeof (restore_insns));
  push_insns (code, &add_sp, sizeof (add_sp));
  push_insns (code, &jmp_insn, sizeof (jmp_insn));
  while (VARR_LENGTH (uint8_t, code) % 8 != 0) VARR_PUSH (uint8_t, code, 0); /* align */
  offset = VARR_LENGTH (uint8_t, code) - args_start;
  push_insns (code, &ctx, sizeof (ctx));
  push_insns (code, &called_func, sizeof (called_func));
  push_insns (code, &hook_address, sizeof (hook_address));
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[1] |= get_i_format_imm (offset);
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[2] |= get_i_format_imm (offset + 8);
  ((uint32_t *) (VARR_ADDR (uint8_t, code) + args_start))[3] |= get_i_format_imm (offset + 16);
  res_code = _MIR_publish_code (ctx, VARR_ADDR (uint8_t, code), VARR_LENGTH (uint8_t, code));
  VARR_DESTROY (uint8_t, code);
  return res_code;
}
