/* This file is a part of MIR project.
   Copyright (C) 2018-2021 Vladimir Makarov <vmakarov.gcc@gmail.com>.
   riscv64 call ABI target specific code.
*/

typedef int target_arg_info_t;

static void target_init_arg_vars (c2m_ctx_t c2m_ctx, target_arg_info_t *arg_info) {}

static int target_return_by_addr_p (c2m_ctx_t c2m_ctx, struct type *ret_type) {
  return ((ret_type->mode == TM_STRUCT || ret_type->mode == TM_UNION)
          && type_size (c2m_ctx, ret_type) > 2 * 8);
}

static int reg_aggregate_size (c2m_ctx_t c2m_ctx, struct type *type) {
  int size;

  if (type->mode != TM_STRUCT && type->mode != TM_UNION) return -1;
  return (size = type_size (c2m_ctx, type)) <= 2 * 8 ? size : -1;
}

#define MAX_FP_TYPES 2

static int small_fp_struct_p (c2m_ctx_t c2m_ctx, struct type *type, int *fp_types_n,
                              MIR_type_t fp_types[MAX_FP_TYPES]) {
  size_t size = type_size (c2m_ctx, type);
  int n_members = 0;
  MIR_type_t subtypes[MAX_FP_TYPES];
  MIR_type_t mir_type;

  if (type->mode != TM_STRUCT) return FALSE;
  for (node_t el = NL_HEAD (NL_EL (type->u.tag_type->u.ops, 1)->u.ops); el != NULL;
       el = NL_NEXT (el))
    if (el->code == N_MEMBER) {
      decl_t decl = el->attr;
      MIR_type_t sub_types[MAX_FP_TYPES];
      int sub_n;

      if (decl->bit_offset >= 0) return FALSE;
      if (decl->decl_spec.type->mode == TM_STRUCT) {
        if (!small_fp_struct_p (c2m_ctx, decl->decl_spec.type, &sub_n, subtypes)) return FALSE;
        if (sub_n + n_members > 2) return FALSE;
        for (int i = 0; i < sub_n; i++) fp_types[n_members + i] = subtypes[i];
        n_members += sub_n;
      } else {
        if (!scalar_type_p (decl->decl_spec.type)) return FALSE;
        if ((mir_type = get_mir_type (c2m_ctx, decl->decl_spec.type)) != MIR_T_F
            && mir_type != MIR_T_D)
          return FALSE;
        if (n_members >= 2) return FALSE;
        fp_types[n_members] = mir_type;
        n_members++;
      }
    }
  *fp_types_n = n_members;
  return TRUE;
}

static void target_add_res_proto (c2m_ctx_t c2m_ctx, struct type *ret_type,
                                  target_arg_info_t *arg_info, VARR (MIR_type_t) * res_types,
                                  VARR (MIR_var_t) * arg_vars) {
  MIR_var_t var;
  int size, n;
  MIR_type_t fp_types[MAX_FP_TYPES];

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0) {
    simple_add_res_proto (c2m_ctx, ret_type, arg_info, res_types, arg_vars);
    return;
  }
  if (size == 0) return;
  if (small_fp_struct_p (c2m_ctx, ret_type, &n, fp_types)) {
    VARR_PUSH (MIR_type_t, res_types, fp_types[0]);
    if (n > 1) VARR_PUSH (MIR_type_t, res_types, fp_types[1]);
  } else {
    VARR_PUSH (MIR_type_t, res_types, MIR_T_I64);
    if (size > 8) VARR_PUSH (MIR_type_t, res_types, MIR_T_I64);
  }
}

static int target_add_call_res_op (c2m_ctx_t c2m_ctx, struct type *ret_type,
                                   target_arg_info_t *arg_info, size_t call_arg_area_offset) {
  gen_ctx_t gen_ctx = c2m_ctx->gen_ctx;
  MIR_context_t ctx = c2m_ctx->ctx;
  MIR_type_t fp_types[MAX_FP_TYPES];
  int size, n;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0)
    return simple_add_call_res_op (c2m_ctx, ret_type, arg_info, call_arg_area_offset);
  if (size == 0) return -1;
  if (small_fp_struct_p (c2m_ctx, ret_type, &n, fp_types)) {
    VARR_PUSH (MIR_op_t, call_ops,
               MIR_new_reg_op (ctx, get_new_temp (c2m_ctx, fp_types[0]).mir_op.u.reg));
    if (n > 1)
      VARR_PUSH (MIR_op_t, call_ops,
                 MIR_new_reg_op (ctx, get_new_temp (c2m_ctx, fp_types[1]).mir_op.u.reg));
    return n;
  } else {
    VARR_PUSH (MIR_op_t, call_ops,
               MIR_new_reg_op (ctx, get_new_temp (c2m_ctx, MIR_T_I64).mir_op.u.reg));
    if (size > 8)
      VARR_PUSH (MIR_op_t, call_ops,
                 MIR_new_reg_op (ctx, get_new_temp (c2m_ctx, MIR_T_I64).mir_op.u.reg));
    return size <= 8 ? 1 : 2;
  }
}

static op_t target_gen_post_call_res_code (c2m_ctx_t c2m_ctx, struct type *ret_type, op_t res,
                                           MIR_insn_t call, size_t call_ops_start) {
  gen_ctx_t gen_ctx = c2m_ctx->gen_ctx;
  MIR_context_t ctx = c2m_ctx->ctx;
  MIR_type_t fp_types[MAX_FP_TYPES];
  MIR_insn_t insn;
  int size, n;

  if (void_type_p (ret_type)) return res;
  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0)
    return simple_gen_post_call_res_code (c2m_ctx, ret_type, res, call, call_ops_start);
  if (size == 0) return res;
  assert (res.mir_op.mode == MIR_OP_MEM);
  if (small_fp_struct_p (c2m_ctx, ret_type, &n, fp_types)) {
    assert (n == 1 || n == 2);
    insn = MIR_new_insn (ctx, tp_mov (fp_types[0]),
                         MIR_new_mem_op (ctx, fp_types[0], res.mir_op.u.mem.disp,
                                         res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                         res.mir_op.u.mem.scale),
                         VARR_GET (MIR_op_t, call_ops, call_ops_start + 2));
    MIR_append_insn (ctx, curr_func, insn);
    if (n > 1) {
      insn = MIR_new_insn (ctx, tp_mov (fp_types[1]),
                           MIR_new_mem_op (ctx, fp_types[1],
                                           res.mir_op.u.mem.disp + (fp_types[0] == MIR_T_F ? 4 : 8),
                                           res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                           res.mir_op.u.mem.scale),
                           VARR_GET (MIR_op_t, call_ops, call_ops_start + 3));
      MIR_append_insn (ctx, curr_func, insn);
    }
  } else {
    gen_multiple_load_store (c2m_ctx, ret_type, &VARR_ADDR (MIR_op_t, call_ops)[call_ops_start + 2],
                             res.mir_op, FALSE);
  }
  return res;
}

static void target_add_ret_ops (c2m_ctx_t c2m_ctx, struct type *ret_type, op_t res) {
  gen_ctx_t gen_ctx = c2m_ctx->gen_ctx;
  MIR_context_t ctx = c2m_ctx->ctx;
  int i, n, size;
  MIR_type_t fp_types[MAX_FP_TYPES];
  MIR_insn_t insn;
  op_t temp;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0) {
    simple_add_ret_ops (c2m_ctx, ret_type, res);
    return;
  }
  if (size == 0) return;
  assert (res.mir_op.mode == MIR_OP_MEM && VARR_LENGTH (MIR_op_t, ret_ops) == 0 && size <= 2 * 8);
  if (small_fp_struct_p (c2m_ctx, ret_type, &n, fp_types)) {
    assert (n == 1 || n == 2);
    temp = get_new_temp (c2m_ctx, fp_types[0]);
    insn = MIR_new_insn (ctx, tp_mov (fp_types[0]), temp.mir_op,
                         MIR_new_mem_op (ctx, fp_types[0], res.mir_op.u.mem.disp,
                                         res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                         res.mir_op.u.mem.scale));
    MIR_append_insn (ctx, curr_func, insn);
    VARR_PUSH (MIR_op_t, ret_ops, temp.mir_op);
    if (n > 1) {
      temp = get_new_temp (c2m_ctx, fp_types[1]);
      insn = MIR_new_insn (ctx, tp_mov (fp_types[1]), temp.mir_op,
                           MIR_new_mem_op (ctx, fp_types[1],
                                           res.mir_op.u.mem.disp + (fp_types[0] == MIR_T_F ? 4 : 8),
                                           res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                           res.mir_op.u.mem.scale));
      MIR_append_insn (ctx, curr_func, insn);
      VARR_PUSH (MIR_op_t, ret_ops, temp.mir_op);
    }
  } else {
    for (i = 0; size > 0; size -= 8, i++)
      VARR_PUSH (MIR_op_t, ret_ops, get_new_temp (c2m_ctx, MIR_T_I64).mir_op);
    gen_multiple_load_store (c2m_ctx, ret_type, VARR_ADDR (MIR_op_t, ret_ops), res.mir_op, TRUE);
  }
}

static MIR_type_t target_get_blk_type (c2m_ctx_t c2m_ctx, struct type *arg_type) {
  int n;
  MIR_type_t float_types[MAX_FP_TYPES];

  assert (arg_type->mode == TM_STRUCT || arg_type->mode == TM_UNION);
  if (!small_fp_struct_p (c2m_ctx, arg_type, &n, float_types) || n == 0) return MIR_T_BLK;
  assert (n == 1 || n == 2);
  if (float_types[0] == MIR_T_F) {
    if (n == 1 || float_types[1] == MIR_T_F) return MIR_T_BLK + 2;
    return MIR_T_BLK + 4;
  } else {
    if (n == 1 || float_types[1] == MIR_T_D) return MIR_T_BLK + 3;
    return MIR_T_BLK + 5;
  }
}

static void target_add_arg_proto (c2m_ctx_t c2m_ctx, const char *name, struct type *arg_type,
                                  target_arg_info_t *arg_info, VARR (MIR_var_t) * arg_vars) {
  MIR_var_t var;
  MIR_type_t type;

  /* pass aggregates on the stack and pass by value for others: */
  var.name = name;
  if (arg_type->mode != TM_STRUCT && arg_type->mode != TM_UNION) {
    type = get_mir_type (c2m_ctx, arg_type);
    var.type = type;
  } else {
    var.type = target_get_blk_type (c2m_ctx, arg_type);
    var.size = type_size (c2m_ctx, arg_type);
  }
  VARR_PUSH (MIR_var_t, arg_vars, var);
}

static void target_add_call_arg_op (c2m_ctx_t c2m_ctx, struct type *arg_type,
                                    target_arg_info_t *arg_info, op_t arg) {
  gen_ctx_t gen_ctx = c2m_ctx->gen_ctx;
  MIR_context_t ctx = c2m_ctx->ctx;
  MIR_type_t type;

  /* pass aggregates on the stack and pass by value for others: */
  if (arg_type->mode != TM_STRUCT && arg_type->mode != TM_UNION) {
    type = get_mir_type (c2m_ctx, arg_type);
    VARR_PUSH (MIR_op_t, call_ops, arg.mir_op);
  } else {
    assert (arg.mir_op.mode == MIR_OP_MEM);
    arg = mem_to_address (c2m_ctx, arg, TRUE);
    type = target_get_blk_type (c2m_ctx, arg_type);
    VARR_PUSH (MIR_op_t, call_ops,
               MIR_new_mem_op (ctx, type, type_size (c2m_ctx, arg_type), arg.mir_op.u.reg, 0, 1));
  }
}

static int target_gen_gather_arg (c2m_ctx_t c2m_ctx, const char *name, struct type *arg_type,
                                  decl_t param_decl, target_arg_info_t *arg_info) {
  return FALSE;
}
