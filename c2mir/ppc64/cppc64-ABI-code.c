/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
   ppc64 call ABI target specific code.
*/

#define CUSTOM_CALL_ABI

typedef int target_arg_info_t;

static void target_init_arg_vars (MIR_context_t ctx, target_arg_info_t *arg_info) {}

static MIR_type_t fp_homogeneous_type (MIR_context_t ctx, struct type *param_type, int *num) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return MIR_T_UNDEF;
#else
  return MIR_T_UNDEF;
#endif
}

static int reg_aggregate_p (c2m_ctx_t c2m_ctx, struct type *ret_type) {
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  return FALSE;
#else
  return type_size (c2m_ctx, ret_type) <= 2 * 8;
#endif
}

static void multiple_load_store (MIR_context_t ctx, struct type *type, MIR_op_t *var_ops,
                                 MIR_op_t mem_op, int load_p) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_op_t op, var_op;
  MIR_insn_t insn;
  int i, sh, size = type_size (c2m_ctx, type);

  if (size == 0) return;
  if (type_align (type) == 8) {
    assert (size % 8 == 0);
    for (i = 0; size > 0; size -= 8, i++) {
      if (load_p) {
        insn = MIR_new_insn (ctx, MIR_MOV, var_ops[i],
                             MIR_new_mem_op (ctx, MIR_T_I64, mem_op.u.mem.disp + i * 8,
                                             mem_op.u.mem.base, mem_op.u.mem.index,
                                             mem_op.u.mem.scale));
      } else {
        insn = MIR_new_insn (ctx, MIR_MOV,
                             MIR_new_mem_op (ctx, MIR_T_I64, mem_op.u.mem.disp + i * 8,
                                             mem_op.u.mem.base, mem_op.u.mem.index,
                                             mem_op.u.mem.scale),
                             var_ops[i]);
      }
      MIR_append_insn (ctx, curr_func, insn);
    }
  } else {
    op = get_new_temp (ctx, MIR_T_I64).mir_op;
    if (load_p) {
      for (i = 0; i < size; i += 8) {
        var_op = var_ops[i / 8];
        insn = MIR_new_insn (ctx, MIR_MOV, var_op, MIR_new_int_op (ctx, 0));
        MIR_append_insn (ctx, curr_func, insn);
      }
    }
    for (i = 0; size > 0; size--, i++) {
      var_op = var_ops[i / 8];
      if (load_p) {
        insn
          = MIR_new_insn (ctx, MIR_MOV, op,
                          MIR_new_mem_op (ctx, MIR_T_U8, mem_op.u.mem.disp + i, mem_op.u.mem.base,
                                          mem_op.u.mem.index, mem_op.u.mem.scale));
        MIR_append_insn (ctx, curr_func, insn);
        if ((sh = i * 8 % 64) != 0) {
          insn = MIR_new_insn (ctx, MIR_LSH, op, op, MIR_new_int_op (ctx, sh));
          MIR_append_insn (ctx, curr_func, insn);
        }
        insn = MIR_new_insn (ctx, MIR_OR, var_op, var_op, op);
        MIR_append_insn (ctx, curr_func, insn);
      } else {
        if ((sh = i * 8 % 64) == 0)
          insn = MIR_new_insn (ctx, MIR_MOV, op, var_op);
        else
          insn = MIR_new_insn (ctx, MIR_URSH, op, var_op, MIR_new_int_op (ctx, sh));
        MIR_append_insn (ctx, curr_func, insn);
        insn
          = MIR_new_insn (ctx, MIR_MOV,
                          MIR_new_mem_op (ctx, MIR_T_U8, mem_op.u.mem.disp + i, mem_op.u.mem.base,
                                          mem_op.u.mem.index, mem_op.u.mem.scale),
                          op);
        MIR_append_insn (ctx, curr_func, insn);
      }
    }
  }
}

static int target_return_by_addr_p (MIR_context_t ctx, struct type *ret_type) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t type;
  int n;

  if (ret_type->mode != TM_STRUCT && ret_type->mode != TM_UNION) return FALSE;
  if (((type = fp_homogeneous_type (ctx, ret_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8)
    return FALSE;
  return !reg_aggregate_p (c2m_ctx, ret_type);
}

static void target_add_res_proto (MIR_context_t ctx, struct type *ret_type,
                                  target_arg_info_t *arg_info, VARR (MIR_type_t) * res_types,
                                  VARR (MIR_var_t) * arg_vars) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_var_t var;
  MIR_type_t type;
  int i, n, size;

  if (void_type_p (ret_type)) return;
  if (((type = fp_homogeneous_type (ctx, ret_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    for (i = 0; i < n; i++) VARR_PUSH (MIR_type_t, res_types, type);
  } else if (ret_type->mode != TM_STRUCT && ret_type->mode != TM_UNION) {
    VARR_PUSH (MIR_type_t, res_types, get_mir_type (ctx, ret_type));
  } else if (reg_aggregate_p (c2m_ctx, ret_type)) {
    size = type_size (c2m_ctx, ret_type);
    for (; size > 0; size -= 8) VARR_PUSH (MIR_type_t, res_types, MIR_T_I64);
  } else {
    var.name = RET_ADDR_NAME;
    var.type = MIR_POINTER_TYPE;
    VARR_PUSH (MIR_var_t, arg_vars, var);
  }
}

static int target_add_call_res_op (MIR_context_t ctx, struct type *ret_type,
                                   target_arg_info_t *arg_info, size_t call_arg_area_offset) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t type;
  op_t temp;
  int i, n, size;

  if (void_type_p (ret_type)) return -1;
  if (((type = fp_homogeneous_type (ctx, ret_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    for (i = 0; i < n; i++) {
      temp = get_new_temp (ctx, type);
      VARR_PUSH (MIR_op_t, call_ops, temp.mir_op);
    }
    return n;
  } else if (ret_type->mode != TM_STRUCT && ret_type->mode != TM_UNION) {
    type = get_mir_type (ctx, ret_type);
    type = promote_mir_int_type (type);
    temp = get_new_temp (ctx, type);
    VARR_PUSH (MIR_op_t, call_ops, temp.mir_op);
    return 1;
  } else if (reg_aggregate_p (c2m_ctx, ret_type)) {
    size = type_size (c2m_ctx, ret_type);
    if (size == 0) return -1;
    for (int s = size; s > 0; s -= 8) {
      temp = get_new_temp (ctx, MIR_T_I64);
      VARR_PUSH (MIR_op_t, call_ops, temp.mir_op);
    }
    return (size + 7) / 8;
  } else {
    temp = get_new_temp (ctx, MIR_T_I64);
    emit3 (ctx, MIR_ADD, temp.mir_op,
           MIR_new_reg_op (ctx, MIR_reg (ctx, FP_NAME, curr_func->u.func)),
           MIR_new_int_op (ctx, call_arg_area_offset));
    VARR_PUSH (MIR_op_t, call_ops, temp.mir_op);
    return 0;
  }
}

static op_t target_gen_post_call_res_code (MIR_context_t ctx, struct type *ret_type, op_t res,
                                           MIR_insn_t call, size_t call_ops_start) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t type;
  MIR_insn_t insn;
  int i, n;

  if (void_type_p (ret_type)) return res;
  if (((type = fp_homogeneous_type (ctx, ret_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    assert (res.mir_op.mode == MIR_OP_REG); /* addr */
    for (i = 0; i < n; i++) {
      assert (res.mir_op.mode == MIR_OP_MEM);
      //      res.mir_op = MIR_new_mem_op (ctx, MIR_T_UNDEF, 0, res.mir_op.u.reg, 0, 1);
      insn = MIR_new_insn (ctx, tp_mov (type),
                           MIR_new_mem_op (ctx, type,
                                           res.mir_op.u.mem.disp + (type == MIR_T_F ? 4 : 8) * i,
                                           res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                           res.mir_op.u.mem.scale),
                           VARR_GET (MIR_op_t, call_ops, i + call_ops_start + 2));
      MIR_append_insn (ctx, curr_func, insn);
    }
  } else if ((ret_type->mode == TM_STRUCT || ret_type->mode == TM_UNION)
             && reg_aggregate_p (c2m_ctx, ret_type)) {
    assert (res.mir_op.mode == MIR_OP_MEM); /* addr */
    multiple_load_store (ctx, ret_type, &VARR_ADDR (MIR_op_t, call_ops)[call_ops_start + 2],
                         res.mir_op, FALSE);
  }
  return res;
}

static void target_add_ret_ops (MIR_context_t ctx, struct type *ret_type, op_t res) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t type;
  MIR_insn_t insn;
  MIR_reg_t ret_addr_reg;
  op_t temp, var;
  int i, n, size;

  if (void_type_p (ret_type)) return;
  if (((type = fp_homogeneous_type (ctx, ret_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    assert (res.mir_op.mode == MIR_OP_MEM);
    for (int i = 0; i < n; i++) {
      temp = get_new_temp (ctx, type);
      insn = MIR_new_insn (ctx, tp_mov (type), temp.mir_op,
                           MIR_new_mem_op (ctx, type,
                                           res.mir_op.u.mem.disp + (type == MIR_T_F ? 4 : 8) * i,
                                           res.mir_op.u.mem.base, res.mir_op.u.mem.index,
                                           res.mir_op.u.mem.scale));
      MIR_append_insn (ctx, curr_func, insn);
      VARR_PUSH (MIR_op_t, ret_ops, temp.mir_op);
    }
  } else if (ret_type->mode != TM_STRUCT && ret_type->mode != TM_UNION) {
    VARR_PUSH (MIR_op_t, ret_ops, res.mir_op);
  } else if (reg_aggregate_p (c2m_ctx, ret_type)) {
    size = type_size (c2m_ctx, ret_type);
    assert (res.mir_op.mode == MIR_OP_MEM && VARR_LENGTH (MIR_op_t, ret_ops) == 0);
    for (int i = 0; size > 0; size -= 8, i++)
      VARR_PUSH (MIR_op_t, ret_ops, get_new_temp (ctx, MIR_T_I64).mir_op);
    multiple_load_store (ctx, ret_type, &VARR_ADDR (MIR_op_t, ret_ops)[0], res.mir_op, TRUE);
  } else {
    ret_addr_reg = MIR_reg (ctx, RET_ADDR_NAME, curr_func->u.func);
    var = new_op (NULL, MIR_new_mem_op (ctx, MIR_T_I8, 0, ret_addr_reg, 0, 1));
    size = type_size (c2m_ctx, ret_type);
    block_move (ctx, var, res, size);
  }
}

static void target_add_arg_proto (MIR_context_t ctx, const char *name, struct type *arg_type,
                                  target_arg_info_t *arg_info, VARR (MIR_var_t) * arg_vars) {
  MIR_var_t var;
  MIR_type_t type;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  int n;

  if (((type = fp_homogeneous_type (ctx, arg_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    for (int i = 0; i < n; i++) {
      var.name = name;
      var.type = type;
      VARR_PUSH (MIR_var_t, arg_vars, var);
    }
    return;
  }
  type = (arg_type->mode == TM_STRUCT || arg_type->mode == TM_UNION ? MIR_T_BLK
                                                                    : get_mir_type (ctx, arg_type));
  var.name = name;
  var.type = type;
  if (type == MIR_T_BLK) var.size = type_size (c2m_ctx, arg_type);
  VARR_PUSH (MIR_var_t, arg_vars, var);
}

static void target_add_call_arg_op (MIR_context_t ctx, struct type *arg_type,
                                    target_arg_info_t *arg_info, op_t arg) {
  MIR_var_t var;
  MIR_type_t type;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  op_t temp;
  int n;

  if (((type = fp_homogeneous_type (ctx, arg_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    for (int i = 0; i < n; i++) {
      assert (arg.mir_op.mode == MIR_OP_REG);
      temp = get_new_temp (ctx, type);
      MIR_append_insn (ctx, curr_func,
                       MIR_new_insn (ctx, tp_mov (type), temp.mir_op,
                                     MIR_new_mem_op (ctx, type, (type == MIR_T_F ? 4 : 8) * i,
                                                     arg.mir_op.u.reg, 0, 1)));
      VARR_PUSH (MIR_op_t, call_ops, temp.mir_op);
    }
    return;
  }
  if (arg_type->mode != TM_STRUCT && arg_type->mode != TM_UNION) {
    VARR_PUSH (MIR_op_t, call_ops, arg.mir_op);
  } else {
    assert (arg.mir_op.mode == MIR_OP_MEM);
    arg = mem_to_address (ctx, arg, TRUE);
    VARR_PUSH (MIR_op_t, call_ops,
               MIR_new_mem_op (ctx, MIR_T_BLK, type_size (c2m_ctx, arg_type), arg.mir_op.u.reg, 0,
                               1));
  }
}

static int target_gen_gather_arg (MIR_context_t ctx, const char *name, struct type *arg_type,
                                  decl_t param_decl, target_arg_info_t *arg_info) {
  MIR_var_t var;
  MIR_type_t type;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  reg_var_t reg_var;
  int i, n;

  if (((type = fp_homogeneous_type (ctx, arg_type, &n)) == MIR_T_F || type == MIR_T_D) && n <= 8) {
    for (i = 0; i < n; i++) {
      assert (!param_decl->reg_p);
      reg_var = get_reg_var (ctx, type, name);
      MIR_append_insn (ctx, curr_func,
                       MIR_new_insn (ctx, tp_mov (type), MIR_new_reg_op (ctx, reg_var.reg),
                                     MIR_new_mem_op (ctx, type,
                                                     param_decl->offset
                                                       + (type == MIR_T_F ? 4 : 8) * i,
                                                     MIR_reg (ctx, FP_NAME, curr_func->u.func), 0,
                                                     1)));
    }
    return TRUE;
  }
  return FALSE;
}
