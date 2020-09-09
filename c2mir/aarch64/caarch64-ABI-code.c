/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
   aarch64 call ABI target specific code.
*/

typedef struct target_arg_info {
  int n_iregs;
} target_arg_info_t;

static void target_init_arg_vars (MIR_context_t ctx, target_arg_info_t *arg_info) {
  arg_info->n_iregs = 0;
}

static int target_return_by_addr_p (MIR_context_t ctx, struct type *ret_type) {
  return ((ret_type->mode == TM_STRUCT || ret_type->mode == TM_UNION)
	  && type_size (*c2m_ctx_loc (ctx), ret_type) > 2 * 8);
}

static const char *RET_AGGR_NAME = "Ret_Aggr";
static const char *RET_AGGR2_NAME = "Ret_Aggr2";

static int reg_aggregate_size (c2m_ctx_t c2m_ctx, struct type *type) {
  int size;

  if (type->mode != TM_STRUCT && type->mode != TM_UNION) return -1;
  return (size = type_size (c2m_ctx, type)) <= 2 * 8 ? size : -1;
}

static void target_add_res_proto (MIR_context_t ctx, struct type *ret_type,
                                  target_arg_info_t *arg_info, VARR (MIR_type_t) * res_types,
                                  VARR (MIR_var_t) * arg_vars) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_var_t var;
  int size;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0) {
    simple_add_res_proto (ctx, ret_type, arg_info, res_types, arg_vars);
    return;
  }
  if (size == 0) return;
  VARR_PUSH (MIR_type_t, res_types, MIR_T_I64);
  if (size > 8) VARR_PUSH (MIR_type_t, res_types, MIR_T_I64);
}

static int target_add_call_res_op (MIR_context_t ctx, struct type *ret_type,
                                   target_arg_info_t *arg_info, size_t call_arg_area_offset) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  int size;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0)
    return simple_add_call_res_op (ctx, ret_type, arg_info, call_arg_area_offset);
  if (size == 0) return -1;
  VARR_PUSH (MIR_op_t, call_ops, MIR_new_reg_op (ctx, get_new_temp (ctx, MIR_T_I64).mir_op.u.reg));
  if (size > 8)
    VARR_PUSH (MIR_op_t, call_ops, MIR_new_reg_op (ctx, get_new_temp (ctx, MIR_T_I64).mir_op.u.reg));
  return size <= 8 ? 1 : 2;
}

static op_t target_gen_post_call_res_code (MIR_context_t ctx, struct type *ret_type, op_t res,
                                           MIR_insn_t call, size_t call_ops_start) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  int size;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0)
    return simple_gen_post_call_res_code (ctx, ret_type, res, call, call_ops_start);
  if (size != 0)
    multiple_load_store (ctx, ret_type, &VARR_ADDR (MIR_op_t, call_ops)[call_ops_start + 2],
			 res.mir_op, FALSE);
  return res;
}

static void target_add_ret_ops (MIR_context_t ctx, struct type *ret_type, op_t res) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  int i, size;

  if ((size = reg_aggregate_size (c2m_ctx, ret_type)) < 0) {
    simple_add_ret_ops (ctx, ret_type, res);
    return;
  }
  assert (res.mir_op.mode == MIR_OP_MEM && VARR_LENGTH (MIR_op_t, ret_ops) == 0 && size <= 2 * 8);
  for (i = 0; size > 0; size -= 8, i++)
    VARR_PUSH (MIR_op_t, ret_ops, get_new_temp (ctx, MIR_T_I64).mir_op);
  multiple_load_store (ctx, ret_type, VARR_ADDR (MIR_op_t, ret_ops), res.mir_op, TRUE);
}

static const char *get_indexed_name (MIR_context_t ctx, const char *name, int index) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);

  assert (index >= 0 && index <= 9);
  VARR_TRUNC (char, temp_string, 0);
  VARR_PUSH_ARR (char, temp_string, name, strlen (name));
  VARR_PUSH (char, temp_string, '#');
  VARR_PUSH (char, temp_string, '0' + index);
  VARR_PUSH (char, temp_string,'\0');
  return _MIR_uniq_string (ctx, VARR_ADDR (char, temp_string));
}

static void target_add_arg_proto (MIR_context_t ctx, const char *name, struct type *arg_type,
                                  target_arg_info_t *arg_info, VARR (MIR_var_t) * arg_vars) {
  MIR_var_t var;
  MIR_type_t type;
  int i, size;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);

  if ((size = reg_aggregate_size (c2m_ctx, arg_type)) < 0) {
    simple_add_arg_proto (ctx, name, arg_type, arg_info, arg_vars);
    return;
  }
  assert (size <= 2 * 8);
  for (i = 0; size > 0; size -= 8, i++) {
    var.name = get_indexed_name (ctx, name, i);
    var.type = MIR_T_I64;
    VARR_PUSH (MIR_var_t, arg_vars, var);
  }
}

static void target_add_call_arg_op (MIR_context_t ctx, struct type *arg_type,
                                    target_arg_info_t *arg_info, op_t arg) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  int i, size;
  MIR_op_t ops[2];

  if ((size = reg_aggregate_size (c2m_ctx, arg_type)) < 0) {
    simple_add_call_arg_op (ctx, arg_type, arg_info, arg);
    return;
  }
  assert (size <= 2 * 8);
  for (i = 0; size > 0; size -= 8, i++) {
    ops[i] = get_new_temp (ctx, MIR_T_I64).mir_op;
    VARR_PUSH (MIR_op_t, call_ops, ops[i]);
  }
  multiple_load_store (ctx, arg_type, ops, arg.mir_op, TRUE);
}

static int target_gen_gather_arg (MIR_context_t ctx, const char *name, struct type *arg_type,
                                  decl_t param_decl, target_arg_info_t *arg_info) {
  MIR_type_t type;
  MIR_op_t param_ops[2];
  int i, size;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  reg_var_t reg_var;

  if ((size = reg_aggregate_size (c2m_ctx, arg_type)) < 0)
    return FALSE;
  assert (!param_decl->reg_p && size <= 2 * 8);
  for (i = 0; size > 0; size -= 8, i++) {
    reg_var = get_reg_var (ctx, MIR_T_I64, get_indexed_name (ctx, name, i));
    param_ops[i] = MIR_new_reg_op (ctx, reg_var.reg);
  }
  multiple_load_store (ctx, arg_type, param_ops,
                       MIR_new_mem_op (ctx, MIR_T_UNDEF, param_decl->offset,
                                       MIR_reg (ctx, FP_NAME, curr_func->u.func), 0, 1),
                       FALSE);
  return TRUE;
}
