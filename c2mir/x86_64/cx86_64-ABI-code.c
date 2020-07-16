/* This file is a part of MIR project.
   Copyright (C) 2018-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
   x86_64 ABI target specific code.
*/

#define ATYPICAL_CALL_ABI

/* See https://github.com/hjl-tools/x86-psABI/wiki/x86-64-psABI-1.0.pdf.  We use MIR_T_UNDEF for
   MEMORY. */

enum { NO_CLASS = MIR_T_BOUND + 1, X87UP_CLASS };

#define MAX_QWORDS 8

static MIR_type_t get_result_type (MIR_type_t arg_type1, MIR_type_t arg_type2) {
  if (arg_type1 == arg_type2) return arg_type1;
  if (arg_type1 == NO_CLASS) return arg_type2;
  if (arg_type2 == NO_CLASS) return arg_type1;

  if (arg_type1 == MIR_T_UNDEF || arg_type2 == MIR_T_UNDEF) return MIR_T_UNDEF;

  if ((arg_type1 == MIR_T_I32 && arg_type2 == MIR_T_F)
      || (arg_type2 == MIR_T_I32 && arg_type1 == MIR_T_F))
    return MIR_T_I32;
  if (arg_type1 == MIR_T_I64 || arg_type1 == MIR_T_I32 || arg_type2 == MIR_T_I64
      || arg_type2 == MIR_T_I32)
    return MIR_T_I64;

  if (arg_type1 == MIR_T_LD || arg_type2 == MIR_T_LD || arg_type1 == X87UP_CLASS
      || arg_type2 == X87UP_CLASS)
    return MIR_T_UNDEF;

  return MIR_T_D;
}

static int classify_arg (MIR_context_t ctx, struct type *type, MIR_type_t types[MAX_QWORDS],
                         mir_size_t offset, int bit_field_p) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  size_t size = type_size (c2m_ctx, type);
  int i, n_el_qwords, n_qwords = (size + 7) / 8;
  MIR_type_t mir_type;

  if (type->mode == TM_STRUCT || type->mode == TM_UNION || type->mode == TM_STRUCT) {
    MIR_type_t subtypes[MAX_QWORDS];

    if (n_qwords > 8) return 0; /* too big aggregate */

    for (i = 0; i < n_qwords; i++) types[i] = NO_CLASS;

    switch (type->mode) {
    case TM_ARR: { /* Arrays are handled as small records.  */
      n_el_qwords = classify_arg (ctx, type->u.arr_type->el_type, subtypes, 0, FALSE);
      if (n_el_qwords == 0) return 0;
      /* make full types: */
      if (subtypes[0] == MIR_T_F && size != 4) subtypes[0] = MIR_T_D;
      if (subtypes[0] == MIR_T_I32 && (bit_field_p || size != 4)) subtypes[0] = MIR_T_I64;
      for (i = 0; i < n_qwords; i++) types[i] = subtypes[i % n_el_qwords];

      break;
    }
    case TM_STRUCT:
    case TM_UNION:
      for (node_t el = NL_HEAD (NL_EL (type->u.tag_type->ops, 1)->ops); el != NULL;
           el = NL_NEXT (el))
        if (el->code == N_MEMBER) {
          decl_t decl = el->attr;
          int start_qword = (offset + decl->offset) / 8;

          if (decl->bit_offset >= 0) {
            types[start_qword] = get_result_type (MIR_T_I64, types[start_qword]);
          } else {
            n_el_qwords = classify_arg (ctx, decl->decl_spec.type, subtypes,
                                        offset + (type->mode == TM_STRUCT ? decl->offset : 0),
                                        decl->bit_offset >= 0);
            if (n_el_qwords == 0) return 0;
            for (i = 0; i < n_el_qwords && (i + start_qword) < n_qwords; i++)
              types[i + start_qword] = get_result_type (subtypes[i], types[i + start_qword]);
          }
        }
      break;
    default: assert (FALSE);
    }

    if (n_qwords > 2) return 0; /* as we don't have vector values (see SSEUP_CLASS) */

    for (i = 0; i < n_qwords; i++) {
      if (types[i] == MIR_T_UNDEF) return 0; /* pass in memory if a word class is memory.  */
      if (types[i] == X87UP_CLASS && (i == 0 || types[i - 1] != MIR_T_LD)) return 0;
    }
    return n_qwords;
  }

  assert (scalar_type_p (type));
  switch (mir_type = get_mir_type (ctx, type)) {
  case MIR_T_F: types[0] = offset % 8 != 0 ? MIR_T_D : MIR_T_F; return 1;
  case MIR_T_D: types[0] = MIR_T_D; return 1;
  case MIR_T_LD:
    types[0] = MIR_T_LD;
    types[1] = X87UP_CLASS;
    return 2;
  default:
    if (!bit_field_p && offset % 8 + size <= 4) {
      types[0] = MIR_T_I32;
    } else {
      assert (size <= 8);
      types[0] = MIR_T_I64;
    }
    return 1;
  }
}

typedef struct target_arg_info {
  int n_iregs, n_fregs;
} target_arg_info_t;

static void target_init_arg_vars (MIR_context_t ctx, target_arg_info_t *arg_info) {
  arg_info->n_iregs = arg_info->n_fregs = 0;
}

static const char *qword_name (MIR_context_t ctx, const char *name, int num) {
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  char prefix[50];

  sprintf (prefix, "Q%u_", num);
  VARR_TRUNC (char, temp_string, 0);
  add_to_temp_string (c2m_ctx, prefix);
  add_to_temp_string (c2m_ctx, name);
  return uniq_cstr (c2m_ctx, VARR_ADDR (char, temp_string)).s;
}

static void target_add_res (MIR_context_t ctx, struct func_type *func_type,
                            target_arg_info_t *arg_info) {
  MIR_var_t var;
  MIR_type_t type;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t qword_types[MAX_QWORDS];
  int n_iregs, n_fregs, n_stregs, n, n_qwords, curr;

  if (void_type_p (func_type->ret_type)) return;
  n_qwords = classify_arg (ctx, func_type->ret_type, qword_types, 0, FALSE);
  if (n_qwords != 0) {
    n_iregs = n_fregs = n_stregs = curr = 0;
    for (n = 0; n < n_qwords; n++) { /* start from the last qword */
      type = qword_types[n];
      qword_types[curr++] = type;
      switch (type) {
      case MIR_T_I32:
      case MIR_T_I64: n_iregs++; break;
      case MIR_T_F:
      case MIR_T_D: n_fregs++; break;
      case MIR_T_LD: n_stregs++; break;
      case X87UP_CLASS:
        n_qwords--;
        curr--;
        break;
      case NO_CLASS:
      case MIR_T_UNDEF: assert (FALSE);
      }
    }
    if (n_iregs > 2 || n_fregs > 2 || n_stregs > 1) {
      n_qwords = 0;
    }
  }

  proto_info.res_ref_p = FALSE;
  if (n_qwords == 0) { /* return by reference */
    var.name = RET_ADDR_NAME;
    var.type = MIR_POINTER_TYPE;
    VARR_PUSH (MIR_var_t, proto_info.arg_vars, var);
    proto_info.res_ref_p = TRUE;
    arg_info->n_iregs++;
    return;
  } else {
    for (n = 0; n < n_qwords; n++) VARR_PUSH (MIR_type_t, proto_info.ret_types, qword_types[n]);
  }
}

static void target_add_param (MIR_context_t ctx, const char *name, struct type *param_type,
                              decl_t param_decl, target_arg_info_t *arg_info) {
  MIR_var_t var;
  MIR_type_t type;
  c2m_ctx_t c2m_ctx = *c2m_ctx_loc (ctx);
  MIR_type_t qword_types[MAX_QWORDS];
  int n_iregs, n_fregs, n;
  int n_qwords = classify_arg (ctx, param_type, qword_types, 0, FALSE);

  if (n_qwords != 0) {
    n_iregs = n_fregs = 0;
    for (n = 0; n < n_qwords; n++) { /* start from the last qword */
      switch ((type = qword_types[n])) {
      case MIR_T_I32:
      case MIR_T_I64: n_iregs++; break;
      case MIR_T_F:
      case MIR_T_D: n_fregs++; break;
      case X87UP_CLASS:
      case MIR_T_LD: n_qwords = 0; goto pass_by_ref;
      case NO_CLASS:
      case MIR_T_UNDEF: assert (FALSE);
      }
    }
    if (arg_info->n_iregs + n_iregs > 6 || arg_info->n_fregs + n_fregs > 8) {
      n_qwords = 0;
    } else { /* aggregate passed by value: */
      arg_info->n_iregs += n_iregs;
      arg_info->n_fregs += n_fregs;
      if (param_decl != NULL) {
        param_decl->param_args_num = n_iregs + n_fregs;
        param_decl->param_args_start = VARR_LENGTH (MIR_var_t, proto_info.arg_vars);
      }
      for (n = 0; n < n_qwords; n++) {
        var.name = qword_name (ctx, name, n);
        var.type = qword_types[n];
        VARR_PUSH (MIR_var_t, proto_info.arg_vars, var);
      }
    }
  }
pass_by_ref:
  if (n_qwords == 0) { /* pass by ref for aggregates and pass by value for others: */
    type = (param_type->mode == TM_STRUCT || param_type->mode == TM_UNION
              ? MIR_POINTER_TYPE
              : get_mir_type (ctx, param_type));
    var.name = name;
    var.type = type;
    VARR_PUSH (MIR_var_t, proto_info.arg_vars, var);
    if (type == MIR_T_F || type == MIR_T_D)
      arg_info->n_fregs += n_fregs;
    else if (type != MIR_T_LD)
      arg_info->n_iregs += n_iregs;
  }
}
