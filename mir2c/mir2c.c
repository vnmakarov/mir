/* This file is a part of MIR project.
   Copyright (C) 2018-2021 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#include "mir2c.h"
#include <float.h>
#include <inttypes.h>

static MIR_func_t curr_func;

static void out_type (FILE *f, MIR_type_t t) {
  switch (t) {
  case MIR_T_I8: fprintf (f, "int8_t"); break;
  case MIR_T_U8: fprintf (f, "uint8_t"); break;
  case MIR_T_I16: fprintf (f, "int16_t"); break;
  case MIR_T_U16: fprintf (f, "uint16_t"); break;
  case MIR_T_I32: fprintf (f, "int32_t"); break;
  case MIR_T_U32: fprintf (f, "uint32_t"); break;
  case MIR_T_I64: fprintf (f, "int64_t"); break;
  case MIR_T_U64: fprintf (f, "uint64_t"); break;
  case MIR_T_F: fprintf (f, "float"); break;
  case MIR_T_D: fprintf (f, "double"); break;
  case MIR_T_LD: fprintf (f, "long double"); break;
  case MIR_T_P: fprintf (f, "void *"); break;
  default: mir_assert (FALSE);
  }
}

static void out_op (MIR_context_t ctx, FILE *f, MIR_op_t op) {
  switch (op.mode) {
  case MIR_OP_REG: fprintf (f, "%s", MIR_reg_name (ctx, op.u.reg, curr_func)); break;
  case MIR_OP_INT: fprintf (f, "%" PRId64, op.u.i); break;
  case MIR_OP_UINT: fprintf (f, "%" PRIu64, op.u.u); break;
  case MIR_OP_FLOAT: fprintf (f, "%#.*gf", FLT_MANT_DIG, op.u.f); break;
  case MIR_OP_DOUBLE: fprintf (f, "%#.*g", DBL_MANT_DIG, op.u.d); break;
  case MIR_OP_LDOUBLE: fprintf (f, "%#.*lgl", LDBL_MANT_DIG, op.u.d); break;
  case MIR_OP_REF: fprintf (f, "%s", MIR_item_name (ctx, op.u.ref)); break;
  case MIR_OP_MEM: {
    MIR_reg_t no_reg = 0;
    int disp_p = FALSE;

    fprintf (f, "*(");
    out_type (f, op.u.mem.type);
    fprintf (f, "*) (");
    if (op.u.mem.disp != 0 || (op.u.mem.base == no_reg && op.u.mem.index == no_reg)) {
      fprintf (f, "%" PRId64, op.u.mem.disp);
      disp_p = TRUE;
    }
    if (op.u.mem.base != no_reg || op.u.mem.index != no_reg) {
      if (disp_p) fprintf (f, " + ");
      if (op.u.mem.base != no_reg) fprintf (f, "%s", MIR_reg_name (ctx, op.u.mem.base, curr_func));
      if (op.u.mem.index != no_reg) {
        if (op.u.mem.base != no_reg) fprintf (f, " + ");
        fprintf (f, "%s", MIR_reg_name (ctx, op.u.mem.index, curr_func));
        if (op.u.mem.scale != 1) fprintf (f, " * %u", op.u.mem.scale);
      }
    }
    fprintf (f, ")");
    break;
  }
  case MIR_OP_LABEL:
    mir_assert (op.u.label->ops[0].mode == MIR_OP_INT);
    fprintf (f, "l%" PRId64, op.u.label->ops[0].u.i);
    break;
  default: mir_assert (FALSE);
  }
}

static void out_op2 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = ");
  if (str != NULL) fprintf (f, "%s ", str);
  out_op (ctx, f, ops[1]);
  fprintf (f, ";\n");
}

static void out_op3 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = (int64_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (int64_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ";\n");
}

static void out_uop3 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = (uint64_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (uint64_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ";\n");
}

static void out_sop3 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = (int32_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (int32_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ";\n");
}

static void out_usop3 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = (uint32_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (uint32_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ";\n");
}

static void out_jmp (MIR_context_t ctx, FILE *f, MIR_op_t label_op) {
  mir_assert (label_op.mode == MIR_OP_LABEL);
  fprintf (f, "goto ");
  out_op (ctx, f, label_op);
  fprintf (f, ";\n");
}

static void out_bcmp (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  fprintf (f, "if ((int64_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (int64_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ") ");
  out_jmp (ctx, f, ops[0]);
}

static void out_bucmp (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  fprintf (f, "if ((uint64_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (uint64_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ") ");
  out_jmp (ctx, f, ops[0]);
}

static void out_bscmp (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  fprintf (f, "if ((int32_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (int32_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ") ");
  out_jmp (ctx, f, ops[0]);
}

static void out_buscmp (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  fprintf (f, "if ((uint32_t) ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s (uint32_t) ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ") ");
  out_jmp (ctx, f, ops[0]);
}

static void out_fop3 (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  out_op (ctx, f, ops[0]);
  fprintf (f, " = ");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ";\n");
}

static void out_bfcmp (MIR_context_t ctx, FILE *f, MIR_op_t *ops, const char *str) {
  fprintf (f, "if (");
  out_op (ctx, f, ops[1]);
  fprintf (f, " %s ", str);
  out_op (ctx, f, ops[2]);
  fprintf (f, ") ");
  out_jmp (ctx, f, ops[0]);
}

static void out_insn (MIR_context_t ctx, FILE *f, MIR_insn_t insn) {
  MIR_op_t *ops = insn->ops;

  if (insn->code != MIR_LABEL) fprintf (f, "  ");
  switch (insn->code) {
  case MIR_MOV:
  case MIR_FMOV:
  case MIR_DMOV: out_op2 (ctx, f, ops, NULL); break;
  case MIR_EXT8: out_op2 (ctx, f, ops, "(int64_t) (int8_t)"); break;
  case MIR_EXT16: out_op2 (ctx, f, ops, "(int64_t) (int16_t)"); break;
  case MIR_EXT32: out_op2 (ctx, f, ops, "(int64_t) (int32_t)"); break;
  case MIR_UEXT8: out_op2 (ctx, f, ops, "(int64_t) (uint8_t)"); break;
  case MIR_UEXT16: out_op2 (ctx, f, ops, "(int64_t) (uint16_t)"); break;
  case MIR_UEXT32: out_op2 (ctx, f, ops, "(int64_t) (uint32_t)"); break;
  case MIR_F2I:
  case MIR_D2I:
  case MIR_LD2I: out_op2 (ctx, f, ops, "(int64_t)"); break;
  case MIR_I2D:
  case MIR_F2D:
  case MIR_LD2D: out_op2 (ctx, f, ops, "(double)"); break;
  case MIR_I2F:
  case MIR_D2F:
  case MIR_LD2F: out_op2 (ctx, f, ops, "(float)"); break;
  case MIR_I2LD:
  case MIR_D2LD:
  case MIR_F2LD: out_op2 (ctx, f, ops, "(long double)"); break;
  case MIR_UI2D: out_op2 (ctx, f, ops, "(double) (uint64_t)"); break;
  case MIR_UI2F: out_op2 (ctx, f, ops, "(float) (uint64_t)"); break;
  case MIR_UI2LD: out_op2 (ctx, f, ops, "(long double) (uint64_t)"); break;
  case MIR_NEG: out_op2 (ctx, f, ops, "- (int64_t)"); break;
  case MIR_NEGS: out_op2 (ctx, f, ops, "- (int32_t)"); break;
  case MIR_FNEG:
  case MIR_DNEG:
  case MIR_LDNEG: out_op2 (ctx, f, ops, "-"); break;
  case MIR_ADD: out_op3 (ctx, f, ops, "+"); break;
  case MIR_SUB: out_op3 (ctx, f, ops, "-"); break;
  case MIR_MUL: out_op3 (ctx, f, ops, "*"); break;
  case MIR_DIV: out_op3 (ctx, f, ops, "/"); break;
  case MIR_MOD: out_op3 (ctx, f, ops, "%"); break;
  case MIR_UDIV: out_uop3 (ctx, f, ops, "/"); break;
  case MIR_UMOD: out_uop3 (ctx, f, ops, "%"); break;
  case MIR_ADDS: out_sop3 (ctx, f, ops, "+"); break;
  case MIR_SUBS: out_sop3 (ctx, f, ops, "-"); break;
  case MIR_MULS: out_sop3 (ctx, f, ops, "*"); break;
  case MIR_DIVS: out_sop3 (ctx, f, ops, "/"); break;
  case MIR_MODS: out_sop3 (ctx, f, ops, "%"); break;
  case MIR_UDIVS: out_usop3 (ctx, f, ops, "/"); break;
  case MIR_UMODS: out_usop3 (ctx, f, ops, "%"); break;
  case MIR_FADD:
  case MIR_DADD:
  case MIR_LDADD: out_fop3 (ctx, f, ops, "+"); break;
  case MIR_FSUB:
  case MIR_DSUB:
  case MIR_LDSUB: out_fop3 (ctx, f, ops, "-"); break;
  case MIR_FMUL:
  case MIR_DMUL:
  case MIR_LDMUL: out_fop3 (ctx, f, ops, "*"); break;
  case MIR_FDIV:
  case MIR_DDIV:
  case MIR_LDDIV: out_fop3 (ctx, f, ops, "/"); break;
  case MIR_AND: out_op3 (ctx, f, ops, "&"); break;
  case MIR_OR: out_op3 (ctx, f, ops, "|"); break;
  case MIR_XOR: out_op3 (ctx, f, ops, "^"); break;
  case MIR_ANDS: out_sop3 (ctx, f, ops, "&"); break;
  case MIR_ORS: out_sop3 (ctx, f, ops, "|"); break;
  case MIR_XORS: out_sop3 (ctx, f, ops, "^"); break;
  case MIR_LSH: out_op3 (ctx, f, ops, "<<"); break;
  case MIR_RSH: out_op3 (ctx, f, ops, ">>"); break;
  case MIR_URSH: out_uop3 (ctx, f, ops, ">>"); break;
  case MIR_LSHS: out_sop3 (ctx, f, ops, "<<"); break;
  case MIR_RSHS: out_sop3 (ctx, f, ops, ">>"); break;
  case MIR_URSHS: out_usop3 (ctx, f, ops, ">>"); break;
  case MIR_EQ: out_op3 (ctx, f, ops, "=="); break;
  case MIR_NE: out_op3 (ctx, f, ops, "!="); break;
  case MIR_LT: out_op3 (ctx, f, ops, "<"); break;
  case MIR_LE: out_op3 (ctx, f, ops, "<="); break;
  case MIR_GT: out_op3 (ctx, f, ops, ">"); break;
  case MIR_GE: out_op3 (ctx, f, ops, ">="); break;
  case MIR_EQS: out_sop3 (ctx, f, ops, "=="); break;
  case MIR_NES: out_sop3 (ctx, f, ops, "!="); break;
  case MIR_LTS: out_sop3 (ctx, f, ops, "<"); break;
  case MIR_LES: out_sop3 (ctx, f, ops, "<="); break;
  case MIR_GTS: out_sop3 (ctx, f, ops, ">"); break;
  case MIR_GES: out_sop3 (ctx, f, ops, ">="); break;
  case MIR_ULT: out_uop3 (ctx, f, ops, "<"); break;
  case MIR_ULE: out_uop3 (ctx, f, ops, "<="); break;
  case MIR_UGT: out_uop3 (ctx, f, ops, ">"); break;
  case MIR_UGE: out_uop3 (ctx, f, ops, ">"); break;
  case MIR_ULTS: out_usop3 (ctx, f, ops, "<"); break;
  case MIR_ULES: out_usop3 (ctx, f, ops, "<="); break;
  case MIR_UGTS: out_usop3 (ctx, f, ops, ">"); break;
  case MIR_UGES: out_usop3 (ctx, f, ops, ">="); break;
  case MIR_FEQ:
  case MIR_DEQ:
  case MIR_LDEQ: out_fop3 (ctx, f, ops, "=="); break;
  case MIR_FNE:
  case MIR_DNE:
  case MIR_LDNE: out_fop3 (ctx, f, ops, "!="); break;
  case MIR_FLT:
  case MIR_DLT:
  case MIR_LDLT: out_fop3 (ctx, f, ops, "<"); break;
  case MIR_FLE:
  case MIR_DLE:
  case MIR_LDLE: out_fop3 (ctx, f, ops, "<="); break;
  case MIR_FGT:
  case MIR_DGT:
  case MIR_LDGT: out_fop3 (ctx, f, ops, ">"); break;
  case MIR_FGE:
  case MIR_DGE:
  case MIR_LDGE: out_fop3 (ctx, f, ops, ">="); break;
  case MIR_JMP: out_jmp (ctx, f, ops[0]); break;
  case MIR_BT:
    fprintf (f, "if ((int64_t) ");
    out_op (ctx, f, ops[1]);
    fprintf (f, ") ");
    out_jmp (ctx, f, ops[0]);
    break;
  case MIR_BF:
    fprintf (f, "if (! (int64_t) ");
    out_op (ctx, f, ops[1]);
    fprintf (f, ") ");
    out_jmp (ctx, f, ops[0]);
    break;
    /* ??? case MIR_BTS: case MIR_BFS: */
  case MIR_BEQ: out_bcmp (ctx, f, ops, "=="); break;
  case MIR_BNE: out_bcmp (ctx, f, ops, "!="); break;
  case MIR_BLT: out_bcmp (ctx, f, ops, "<"); break;
  case MIR_BLE: out_bcmp (ctx, f, ops, "<="); break;
  case MIR_BGT: out_bcmp (ctx, f, ops, ">"); break;
  case MIR_BGE: out_bcmp (ctx, f, ops, ">="); break;
  case MIR_BEQS: out_bscmp (ctx, f, ops, "=="); break;
  case MIR_BNES: out_bscmp (ctx, f, ops, "!="); break;
  case MIR_BLTS: out_bscmp (ctx, f, ops, "<"); break;
  case MIR_BLES: out_bscmp (ctx, f, ops, "<="); break;
  case MIR_BGTS: out_bscmp (ctx, f, ops, ">"); break;
  case MIR_BGES: out_bscmp (ctx, f, ops, ">="); break;
  case MIR_UBLT: out_bucmp (ctx, f, ops, "<"); break;
  case MIR_UBLE: out_bucmp (ctx, f, ops, "<="); break;
  case MIR_UBGT: out_bucmp (ctx, f, ops, ">"); break;
  case MIR_UBGE: out_bucmp (ctx, f, ops, ">="); break;
  case MIR_UBLTS: out_buscmp (ctx, f, ops, "<"); break;
  case MIR_UBLES: out_buscmp (ctx, f, ops, "<="); break;
  case MIR_UBGTS: out_buscmp (ctx, f, ops, ">"); break;
  case MIR_UBGES: out_buscmp (ctx, f, ops, ">="); break;
  case MIR_FBEQ:
  case MIR_DBEQ:
  case MIR_LDBEQ: out_bfcmp (ctx, f, ops, "=="); break;
  case MIR_FBNE:
  case MIR_DBNE:
  case MIR_LDBNE: out_bfcmp (ctx, f, ops, "!="); break;
  case MIR_FBLT:
  case MIR_DBLT:
  case MIR_LDBLT: out_bfcmp (ctx, f, ops, "<"); break;
  case MIR_FBLE:
  case MIR_DBLE:
  case MIR_LDBLE: out_bfcmp (ctx, f, ops, "<="); break;
  case MIR_FBGT:
  case MIR_DBGT:
  case MIR_LDBGT: out_bfcmp (ctx, f, ops, ">"); break;
  case MIR_FBGE:
  case MIR_DBGE:
  case MIR_LDBGE: out_bfcmp (ctx, f, ops, ">="); break;
  case MIR_ALLOCA:
    out_op (ctx, f, ops[0]);
    fprintf (f, " = alloca (");
    out_op (ctx, f, ops[1]);
    fprintf (f, ");\n");
    break;
  case MIR_CALL:
  case MIR_INLINE: {
    MIR_proto_t proto;
    size_t start = 2;

    mir_assert (insn->nops >= 2 && ops[0].mode == MIR_OP_REF
                && ops[0].u.ref->item_type == MIR_proto_item);
    proto = ops[0].u.ref->u.proto;
    if (proto->nres > 1) {
      (*MIR_get_error_func (ctx)) (MIR_call_op_error,
                                   " can not translate multiple results functions into C");
    } else if (proto->nres == 1) {
      out_op (ctx, f, ops[2]);
      fprintf (f, " = ");
      start = 3;
    }
    fprintf (f, "((%s) ", proto->name);
    out_op (ctx, f, ops[1]);
    fprintf (f, ") (");
    for (size_t i = start; i < insn->nops; i++) {
      if (i != start) fprintf (f, ", ");
      out_op (ctx, f, ops[i]);
    }
    fprintf (f, ");\n");
    break;
  }
  case MIR_RET:
    fprintf (f, "return ");
    if (insn->nops > 1) {
      fprintf (stderr, "return with multiple values is not implemented\n");
      exit (1);
    }
    if (insn->nops != 0) out_op (ctx, f, ops[0]);
    fprintf (f, ";\n");
    break;
  case MIR_LABEL:
    mir_assert (ops[0].mode == MIR_OP_INT);
    fprintf (f, "l%" PRId64 ":\n", ops[0].u.i);
    break;
  default: mir_assert (FALSE);
  }
}

void out_item (MIR_context_t ctx, FILE *f, MIR_item_t item) {
  MIR_var_t var;
  size_t i, nlocals;

  if (item->item_type == MIR_export_item) return;
  if (item->item_type == MIR_import_item) {
    fprintf (f, "extern char %s[];\n", item->u.import_id);
    return;
  }
  if (item->item_type == MIR_forward_item) {  // ???
    return;
  }
  if (item->item_type == MIR_proto_item) {
    MIR_proto_t proto = item->u.proto;

    fprintf (f, "typedef ");
    if (proto->nres == 0)
      fprintf (f, "void");
    else if (proto->nres == 1)
      out_type (f, proto->res_types[0]);
    else
      (*MIR_get_error_func (ctx)) (MIR_func_error,
                                   "Multiple result functions can not be called in C");
    fprintf (f, " (*%s) (", proto->name);
    for (i = 0; i < VARR_LENGTH (MIR_var_t, proto->args); i++) {
      var = VARR_GET (MIR_var_t, proto->args, i);
      if (i != 0) fprintf (f, ", ");
      out_type (f, var.type);
      if (var.name != NULL) fprintf (f, " %s", var.name);
    }
    if (i == 0) fprintf (f, "void");
    fprintf (f, ");\n");
    return;
  }
  if (!item->export_p) fprintf (f, "static ");
  curr_func = item->u.func;
  if (curr_func->nres == 0)
    fprintf (f, "void");
  else if (curr_func->nres == 1)
    out_type (f, curr_func->res_types[0]);
  else
    (*MIR_get_error_func (ctx)) (MIR_func_error,
                                 "Multiple result functions can not be represented in C");
  fprintf (f, " %s (", curr_func->name);
  if (curr_func->nargs == 0) fprintf (f, "void");
  for (i = 0; i < curr_func->nargs; i++) {
    if (i != 0) fprintf (f, ", ");
    var = VARR_GET (MIR_var_t, curr_func->vars, i);
    out_type (f, var.type);
    fprintf (f,
             var.type == MIR_T_I64 || var.type == MIR_T_F || var.type == MIR_T_D
                 || var.type == MIR_T_LD
               ? " %s"
               : " _%s",
             var.name);
  }
  fprintf (f, ") {\n");
  for (i = 0; i < curr_func->nargs; i++) {
    var = VARR_GET (MIR_var_t, curr_func->vars, i);
    if (var.type == MIR_T_I64 || var.type == MIR_T_F || var.type == MIR_T_D || var.type == MIR_T_LD)
      continue;
    fprintf (f, "  int64_t %s = _%s;\n", var.name, var.name);
  }
  nlocals = VARR_LENGTH (MIR_var_t, curr_func->vars) - curr_func->nargs;
  for (i = 0; i < nlocals; i++) {
    var = VARR_GET (MIR_var_t, curr_func->vars, i + curr_func->nargs);
    fprintf (f, "  ");
    out_type (f, var.type);
    fprintf (f, " %s;\n", var.name);
  }
  for (MIR_insn_t insn = DLIST_HEAD (MIR_insn_t, curr_func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn))
    out_insn (ctx, f, insn);
  fprintf (f, "}\n");
}

void MIR_module2c (MIR_context_t ctx, FILE *f, MIR_module_t m) {
  fprintf (f, "#include <stdint.h>\n");
  for (MIR_item_t item = DLIST_HEAD (MIR_item_t, m->items); item != NULL;
       item = DLIST_NEXT (MIR_item_t, item))
    out_item (ctx, f, item);
}

/* ------------------------- Small test example ------------------------- */
#if defined(TEST_MIR2C)

#include "mir-tests/scan-sieve.h"
#include "mir-tests/scan-hi.h"

int main (int argc, const char *argv[]) {
  MIR_module_t m;
  MIR_context_t ctx = MIR_init ();

  create_mir_func_sieve (ctx, NULL, &m);
  MIR_module2c (ctx, stdout, m);
  m = create_hi_module (ctx);
  MIR_module2c (ctx, stdout, m);
  MIR_finish (ctx);
  return 0;
}
#elif defined(MIR2C)

DEF_VARR (char);

int main (int argc, const char *argv[]) {
  int c;
  FILE *f;
  VARR (char) * input;
  MIR_module_t m;
  MIR_context_t ctx = MIR_init ();

  if (argc == 1)
    f = stdin;
  else if (argc == 2) {
    if ((f = fopen (argv[1], "r")) == NULL) {
      fprintf (stderr, "%s: cannot open file %s\n", argv[0], argv[1]);
      exit (1);
    }
  } else {
    fprintf (stderr, "usage: %s < file or %s mir-file\n", argv[0], argv[0]);
    exit (1);
  }
  VARR_CREATE (char, input, 0);
  while ((c = getc (f)) != EOF) VARR_PUSH (char, input, c);
  VARR_PUSH (char, input, 0);
  if (ferror (f)) {
    fprintf (stderr, "%s: error in reading input file\n", argv[0]);
    exit (1);
  }
  fclose (f);
  MIR_scan_string (ctx, VARR_ADDR (char, input));
  m = DLIST_TAIL (MIR_module_t, *MIR_get_module_list (ctx));
  MIR_module2c (ctx, stdout, m);
  MIR_finish (ctx);
  VARR_DESTROY (char, input);
  return 0;
}
#endif
