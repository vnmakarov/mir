#include "mir.h"
#include "mir-varr.h"
#include <stdarg.h>
#include <inttypes.h>
#include <float.h>

#define FALSE 0
#define TRUE 1

DEF_VARR (MIR_op_t);

static VARR (MIR_op_t) *temp_insn_ops;

DEF_VARR (MIR_type_t);

static VARR (MIR_type_t) *temp_arg_types;

struct insn_desc {
  MIR_insn_code_t code; const char *name; unsigned op_modes[4];
};

#define OUTPUT_FLAG (1 << 31)

static struct insn_desc insn_descs[] = {
  {MIR_MOV, "mov", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FMOV, "fmov", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DMOV, "dmov", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_I2F, "i2f", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_I2D, "i2d", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_F2I, "f2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_D2I, "d2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_F2D, "f2d", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_D2F, "d2f", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_NEG, "neg", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FNEG, "fneg", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DNEG, "dneg", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_ADD, "add", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FADD, "fadd", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DADD, "dadd", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_SUB, "sub", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FSUB, "fsub", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DSUB, "dsub", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_MUL, "mul", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FMUL, "fmul", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DMUL, "dmul", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_DIV, "div", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UDIV, "udiv", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FDIV, "fdiv", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DDIV, "ddiv", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_MOD, "mod", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UMOD, "umod", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_AND, "and", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_OR, "or", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_XOR, "xor", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_LSH, "lsh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_RSH, "rsh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_URSH, "ursh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_EQ, "eq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FEQ, "feq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DEQ, "deq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_NE, "ne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FNE, "fne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DNE, "dne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LT, "lt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULT, "ult", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FLT, "flt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DLT, "dlt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LE, "le", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULE, "ule", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FLE, "fle", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DLE, "dle", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_GT, "gt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGT, "ugt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FGT, "fgt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DGT, "dgt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_GE, "ge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGE, "uge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FGE, "fge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DGE, "dge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_JMP, "jmp", {MIR_OP_LABEL, MIR_OP_UNDEF}},
  {MIR_BT, "bt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BF, "bf", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BEQ, "beq", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBEQ, "fbeq", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBEQ, "dbeq", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BNE, "bne", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBNE, "fbne", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBNE, "dbne", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BLT, "blt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLT, "ublt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBLT, "fblt", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBLT, "dblt", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BLE, "ble", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLE, "uble", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBLE, "fble", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBLE, "dble", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BGT, "bgt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGT, "ubgt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBGT, "fbgt", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBGT, "dbgt", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BGE, "bge", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGE, "ubge", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBGE, "fbge", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBGE, "dbge", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_CALL, "call", {MIR_OP_UNDEF}},
  {MIR_CALL_C, "call_c", {MIR_OP_UNDEF}},
  {MIR_RET, "ret", {MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FRET, "fret", {MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DRET, "dret", {MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LABEL, "label", {MIR_OP_UNDEF}},
};

DEF_VARR (size_t);

static VARR (size_t) *insn_nops;

static void check_and_prepare_insn_descs (void) {
  size_t i, j;
  
  VARR_CREATE (size_t, insn_nops, 0);
  for (i = 0; i < MIR_INSN_BOUND; i++) {
    if (insn_descs[i].code != i)
      abort ();
    for (j = 0; insn_descs[i].op_modes[j] != MIR_OP_UNDEF; j++)
      ;
    VARR_PUSH (size_t, insn_nops, j);
  }
}

DEF_VARR (MIR_op_mode_t);

static VARR (MIR_op_mode_t) *reg_modes;

DEF_VARR (MIR_reg_t);

static VARR (MIR_reg_t) *temp_regs;

static int curr_label_num;
static size_t curr_reg_num;

DLIST (MIR_item_t) MIR_items; /* List of all items */

int MIR_init (void) {

  curr_label_num = curr_reg_num = 0;
  VARR_CREATE (MIR_op_t, temp_insn_ops, 0);
  VARR_CREATE (MIR_type_t, temp_arg_types, 0);
  VARR_CREATE (MIR_op_mode_t, reg_modes, 0);
  VARR_PUSH (MIR_op_mode_t, reg_modes, MIR_OP_UNDEF);
  check_and_prepare_insn_descs ();
  VARR_CREATE (MIR_reg_t, temp_regs, 0);
  DLIST_INIT (MIR_item_t, MIR_items);
  return TRUE;
}

void MIR_finish (void) {
  VARR_DESTROY (MIR_reg_t, temp_regs);
  VARR_DESTROY (MIR_type_t, temp_arg_types);
  VARR_DESTROY (MIR_op_mode_t, reg_modes);
  VARR_DESTROY (size_t, insn_nops);
  VARR_DESTROY (MIR_op_t, temp_insn_ops);
}

MIR_item_t MIR_new_func_arr (const char *name, size_t frame_size, size_t nargs, MIR_type_t *arg_types) {
  MIR_item_t func_item = malloc (sizeof (struct MIR_item));
  MIR_func_t func;
  size_t i;
  
  if (func_item == NULL)
    abort ();
  func_item->data = NULL;
  func_item->func_p = TRUE;
  func_item->u.func = func = malloc (sizeof (struct MIR_func) +  sizeof (MIR_op_mode_t) * (nargs == 0 ? 0 : nargs - 1));
  if (func == NULL)
    abort ();
  func->name = name;
  DLIST_INIT (MIR_insn_t, func->insns);
  func->frame_size = frame_size;
  func->nargs = nargs;
  for (i = 0; i < nargs; i++)
    func->arg_types[i] = arg_types[i];
  DLIST_APPEND (MIR_item_t, MIR_items, func_item);
  return func_item;
}

MIR_item_t MIR_new_func (const char *name, size_t frame_size, size_t nargs, ...) {
  va_list argp;
  MIR_op_mode_t op_mode;
  size_t i;
  
  va_start (argp, nargs);
  VARR_TRUNC (MIR_type_t, temp_arg_types, 0);
  for (i = 0; i < nargs; i++) {
    op_mode = va_arg (argp, MIR_op_mode_t);
    VARR_PUSH (MIR_type_t, temp_arg_types, op_mode);
  }
  va_end(argp);
  return MIR_new_func_arr (name, frame_size, nargs, VARR_ADDR (MIR_type_t, temp_arg_types));
}

const char *MIR_insn_name (MIR_insn_code_t code) {
  if (code >= MIR_INSN_BOUND)
    abort ();
  return insn_descs[code].name;
}

size_t MIR_insn_nops (MIR_insn_code_t code) {
  if (code >= MIR_INSN_BOUND)
    abort ();
  return VARR_GET (size_t, insn_nops, code);
}

MIR_op_mode_t MIR_insn_op_mode (MIR_insn_code_t code, size_t nop, int *out_p) {
  size_t nops = MIR_insn_nops (code);
  unsigned mode;

  if (nop >= nops)
    return MIR_OP_UNDEF;
  mode = insn_descs[code].op_modes[nop];
  *out_p = (mode & OUTPUT_FLAG) != 0;
  return *out_p ? mode ^ OUTPUT_FLAG : mode;
}

static MIR_insn_t create_insn (size_t nops, MIR_insn_code_t code) {
  MIR_insn_t insn;

  if (nops == 0)
    nops = 1;
  insn = malloc (sizeof (struct MIR_insn) + sizeof (MIR_op_t) * (nops - 1));
  if (insn == NULL)
    abort ();
  insn->code = code; insn->data = NULL;
  return insn;
}

static MIR_insn_t new_insn1 (MIR_insn_code_t code) { return create_insn (1, code); }

MIR_insn_t MIR_new_insn (MIR_insn_code_t code, ...) {
  va_list argp;
  MIR_op_t op;
  size_t i, nops = MIR_insn_nops (code);
  
  va_start (argp, code);
  VARR_TRUNC (MIR_op_t, temp_insn_ops, 0);
  for (i = 0; i < nops; i++) {
    op = va_arg (argp, MIR_op_t);
    VARR_PUSH (MIR_op_t, temp_insn_ops, op);
  }
  va_end(argp);
  return MIR_new_insn_arr (code, nops, VARR_ADDR (MIR_op_t, temp_insn_ops));
}

static MIR_op_mode_t
get_general_op_mode (MIR_op_t op, MIR_op_mode_t expected_mode) {
  switch (op.mode) {
  case MIR_OP_UNDEF: case MIR_OP_INT: case MIR_OP_FLOAT: case MIR_OP_DOUBLE:
  case MIR_OP_NAME: case MIR_OP_LABEL:
    return op.mode;
  case MIR_OP_HARD_REG:
    return expected_mode;
  case MIR_OP_REG: {
    MIR_op_mode_t mode = VARR_GET (MIR_op_mode_t, reg_modes, op.u.reg);
    
    return mode == MIR_OP_UNDEF ? expected_mode : mode;
  }
  case MIR_OP_MEM:
  case MIR_OP_HARD_REG_MEM:
    switch (op.u.mem.type) {
    case MIR_I8: case MIR_U8: case MIR_I16: case MIR_U16:
    case MIR_I32: case MIR_U32: case MIR_I64:
      return MIR_OP_INT;
    case MIR_F:
      return MIR_OP_FLOAT;
    case MIR_D:
      return MIR_OP_DOUBLE;
    default:
      abort ();
    }
  default:
    abort ();
  }
}

MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops) {
  MIR_insn_t insn;
  MIR_op_mode_t mode, reg_mode;
  int out_p;
  size_t i, insn_nops = MIR_insn_nops (code);
  
  if (nops != insn_nops)
    ;
  for (i = 0; i < nops; i++) {
    mode = MIR_insn_op_mode (code, i, &out_p);
    if (mode != get_general_op_mode (ops[i], mode))
      abort ();
    switch (ops[i].mode) {
    case MIR_OP_REG:
      VARR_SET (MIR_op_mode_t, reg_modes, ops[i].u.reg, mode);
      break;
    case MIR_OP_MEM:
      if (ops[i].u.mem.base != 0) {
	reg_mode = VARR_GET (MIR_op_mode_t, reg_modes, ops[i].u.mem.base);
	if (reg_mode != MIR_OP_UNDEF && reg_mode != MIR_OP_INT)
	  abort ();
	VARR_SET (MIR_op_mode_t, reg_modes, ops[i].u.mem.base, MIR_OP_INT);
      }
      if (ops[i].u.mem.index != 0) {
	reg_mode = VARR_GET (MIR_op_mode_t, reg_modes, ops[i].u.mem.index);
	if (reg_mode != MIR_OP_UNDEF && reg_mode != MIR_OP_INT)
	  abort ();
	VARR_SET (MIR_op_mode_t, reg_modes, ops[i].u.mem.index, MIR_OP_INT);
      }
      break;
    }
  }
  insn = create_insn (nops, code);
  for (i = 0; i < nops; i++)
    insn->ops[i] = ops[i];
  return insn;
}

MIR_insn_t MIR_new_label (void) {
  MIR_insn_t insn = new_insn1 (MIR_LABEL);

  insn->ops[0] = MIR_new_int_op (++curr_label_num);
  return insn;
}

MIR_reg_t MIR_new_reg (void) {
  MIR_reg_t reg = ++curr_reg_num;
  
  VARR_PUSH (MIR_op_mode_t, reg_modes, MIR_OP_UNDEF);
  return reg;
}

MIR_reg_t MIR_reg_mode (MIR_reg_t reg) {
  assert (reg < VARR_LENGTH (MIR_op_mode_t, reg_modes));
  return VARR_GET (MIR_op_mode_t, reg_modes, reg);
}

/* Functions to create operands.  */

static void init_op (MIR_op_t *op, MIR_op_mode_t mode) { op->mode = mode; op->data = NULL; }

MIR_op_t MIR_new_reg_op (MIR_reg_t reg) {
  MIR_op_t op;

  assert (reg < VARR_LENGTH (MIR_op_mode_t, reg_modes));
  init_op (&op, MIR_OP_REG); op.u.reg = reg;
  return op;
}

MIR_op_t MIR_new_hard_reg_op (MIR_reg_t hard_reg) { /* It is used only internally */
  MIR_op_t op;

  init_op (&op, MIR_OP_HARD_REG); op.u.hard_reg = hard_reg;
  return op;
}

MIR_op_t MIR_new_int_op (int64_t i) {
  MIR_op_t op;

  init_op (&op, MIR_OP_INT); op.u.i = i;
  return op;
}

MIR_op_t MIR_new_float_op (float f) {
  MIR_op_t op;

  init_op (&op, MIR_OP_FLOAT); op.u.f = f;
  return op;
}

MIR_op_t MIR_new_double_op (double d) {
  MIR_op_t op;

  init_op (&op, MIR_OP_DOUBLE); op.u.d = d;
  return op;
}

MIR_op_t MIR_new_name_op (MIR_name_t name) {
  MIR_op_t op;

  init_op (&op, MIR_OP_NAME); op.u.name = name;
  return op;
}

MIR_op_t MIR_new_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
			 MIR_reg_t index, MIR_scale_t scale) {
  MIR_op_t op;

  init_op (&op, MIR_OP_MEM); op.u.mem.type = type; op.u.mem.disp = disp;
  op.u.mem.base = base; op.u.mem.index = index; op.u.mem.scale = scale;
  return op;
}

MIR_op_t MIR_new_hard_reg_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
				  MIR_reg_t index, MIR_scale_t scale) {
  MIR_op_t op;

  init_op (&op, MIR_OP_HARD_REG_MEM); op.u.hard_reg_mem.type = type; op.u.hard_reg_mem.disp = disp;
  op.u.hard_reg_mem.base = base; op.u.hard_reg_mem.index = index; op.u.hard_reg_mem.scale = scale;
  return op;
}

MIR_op_t MIR_new_label_op (MIR_label_t label) {
  MIR_op_t op;

  init_op (&op, MIR_OP_LABEL); op.u.label = label;
  return op;
}

void MIR_append_insn (MIR_item_t func_item, MIR_insn_t insn) {
  if (! func_item->func_p)
    abort ();
  DLIST_APPEND (MIR_insn_t, func_item->u.func->insns, insn);
}

void MIR_prepend_insn (MIR_item_t func_item, MIR_insn_t insn) {
  if (! func_item->func_p)
    abort ();
  DLIST_PREPEND (MIR_insn_t, func_item->u.func->insns, insn);
}

void MIR_insert_insn_after (MIR_item_t func_item, MIR_insn_t after, MIR_insn_t insn) {
  if (! func_item->func_p)
    abort ();
  DLIST_INSERT_AFTER (MIR_insn_t, func_item->u.func->insns, after, insn);
}

void MIR_insert_insn_before (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t insn) {
  if (! func_item->func_p)
    abort ();
  DLIST_INSERT_BEFORE (MIR_insn_t, func_item->u.func->insns, before, insn);
}

void MIR_remove_insn (MIR_item_t func_item, MIR_insn_t insn) { // ??? freeing
  if (! func_item->func_p)
    abort ();
  DLIST_REMOVE (MIR_insn_t, func_item->u.func->insns, insn);
}

const char *MIR_type_str (MIR_type_t tp) {
  switch (tp) {
  case MIR_I8: return "i8";
  case MIR_U8: return "u8";
  case MIR_I16: return "i16";
  case MIR_U16: return "u16";
  case MIR_I32: return "i32";
  case MIR_U32: return "u32";
  case MIR_I64: return "i64";
  case MIR_F: return "f";
  case MIR_D: return "d";
  default: abort ();
  }
}

void MIR_output_type (FILE *f, MIR_type_t tp) { fprintf (f, "%s", MIR_type_str (tp)); }

void MIR_output_disp (FILE *f, MIR_disp_t disp) { fprintf (f, "%" PRId64, (int64_t) disp); }

void MIR_output_scale (FILE *f, unsigned scale) { fprintf (f, "%u", scale); }

void MIR_output_reg (FILE *f, MIR_reg_t reg) { fprintf (f, "r%u", reg); }

void MIR_output_hard_reg (FILE *f, MIR_reg_t reg) { fprintf (f, "hr%u", reg); }

void MIR_output_label (FILE *f, MIR_label_t label);

void MIR_output_op (FILE *f, MIR_op_t op) {
  switch (op.mode) {
  case MIR_OP_REG:
    MIR_output_reg (f, op.u.reg);
    break;
  case MIR_OP_HARD_REG:
    MIR_output_hard_reg (f, op.u.hard_reg);
    break;
  case MIR_OP_INT:
    fprintf (f, "%" PRId64, op.u.i);
    break;
  case MIR_OP_FLOAT:
    fprintf (f, "%.*g", FLT_DECIMAL_DIG, op.u.f);
    break;
  case MIR_OP_DOUBLE:
    fprintf (f, "%.*g", DBL_DECIMAL_DIG, op.u.d);
    break;
  case MIR_OP_MEM:
  case MIR_OP_HARD_REG_MEM: {
    MIR_reg_t no_reg = op.mode == MIR_OP_MEM ? 0 : MIR_NON_HARD_REG;
    void (*out_reg) (FILE *, MIR_reg_t) = op.mode == MIR_OP_MEM ? MIR_output_reg : MIR_output_hard_reg;
    
    MIR_output_type (f, op.u.mem.type);
    fprintf (f, ":");
    if (op.u.mem.disp != 0 || (op.u.mem.base == no_reg && op.u.mem.index == no_reg))
      MIR_output_disp (f, op.u.mem.disp);
    if (op.u.mem.base != no_reg || op.u.mem.index != no_reg) {
      fprintf (f, "[");
      if (op.u.mem.base != no_reg)
	out_reg (f, op.u.mem.base);
      if (op.u.mem.index != no_reg) {
	fprintf(f, ", ");
	out_reg (f, op.u.mem.index);
	if (op.u.mem.scale != 1) {
	  fprintf(f, " * ");
	  MIR_output_scale (f, op.u.mem.scale);
	}
      }
      fprintf (f, "]");
    }
    break;
  }
  case MIR_OP_NAME:
    fprintf (f, "%s", op.u.name);
    break;
  case MIR_OP_LABEL:
    MIR_output_label (f, op.u.label);
    break;
  default:
    abort ();
  }
}

void MIR_output_label (FILE *f, MIR_label_t label) {
  fprintf (f, "L"); MIR_output_op (f, label->ops[0]);
}

void MIR_output_insn (FILE *f, MIR_insn_t insn) {
  size_t i, nops;
  
  if (insn->code == MIR_LABEL) {
    MIR_output_label (f, insn); fprintf (f, ":\n");
    return;
  }
  fprintf (f, "\t%s", MIR_insn_name (insn->code));
  nops = MIR_insn_nops (insn->code);
  for (i = 0; i < nops; i++) {
    fprintf (f, i == 0 ? "\t" : ", ");
    MIR_output_op (f, insn->ops[i]);
  }
  fprintf (f, "\n");
}

void MIR_output_item (FILE *f, MIR_item_t item) {
  MIR_insn_t insn;
  MIR_func_t func;
  size_t i;
  
  if (! item->func_p) {
    fprintf (f, "%s:\textern\n", item->u.external);
    return;
  }
  func = item->u.func;
  fprintf (f, "%s:\tfunc\t%lu", func->name, (unsigned long) func->frame_size);
  for (i = 0; i < func->nargs; i++)
    fprintf (f, ", %s", MIR_type_str (func->arg_types[i]));
  fprintf (f, " # frame size = %lu, %lu arg%s\n", (unsigned long) func->frame_size,
	   (unsigned long) func->nargs, func->nargs == 1 ? "" : "s");
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = DLIST_NEXT (MIR_insn_t, insn))
    MIR_output_insn (f, insn);
  
}

void MIR_output (FILE *f) {
  MIR_item_t item;
  
  for (item = DLIST_HEAD (MIR_item_t, MIR_items); item != NULL; item = DLIST_NEXT (MIR_item_t, item))
    MIR_output_item (f, item);
}

static MIR_insn_t insert_op_insn (int out_p, MIR_item_t func_item, 
				  MIR_insn_t anchor, MIR_insn_t insn) {
  if (! out_p) {
    MIR_insert_insn_before (func_item, anchor, insn);
    return anchor;
  }
  MIR_insert_insn_after (func_item, anchor, insn);
  return insn;
}

void MIR_simplify_op (MIR_item_t func_item, MIR_insn_t insn, MIR_op_t *op, int out_p, int move_p) {
  MIR_op_t new_op, mem_op;
  MIR_insn_t new_insn;
  
  switch (op->mode) {
  case MIR_OP_INT:
  case MIR_OP_FLOAT:
  case MIR_OP_DOUBLE:
  case MIR_OP_NAME:
    assert (! out_p);
    if (move_p)
      return;
    new_op = MIR_new_reg_op (MIR_new_reg ());
    MIR_insert_insn_before (func_item, insn,
			    MIR_new_insn (op->mode == MIR_OP_FLOAT ? MIR_FMOV : op->mode == MIR_OP_DOUBLE ? MIR_DMOV : MIR_MOV, new_op, *op));
    *op = new_op;
    break;
  case MIR_OP_REG:
  case MIR_OP_LABEL:
    break; /* Do nothing */
  case MIR_OP_MEM:
    new_op = MIR_new_reg_op (MIR_new_reg ());
    mem_op = *op;
    if (op->u.mem.base != 0 && op->u.mem.disp == 0 && (op->u.mem.index == 0 || op->u.mem.scale == 0)) {
      mem_op.u.mem.index = 0; mem_op.u.mem.scale = 0;
    } else if (op->u.mem.base == 0 && op->u.mem.index != 0 && op->u.mem.scale == 1 && op->u.mem.disp == 0) {
      mem_op.u.mem.base = op->u.mem.index; mem_op.u.mem.index = 0; mem_op.u.mem.scale = 0;
    } else {
      MIR_op_t addr_op, base_op, ind_op;
      MIR_reg_t addr_reg;
      int after_p = ! move_p && out_p;
      
      addr_reg = MIR_new_reg ();
      addr_op = MIR_new_reg_op (addr_reg);
      if (op->u.mem.disp != 0)
	insn = insert_op_insn (after_p, func_item, insn, MIR_new_insn (MIR_MOV, addr_op, MIR_new_int_op (op->u.mem.disp)));
      if (op->u.mem.base != 0) {
	base_op = MIR_new_reg_op (op->u.mem.base);
	if (op->u.mem.disp != 0)
	  insn = insert_op_insn (after_p, func_item, insn, MIR_new_insn (MIR_ADD, addr_op, addr_op, base_op));
      }
      if (op->u.mem.index != 0 && op->u.mem.scale != 0) {
	if (op->u.mem.scale == 1)
	  ind_op = MIR_new_reg_op (op->u.mem.index);
	else {
	  ind_op = (op->u.mem.disp != 0 || op->u.mem.base != 0
		    ? MIR_new_reg_op (MIR_new_reg ()) : addr_op);
	  insn = insert_op_insn (after_p, func_item, insn, MIR_new_insn (MIR_MOV, ind_op, MIR_new_int_op (op->u.mem.scale)));
	  insn = insert_op_insn (after_p, func_item, insn, MIR_new_insn (MIR_MUL, ind_op, MIR_new_reg_op (op->u.mem.index), ind_op));
	}
	if (op->u.mem.disp != 0 || op->u.mem.base != 0) {
	  insn = insert_op_insn (after_p, func_item, insn, MIR_new_insn (MIR_ADD, addr_op, base_op, ind_op));
	}
      }
      mem_op.u.mem.base = addr_reg;
      mem_op.u.mem.disp = 0; mem_op.u.mem.index = 0; mem_op.u.mem.scale = 0;
    }
    if (move_p) {
      *op = mem_op;
    } else {
	if (out_p)
	  new_insn = MIR_new_insn (MIR_MOV, mem_op, new_op);
	else
	  new_insn = MIR_new_insn (MIR_MOV, new_op, mem_op);
	insn = insert_op_insn (out_p, func_item, insn, new_insn);
	*op = new_op;
      }
    break;
  default:
    /* We don't simplify code with hard regs.  */
    abort ();
  }
}

void MIR_simplify_insn (MIR_item_t func_item, MIR_insn_t insn) {
  int out_p;
  MIR_insn_code_t code = insn->code;
  size_t i, nops = MIR_insn_nops (code);

  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (code, i, &out_p);
    
    MIR_simplify_op (func_item, insn, &insn->ops[i], out_p, code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV);
  }
}

void MIR_simplify_func (MIR_item_t func_item) {
  MIR_func_t func = func_item->u.func;
  MIR_insn_t insn, next_insn;

  if (! func_item->func_p)
    abort ();
  func = func_item->u.func;
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    MIR_insn_code_t code = insn->code;
    MIR_op_t temp_op;
    
    if ((code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV) && insn->ops[0].mode == MIR_OP_MEM  && insn->ops[1].mode == MIR_OP_MEM) {
      temp_op = MIR_new_reg_op (MIR_new_reg ());
      MIR_insert_insn_after (func_item, insn, MIR_new_insn (code, insn->ops[0], temp_op));
      insn->ops[0] = temp_op;
    }
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    MIR_simplify_insn (func_item, insn);
  }
}

#if defined(TEST_MIR) || defined(TEST_MIR_GEN)
MIR_item_t create_mir_example1 (void) {
  MIR_item_t func;
  MIR_label_t fin, cont;
  MIR_reg_t ARG1, R2;
  
  ARG1 = MIR_new_reg (); R2 = MIR_new_reg ();
  func = MIR_new_func ("test", 0, 1, MIR_I64);
  fin = MIR_new_label (); cont = MIR_new_label ();
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (R2), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, cont);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (R2), MIR_new_reg_op (R2), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_BLT, MIR_new_label_op (cont), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, fin);
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_reg_op (R2)));
  return func;
}

MIR_item_t create_mir_example2 (void) {
  MIR_item_t func;
  MIR_reg_t ARG1, R2;
  
  ARG1 = MIR_new_reg (); R2 = MIR_new_reg ();
  func = MIR_new_func ("test2", 0, 2, MIR_I64, MIR_I64);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_mem_op (MIR_I64, 0, ARG1, R2, 8),
				       MIR_new_mem_op (MIR_I64, 64, ARG1, 0, 0), MIR_new_mem_op (MIR_I64, 0, 0, ARG1, 8)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 0, ARG1, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 0, 0, R2, 1)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 1024, 0, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_mem_op (MIR_I64, 0, ARG1, R2, 8), MIR_new_mem_op (MIR_I64, 0, ARG1, 0, 8)));
  return func;
}
#endif

#ifdef TEST_MIR
static void error (const char *msg) {
  fprintf (stderr, "%s -- goodbye\n", msg);
  exit (1);
}

int main (void) {
  MIR_item_t func1, func2;
  
  MIR_init ();
  func = create_mir_example1 ();
  func = create_mir_example2 ();
  MIR_simplify_func (func1);
  MIR_simplify_func (func2);
  MIR_output (stderr);
  MIR_finish ();
  return 0;
}

#endif
