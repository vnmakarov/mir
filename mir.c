#include "mir.h"

static void util_error (const char *message);
#define MIR_VARR_ERROR util_error
#define MIR_HTAB_ERROR MIR_VARR_ERROR 

#include "mir-htab.h"
#include "mir-mum.h"
#include <string.h>
#include <stdarg.h>
#include <inttypes.h>
#include <float.h>

#define FALSE 0
#define TRUE 1

typedef void MIR_NO_RETURN (*MIR_error_func_t) (enum MIR_error_type error_type, const char *message);

static MIR_error_func_t error_func;

static void MIR_NO_RETURN default_error (enum MIR_error_type error_type, const char *message) {
  fprintf (stderr, "%s\n", message);
  exit (0);
}

static void MIR_NO_RETURN util_error (const char *message) { (*error_func) (MIR_alloc_error, message); }

#define TEMP_REG_NAME_PREFIX "t"
#define HARD_REG_NAME_PREFIX "hr"

/* Reserved names:
   fp - frame pointer
   t<number> - a temp reg
   hr<number> - a hardware reg */
static int reserved_name_p (const char *name) {
  size_t i, start;
  
  if (strcmp (name, FP_NAME) == 0)
    return TRUE;
  if (strncmp (name, TEMP_REG_NAME_PREFIX, strlen (TEMP_REG_NAME_PREFIX)) == 0)
    start = strlen (TEMP_REG_NAME_PREFIX);
  else if (strncmp (name, HARD_REG_NAME_PREFIX, strlen (HARD_REG_NAME_PREFIX)) == 0)
    start = strlen (HARD_REG_NAME_PREFIX);
  else
    return FALSE;
  for (i = start; name[i] != '\0'; i++)
    if (name[i] < '0' || name[i] > '9')
      return FALSE;
  return TRUE;
}

DEF_VARR (MIR_op_t);

static VARR (MIR_op_t) *temp_insn_ops;
static VARR (MIR_var_t) *temp_vars;

struct insn_desc {
  MIR_insn_code_t code; const char *name; unsigned op_modes[4];
};

#define OUTPUT_FLAG (1 << 31)

static struct insn_desc insn_descs[] = {
  {MIR_MOV, "mov", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FMOV, "fmov", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DMOV, "dmov", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_S2I, "s2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_US2I, "us2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_I2F, "i2f", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_I2D, "i2d", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_F2I, "f2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_D2I, "d2i", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_F2D, "f2d", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_D2F, "d2f", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_NEG, "neg", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_NEGS, "negs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FNEG, "fneg", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DNEG, "dneg", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_ADD, "add", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ADDS, "adds", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FADD, "fadd", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DADD, "dadd", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_SUB, "sub", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_SUBS, "subs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FSUB, "fsub", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DSUB, "dsub", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_MUL, "mul", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UMUL, "umul", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_MULS, "muls", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UMULS, "umuls", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FMUL, "fmul", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DMUL, "dmul", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_DIV, "div", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_DIVS, "divs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UDIV, "udiv", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UDIVS, "udivs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FDIV, "fdiv", {MIR_OP_FLOAT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DDIV, "ddiv", {MIR_OP_DOUBLE | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_MOD, "mod", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_MODS, "mods", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UMOD, "umod", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UMODS, "umods", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_AND, "and", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ANDS, "ands", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_OR, "or", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ORS, "ors", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_XOR, "xor", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_XORS, "xors", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_LSH, "lsh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_LSHS, "lshs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_RSH, "rsh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_RSHS, "rshs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_URSH, "ursh", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_URSHS, "urshs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_EQ, "eq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_EQS, "eqs", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FEQ, "feq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DEQ, "deq", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_NE, "ne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_NES, "nes", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FNE, "fne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DNE, "dne", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LT, "lt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_LTS, "lts", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULT, "ult", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULTS, "ults", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FLT, "flt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DLT, "dlt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LE, "le", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_LES, "les", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULE, "ule", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_ULES, "ules", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FLE, "fle", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DLE, "dle", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_GT, "gt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_GTS, "gts", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGT, "ugt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGTS, "ugts", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FGT, "fgt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DGT, "dgt", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_GE, "ge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_GES, "ges", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGE, "uge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UGES, "uges", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FGE, "fge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DGE, "dge", {MIR_OP_INT | OUTPUT_FLAG, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_JMP, "jmp", {MIR_OP_LABEL, MIR_OP_UNDEF}},
  {MIR_BT, "bt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BF, "bf", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BEQ, "beq", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BEQS, "beq", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBEQ, "fbeq", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBEQ, "dbeq", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BNE, "bne", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BNES, "bne", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBNE, "fbne", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBNE, "dbne", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BLT, "blt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BLTS, "blts", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLT, "ublt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLTS, "ublts", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBLT, "fblt", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBLT, "dblt", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BLE, "ble", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BLES, "bles", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLE, "uble", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBLES, "ubles", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBLE, "fble", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBLE, "dble", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BGT, "bgt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BGTS, "bgts", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGT, "ubgt", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGTS, "ubgts", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBGT, "fbgt", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBGT, "dbgt", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_BGE, "bge", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_BGES, "bges", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGE, "ubge", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_UBGES, "ubges", {MIR_OP_LABEL, MIR_OP_INT, MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FBGE, "fbge", {MIR_OP_LABEL, MIR_OP_FLOAT, MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DBGE, "dbge", {MIR_OP_LABEL, MIR_OP_DOUBLE, MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_CALL, "call", {MIR_OP_UNDEF}},
  {MIR_CALL_C, "call_c", {MIR_OP_UNDEF}},
  {MIR_RET, "ret", {MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_RETS, "rets", {MIR_OP_INT, MIR_OP_UNDEF}},
  {MIR_FRET, "fret", {MIR_OP_FLOAT, MIR_OP_UNDEF}},
  {MIR_DRET, "dret", {MIR_OP_DOUBLE, MIR_OP_UNDEF}},
  {MIR_LABEL, "label", {MIR_OP_UNDEF}},
  {MIR_INVALID_INSN, "invalid-insn", {MIR_OP_UNDEF}},
};

DEF_VARR (size_t);

static VARR (size_t) *insn_nops;

static void check_and_prepare_insn_descs (void) {
  size_t i, j;
  
  VARR_CREATE (size_t, insn_nops, 0);
  for (i = 0; i < MIR_INSN_BOUND; i++) {
    assert (insn_descs[i].code == i);
    for (j = 0; insn_descs[i].op_modes[j] != MIR_OP_UNDEF; j++)
      ;
    VARR_PUSH (size_t, insn_nops, j);
  }
}

static MIR_op_mode_t type2mode (MIR_type_t type) {
  return type == MIR_F ? MIR_OP_FLOAT : type == MIR_D ? MIR_OP_DOUBLE : MIR_OP_INT;
}

typedef struct string {
  size_t num; /* string number starting with 1 */
  const char *str;
} string_t;

DEF_VARR (string_t);
static VARR (string_t) *strings;

DEF_HTAB (string_t);
static HTAB (string_t) *string_tab;

static int str_eq (string_t str1, string_t str2) { return strcmp (str1.str, str2.str) == 0; }
static htab_hash_t str_hash (string_t str) { return mum_hash (str.str, strlen (str.str), 0x42); }

static void string_init (VARR (string_t) **strs, HTAB (string_t) **str_tab) {
  static string_t string = {0, NULL};
  
  VARR_CREATE (string_t, *strs, 0);
  VARR_PUSH (string_t, *strs, string); /* don't use 0th string */
  HTAB_CREATE (string_t, *str_tab, 1000, str_hash, str_eq);
}

static int string_find (VARR (string_t) **strs, HTAB (string_t) **str_tab,
			const char *str, string_t *s) {
  string_t string;
  
  string.str = str;
  return HTAB_DO (string_t, *str_tab, string, HTAB_FIND, *s);
}

static string_t string_store (VARR (string_t) **strs, HTAB (string_t) **str_tab, const char *str) {
  char *heap_str;
  string_t el, string;
  
  if (string_find (strs, str_tab, str, &el))
    return el;
  if ((heap_str = malloc (strlen (str) + 1)) == NULL)
    (*error_func) (MIR_alloc_error, "Not enough memory");
  strcpy (heap_str, str);
  string.str = heap_str;
  string.num = VARR_LENGTH (string_t, *strs);
  VARR_PUSH (string_t, *strs, string);
  HTAB_DO (string_t, *str_tab, string, HTAB_INSERT, el);
  return string;
}

static void string_finish (VARR (string_t) **strs, HTAB (string_t) **str_tab) {
  size_t i;
  
  for (i = 1; i < VARR_LENGTH (string_t, *strs); i++)
    free ((char *) VARR_ADDR (string_t, *strs)[i].str);
  VARR_DESTROY (string_t, *strs);
  HTAB_DESTROY (string_t, *str_tab);
}

typedef struct reg_desc {
  size_t name_num;   /* 1st key for the namenum2rdn hash tab */
  MIR_func_t func;   /* 2nd key for hash the both tabs */
  MIR_type_t type;
  MIR_reg_t reg;     /* 1st key reg2rdn hash tab */
} reg_desc_t;

DEF_VARR (reg_desc_t);
static VARR (reg_desc_t) *reg_descs;

DEF_HTAB (size_t);
static HTAB (size_t) *namenum2rdn_tab;
static HTAB (size_t) *reg2rdn_tab;

static int namenum2rdn_eq (size_t rdn1, size_t rdn2) {
  reg_desc_t *addr = VARR_ADDR (reg_desc_t, reg_descs);
  
  return addr[rdn1].name_num == addr[rdn2].name_num && addr[rdn1].func == addr[rdn2].func;
}

static htab_hash_t namenum2rdn_hash (size_t rdn) {
  reg_desc_t *addr = VARR_ADDR (reg_desc_t, reg_descs);

  return mum_hash_finish (mum_hash_step
			  (mum_hash_step (mum_hash_init (0x24), (uint64_t) addr[rdn].func),
			   (uint64_t) addr[rdn].name_num));
}

static int reg2rdn_eq (size_t rdn1, size_t rdn2) {
  reg_desc_t *addr = VARR_ADDR (reg_desc_t, reg_descs);
  
  return addr[rdn1].reg == addr[rdn2].reg && addr[rdn1].func == addr[rdn2].func;
}

static htab_hash_t reg2rdn_hash (size_t rdn) {
  reg_desc_t *addr = VARR_ADDR (reg_desc_t, reg_descs);

  return mum_hash_finish (mum_hash_step
			  (mum_hash_step (mum_hash_init (0x24),	(uint64_t) addr[rdn].func),
			   addr[rdn].reg));
}

static void reg_init (void) {
  static reg_desc_t rd = {0, NULL, MIR_I64, 0};
  
  VARR_CREATE (reg_desc_t, reg_descs, 300);
  VARR_PUSH (reg_desc_t, reg_descs, rd); /* for 0 reg */
  HTAB_CREATE (size_t, namenum2rdn_tab, 300, namenum2rdn_hash, namenum2rdn_eq);
  HTAB_CREATE (size_t, reg2rdn_tab, 300, reg2rdn_hash, reg2rdn_eq);
}

static void reg_create (MIR_func_t func, MIR_reg_t reg, const char *name, MIR_type_t type, int any_p) {
  reg_desc_t rd;
  size_t rdn, tab_rdn;
  int htab_res;
  
  if (! any_p && reserved_name_p (name))
    (*error_func) (MIR_reserved_name_error, "redefining a reserved name");
  rd.name_num = string_store (&strings, &string_tab, name).num;
  rd.func = func;
  rd.type = type;
  rd.reg = reg;
  rdn = VARR_LENGTH (reg_desc_t, reg_descs);
  VARR_PUSH (reg_desc_t, reg_descs, rd);
  if (HTAB_DO (size_t, namenum2rdn_tab, rdn, HTAB_FIND, tab_rdn)) {
    VARR_POP (reg_desc_t, reg_descs);
    (*error_func) (MIR_repeated_decl_error, "Repeated reg declaration");
  }
  htab_res = HTAB_DO (size_t, namenum2rdn_tab, rdn, HTAB_INSERT, tab_rdn);
  assert (! htab_res);
  htab_res = HTAB_DO (size_t, reg2rdn_tab, rdn, HTAB_INSERT, tab_rdn);
  assert (! htab_res);
}

static void reg_finish (void) {
  VARR_DESTROY (reg_desc_t, reg_descs);
  HTAB_DESTROY (size_t, namenum2rdn_tab);
  HTAB_DESTROY (size_t, reg2rdn_tab);
}

DEF_VARR (MIR_insn_t);
static VARR (MIR_insn_t) *ret_insns;

static MIR_func_t curr_func;
static int curr_label_num;

DLIST (MIR_item_t) MIR_items; /* List of all items */

#if MIR_SCAN || MIR_IO
DEF_VARR (char);
static VARR (char) *temp_string; 
#endif

#if MIR_SCAN
static void scan_init (void);
static void scan_finish (void);
#endif

int MIR_init (void) {
  error_func = default_error;
  curr_func = NULL;
  curr_label_num = 0;
  string_init (&strings, &string_tab);
  reg_init ();
  VARR_CREATE (MIR_op_t, temp_insn_ops, 0);
  VARR_CREATE (MIR_var_t, temp_vars, 0);
  check_and_prepare_insn_descs ();
  VARR_CREATE (MIR_insn_t, ret_insns, 0);
  DLIST_INIT (MIR_item_t, MIR_items);
#if MIR_SCAN || MIR_IO
  VARR_CREATE (char, temp_string, 64);
#endif
#if MIR_SCAN
  scan_init ();
#endif
  return TRUE;
}

void MIR_finish (void) {
#if MIR_SCAN
  scan_finish ();
#endif
#if MIR_SCAN || MIR_IO
  VARR_DESTROY (char, temp_string);
#endif
  reg_finish ();
  string_finish (&strings, &string_tab);
  VARR_DESTROY (MIR_insn_t, ret_insns);
  VARR_DESTROY (MIR_var_t, temp_vars);
  VARR_DESTROY (size_t, insn_nops);
  VARR_DESTROY (MIR_op_t, temp_insn_ops);
  if (curr_func != NULL)
    (*error_func) (MIR_finish_error, "finish when function is not finished"); 
}

MIR_error_func_t MIR_get_error_func (void) { return error_func; }

void MIR_set_error_func (MIR_error_func_t func) { error_func = func; }

MIR_item_t MIR_new_func_arr (const char *name, size_t frame_size, size_t nargs, MIR_var_t *vars) {
  MIR_item_t func_item = malloc (sizeof (struct MIR_item));
  MIR_func_t func;
  size_t i;
  
  if (func_item == NULL)
    (*error_func) (MIR_alloc_error, "Not enough memory");
  func_item->data = NULL;
  func_item->func_p = TRUE;
  curr_func = func_item->u.func = func = malloc (sizeof (struct MIR_func));
  if (func == NULL) {
    free (func_item);
    (*error_func) (MIR_alloc_error, "Not enough memory");
  }
  func->name = string_store (&strings, &string_tab, name).str;
  DLIST_INIT (MIR_insn_t, func->insns);
  VARR_CREATE (MIR_var_t, func->vars, nargs + 8);
  func->frame_size = frame_size; func->nargs = nargs; func->ntemps = 0;
  for (i = 0; i < nargs; i++) {
    VARR_PUSH (MIR_var_t, func->vars, vars[i]);
    reg_create (func, i + 1, vars[i].name, vars[i].type, FALSE);
  }
  reg_create (func, nargs + 1, "fp", MIR_I64, TRUE);
  DLIST_APPEND (MIR_item_t, MIR_items, func_item);
  return func_item;
}

MIR_item_t MIR_new_func (const char *name, size_t frame_size, size_t nargs, ...) {
  va_list argp;
  MIR_var_t var;
  size_t i;
  
  va_start (argp, nargs);
  VARR_TRUNC (MIR_var_t, temp_vars, 0);
  for (i = 0; i < nargs; i++) {
    var.type = va_arg (argp, MIR_type_t);
    var.name = va_arg (argp, const char *);
    VARR_PUSH (MIR_var_t, temp_vars, var);
  }
  va_end(argp);
  return MIR_new_func_arr (name, frame_size, nargs, VARR_ADDR (MIR_var_t, temp_vars));
}

void MIR_create_func_var (MIR_func_t func, MIR_type_t type, const char *name) {
  MIR_var_t var;
  
  var.type = type; var.name = name;
  VARR_PUSH (MIR_var_t, func->vars, var);
  reg_create (func, VARR_LENGTH (MIR_var_t, func->vars) + 1 /* FP */, name, type, FALSE);
}

static reg_desc_t *find_rd_by_name_num (size_t name_num, MIR_func_t func) {
  size_t rdn, temp_rdn;
  reg_desc_t rd;

  rd.name_num = name_num; rd.func = func; /* keys */
  rd.type = MIR_I64; rd.reg = 0; /* to eliminate warnings */
  temp_rdn = VARR_LENGTH (reg_desc_t, reg_descs);
  VARR_PUSH (reg_desc_t, reg_descs, rd);
  if (! HTAB_DO (size_t, namenum2rdn_tab, temp_rdn, HTAB_FIND, rdn)) {
    VARR_POP (reg_desc_t, reg_descs);
    return NULL; /* undeclared */
  }
  return &VARR_ADDR (reg_desc_t, reg_descs)[rdn];
}

void MIR_finish_func (void) {
  MIR_insn_t insn;
  MIR_error_type_t err = MIR_no_error; /* to eliminate warning */
  const char *err_msg = NULL;
  
  if (curr_func == NULL)
    (*error_func) (MIR_no_func_error, "finish of non-existing function");
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func->insns); insn != NULL; insn = DLIST_NEXT (MIR_insn_t, insn)) {
    MIR_insn_code_t code = insn->code;
    size_t i, insn_nops = MIR_insn_nops (code);
    MIR_op_mode_t mode, expected_mode;
    reg_desc_t *rd;
    int out_p;
    
    for (i = 0; i < insn_nops; i++) {
      expected_mode = MIR_insn_op_mode (code, i, &out_p);
      switch (insn->ops[i].mode) {
      case MIR_OP_REG:
	rd = find_rd_by_name_num (insn->ops[i].u.reg, curr_func);
	if (rd == NULL) {
	  insn->code = MIR_INVALID_INSN;
	  (*error_func) (MIR_undeclared_reg_error, "undeclared reg");
	}
	insn->ops[i].u.reg = rd->reg;
	mode = type2mode (rd->type);
	break;
      case MIR_OP_MEM:
	if (insn->ops[i].u.mem.base != 0) {
	  rd = find_rd_by_name_num (insn->ops[i].u.mem.base, curr_func);
	  if (rd == NULL) {
	    insn->code = MIR_INVALID_INSN;
	    if (err == MIR_no_error) {
	      err = MIR_undeclared_reg_error; err_msg = "undeclared reg";
	    }
	  } else {
	    insn->ops[i].u.mem.base = rd->reg;
	    if (type2mode (rd->type) != MIR_OP_INT) {
	      insn->code = MIR_INVALID_INSN;
	      if (err == MIR_no_error) {
		err = MIR_reg_type_error; err_msg = "base reg of non-integer type";
	      }
	    }
	  }
	}
	if (insn->ops[i].u.mem.index != 0) {
	  rd = find_rd_by_name_num (insn->ops[i].u.mem.index, curr_func);
	  if (rd == NULL) {
	    insn->code = MIR_INVALID_INSN;
	    if (err == MIR_no_error) {
	      err = MIR_undeclared_reg_error; err_msg = "undeclared reg";
	    }
	  } else {
	    insn->ops[i].u.mem.index = rd->reg;
	    if (type2mode (rd->type) != MIR_OP_INT) {
	      insn->code = MIR_INVALID_INSN;
	      if (err == MIR_no_error) {
		err = MIR_reg_type_error; err_msg = "index reg of non-integer type";
	      }
	    }
	  }
	}
	mode = type2mode (insn->ops[i].u.mem.type);
	break;
      case MIR_OP_HARD_REG:
	mode = expected_mode;
	break;
      default:
	mode = insn->ops[i].mode;
	break;
      }
      if (mode != expected_mode) {
	insn->code = MIR_INVALID_INSN;
	if (err == MIR_no_error) {
	  err = MIR_op_mode_error; err_msg = "unexpected operand mode";
	}
      }
    }
  }
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func->insns); insn != NULL; insn = DLIST_NEXT (MIR_insn_t, insn))
    if (insn->code == MIR_INVALID_INSN) {
      curr_func = NULL;
      (*error_func) (err, err_msg);
    }
  curr_func = NULL;
}

const char *MIR_insn_name (MIR_insn_code_t code) {
  if (code >= MIR_INSN_BOUND)
    (*error_func) (MIR_wrong_param_value_error, "MIR_insn_name");
  return insn_descs[code].name;
}

size_t MIR_insn_nops (MIR_insn_code_t code) {
  if (code >= MIR_INSN_BOUND)
    (*error_func) (MIR_wrong_param_value_error, "MIR_insn_nops");
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
    (*error_func) (MIR_alloc_error, "Not enough memory");
  insn->code = code; insn->data = NULL;
  return insn;
}

static MIR_insn_t new_insn1 (MIR_insn_code_t code) { return create_insn (1, code); }

MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops) {
  MIR_insn_t insn;
  size_t i, insn_nops = MIR_insn_nops (code);
  
  if (nops != insn_nops)
    (*error_func) (MIR_ops_num_error, "wrong number of operands");
  insn = create_insn (nops, code);
  for (i = 0; i < nops; i++)
    insn->ops[i] = ops[i];
  return insn;
}

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

static MIR_insn_t create_label (int64_t label_num) {
  MIR_insn_t insn = new_insn1 (MIR_LABEL);

  insn->ops[0] = MIR_new_int_op (label_num);
  return insn;
}

MIR_insn_t MIR_new_label (void) { return create_label (++curr_label_num); }

static reg_desc_t *find_rd_by_reg (MIR_reg_t reg, MIR_func_t func) {
  size_t rdn, temp_rdn;
  reg_desc_t rd;

  rd.reg = reg; rd.func = func; /* keys */
  rd.name_num = 0; rd.type = MIR_I64; /* to eliminate warnings */
  temp_rdn = VARR_LENGTH (reg_desc_t, reg_descs);
  VARR_PUSH (reg_desc_t, reg_descs, rd);
  if (! HTAB_DO (size_t, reg2rdn_tab, temp_rdn, HTAB_FIND, rdn)) {
    VARR_POP (reg_desc_t, reg_descs);
    (*error_func) (MIR_undeclared_reg_error, "undeclared reg");
  }
  return &VARR_ADDR (reg_desc_t, reg_descs)[rdn];
}

MIR_reg_t _MIR_new_temp_reg (MIR_type_t type, MIR_func_t func) {
  static char name[30];
  MIR_reg_t reg;
  
  func->ntemps++;
  sprintf (name, "t%d", func->ntemps);
  reg = VARR_LENGTH (MIR_var_t, func->vars) + func->ntemps + 1; /* fp */
  reg_create (func, reg, name, type, TRUE);
  return reg;
}

MIR_reg_t MIR_reg (const char *name) {
  string_t string = string_store (&strings, &string_tab, name);

  return string.num;
}

MIR_type_t MIR_reg_type (MIR_reg_t reg, MIR_func_t func) { return find_rd_by_reg (reg, func)->type; }

const char *MIR_reg_name (MIR_reg_t reg, MIR_func_t func) {
  return VARR_ADDR (string_t, strings) [find_rd_by_reg (reg, func)->name_num].str;
}

MIR_reg_t MIR_func_reg (const char *reg_name, MIR_func_t func) {
  string_t string = string_store (&strings, &string_tab, reg_name);
  reg_desc_t *rd;
  
  rd = find_rd_by_name_num (string.num, func);
  if (rd == NULL)
    (*error_func) (MIR_undeclared_reg_error, "undeclared reg");
  return rd->reg;
}

/* Functions to create operands.  */

static void init_op (MIR_op_t *op, MIR_op_mode_t mode) { op->mode = mode; op->data = NULL; }

MIR_op_t MIR_new_reg_op (MIR_reg_t reg) {
  MIR_op_t op;

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

MIR_op_t MIR_new_uint_op (uint64_t u) {
  MIR_op_t op;

  init_op (&op, MIR_OP_UINT); op.u.u = u;
  return op;
}

MIR_op_t MIR_new_float_op (float f) {
  MIR_op_t op;

  assert (sizeof (float) == 4); /* IEEE single */
  init_op (&op, MIR_OP_FLOAT); op.u.f = f;
  return op;
}

MIR_op_t MIR_new_double_op (double d) {
  MIR_op_t op;

  assert (sizeof (double) == 8); /* IEEE double */
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
    (*error_func) (MIR_wrong_param_value_error, "MIR_append_insn");
  DLIST_APPEND (MIR_insn_t, func_item->u.func->insns, insn);
}

void MIR_prepend_insn (MIR_item_t func_item, MIR_insn_t insn) {
  if (! func_item->func_p)
    (*error_func) (MIR_wrong_param_value_error, "MIR_prepend_insn");
  DLIST_PREPEND (MIR_insn_t, func_item->u.func->insns, insn);
}

void MIR_insert_insn_after (MIR_item_t func_item, MIR_insn_t after, MIR_insn_t insn) {
  if (! func_item->func_p)
    (*error_func) (MIR_wrong_param_value_error, "MIR_insert_insn_after");
  DLIST_INSERT_AFTER (MIR_insn_t, func_item->u.func->insns, after, insn);
}

void MIR_insert_insn_before (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t insn) {
  if (! func_item->func_p)
    (*error_func) (MIR_wrong_param_value_error, "MIR_insert_insn_before");
  DLIST_INSERT_BEFORE (MIR_insn_t, func_item->u.func->insns, before, insn);
}

void MIR_remove_insn (MIR_item_t func_item, MIR_insn_t insn) { // ??? freeing
  if (! func_item->func_p)
    (*error_func) (MIR_wrong_param_value_error, "MIR_remove_insn");
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
  default:
    (*error_func) (MIR_wrong_param_value_error, "MIR_type_str");
  }
}

static MIR_func_t curr_output_func;

void MIR_output_type (FILE *f, MIR_type_t tp) { fprintf (f, "%s", MIR_type_str (tp)); }

void MIR_output_disp (FILE *f, MIR_disp_t disp) { fprintf (f, "%" PRId64, (int64_t) disp); }

void MIR_output_scale (FILE *f, unsigned scale) { fprintf (f, "%u", scale); }

void MIR_output_reg (FILE *f, MIR_reg_t reg) {
  fprintf (f, "%s", MIR_reg_name (reg, curr_output_func));
}

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
  case MIR_OP_UINT:
    fprintf (f, "%" PRIu64, op.u.u);
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
      fprintf (f, "(");
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
      fprintf (f, ")");
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
    assert (FALSE);
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
  MIR_var_t var;
  size_t i, nlocals;
  
  if (! item->func_p) {
    fprintf (f, "%s:\textern\n", item->u.external);
    return;
  }
  curr_output_func = func = item->u.func;
  fprintf (f, "%s:\tfunc\t%u", func->name, func->frame_size);
  for (i = 0; i < func->nargs; i++) {
    var = VARR_GET (MIR_var_t, func->vars, i);
    fprintf (f, ", %s:%s", MIR_type_str (var.type), var.name);
  }
  fprintf (f, "\n");
  nlocals = VARR_LENGTH (MIR_var_t, func->vars) - func->nargs;
  fprintf (f, "\tlocal\t");
  for (i = 0; i < nlocals; i++) {
    var = VARR_GET (MIR_var_t, func->vars, i + func->nargs);
    fprintf (f, i == 0 ? "%s:%s" : ", %s:%s", MIR_type_str (var.type), var.name);
  }
  fprintf (f, "\n# frame size = %u, %u arg%s, %u local%s\n", func->frame_size,
	   func->nargs, func->nargs == 1 ? "" : "s", (unsigned) nlocals, nlocals == 1 ? "" : "s");
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = DLIST_NEXT (MIR_insn_t, insn))
    MIR_output_insn (f, insn);
  fprintf (f, "\tendfunc\n");
}

void MIR_output (FILE *f) {
  for (MIR_item_t item = DLIST_HEAD (MIR_item_t, MIR_items);
       item != NULL;
       item = DLIST_NEXT (MIR_item_t, item))
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

void MIR_simplify_op (MIR_item_t func_item, MIR_insn_t insn, int nop, int out_p, int move_p) {
  MIR_op_t new_op, mem_op, *op = &insn->ops[nop];
  MIR_insn_t new_insn;
  MIR_func_t func = func_item->u.func;
  MIR_type_t type;
  
  switch (op->mode) {
  case MIR_OP_INT:
  case MIR_OP_FLOAT:
  case MIR_OP_DOUBLE:
  case MIR_OP_NAME:
    assert (! out_p);
    if (move_p)
      return;
    type = op->mode == MIR_OP_FLOAT ? MIR_F : op->mode == MIR_OP_FLOAT ? MIR_D : MIR_I64;
    new_op = MIR_new_reg_op (_MIR_new_temp_reg (type, func));
    MIR_insert_insn_before (func_item, insn,
			    MIR_new_insn (type == MIR_F ? MIR_FMOV : type == MIR_D ? MIR_DMOV : MIR_MOV, new_op, *op));
    *op = new_op;
    break;
  case MIR_OP_REG:
  case MIR_OP_LABEL:
    break; /* Do nothing */
  case MIR_OP_MEM:
    mem_op = *op;
    type = mem_op.u.mem.type;
    if (op->u.mem.base != 0 && op->u.mem.disp == 0 && (op->u.mem.index == 0 || op->u.mem.scale == 0)) {
      mem_op.u.mem.index = 0; mem_op.u.mem.scale = 0;
    } else if (op->u.mem.base == 0 && op->u.mem.index != 0 && op->u.mem.scale == 1 && op->u.mem.disp == 0) {
      mem_op.u.mem.base = op->u.mem.index; mem_op.u.mem.index = 0; mem_op.u.mem.scale = 0;
    } else {
      MIR_op_t addr_op, base_op, ind_op;
      MIR_reg_t addr_reg;
      int after_p = ! move_p && out_p;
      
      addr_reg = _MIR_new_temp_reg (MIR_I64, func);
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
		    ? MIR_new_reg_op (_MIR_new_temp_reg (MIR_I64, func)) : addr_op);
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
    if (move_p && (nop == 1 || insn->ops[1].mode == MIR_OP_REG)) {
      *op = mem_op;
    } else {
      new_op = MIR_new_reg_op (_MIR_new_temp_reg (type != MIR_F && type != MIR_D ? MIR_I64 : type, func));
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
    assert (FALSE);
  }
}

void MIR_simplify_insn (MIR_item_t func_item, MIR_insn_t insn) {
  int out_p;
  MIR_insn_code_t code = insn->code;
  size_t i, nops = MIR_insn_nops (code);

  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (code, i, &out_p);
    MIR_simplify_op (func_item, insn, i, out_p, code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV);
  }
}

static void make_one_ret (MIR_item_t func_item, MIR_insn_code_t ret_code) {
  size_t i;
  MIR_insn_code_t mov_code;
  MIR_type_t ret_type;
  MIR_reg_t ret_reg;
  MIR_op_t reg_op;
  MIR_insn_t ret_label, insn = DLIST_TAIL (MIR_insn_t, func_item->u.func->insns);
  
  if (VARR_LENGTH (MIR_insn_t, ret_insns) == 1 && VARR_GET (MIR_insn_t, ret_insns, 0) == insn)
    return;
  assert (ret_code == MIR_RET || ret_code == MIR_FRET || ret_code == MIR_DRET);
  ret_type = ret_code == MIR_RET ? MIR_I64 : ret_code == MIR_FRET ? MIR_F : MIR_D;
  mov_code = ret_code == MIR_RET ? MIR_MOV : ret_code == MIR_FRET ? MIR_FMOV : MIR_DMOV;
  ret_reg = _MIR_new_temp_reg (ret_type, func_item->u.func);
  ret_label = NULL;
  if (VARR_LENGTH (MIR_insn_t, ret_insns) != 0) {
    ret_label = MIR_new_label ();
    MIR_append_insn (func_item, ret_label);
  }
  MIR_append_insn (func_item, MIR_new_insn (ret_code, MIR_new_reg_op (ret_reg)));
  for (i = 0; i < VARR_LENGTH (MIR_insn_t, ret_insns); i++) {
    insn = VARR_GET (MIR_insn_t, ret_insns, i);
    reg_op = insn->ops[0];
    assert (reg_op.mode == MIR_OP_REG);
    MIR_insert_insn_before (func_item, insn, MIR_new_insn (mov_code, MIR_new_reg_op (ret_reg), reg_op));
    MIR_insert_insn_before (func_item, insn, MIR_new_insn (MIR_JMP, MIR_new_label_op (ret_label)));
    MIR_remove_insn (func_item, insn);
  }
}

void MIR_simplify_func (MIR_item_t func_item) {
  MIR_func_t func = func_item->u.func;
  MIR_insn_t insn, next_insn;
  MIR_insn_code_t ret_code = MIR_INSN_BOUND;
  
  if (! func_item->func_p)
    (*error_func) (MIR_wrong_param_value_error, "MIR_remove_simplify");
  func = func_item->u.func;
  VARR_TRUNC (MIR_insn_t, ret_insns, 0);
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    MIR_insn_code_t code = insn->code;
    MIR_op_t temp_op;
    
    if ((code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV) && insn->ops[0].mode == MIR_OP_MEM  && insn->ops[1].mode == MIR_OP_MEM) {
      temp_op = MIR_new_reg_op (_MIR_new_temp_reg (code == MIR_MOV ? MIR_I64 : code == MIR_FMOV ? MIR_F : MIR_D, func));
      MIR_insert_insn_after (func_item, insn, MIR_new_insn (code, insn->ops[0], temp_op));
      insn->ops[0] = temp_op;
    }
    if (code == MIR_RET || code == MIR_FRET || code == MIR_DRET) {
      if (ret_code == MIR_INSN_BOUND)
	ret_code = code;
      else if (ret_code != code)
	(*error_func) (MIR_repeated_decl_error, "Different types in returns");
      VARR_PUSH (MIR_insn_t, ret_insns, insn);
    }
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    MIR_simplify_insn (func_item, insn);
  }
  make_one_ret (func_item, ret_code == MIR_INSN_BOUND ? MIR_RET : ret_code);
}

const char *_MIR_uniq_string (const char * str) {
  return string_store (&strings, &string_tab, str).str;
}



#if MIR_IO

/* Input/output of binary MIR.  Major goal of binary MIR is fast
   reading, not compression ratio.  Text MIR major CPU time consumer
   is a scanner.  Mostly in reading binary MIR we skip the scanner
   part by using tokens.  Each token starts with a tag which describes
   subsequent optional bytes.  */

typedef enum {
  TAG_U0, TAG_U1, TAG_U2, TAG_U3, TAG_U4, TAG_U5, TAG_U6, TAG_U7, TAG_U8,
  TAG_I1, TAG_I2, TAG_I3, TAG_I4, TAG_I5, TAG_I6, TAG_I7, TAG_I8,
  TAG_F, TAG_D, /* 4 and 8 bytes for floating point numbers */
  TAG_REG1, TAG_REG2, TAG_REG3, TAG_REG4, /* Reg string number in 1, 2, 3, 4 bytes */
  TAG_STR1, TAG_STR2, TAG_STR3, TAG_STR4, /* String number in 1, 2, 3, 4 bytes */
  TAG_LAB1, TAG_LAB2, TAG_LAB3, TAG_LAB4, /* Label number in 1, 2, 3, 4 bytes */
  /* Tags for memory operands.  The memory address parts are the subsequent tokens */
  TAG_MEM_DISP, TAG_MEM_BASE, TAG_MEM_INDEX, TAG_MEM_DISP_BASE, TAG_MEM_DISP_INDEX,
  TAG_MEM_BASE_INDEX, TAG_MEM_DISP_BASE_INDEX,
  /* MIR types. The same order as MIR types: */
  TAG_TI8, TAG_TU8, TAG_TI16, TAG_TU16, TAG_TI32, TAG_TU32, TAG_TI64, TAG_TU64,
  TAG_TF, TAG_TD, TAG_TBLOCK,
  TAG_EOI, TAG_EOF, /* end of insn with variable number operands (e.g. a call) or end of file */
  /* unsigned integer 0..127 is kept in one byte.  The most significant bit of the byte is 1: */
  U0_MASK = 0x7f, U0_FLAG = 0x80,
} bin_tag_t;

/* MIR binary format:

   VERSION
   NSTR
   (string)*
   ( ((label)* (insn code) (operand)* | STRN=(func|local|import|export) ...) EOI? )*
   EOF
   MUM_HASH

   where
   o VERSION and NSTR are unsigned tokens
   o insn code is unsigned token
   o string is string number tokens
   o operand is unsigned, signed, float, double, string, label, memory tokens
   o EOI, EOF - tokens for end of insn (optional for most insns) and end of file
   o MUM hash - unsigned of the all read code.
*/

static int CURR_BIN_VERSION = 1;

static VARR (string_t) *output_strings;
static HTAB (string_t) *output_string_tab;

static void put_byte (FILE *f, int ch) {
  if (f == NULL)
    return;
  fputc (ch, f);
}

static int uint_length (uint64_t u) {
  int n;
  
  if (u <= 127)
    return 0;
  for (n = 0; u != 0; n++)
    u >>= CHAR_BIT;
  return n;
}

static void put_uint (FILE *f, uint64_t u, int nb) {
  if (f == NULL)
    return;
  for (int n = 0; n < nb; n++) {
    put_byte (f, u & 0xff);
    u >>= CHAR_BIT;
  }
}

static int int_length (int64_t i) {
  int n = 0;
  
  do {
    n++;
    i /= (1 << CHAR_BIT);
  } while (i != 0);
  return n;
}

static void put_int (FILE *f, int64_t u, int nb) {
  if (f == NULL)
    return;
  for (int n = 0; n < nb; n++) {
    put_byte (f, u & 0xff);
    u >>= CHAR_BIT;
  }
}

static void put_float (FILE *f, float fl) {
  union {uint32_t u; float f;} u;

  if (f == NULL)
    return;
  u.f = fl;
  put_uint (f, u.u, sizeof (uint32_t));
}

static void put_double (FILE *f, double d) {
  union {uint64_t u; double d;} u;

  if (f == NULL)
    return;
  u.d = d;
  put_uint (f, u.d, sizeof (uint64_t));
}

/* Write binary MIR */

static void write_int (FILE *f, int64_t i) {
  int nb;

  if (f == NULL)
    return;
  nb = int_length (i);
  put_byte (f, TAG_I1 + nb - 1);
  put_int (f, i, nb);
}

static void write_uint (FILE *f, uint64_t u) {
  int nb;

  if (f == NULL)
    return;
  if ((nb = uint_length (u)) == 0) {
    put_byte (f, 0x80 | u);
    return;
  }
  put_byte (f, TAG_U1 + nb - 1);
  put_uint (f, u, nb);
}

static void write_float (FILE *f, float fl) {
  if (f == NULL)
    return;
  put_byte (f, TAG_F);
  put_float (f, fl);
}

static void write_double (FILE *f, double d) {
  if (f == NULL)
    return;
  put_byte (f, TAG_D);
  put_double (f, d);
}

static void write_str_tag (FILE *f, const char *str, bin_tag_t start_tag) {
  int nb, ok_p;
  string_t string;
  
  if (f == NULL) {
    string_store (&output_strings, &output_string_tab, str);
    return;
  }
  ok_p = string_find (&output_strings, &output_string_tab, str, &string);
  assert (ok_p && string.num >= 1);
  nb = uint_length (string.num - 1);
  assert (nb <= 4);
  if (nb == 0)
    nb = 1;
  put_byte (f, start_tag + nb - 1);
  put_uint (f, string.num - 1, nb);
}

static void write_str (FILE *f, const char *str) { write_str_tag (f, str, TAG_STR1); }
static void write_reg (FILE *f, const char *reg_name) { write_str_tag (f, reg_name, TAG_REG1); }

static void write_type (FILE *f, MIR_type_t t) { put_byte (f, TAG_TI8 + (t - MIR_I8)); }

static void write_lab (FILE *f, MIR_label_t lab) {
  int nb;
  uint64_t lab_num;
  
  if (f == NULL)
    return;
  lab_num = lab->ops[0].u.u;
  nb = uint_length (lab_num);
  assert (nb <= 4);
  if (nb == 0)
    nb = 1;
  put_byte (f, TAG_LAB1 + nb - 1);
  put_uint (f, lab_num, nb);
}

static void MIR_write_op (FILE *f, MIR_op_t op) {
  switch (op.mode) {
  case MIR_OP_REG:
    write_reg (f, MIR_reg_name (op.u.reg, curr_output_func));
    break;
  case MIR_OP_INT:
    write_int (f, op.u.i);
    break;
  case MIR_OP_UINT:
    write_uint (f, op.u.u);
    break;
  case MIR_OP_FLOAT:
    write_float (f, op.u.f);
    break;
  case MIR_OP_DOUBLE:
    write_double (f, op.u.d);
    break;
  case MIR_OP_MEM: {
    bin_tag_t tag;
    
    if (op.u.mem.disp != 0) {
      if (op.u.mem.base != 0)
	tag = op.u.mem.index != 0 ? TAG_MEM_DISP_BASE_INDEX : TAG_MEM_DISP_BASE;
      else  
	tag = op.u.mem.index != 0 ? TAG_MEM_DISP_INDEX : TAG_MEM_DISP;
    } else if (op.u.mem.base != 0) {
      tag = op.u.mem.index != 0 ? TAG_MEM_BASE_INDEX : TAG_MEM_BASE;
    } else if (op.u.mem.index != 0) {
      tag = TAG_MEM_INDEX;
    }
    put_byte (f, tag);
    write_type (f, op.u.mem.type);
    if (op.u.mem.disp != 0)
      write_int (f, op.u.mem.disp);
    if (op.u.mem.base != 0)
      write_reg (f, MIR_reg_name (op.u.mem.base, curr_output_func));
    if (op.u.mem.index != 0) {
      write_reg (f, MIR_reg_name (op.u.mem.index, curr_output_func));
      write_uint (f, op.u.mem.scale);
    }
    break;
  }
  case MIR_OP_NAME:
    write_str (f, op.u.name);
    break;
  case MIR_OP_LABEL:
    write_lab (f, op.u.label);
    break;
  default: /* ??? HARD_REG, HARD_REG_MEM */
    assert (FALSE);
  }
}

static void MIR_write_insn (FILE *f, MIR_insn_t insn) {
  size_t i, nops;

  if (insn->code == MIR_LABEL) {
    write_lab (f, insn);
    return;
  }
  nops = MIR_insn_nops (insn->code);
  write_uint (f, insn->code);
  for (i = 0; i < nops; i++) {
    MIR_write_op (f, insn->ops[i]);
  }
  if (insn_descs[insn->code].op_modes[0] == MIR_OP_UNDEF)
    /* first operand mode iff it is a variable parameter insn */
    put_byte (f, TAG_EOI);
}

static void MIR_write_item (FILE *f, MIR_item_t item) {
  MIR_insn_t insn;
  MIR_func_t func;
  MIR_var_t var;
  size_t i, nlocals;

  if (! item->func_p) {
    write_str (f, "import");
    write_str (f, item->u.external);
    put_byte (f, TAG_EOI);
    return;
  }
  func = item->u.func;
  write_str (f, "func");
  write_str (f, func->name);
  write_uint (f, func->frame_size);
  for (i = 0; i < func->nargs; i++) {
    var = VARR_GET (MIR_var_t, func->vars, i);
    write_type (f, var.type);
    write_str (f, var.name);
  }
  put_byte (f, TAG_EOI);
  nlocals = VARR_LENGTH (MIR_var_t, func->vars) - func->nargs;
  if (nlocals !=  0) {
    write_str (f, "local");
    for (i = 0; i < nlocals; i++) {
      var = VARR_GET (MIR_var_t, func->vars, i + func->nargs);
      write_type (f, var.type);
      write_str (f, var.name);
    }
    put_byte (f, TAG_EOI);
  }
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = DLIST_NEXT (MIR_insn_t, insn))
    MIR_write_insn (f, insn);
  write_str (f, "endfunc");
}

static void write_items (FILE *f) {
  for (MIR_item_t item = DLIST_HEAD (MIR_item_t, MIR_items);
       item != NULL;
       item = DLIST_NEXT (MIR_item_t, item))
    MIR_write_item (f, item);
}

void MIR_write (FILE *f) {
  string_init (&output_strings, &output_string_tab);
  write_items (NULL); /* store strings */
  write_uint (f, CURR_BIN_VERSION);
  write_uint (f, VARR_LENGTH (string_t, output_strings) - 1);
  for (size_t i = 1; i < VARR_LENGTH (string_t, output_strings); i++) { /* output strings */
    fputs (VARR_GET (string_t, output_strings, i).str, f);
    fputc ('\0', f);
  }
  write_items (f);
  put_byte (f, TAG_EOF);
  string_finish (&output_strings, &output_string_tab);
}



static int get_byte (FILE *f) {
  int c = fgetc (f);

  if (c == EOF)
    (*error_func) (MIR_binary_io_error, "unfinished binary MIR");
  return c;
}

typedef union {
  uint64_t u;
  int64_t i;
  float f;
  double d;
  MIR_type_t t;
  MIR_reg_t reg;
} token_attr_t;

static uint64_t get_uint (FILE *f, int nb) {
  uint64_t res = 0;
  
  for (int i = 0; i < nb; i++)
    res |= (unsigned char) get_byte (f) << (i * CHAR_BIT);
  return res;
}

static int64_t get_int (FILE *f, int nb) {
  int sh = (8 - nb) * CHAR_BIT;
  
  assert (0 < nb && nb <= 8);
  return (int64_t) (get_uint (f, nb) << sh) >> sh;
}

static float get_float (FILE *f) {
  union {uint32_t u; float f;} u;

  u.u = get_uint (f, sizeof (uint32_t));
  return u.f;
}

static double get_double (FILE *f) {
  union {uint64_t u; double d;} u;

  u.u = get_uint (f, sizeof (uint64_t));
  return u.d;
}

typedef char *char_ptr_t;
DEF_VARR (char_ptr_t);
static VARR (char_ptr_t) *bin_strings; 

static const char *to_str (uint64_t str_num) {
  if (str_num >= VARR_LENGTH (char_ptr_t, bin_strings))
    (*error_func) (MIR_binary_io_error, "wrong string num");
  return VARR_GET (char_ptr_t, bin_strings, str_num);
}

static MIR_reg_t to_reg (uint64_t reg_str_num) {
  return MIR_reg (to_str (reg_str_num));
}

DEF_VARR (MIR_label_t);
static VARR (MIR_label_t) *label_map;

static MIR_label_t to_lab (uint64_t lab_num) { return create_label (lab_num); }

static void read_all_strings (FILE *f, uint64_t nstr) {
  int c;
  char *str;

  VARR_CREATE (char_ptr_t, bin_strings, nstr);
  for (uint64_t i = 0; i < nstr; i++) {
    VARR_TRUNC (char, temp_string, 0);
    do {
      c = get_byte (f);
      VARR_PUSH (char, temp_string, c);
    } while (c != '\0');
    str = malloc (VARR_LENGTH (char, temp_string));
    strcpy (str, VARR_ADDR (char, temp_string));
    VARR_PUSH (char_ptr_t, bin_strings, str);
  }
}

static uint64_t read_uint (FILE *f, const char *err_msg) {
  int c = get_byte (f);
  
  if (c & U0_FLAG)
    return c & U0_MASK;
  if (TAG_U1 > c || c > TAG_U8)
    (*error_func) (MIR_binary_io_error, err_msg);
  return get_uint (f, c - TAG_U1 + 1);
}

static MIR_type_t tag_type (bin_tag_t tag) { return (MIR_type_t) (tag - TAG_TI8) + MIR_I8; }

static MIR_type_t read_type (FILE *f, const char *err_msg) {
  int c = get_byte (f);
  
  if (TAG_TI8 > c || c > TAG_TBLOCK)
    (*error_func) (MIR_binary_io_error, err_msg);
  return tag_type (c);
}

static const char *read_string (FILE *f, const char *err_msg) {
  int c = get_byte (f);
  
  if (TAG_STR1 > c || c > TAG_STR4)
    (*error_func) (MIR_binary_io_error, err_msg);
  return to_str (get_uint (f, c - TAG_STR1 + 1));
}

static bin_tag_t read_token (FILE *f, token_attr_t *attr) {
  int c = get_byte (f);
  
  if (c & U0_FLAG) {
    attr->u = c & U0_MASK;
    return TAG_U0;
  }
  switch (c) {
  case TAG_U1: case TAG_U2: case TAG_U3: case TAG_U4: case TAG_U5: case TAG_U6: case TAG_U7: case TAG_U8:
    attr->u = get_uint (f, c - TAG_U1 + 1); break;
  case TAG_I1: case TAG_I2: case TAG_I3: case TAG_I4: case TAG_I5: case TAG_I6: case TAG_I7: case TAG_I8:
    attr->i = get_int (f, c - TAG_I1 + 1); break;
  case TAG_F: attr->f = get_float (f); break;
  case TAG_D: attr->f = get_double (f); break;
  case TAG_REG1: case TAG_REG2: case TAG_REG3: case TAG_REG4:
    attr->u = get_uint (f, c - TAG_REG1 + 1); break;
  case TAG_STR1: case TAG_STR2: case TAG_STR3: case TAG_STR4:
    attr->u = get_uint (f, c - TAG_STR1 + 1); break;
  case TAG_LAB1: case TAG_LAB2: case TAG_LAB3: case TAG_LAB4:
    attr->u = get_uint (f, c - TAG_LAB1 + 1); break;
  case TAG_MEM_DISP: case TAG_MEM_BASE: case TAG_MEM_INDEX: case TAG_MEM_DISP_BASE: case TAG_MEM_DISP_INDEX:
  case TAG_MEM_BASE_INDEX: case TAG_MEM_DISP_BASE_INDEX: case TAG_EOI: case TAG_EOF:
    break;
  case TAG_TI8: case TAG_TU8: case TAG_TI16: case TAG_TU16: case TAG_TI32: case TAG_TU32:
  case TAG_TI64: case TAG_TU64: case TAG_TF: case TAG_TD: case TAG_TBLOCK:
    attr->t = (MIR_type_t) (c - TAG_TI8) + MIR_I8;
    break;
  default:
    (*error_func) (MIR_binary_io_error, "wrong tag");
  }
  return c;
}

static MIR_disp_t read_disp (FILE *f) {
  bin_tag_t tag;
  token_attr_t attr;

  tag = read_token (f, &attr);
  if (TAG_I1 > tag || tag > TAG_I8)
    (*error_func) (MIR_binary_io_error, "wrong memory disp");
  return attr.i;
}

static MIR_reg_t read_reg (FILE *f) {
  bin_tag_t tag;
  token_attr_t attr;

  tag = read_token (f, &attr);
  if (TAG_REG1 > tag || tag > TAG_REG4)
    (*error_func) (MIR_binary_io_error, "wrong memory disp");
  return to_reg (attr.u);
}

static int read_operand (FILE *f, MIR_op_t *op) {
  bin_tag_t tag;
  token_attr_t attr;
  MIR_type_t t;
  MIR_disp_t disp;
  MIR_reg_t base, index;
  MIR_scale_t scale;
  
  tag = read_token (f, &attr);
  switch (tag) {
  case TAG_U0: case TAG_U1: case TAG_U2: case TAG_U3: case TAG_U4:
  case TAG_U5: case TAG_U6: case TAG_U7: case TAG_U8:
    *op = MIR_new_uint_op (attr.u); break;
  case TAG_I1: case TAG_I2: case TAG_I3: case TAG_I4: case TAG_I5: case TAG_I6: case TAG_I7: case TAG_I8:
    *op = MIR_new_int_op (attr.i); break;
  case TAG_F: *op = MIR_new_float_op (attr.f); break;
  case TAG_D: *op = MIR_new_double_op (attr.d); break;
  case TAG_REG1: case TAG_REG2: case TAG_REG3: case TAG_REG4:
    *op = MIR_new_reg_op (to_reg (attr.u)); break;
  case TAG_STR1: case TAG_STR2: case TAG_STR3: case TAG_STR4:
    *op = MIR_new_name_op (to_str (attr.u)); break;
  case TAG_LAB1: case TAG_LAB2: case TAG_LAB3: case TAG_LAB4:
    *op = MIR_new_label_op (to_lab (attr.u)); break;
  case TAG_MEM_DISP: case TAG_MEM_BASE: case TAG_MEM_INDEX: case TAG_MEM_DISP_BASE: case TAG_MEM_DISP_INDEX:
  case TAG_MEM_BASE_INDEX: case TAG_MEM_DISP_BASE_INDEX:
    t = read_type (f, "wrong memory type");
    disp = (tag == TAG_MEM_DISP || tag == TAG_MEM_DISP_BASE || tag == TAG_MEM_DISP_INDEX
	    || tag == TAG_MEM_DISP_BASE_INDEX ? read_disp (f) : 0);
    base = (tag == TAG_MEM_BASE || tag == TAG_MEM_DISP_BASE || tag == TAG_MEM_BASE_INDEX
	    || tag == TAG_MEM_DISP_BASE_INDEX ? read_reg (f) : 0);
    index = 0; scale = 0;
    if (tag == TAG_MEM_INDEX || tag == TAG_MEM_DISP_INDEX || tag == TAG_MEM_BASE_INDEX
	|| tag == TAG_MEM_DISP_BASE_INDEX) {
      index = read_reg (f);
      scale = read_uint (f, "wrong memory index scale");
    }
    *op = MIR_new_mem_op (t, disp, base, index, scale);
    break;
  case TAG_EOI:
    return FALSE;
  default:
    assert (FALSE);
  }
  return TRUE;
}

DEF_VARR (uint64_t);

void MIR_read (FILE *f) {
  int version;
  bin_tag_t tag;
  token_attr_t attr;
  MIR_error_func_t saved_error_func;
  MIR_label_t lab;
  uint64_t nstr, u;
  MIR_op_t op;
  size_t n, nop;
  const char *name;
  MIR_item_t func;
  MIR_var_t var;
  VARR (uint64_t) *insn_label_string_nums;
  
  saved_error_func = MIR_get_error_func ();
  MIR_set_error_func (error_func);
  version = read_uint (f, "wrong header");
  if (version > CURR_BIN_VERSION)
    (*error_func) (MIR_binary_io_error, "can not read a newer MIR format version binary");
  nstr = read_uint (f, "wrong header");
  read_all_strings (f, nstr);
  func = NULL;
  VARR_CREATE (uint64_t, insn_label_string_nums, 64);
  VARR_CREATE (MIR_label_t, label_map, 64);
  for (;;) {
    VARR_TRUNC (uint64_t, insn_label_string_nums, 0);
    tag = read_token (f, &attr);
    while (TAG_LAB1 <= tag && tag <= TAG_LAB4) {
      VARR_PUSH (uint64_t, insn_label_string_nums, attr.u);
      tag = read_token (f, &attr);
    }
    VARR_TRUNC (MIR_op_t, temp_insn_ops, 0);
    if (TAG_STR1 <= tag && tag <= TAG_STR4) {
      name = to_str (attr.u);
      if (strcmp (name, "func") == 0) {
	if (VARR_LENGTH (uint64_t, insn_label_string_nums) != 0)
	  (*error_func) (MIR_binary_io_error, "insn label before func");
	if (func != NULL)
	  (*error_func) (MIR_binary_io_error, "nested func");
	/* Clear label map */
	VARR_TRUNC (MIR_label_t, label_map, 0);
	while (VARR_LENGTH (MIR_label_t, label_map) != nstr)
	  VARR_PUSH (MIR_label_t, label_map, NULL);
	name = read_string (f, "wrong func name");
	u = read_uint (f, "wrong func frame size");
	VARR_TRUNC (MIR_var_t, temp_vars, 0);
	for (;;) {
	  tag = read_token (f, &attr);
	  if (tag == TAG_EOI)
	    break;
	  if (TAG_TI8 > tag || tag > TAG_TBLOCK)
	    (*error_func) (MIR_binary_io_error, "wrong func arg type");
	  var.type = tag_type (tag);
	  var.name = read_string (f, "wrong arg name");
	  VARR_PUSH (MIR_var_t, temp_vars, var);
	}
	func = MIR_new_func_arr (name, u, VARR_LENGTH (MIR_var_t, temp_vars), VARR_ADDR (MIR_var_t, temp_vars));
      } else if (strcmp (name, "endfunc") == 0) {
	if (VARR_LENGTH (uint64_t, insn_label_string_nums) != 0)
	  (*error_func) (MIR_binary_io_error, "endfunc should have no labels");
	if (func == NULL)
	  (*error_func) (MIR_binary_io_error, "endfunc without func");
	MIR_finish_func ();
      } else if (strcmp (name, "local") == 0) {
	if (func == NULL)
	  (*error_func) (MIR_syntax_error, "local outside func");
	if (VARR_LENGTH (uint64_t, insn_label_string_nums) != 0)
	  (*error_func) (MIR_syntax_error, "local should have no labels");
	for (;;) {
	  tag = read_token (f, &attr);
	  if (tag == TAG_EOI)
	    break;
	  if (TAG_TI8 > tag || tag > TAG_TBLOCK)
	    (*error_func) (MIR_binary_io_error, "wrong local var type");
	  MIR_create_func_var (func->u.func, tag_type (tag), read_string (f, "wrong local name"));
	}
      } else {
	(*error_func) (MIR_binary_io_error, "unknown insn name");
      }
    } else if (TAG_U0 <= tag && tag <= TAG_U8) { /* insn code */
      MIR_insn_code_t insn_code = attr.u;
      
      if (insn_code >= MIR_LABEL)
	(*error_func) (MIR_binary_io_error, "wrong insn code");
      for (uint64_t i = 0; i < VARR_LENGTH (uint64_t, insn_label_string_nums); i++) {
	lab = to_lab (VARR_GET (uint64_t, insn_label_string_nums, i));
	MIR_append_insn (func, lab);
      }
      nop = MIR_insn_nops (insn_code);
      for (n = 0; (nop == 0 || n < nop) && read_operand (f, &op); n++)
	VARR_PUSH (MIR_op_t, temp_insn_ops, op);
      if (nop != 0 && n < nop)
	(*error_func) (MIR_binary_io_error, "wrong number of insn operands");
      MIR_append_insn (func, MIR_new_insn_arr (insn_code, n, VARR_ADDR (MIR_op_t, temp_insn_ops)));
    } else if (tag == TAG_EOF) {
      break;
    } else {
      (*error_func) (MIR_binary_io_error, "wrong token");
    }
  }
  VARR_DESTROY (MIR_label_t, label_map);
  VARR_DESTROY (uint64_t, insn_label_string_nums);
  VARR_DESTROY (char_ptr_t, bin_strings);
  if (fgetc (f) != EOF)
    (*error_func) (MIR_binary_io_error, "garbage at the end of file");
  MIR_set_error_func (saved_error_func);
}

#endif /* if MIR_IO */



/* Reading MIR text file */

#if MIR_SCAN

#include <stddef.h>
#include <stdlib.h>
#include <ctype.h>
#include <errno.h>
#include <setjmp.h>

static size_t curr_line_num;

typedef struct insn_name {
  const char *name;
  MIR_insn_code_t code;
} insn_name_t;

static int insn_name_eq (insn_name_t in1, insn_name_t in2) { return strcmp (in1.name, in2.name) == 0; }
static htab_hash_t insn_name_hash (insn_name_t in) { return mum_hash (in.name, strlen (in.name), 0x42); }

DEF_HTAB (insn_name_t);
static HTAB (insn_name_t) *insn_name_tab;

enum token_code { TC_INT, TC_FLOAT, TC_DOUBLE, TC_NAME, TC_STR, TC_NL, TC_EOF, TC_LEFT_PAR, TC_RIGHT_PAR, TC_COMMA, TC_SEMICOL, TC_COL };

typedef struct token {
  enum token_code code;
  union {
    int64_t i;
    float f;
    double d;
    const char *name;
    const char *str;
  } u;
} token_t;

static jmp_buf error_jmp_buf;

static void MIR_NO_RETURN process_error (enum MIR_error_type error_type, const char *message) {
  (*error_func) (error_type, message);
  longjmp (error_jmp_buf, TRUE);
}

/* Read number using GET_CHAR and UNGET_CHAR and already read
   character CH.  It should be guaranted that the input has a righ
   prefix (+|-)?[0-9].  Return base, float and double flag through
   BASE, FLOAT_P, DOUBLE_P.  Put number representation (0x or 0X
   prefix is removed) into TEMP_STRING.  */
static void scan_number (int ch, int get_char (void), void unget_char (int),
			 int *base, int *float_p, int *double_p) {
  enum scan_number_code {NUMBER_OK, ABSENT_EXPONENT, NON_DECIMAL_FLOAT, WRONG_OCTAL_INT} err_code = NUMBER_OK;
  int dec_p, hex_p, hex_char_p;
  
  *base = 10;
  *double_p = *float_p = FALSE;
  if (ch == '+' || ch == '-') {
    VARR_PUSH (char, temp_string, ch);
    ch = get_char ();
  }
  assert ('0' <= ch && ch <= '9');
  if (ch == '0') {
    ch = get_char ();
    if (ch != 'x' && ch != 'X') {
      *base = 8;
      unget_char (ch);
      ch = '0';
    } else {
      ch = get_char ();
      *base = 16;
    }
  }
  dec_p = hex_p = FALSE;
  for (;;) {
    if (ch != '_')
      VARR_PUSH (char, temp_string, ch);
    ch = get_char ();
    if (ch == '8' || ch == '9')
      dec_p = TRUE;
    hex_char_p = (('a' <= ch && ch <= 'f') || ('A' <= ch && ch <= 'F'));
    if (ch != '_' && ! isdigit (ch) && (*base != 16 || ! hex_char_p))
      break;
    if (hex_char_p)
      hex_p = TRUE;
  }
  assert (*base == 16 || ! hex_p);
  if (ch == '.') {
    *double_p = TRUE;
    do {
      if (ch != '_')
	VARR_PUSH (char, temp_string, ch);
      ch = get_char ();
    } while (isdigit (ch) || ch == '_');
  }
  if (ch == 'e' || ch == 'E') {
    *double_p = TRUE;
    ch = get_char ();
    if (ch != '+' && ch != '-' && ! isdigit (ch))
      err_code = ABSENT_EXPONENT;
    else {
      VARR_PUSH (char, temp_string, 'e');
      if (ch == '+' || ch == '-') {
	VARR_PUSH (char, temp_string, '-');
	ch = get_char ();
	if (! isdigit (ch))
	  err_code = ABSENT_EXPONENT;
      }
      if (err_code == NUMBER_OK)
	do {
	  if (ch != '_')
	    VARR_PUSH (char, temp_string, ch);
	  ch = get_char ();
	} while (isdigit (ch) || ch == '_');
    }
  }
  if (*double_p) {
    if (*base == 16)
      err_code = NON_DECIMAL_FLOAT;
    else if (ch == 'f' || ch == 'F') {
      *float_p = TRUE; *double_p = FALSE;
    }
  } else if (*base == 8 && dec_p)
    err_code = WRONG_OCTAL_INT;
  VARR_PUSH (char, temp_string, '\0');
  unget_char (ch);
}

static const char *input_string;
static size_t input_string_char_num;

static int get_string_char (void) {
  int ch = input_string[input_string_char_num];

  if (ch == '\0')
    return EOF;
  input_string_char_num++;
  return ch;
}

static void unget_string_char (int ch) {
  if (input_string_char_num == 0 || ch == EOF)
    return;
  input_string_char_num--;
  assert (input_string[input_string_char_num] == ch);
}

static token_t scan_token (int (*get_char) (void), void (*unget_char) (int)) {
  int ch;
  token_t token;
  
  for (;;) {
    ch = get_char ();
    switch (ch) {
    case EOF:
      token.code = TC_EOF;
      return token;
    case ' ': case '\t':
      break;
    case '#':
      while ((ch = get_char ()) != '\n' && ch != EOF)
	;
      /* Fall through: */
    case '\n':
      curr_line_num++;
      token.code = TC_NL;
      return token;
      break;
    case '(':
      token.code = TC_LEFT_PAR;
      return token;
      break;
    case ')':
      token.code = TC_RIGHT_PAR;
      return token;
      break;
    case ',':
      token.code = TC_COMMA;
      return token;
    case ';':
      token.code = TC_SEMICOL;
      return token;
    case ':':
      token.code = TC_COL;
      return token;
    default:
      VARR_TRUNC (char, temp_string, 0);
      if (isalpha (ch) || ch == '_') {
	do {
	  VARR_PUSH (char, temp_string, ch);
	  ch = get_char ();
	} while (isalpha (ch) || isdigit (ch) || ch == '_');
	VARR_PUSH (char, temp_string, '\0');
	unget_char (ch);
	token.u.str = _MIR_uniq_string (VARR_ADDR (char, temp_string));
	token.code = TC_NAME;
	return token;
      } else if (ch == '+' || ch == '-' || isdigit (ch)) {
	const char *repr;
	char *end;
	int next_ch, base, float_p, double_p;
	
	if (ch == '+' || ch == '-') {
	  next_ch = get_char ();
	  if (! isdigit (next_ch))
	    process_error (MIR_syntax_error, "no number after a sign");
	  unget_char (next_ch);
	}
	scan_number (ch, get_char, unget_char, &base, &float_p, &double_p);
	repr = VARR_ADDR (char, temp_string);
	errno = 0;
	if (float_p) {
	  token.code = TC_FLOAT;
	  token.u.f = strtof (repr, &end);
	} else if (double_p) {
	  token.code = TC_DOUBLE;
	  token.u.d = strtod (repr, &end);
	} else {
	  token.code = TC_INT;
	  token.u.i = sizeof (long) == sizeof (int64_t) ? strtol (repr, &end, base) : strtoll (repr, &end, base);
	}
	assert (*end == '\0');
	if (errno != 0)
	  ;
	return token;
      } else {
	process_error (MIR_syntax_error, "wrong char");
      }
    }
  }
}

typedef const char *label_name_t;
DEF_VARR (label_name_t);
static VARR (label_name_t) *label_names;

typedef struct label_desc {
  const char *name;
  MIR_label_t label;
} label_desc_t;

DEF_HTAB (label_desc_t);
static HTAB (label_desc_t) *label_desc_tab;

static int label_eq (label_desc_t l1, label_desc_t l2) { return strcmp (l1.name, l2.name) == 0; }
static htab_hash_t label_hash (label_desc_t l) { return mum_hash (l.name, strlen (l.name), 0x42); }

static MIR_label_t create_label_desc (const char *name) {
  MIR_label_t label;
  label_desc_t label_desc;

  label_desc.name = name;
  if (HTAB_DO (label_desc_t, label_desc_tab, label_desc, HTAB_FIND, label_desc)) {
    label = label_desc.label;
  } else {
    label_desc.label = label = MIR_new_label ();
    HTAB_DO (label_desc_t, label_desc_tab, label_desc, HTAB_INSERT, label_desc);
  }
  return label;
}

MIR_type_t MIR_str2type (const char *type_name) {
  if (strcmp (type_name, "i64") == 0)
    return MIR_I64;
  if (strcmp (type_name, "f") == 0)
    return MIR_F;
  if (strcmp (type_name, "d") == 0)
    return MIR_D;
  if (strcmp (type_name, "i32") == 0)
    return MIR_I32;
  if (strcmp (type_name, "u32") == 0)
    return MIR_U32;
  if (strcmp (type_name, "i16") == 0)
    return MIR_I16;
  if (strcmp (type_name, "u16") == 0)
    return MIR_U16;
  if (strcmp (type_name, "i8") == 0)
    return MIR_I8;
  if (strcmp (type_name, "u8") == 0)
    return MIR_U8;
  return MIR_T_BOUND;
}

/* Syntax:
     program: { insn / sep }
     sep : ';' | NL
     insn : {label ':'}* [ code [ {op / ','} ] ]
     label : name
     code : name
     op : name | int | float | double | mem | str
     mem : type ':' addr
     addr : disp
          | [ disp ] '(' sib ')'
     sib : name | [ name ] ',' name [ ',' scale]
     disp : int | name
     scale : int

*/

void MIR_scan_string (const char *str) {
  token_t t;
  const char *name;
  MIR_item_t func = NULL;
  MIR_insn_code_t insn_code;
  MIR_insn_t insn;
  MIR_type_t type;
  MIR_op_t op, *op_addr;
  MIR_label_t label;
  MIR_var_t var;
  size_t n;
  int64_t i, frame_size, nargs;
  int func_p, end_func_p, local_p,  read_p, disp_p;
  insn_name_t in, el;
  MIR_error_func_t saved_error_func;

  saved_error_func = MIR_get_error_func ();
  MIR_set_error_func (process_error);
  input_string = str;
  input_string_char_num = 0;
  t.code = TC_NL;
  for (;;) {
    if (setjmp (error_jmp_buf)) {
      while (t.code != TC_NL && t.code != EOF)
	t = scan_token (get_string_char, unget_string_char);
      if (t.code == TC_EOF)
	break;
    }
    VARR_TRUNC (label_name_t, label_names, 0);
    t = scan_token (get_string_char, unget_string_char);
    while (t.code == TC_NL)
      t = scan_token (get_string_char, unget_string_char);
    if (t.code == TC_EOF)
      break;
    for (;;) { /* label_names */
      if (t.code != TC_NAME)
	process_error (MIR_syntax_error, "insn should start with label or insn name");
      name = t.u.name;
      t = scan_token (get_string_char, unget_string_char);
      if (t.code != TC_COL)
	break;
      VARR_PUSH (label_name_t, label_names, name);
      t = scan_token (get_string_char, unget_string_char);
      if (t.code == TC_NL)
	t = scan_token (get_string_char, unget_string_char); /* label_names without insn */
    }
    end_func_p = func_p = local_p = FALSE;
    if (strcmp (name, "func") == 0) {
      func_p = TRUE;
      if (VARR_LENGTH (label_name_t, label_names) != 1)
	process_error (MIR_syntax_error, "only one label should be used for func");
    } else if (strcmp (name, "endfunc") == 0) {
      end_func_p = TRUE;
      if (VARR_LENGTH (label_name_t, label_names) != 0)
	process_error (MIR_syntax_error, "endfunc should have no labels");
    } else if (strcmp (name, "local") == 0) {
      local_p = TRUE;
      if (func == NULL)
	process_error (MIR_syntax_error, "local outside func");
      if (VARR_LENGTH (label_name_t, label_names) != 0)
	process_error (MIR_syntax_error, "local should have no labels");
    } else {
      in.name = name;
      if (! HTAB_DO (insn_name_t, insn_name_tab, in, HTAB_FIND, el))
	process_error (MIR_syntax_error, "Unknown insn");
      insn_code = el.code;
      for (n = 0; n < VARR_LENGTH (label_name_t, label_names); n++) {
	label = create_label_desc (VARR_GET (label_name_t, label_names, n));
	if (func != NULL)
	  MIR_append_insn (func, label);
      }
    }
    VARR_TRUNC (MIR_op_t, temp_insn_ops, 0);
    for (;;) { /* ops */
      if (t.code == TC_NL || t.code == TC_SEMICOL) {
	/* insn end */
	break;
      }
      read_p = TRUE;
      switch (t.code) {
      case TC_NAME: {
	name = t.u.name;
	t = scan_token (get_string_char, unget_string_char);
	read_p = FALSE;
	if (t.code != TC_COL) {
	  if (! end_func_p && ! func_p && ! local_p && MIR_branch_code_p (insn_code)
	      && VARR_LENGTH (MIR_op_t, temp_insn_ops) == 0) {
	    op = MIR_new_label_op (create_label_desc (name));
	  } else {
	    op.mode = MIR_OP_REG;
	    op.u.reg = MIR_reg (name);
	  }
	  break;
	}
	/* Memory, arg, or var */
	type = MIR_str2type (name);
	if (type == MIR_T_BOUND)
	  process_error (MIR_syntax_error, "Unknown type");
	else if (func_p && type != MIR_I64 && type != MIR_F && type != MIR_D)
	  process_error (MIR_syntax_error, "wrong type for arg");
	else if (local_p && type != MIR_I64 && type != MIR_F && type != MIR_D)
	  process_error (MIR_syntax_error, "wrong type for local var");
	t = scan_token (get_string_char, unget_string_char);
	op.mode = MIR_OP_MEM;
	op.u.mem.type = type; op.u.mem.scale = 1;
	op.u.mem.base = op.u.mem.index = 0; op.u.mem.disp = 0;
	if (func_p || local_p) {
	  if (t.code != TC_NAME)
	    process_error (MIR_syntax_error, func_p ? "wrong arg" : "wrong local var");
	  op.u.mem.disp = (MIR_disp_t) t.u.name;
	  t = scan_token (get_string_char, unget_string_char);
	} else {
	  disp_p = FALSE;
	  if (t.code == TC_INT) {
	    op.u.mem.disp = t.u.i;
	    t = scan_token (get_string_char, unget_string_char);
	    disp_p = TRUE;
	  } else if (t.code == TC_NAME) {
	    op.u.mem.disp = (MIR_disp_t) t.u.name;
	    t = scan_token (get_string_char, unget_string_char);
	    disp_p = TRUE;
	  }
	  if (t.code == TC_LEFT_PAR) {
	    t = scan_token (get_string_char, unget_string_char);
	    if (t.code == TC_NAME) {
	      op.u.mem.base = MIR_reg (t.u.name);
	      t = scan_token (get_string_char, unget_string_char);
	    }
	    if (t.code == TC_COMMA) {
	      t = scan_token (get_string_char, unget_string_char);
	      if (t.code != TC_NAME)
		process_error (MIR_syntax_error, "wrong index");
	      op.u.mem.index = MIR_reg (t.u.name);
	      t = scan_token (get_string_char, unget_string_char);
	      if (t.code == TC_COMMA) {
		t = scan_token (get_string_char, unget_string_char);
		if (t.code != TC_INT)
		  process_error (MIR_syntax_error, "wrong index");
		if (t.u.i != 1 && t.u.i != 2 && t.u.i != 4 && t.u.i != 8)
		  process_error (MIR_syntax_error, "scale is not 1, 2, 4, or 8");
		op.u.mem.scale = t.u.i;
		t = scan_token (get_string_char, unget_string_char);
	      }
	    }  
	    if (t.code != TC_RIGHT_PAR)
	      process_error (MIR_syntax_error, "wrong memory op");
	    t = scan_token (get_string_char, unget_string_char);
	  } else if (! disp_p)
	    process_error (MIR_syntax_error, "wrong memory");
	}
	break;
      }
      case TC_INT:
	op.mode = MIR_OP_INT;
	op.u.i = t.u.i;
	break;
      case TC_FLOAT:
	op.mode = MIR_OP_FLOAT;
	op.u.f = t.u.f;
	break;
      case TC_DOUBLE:
	op.mode = MIR_OP_DOUBLE;
	op.u.d = t.u.d;
	break;
      case TC_STR:
	abort ();
      default:
	break;
      }
      VARR_PUSH (MIR_op_t, temp_insn_ops, op);
      if (read_p)
	t = scan_token (get_string_char, unget_string_char);
      if (t.code != TC_COMMA)
	break;
      t = scan_token (get_string_char, unget_string_char);
    }
    if (t.code != TC_NL && t.code != TC_EOF && t.code != TC_SEMICOL)
      process_error (MIR_syntax_error, "wrong insn end");
    if (func_p) {
      VARR_TRUNC (MIR_var_t, temp_vars, 0);
      if (func != NULL)
	process_error (MIR_syntax_error, "nested func");
      op_addr = VARR_ADDR (MIR_op_t, temp_insn_ops);
      if ((n = VARR_LENGTH (MIR_op_t, temp_insn_ops)) < 1)
	process_error (MIR_syntax_error, "too few params in func");
      if (op_addr[0].mode != MIR_OP_INT || (frame_size = op_addr[0].u.i) < 0)
	process_error (MIR_syntax_error, "wrong frame size");
      nargs = n - 1;
      for (i = 0; i < nargs; i++) {
	assert (op_addr[i + 1].mode == MIR_OP_MEM);
	var.type = op_addr[i + 1].u.mem.type;
	var.name = (const char *) op_addr[i + 1].u.mem.disp;
	VARR_PUSH (MIR_var_t, temp_vars, var);
      }
      func = MIR_new_func_arr (VARR_GET (label_name_t, label_names, 0), frame_size, nargs,
			       VARR_ADDR (MIR_var_t, temp_vars));
      HTAB_CLEAR (label_desc_t, label_desc_tab);
    } else if (end_func_p) {
      if (func == NULL)
	process_error (MIR_syntax_error, "standalone endfunc");
      if (VARR_LENGTH (MIR_op_t, temp_insn_ops) != 0)
	process_error (MIR_syntax_error, "endfunc should have no params");
      func = NULL;
      MIR_finish_func ();
    } else if (local_p) {
      op_addr = VARR_ADDR (MIR_op_t, temp_insn_ops);
      n = VARR_LENGTH (MIR_op_t, temp_insn_ops);
      for (i = 0; i < n; i++) {
	assert (op_addr[i].mode == MIR_OP_MEM);
	MIR_create_func_var (func->u.func, op_addr[i].u.mem.type, (const char *) op_addr[i].u.mem.disp);
      }
    } else {
      insn = MIR_new_insn_arr (insn_code, VARR_LENGTH (MIR_op_t, temp_insn_ops),
			       VARR_ADDR (MIR_op_t, temp_insn_ops));
      if (func != NULL)
	MIR_append_insn (func, insn);
    }
  }
  if (func != NULL)
    process_error (MIR_syntax_error, "absent endfunc");
  MIR_set_error_func (saved_error_func);
}

static void scan_init (void) {
  insn_name_t in, el;
  size_t i;
  
  VARR_CREATE (label_name_t, label_names, 0);
  HTAB_CREATE (label_desc_t, label_desc_tab, 100, label_hash, label_eq);
  HTAB_CREATE (insn_name_t, insn_name_tab, MIR_INSN_BOUND, insn_name_hash, insn_name_eq);
  for (i = 0; i < MIR_INSN_BOUND; i++) {
    in.code = i;
    in.name = MIR_insn_name (i);
    HTAB_DO (insn_name_t, insn_name_tab, in, HTAB_INSERT, el);
  }
}

static void scan_finish (void) {
  VARR_DESTROY (label_name_t, label_names);
  HTAB_DESTROY (label_desc_t, label_desc_tab);
  HTAB_DESTROY (insn_name_t, insn_name_tab);
}

#endif /* if MIR_IO */



#if defined(TEST_MIR) || defined(TEST_MIR_GEN) || defined(TEST_MIR_INTERP)
MIR_item_t create_mir_func_with_loop (void) {
  MIR_item_t func;
  MIR_label_t fin, cont;
  MIR_reg_t ARG1, R2;
  
  func = MIR_new_func ("test", 0, 1, MIR_I64, "arg1");
  MIR_create_func_var (func->u.func, MIR_I64, "count");
  ARG1 = MIR_reg ("arg1"); R2 = MIR_reg ("count");
  fin = MIR_new_label (); cont = MIR_new_label ();
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (R2), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, cont);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (R2), MIR_new_reg_op (R2), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_BLT, MIR_new_label_op (cont), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, fin);
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_reg_op (R2)));
  MIR_finish_func ();
  return func;
}

MIR_item_t create_mir_example2 (void) {
  MIR_item_t func;
  MIR_reg_t ARG1, ARG2;
  
  func = MIR_new_func ("test2", 0, 2, MIR_I64, "arg1", MIR_I64, "arg2");
  ARG1 = MIR_reg ("arg1"); ARG2 = MIR_reg ("arg2");
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_mem_op (MIR_I64, 0, ARG1, ARG2, 8),
				       MIR_new_mem_op (MIR_I64, 64, ARG1, 0, 0), MIR_new_mem_op (MIR_I64, 0, 0, ARG1, 8)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 0, ARG1, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 0, 0, ARG2, 1)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_I64, 1024, 0, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_mem_op (MIR_I64, 0, ARG1, ARG2, 8), MIR_new_mem_op (MIR_I64, 0, ARG1, 0, 8)));
  MIR_finish_func ();
  return func;
}
#endif

#if MIR_SCAN && (TEST_MIR_IO || defined(TEST_MIR_GEN2) || defined(TEST_MIR_INTERP2))

MIR_item_t create_mir_func_sieve (void) {
  MIR_scan_string ("\n\
sieve: func 819000\n\
       local i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags\n\
       mov flags, fp\n\
       mov iter, 0\n\
loop:  bge fin, iter, 1000\n\
       mov count, 0;  mov i, 0\n\
loop2: bge fin2, i, 819000\n\
       mov u8:(flags, i), 1;  add i, i, 1\n\
       jmp loop2\n\
fin2:  mov i, 0\n\
loop3: bge fin3, i, 819000\n\
       beq cont3, u8:(flags,i), 0\n\
       add temp, i, i;  add prime, temp, 3;  add k, i, prime\n\
loop4: bge fin4, k, 819000\n\
       mov u8:(flags, k), 0;  add k, k, prime\n\
       jmp loop4\n\
fin4:  add count, count, 1\n\
cont3: add i, i, 1\n\
       jmp loop3\n\
fin3:  add iter, iter, 1\n\
       jmp loop\n\
fin:   ret count\n\
       endfunc\n\
");
  return DLIST_TAIL (MIR_item_t, MIR_items);
}

#endif

#ifdef TEST_MIR
int main (void) {
  MIR_item_t func1, func2;
  
  MIR_init ();
  func1 = create_mir_func_with_loop ();
  func2 = create_mir_example2 ();
  MIR_simplify_func (func1);
  MIR_simplify_func (func2);
  MIR_output (stderr);
  MIR_finish ();
  return 0;
}

#endif

#if MIR_IO && defined (TEST_MIR_IO)

int main (void) {
  FILE *f;
  const char *fname = "__tmp.mirb";
  
  MIR_init ();
  create_mir_func_sieve ();
  MIR_output (stderr);
  f = fopen (fname, "wb");
  assert  (f != NULL);
  MIR_write (f);
  fclose (f);
  f = fopen (fname, "rb");
  assert  (f != NULL);
  MIR_read (f);
  fclose (f);
  fprintf (stderr, "+++++++++++++After reading:\n");
  MIR_output (stderr);
  remove (fname);
  MIR_finish ();
  return 0;
}
#endif /* MIR_IO && defined (TEST_MIR_IO) */

#if MIR_SCAN && defined (TEST_MIR_SCAN)

int main (void) {
  MIR_init ();
  MIR_scan_string ("\n\
loop: func 0, i64:limit # a comment\n\
\n\
       local i64:count\n\
       mov count, 0\n\
       bge L1, count, limit\n\
L2:    # a separate label\n\
       add count, count, 1; blt L2, count, limit # 2 insn on a line\n\
L1:    ret count  # label with insn\n\
       endfunc\n\
  ");
  MIR_scan_string ("\n\
sieve: func 819000\n\
       local i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags\n\
       sub flags, fp, 819000\n\
       mov iter, 0\n\
loop:  bge fin, iter, 1000\n\
       mov count, 0;  mov i, 0\n\
loop2: bgt fin2, i, 819000\n\
       mov u8:(flags, i), 1;  add i, i, 1\n\
       jmp loop2\n\
fin2:  mov i, 0\n\
loop3: bgt fin3, i, 819000\n\
       beq cont3, u8:(flags,i), 0\n\
       add temp, i, i;  add prime, temp, 3;  add k, i, prime\n\
loop4: bgt fin4, k, 819000\n\
       mov u8:(flags, k), 0;  add k, k, prime\n\
       jmp loop4\n\
fin4:  add count, count, 1\n\
cont3: add i, i, 1\n\
       jmp loop3\n\
fin3:  add iter, iter, 1\n\
       jmp loop\n\
fin:   ret count\n\
       endfunc\n\
");
  MIR_output (stderr);
  fprintf (stderr, "+++++++++++++After sieve simplification:\n");
  MIR_simplify_func (DLIST_TAIL (MIR_item_t, MIR_items));
  MIR_output (stderr);
  MIR_finish ();
  return 0;
}
#endif /* MIR_SCAN && defined (TEST_MIR_SCAN) */
