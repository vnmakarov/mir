#ifndef MIR_H

#define MIR_H

#include <stdio.h>
#include <stdint.h>
#include "mir-dlist.h"
#include "mir-varr.h"
#include "mir-htab.h"

/* Redefine MIR_IO or/and MIR_SCAN if you need the functionality they provide.  */
#ifndef MIR_IO
#define MIR_IO 0
#endif

#ifndef MIR_SCAN
#define MIR_SCAN 0
#endif

#ifdef __GNUC__
#define MIR_UNUSED __attribute__((unused))
#else
#define MIR_UNUSED
#endif

typedef enum MIR_error_type {
  MIR_no_error, MIR_syntax_error, MIR_binary_io_error, MIR_alloc_error, MIR_finish_error,
  MIR_no_func_error, MIR_wrong_param_value_error, MIR_reserved_name_error,
  MIR_undeclared_reg_error, MIR_repeated_decl_error, MIR_reg_type_error, MIR_ops_num_error,
  MIR_op_mode_error, MIR_invalid_insn_error,
} MIR_error_type_t;

#ifdef __GNUC__
#define MIR_NO_RETURN __attribute__((noreturn))
#else
#define MIR_NO_RETURN
#endif

typedef void MIR_NO_RETURN (*MIR_error_func_t) (MIR_error_type_t error_type, const char *message);

#define FP_NAME "fp"

/* The most MIR insns have destination operand and one or two source
   operands.  The destination can be ony a register or memory.

   There are additional constraints on insn operands:

   o A register in porgram can contain only one type values: integer,
     float, or double.
   o Operand types should be what the insn expects */
typedef enum {
  /* Abbreviations:
     I - 64-bit integer, S -short (32-bit), U - unsigned, F -float, D - double.  */
  /* 2 operand insns: */
  MIR_MOV, MIR_FMOV, MIR_DMOV, /* Moves */
  /* Extensions.  Truncation is not necessary because it is just using a part. */
  MIR_S2I, MIR_US2I,
  MIR_I2F, MIR_I2D,                       /* Integer to float or double conversion */
  MIR_F2I, MIR_D2I,                       /* Float or double to integer conversion */
  MIR_F2D, MIR_D2F,                       /* Float <-> double conversion */
  MIR_NEG,  MIR_NEGS, MIR_FNEG, MIR_DNEG, /* Changing sign */
  /* 3 operand insn: */
  MIR_ADD, MIR_ADDS, MIR_FADD, MIR_DADD, /* Addition */
  MIR_SUB, MIR_SUBS, MIR_FSUB, MIR_DSUB, /* Subtraction */
  MIR_MUL, MIR_UMUL, MIR_MULS, MIR_UMULS, MIR_FMUL, MIR_DMUL, /* Multiplication */
  MIR_DIV, MIR_DIVS, MIR_UDIV, MIR_UDIVS, MIR_FDIV, MIR_DDIV, /* Division */
  MIR_MOD, MIR_MODS, MIR_UMOD, MIR_UMODS, /* Modulo */
  MIR_AND, MIR_ANDS, MIR_OR, MIR_ORS, MIR_XOR, MIR_XORS, /* Logical */
  MIR_LSH, MIR_LSHS, MIR_RSH, MIR_RSHS, MIR_URSH, MIR_URSHS, /* Right signed/unsigned shift */
  MIR_EQ, MIR_EQS, MIR_FEQ, MIR_DEQ, /* Equality */
  MIR_NE, MIR_NES, MIR_FNE, MIR_DNE, /* Inequality */
  MIR_LT, MIR_LTS, MIR_ULT, MIR_ULTS, MIR_FLT, MIR_DLT, /* Less then */
  MIR_LE, MIR_LES, MIR_ULE, MIR_ULES, MIR_FLE, MIR_DLE, /* Less or equal */
  MIR_GT, MIR_GTS, MIR_UGT, MIR_UGTS, MIR_FGT, MIR_DGT, /* Greater then */
  MIR_GE, MIR_GES, MIR_UGE, MIR_UGES, MIR_FGE, MIR_DGE, /* Greater or equal */
  /* Uncoditional (1 operand) and conditional (2 operands) branch
     insns.  The first operand is a label.  */
  MIR_JMP, MIR_BT, MIR_BF,
  /* Compare and branch (3 operand) insns.  The first operand is the
     label. */
  MIR_BEQ, MIR_BEQS, MIR_FBEQ, MIR_DBEQ,
  MIR_BNE, MIR_BNES, MIR_FBNE, MIR_DBNE,
  MIR_BLT, MIR_BLTS, MIR_UBLT, MIR_UBLTS, MIR_FBLT, MIR_DBLT,
  MIR_BLE, MIR_BLES, MIR_UBLE, MIR_UBLES, MIR_FBLE, MIR_DBLE,
  MIR_BGT, MIR_BGTS, MIR_UBGT, MIR_UBGTS, MIR_FBGT, MIR_DBGT,
  MIR_BGE, MIR_BGES, MIR_UBGE, MIR_UBGES, MIR_FBGE, MIR_DBGE,
  /* 1st operand is name or op containing func address, 2nd operands
     is immediate integer definining arguments number, 3rd and
     subsequent ops are call arguments. */
  MIR_CALL, MIR_CALL_C,
  /* 1 operand insn: */
  MIR_RET, MIR_RETS, MIR_FRET, MIR_DRET,
  /* Special insns: */
  MIR_LABEL, /* One immediate operand is unique label number  */
  MIR_INVALID_INSN,
  MIR_INSN_BOUND,   /* Should be the last  */
} MIR_insn_code_t;

/* Data types: */
typedef enum {
  /* Integer types of different size: */
  MIR_I8, MIR_U8, MIR_I16, MIR_U16, MIR_I32, MIR_U32, MIR_I64, MIR_U64,
  MIR_F, MIR_D /* Float or double type */, MIR_BLOCK, MIR_T_BOUND
} MIR_type_t;

typedef uint8_t MIR_scale_t; /* Index reg scale in memory */

#define MIR_MAX_SCALE UINT8_MAX

typedef int64_t MIR_disp_t;  /* Address displacement in memory */

/* Register number (> 0).  A register always contain only one type
   value: integer, float, or double.  Register numbers in insn
   operands can be changed in MIR_finish_func.  */
typedef uint32_t MIR_reg_t;

#define MIR_MAX_REG_NUM UINT32_MAX
#define MIR_NON_HARD_REG MIR_MAX_REG_NUM

/* Immediate in immediate moves.  */
typedef union {int64_t i; uint64_t u; float f; double d;} MIR_imm_t;

/* Memory: mem:type[base + index * scale + disp].  It also can be
   memory with hard regs but such memory used only internally.  An
   integer type memory value expands to int64_t value when the insn is
   executed.  */
typedef struct {
  MIR_type_t type : 8; MIR_scale_t scale : 8;
  /* 0 means no reg for memory.  MIR_NON_HARD_REG means no reg for
     hard reg memory. */
  MIR_reg_t base, index;
  MIR_disp_t disp;
} MIR_mem_t;

typedef struct MIR_insn *MIR_label_t;

typedef const char *MIR_name_t;

/* Operand mode */
typedef enum {
  MIR_OP_UNDEF, MIR_OP_REG, MIR_OP_HARD_REG, MIR_OP_INT, MIR_OP_UINT, MIR_OP_FLOAT, MIR_OP_DOUBLE,
  MIR_OP_NAME, MIR_OP_MEM, MIR_OP_HARD_REG_MEM, MIR_OP_LABEL
} MIR_op_mode_t;

/* An insn operand */
typedef struct {
  void *data; /* Aux data  */
  MIR_op_mode_t mode;
  union {
    MIR_reg_t reg;
    MIR_reg_t hard_reg; /* Used only internally */
    int64_t i;
    uint64_t u;
    float f;
    double d;
    MIR_name_t name; /* external or func name */
    MIR_mem_t mem;
    MIR_mem_t hard_reg_mem; /* Used only internally */
    MIR_label_t label;
  } u;
} MIR_op_t;

typedef struct MIR_insn *MIR_insn_t;

/* Definition of link of double list of insns */
DEF_DLIST_LINK (MIR_insn_t);

struct MIR_insn {
  void *data; /* Aux data */
  DLIST_LINK (MIR_insn_t) insn_link;
  MIR_insn_code_t code;
  MIR_op_t ops[1];
};

/* Definition of double list of insns */
DEF_DLIST (MIR_insn_t, insn_link);

typedef struct MIR_var {
  MIR_type_t type;
  const char *name;
} MIR_var_t;

DEF_VARR (MIR_var_t);

/* Function definition */
typedef struct MIR_func {
  const char *name;
  DLIST (MIR_insn_t) insns;
  uint32_t frame_size;
  uint32_t nargs, ntemps;
  VARR (MIR_var_t) *vars; /* args and locals but temps */
} *MIR_func_t;

typedef struct MIR_item *MIR_item_t;

/* Definition of link of double list of MIR_item_t type elements */
DEF_DLIST_LINK (MIR_item_t);

/* MIR items (function or external): */
struct MIR_item {
  void *data;
  DLIST_LINK (MIR_item_t) item_link;
  int func_p; /* Flag of function item */
  union {
    MIR_func_t func;
    MIR_name_t external;
  } u;
};

/* Definition of double list of MIR_item_t type elements */
DEF_DLIST (MIR_item_t, item_link);

extern DLIST (MIR_item_t) MIR_items; /* List of all items */

/* Use it only internally:  */
extern MIR_op_t MIR_new_hard_reg_op (MIR_reg_t hard_reg);

extern MIR_op_t MIR_new_hard_reg_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
					 MIR_reg_t index, MIR_scale_t scale);

static inline int MIR_branch_code_p (MIR_insn_code_t code) {
  return (code == MIR_JMP || code == MIR_BT || code == MIR_BF
	  || code == MIR_BEQ || code == MIR_BEQS || code == MIR_FBEQ || code == MIR_DBEQ
	  || code == MIR_BNE || code == MIR_BNES || code == MIR_FBNE || code == MIR_DBNE
	  || code == MIR_BLT || code == MIR_BLTS || code == MIR_UBLT || code == MIR_UBLTS
	  || code == MIR_FBLT || code == MIR_DBLT
	  || code == MIR_BLE || code == MIR_BLES || code == MIR_UBLE || code == MIR_UBLES
	  || code == MIR_FBLE || code == MIR_DBLE
	  || code == MIR_BGT || code == MIR_BGTS || code == MIR_UBGT || code == MIR_UBGTS
	  || code == MIR_FBGT || code == MIR_DBGT
	  || code == MIR_BGE || code == MIR_BGES || code == MIR_UBGE || code == MIR_UBGES
	  || code == MIR_FBGE || code == MIR_DBGE);
}

static inline int MIR_ret_code_p (MIR_insn_code_t code) {
  return (code == MIR_RET || code == MIR_FRET || code == MIR_DRET);
}

/* Use only the following API to create MIR code.  */
extern int MIR_init (void);
extern void MIR_finish (void);

extern MIR_item_t MIR_new_func_arr (const char *name, size_t frame_size,
				    size_t nargs, MIR_var_t *vars);
extern MIR_item_t MIR_new_func (const char *name, size_t frame_size,  size_t nargs, ...);
extern void MIR_create_func_var (MIR_func_t func, MIR_type_t type, const char *name);
extern void MIR_finish_func (void);

extern MIR_error_func_t MIR_get_error_func (void);
extern void MIR_set_error_func (MIR_error_func_t func);

extern MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops);
extern MIR_insn_t MIR_new_insn (MIR_insn_code_t code, ...);

extern const char *MIR_insn_name (MIR_insn_code_t code);
extern size_t MIR_insn_nops (MIR_insn_code_t code);
extern MIR_op_mode_t MIR_insn_op_mode (MIR_insn_code_t code, size_t nop, int *out_p);

extern MIR_insn_t MIR_new_label (void);

extern MIR_reg_t MIR_reg (const char *reg_name);
/* The following three functions can be used only after
   MIR_finish_func: */
extern MIR_type_t MIR_reg_type (MIR_reg_t reg, MIR_func_t func);
extern const char *MIR_reg_name (MIR_reg_t reg, MIR_func_t func);
extern MIR_reg_t MIR_func_reg (const char *reg_name, MIR_func_t func);

extern MIR_op_t MIR_new_reg_op (MIR_reg_t reg);
extern MIR_op_t MIR_new_int_op (int64_t v);
extern MIR_op_t MIR_new_uint_op (uint64_t v);
extern MIR_op_t MIR_new_float_op (float v);
extern MIR_op_t MIR_new_double_op (double v);
extern MIR_op_t MIR_new_name_op (MIR_name_t name);
extern MIR_op_t MIR_new_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
				MIR_reg_t index, MIR_scale_t scale);
extern MIR_op_t MIR_new_label_op (MIR_label_t label);
extern int MIR_op_eq_p (MIR_op_t op1, MIR_op_t op2);
extern htab_hash_t  MIR_op_hash_step (htab_hash_t h, MIR_op_t op);

extern void MIR_append_insn (MIR_item_t func, MIR_insn_t insn);
extern void MIR_prepend_insn (MIR_item_t func, MIR_insn_t insn);
extern void MIR_insert_insn_after (MIR_item_t func, MIR_insn_t after, MIR_insn_t insn);
extern void MIR_insert_insn_before (MIR_item_t func, MIR_insn_t before, MIR_insn_t insn);
extern void MIR_remove_insn (MIR_item_t func, MIR_insn_t insn);

extern void MIR_output_op (FILE *f, MIR_op_t op, MIR_func_t func);
extern void MIR_output_insn (FILE *f, MIR_insn_t insn, MIR_func_t func);
extern void MIR_output (FILE *f);

extern void MIR_simplify_func (MIR_item_t func);

#if MIR_IO
extern void MIR_write (FILE *f);
extern void MIR_read (FILE *f);
#endif

#if MIR_SCAN
extern void MIR_scan_string (const char *str);
#endif

/* For internal use only:  */
extern const char *_MIR_uniq_string (const char *str);
extern MIR_reg_t _MIR_new_temp_reg (MIR_type_t type, MIR_func_t func); /* for internal use only */

#endif /* #ifndef MIR_H */
