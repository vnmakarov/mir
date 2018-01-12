#ifndef MIR_H

#define MIR_H

#include <stdint.h>
#include "mir-dlist.h"

/* The most MIR insns have destination operand and one or two source
   operands.  The destination can be ony a register or memory.

   There are additional constraints on insn operands:

   o A register in porgram can contain only one type values: integer,
     float, or double.
   o Operand types should be what the insn expects */
typedef enum {
  /* 2 operand insns: */
  MIR_MOV, MIR_FMOV, MIR_DMOV, /* Moves */
  MIR_I2F, MIR_I2D, /* Integer to float or double conversion */
  MIR_F2I, MIR_D2I, /* Float or double to integer conversion */
  MIR_F2D, MIR_D2F, /* Float <-> double conversion */
  MIR_NEG, MIR_FNEG, MIR_DNEG, /* Changing sign */
  /* 3 operand insn: */
  MIR_ADD, MIR_FADD, MIR_DADD, /* Addition */
  MIR_SUB, MIR_FSUB, MIR_DSUB, /* Subtraction */
  MIR_MUL, MIR_FMUL, MIR_DMUL, /* Multiplication */
  MIR_DIV, MIR_UDIV, MIR_FDIV, MIR_DDIV, /* Division, U - unsigned */
  MIR_MOD, MIR_UMOD, /* Modulo */
  MIR_AND, MIR_OR, MIR_XOR, MIR_LSH, /* Logical */
  MIR_RSH, MIR_URSH, /* Right signed/unsigned shift */
  MIR_EQ, MIR_FEQ, MIR_DEQ, /* Equality */
  MIR_NE, MIR_FNE, MIR_DNE, /* Inequality */
  MIR_LT, MIR_ULT, MIR_FLT, MIR_DLT, /* Less then */
  MIR_LE, MIR_ULE, MIR_FLE, MIR_DLE, /* Less or equal */
  MIR_GT, MIR_UGT, MIR_FGT, MIR_DGT, /* Greater then */
  MIR_GE, MIR_UGE, MIR_FGE, MIR_DGE, /* Greater or equal */
  /* Uncoditional (1 operand) and conditional (2 operands) branch
     insns.  The first operand is a label.  */
  MIR_JMP, MIR_BT, MIR_BF,
  /* Compare and branch (3 operand) insns.  The first operand is the
     label. */
  MIR_BEQ, MIR_FBEQ, MIR_DBEQ,
  MIR_BNE, MIR_FBNE, MIR_DBNE,
  MIR_BLT, MIR_UBLT, MIR_FBLT, MIR_DBLT,
  MIR_BLE, MIR_UBLE, MIR_FBLE, MIR_DBLE,
  MIR_BGT, MIR_UBGT, MIR_FBGT, MIR_DBGT,
  MIR_BGE, MIR_UBGE, MIR_FBGE, MIR_DBGE,
  /* 1st operand is name or op containing func address, 2nd operands
     is immediate integer definining arguments number, 3rd and
     subsequent ops are call arguments. */
  MIR_CALL, MIR_CALL_C,
  /* 1 operand insn: */
  MIR_RET, MIR_FRET, MIR_DRET,
  /* Special insns: */
  MIR_LABEL, /* One immediate operand is unique label number  */
  MIR_INSN_BOUND /* Should be the last  */
} MIR_insn_code_t;

/* Data types: */
typedef enum {
  /* Integer types of different size: */
  MIR_I8, MIR_U8, MIR_I16, MIR_U16, MIR_I32, MIR_U32, MIR_I64,
  MIR_F, MIR_D /* Float or double type */
} MIR_type_t;

typedef uint8_t MIR_scale_t; /* Index reg scale in memory */

typedef int64_t MIR_disp_t;  /* Address displacement in memory */

/* Register number (> 0).  A register always contain only one type
   value: integer, float, or double. */
typedef uint32_t MIR_reg_t;

#define MIR_MAX_REG_NUM UINT32_MAX
#define MIR_ABSENT_HARD_REG_NUM MIR_MAX_REG_NUM

/* Immediate in immediate moves.  */
typedef union {int64_t i; float f; double d;} MIR_imm_t;

/* Memory: mem:type[base + index * scale + disp].  It also can be
   memory with hard regs but such memory used only internally.  An
   integer type memory value expands to int64_t value when the insn is
   executed.  */
typedef struct {
  MIR_type_t type : 8; MIR_scale_t scale : 8;
  /* 0 means no reg for memory.  MIR_MAX_REG_NUM means no reg for hard
     reg memory. */
  MIR_reg_t base, index;
  MIR_disp_t disp;
} MIR_mem_t;

typedef struct MIR_insn *MIR_label_t;

typedef const char *MIR_name_t;

/* Operand mode */
typedef enum {
  MIR_OP_UNDEF, MIR_OP_REG, MIR_OP_HARD_REG, MIR_OP_INT, MIR_OP_FLOAT, MIR_OP_DOUBLE,
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

/* Function definition */
typedef struct MIR_func {
  const char *name;
  uint32_t nargs;
  DLIST (MIR_insn_t) insns;
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
extern MIR_op_t MIR_new_reg_op (MIR_reg_t hard_reg);

extern MIR_op_t MIR_new_hard_reg_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
					 MIR_reg_t index, MIR_scale_t scale);

static inline int MIR_branch_code_p (MIR_insn_code_t code) {
  return (code == MIR_JMP || code == MIR_BT || code == MIR_BF
	  || code == MIR_BEQ || code == MIR_FBEQ || code == MIR_DBEQ
	  || code == MIR_BNE || code == MIR_FBNE || code == MIR_DBNE
	  || code == MIR_BLT || code == MIR_UBLT || code == MIR_FBLT || code == MIR_DBLT
	  || code == MIR_BLE || code == MIR_UBLE || code == MIR_FBLE || code == MIR_DBLE
	  || code == MIR_BGT || code == MIR_UBGT || code == MIR_FBGT || code == MIR_DBGT
	  || code == MIR_BGE || code == MIR_UBGE || code == MIR_FBGE || code == MIR_DBGE);
}

static inline int MIR_ret_code_p (MIR_insn_code_t code) {
  return (code == MIR_RET || code == MIR_FRET || code == MIR_DRET);
}

/* Use only the following API to create MIR code.  */
extern int MIR_init (void);
extern void MIR_finish (void);

extern MIR_item_t MIR_new_func (const char *name, size_t nargs);

extern MIR_insn_t MIR_new_insn (MIR_insn_code_t code, ...);
extern MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops);

extern const char *MIR_insn_name (MIR_insn_code_t code);
extern size_t MIR_insn_nops (MIR_insn_code_t code);
extern MIR_op_mode_t MIR_insn_op_mode (MIR_insn_code_t code, size_t nop, int *out_p);

extern MIR_insn_t MIR_new_label (void);

extern MIR_reg_t MIR_new_reg (void);
extern MIR_reg_t MIR_reg_mode (MIR_reg_t reg);

extern MIR_op_t MIR_new_reg_op (MIR_reg_t reg);
extern MIR_op_t MIR_new_int_op (int64_t v);
extern MIR_op_t MIR_new_float_op (float v);
extern MIR_op_t MIR_new_double_op (double v);
extern MIR_op_t MIR_new_name_op (MIR_name_t name);
extern MIR_op_t MIR_new_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
				MIR_reg_t index, MIR_scale_t scale);
extern MIR_op_t MIR_new_label_op (MIR_label_t label);

extern void MIR_append_insn (MIR_item_t func, MIR_insn_t insn);
extern void MIR_insert_insn_after (MIR_item_t func, MIR_insn_t after, MIR_insn_t insn);
extern void MIR_insert_insn_before (MIR_item_t func, MIR_insn_t before, MIR_insn_t insn);
extern void MIR_remove_insn (MIR_item_t func, MIR_insn_t insn);

extern void MIR_simplify (MIR_item_t func);

#endif /* #ifndef MIR_H */
