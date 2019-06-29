/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#ifndef MIR_H

#define MIR_H

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include "mir-dlist.h"
#include "mir-varr.h"
#include "mir-htab.h"

#ifdef NDEBUG
static inline int mir_assert (int cond) {return 0 && cond;}
#else
#define mir_assert(cond) assert (cond)
#endif

#define FALSE 0
#define TRUE 1

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
  MIR_no_module_error, MIR_nested_module_error, MIR_no_func_error, MIR_func_error, MIR_vararg_func_error,
  MIR_nested_func_error, MIR_wrong_param_value_error, MIR_reserved_name_error, MIR_import_export_error,
  MIR_undeclared_func_reg_error, MIR_repeated_decl_error, MIR_reg_type_error, MIR_unique_reg_error,
  MIR_undeclared_op_ref_error, MIR_ops_num_error, MIR_call_op_error, MIR_ret_error,
  MIR_op_mode_error, MIR_out_op_error,
  MIR_invalid_insn_error,
} MIR_error_type_t;

#ifdef __GNUC__
#define MIR_NO_RETURN __attribute__((noreturn))
#else
#define MIR_NO_RETURN
#endif

typedef void MIR_NO_RETURN (*MIR_error_func_t) (MIR_error_type_t error_type, const char *format, ...);

/* The most MIR insns have destination operand and one or two source
   operands.  The destination can be ony a register or memory.

   There are additional constraints on insn operands:

   o A register in porgram can contain only one type values: integer,
     float, double, or long double.
   o Operand types should be what the insn expects */
typedef enum {
  /* Abbreviations:
     I - 64-bit integer, S -short (32-bit), U - unsigned, F -float, D - double, LD - long double.  */
  /* 2 operand insns: */
  MIR_MOV, MIR_FMOV, MIR_DMOV, MIR_LDMOV, /* Moves */
  /* Extensions.  Truncation is not necessary because we can use an extension to use a part. */
  MIR_EXT8, MIR_EXT16, MIR_EXT32, MIR_UEXT8, MIR_UEXT16, MIR_UEXT32,
  MIR_I2F, MIR_I2D, MIR_I2LD,             /* Integer to float or (long) double conversion */
  MIR_UI2F, MIR_UI2D, MIR_UI2LD,          /* Unsigned integer to float or (long) double conversion */
  MIR_F2I, MIR_D2I, MIR_LD2I,             /* Float or (long) double to integer conversion */
  MIR_F2D, MIR_F2LD, MIR_D2F, MIR_D2LD, MIR_LD2F, MIR_LD2D, /* Float, (long) double conversions */
  MIR_NEG, MIR_NEGS, MIR_FNEG, MIR_DNEG, MIR_LDNEG,         /* Changing sign */
  /* 3 operand insn: */
  MIR_ADD, MIR_ADDS, MIR_FADD, MIR_DADD, MIR_LDADD, /* Addition */
  MIR_SUB, MIR_SUBS, MIR_FSUB, MIR_DSUB, MIR_LDSUB, /* Subtraction */
  MIR_MUL, MIR_MULS, MIR_FMUL, MIR_DMUL, MIR_LDMUL, /* Multiplication */
  MIR_DIV, MIR_DIVS, MIR_UDIV, MIR_UDIVS, MIR_FDIV, MIR_DDIV, MIR_LDDIV, /* Division */
  MIR_MOD, MIR_MODS, MIR_UMOD, MIR_UMODS, /* Modulo */
  MIR_AND, MIR_ANDS, MIR_OR, MIR_ORS, MIR_XOR, MIR_XORS, /* Logical */
  MIR_LSH, MIR_LSHS, MIR_RSH, MIR_RSHS, MIR_URSH, MIR_URSHS, /* Right signed/unsigned shift */
  MIR_EQ, MIR_EQS, MIR_FEQ, MIR_DEQ, MIR_LDEQ, /* Equality */
  MIR_NE, MIR_NES, MIR_FNE, MIR_DNE, MIR_LDNE, /* Inequality */
  MIR_LT, MIR_LTS, MIR_ULT, MIR_ULTS, MIR_FLT, MIR_DLT, MIR_LDLT, /* Less then */
  MIR_LE, MIR_LES, MIR_ULE, MIR_ULES, MIR_FLE, MIR_DLE, MIR_LDLE, /* Less or equal */
  MIR_GT, MIR_GTS, MIR_UGT, MIR_UGTS, MIR_FGT, MIR_DGT, MIR_LDGT, /* Greater then */
  MIR_GE, MIR_GES, MIR_UGE, MIR_UGES, MIR_FGE, MIR_DGE, MIR_LDGE, /* Greater or equal */
  /* Uncoditional (1 operand) and conditional (2 operands) branch
     insns.  The first operand is a label.  */
  MIR_JMP, MIR_BT, MIR_BTS, MIR_BF, MIR_BFS,
  /* Compare and branch (3 operand) insns.  The first operand is the
     label. */
  MIR_BEQ, MIR_BEQS, MIR_FBEQ, MIR_DBEQ, MIR_LDBEQ,
  MIR_BNE, MIR_BNES, MIR_FBNE, MIR_DBNE, MIR_LDBNE,
  MIR_BLT, MIR_BLTS, MIR_UBLT, MIR_UBLTS, MIR_FBLT, MIR_DBLT, MIR_LDBLT,
  MIR_BLE, MIR_BLES, MIR_UBLE, MIR_UBLES, MIR_FBLE, MIR_DBLE, MIR_LDBLE,
  MIR_BGT, MIR_BGTS, MIR_UBGT, MIR_UBGTS, MIR_FBGT, MIR_DBGT, MIR_LDBGT,
  MIR_BGE, MIR_BGES, MIR_UBGE, MIR_UBGES, MIR_FBGE, MIR_DBGE, MIR_LDBGE,
  /* 1st operand is a prototype, 2nd one is ref or op containing func
     address, 3rd and subsequent ops are optional result (if result in
     the prototype is not of void type), call arguments. */
  MIR_CALL, MIR_INLINE,
  /* 1 operand insn: */
  MIR_RET,
  MIR_ALLOCA, /* 2 operands: result address and size  */
  MIR_BSTART, MIR_BEND, /* block start: result address; block end: address from block start */
  /* Special insns: */
  MIR_VA_ARG, /* result is arg address, operands: va_list addr and memory */
  MIR_VA_START, MIR_VA_END, /* operand is va_list */
  MIR_LABEL, /* One immediate operand is unique label number  */
  MIR_INVALID_INSN,
  MIR_INSN_BOUND,   /* Should be the last  */
} MIR_insn_code_t;

/* Data types: */
typedef enum {
  /* Integer types of different size: */
  MIR_T_I8, MIR_T_U8, MIR_T_I16, MIR_T_U16, MIR_T_I32, MIR_T_U32, MIR_T_I64, MIR_T_U64,
  MIR_T_F, MIR_T_D, MIR_T_LD /* Float or (long) double type */, MIR_T_P /* Pointer */,
  MIR_T_UNDEF, MIR_T_BOUND,
} MIR_type_t;

#if UINTPTR_MAX == 0xffffffff
#define MIR_PTR32 1
#define MIR_PTR64 0
#elif UINTPTR_MAX == 0xffffffffffffffffu
#define MIR_PTR32 0
#define MIR_PTR64 1
#else
#error MIR can work only for 32- or 64-bit targets
#endif

typedef uint8_t MIR_scale_t; /* Index reg scale in memory */

#define MIR_MAX_SCALE UINT8_MAX

typedef int64_t MIR_disp_t;  /* Address displacement in memory */

/* Register number (> 0).  A register always contain only one type
   value: integer, float, or (long) double.  Register numbers in insn
   operands can be changed in MIR_finish_func.  */
typedef uint32_t MIR_reg_t;

#define MIR_MAX_REG_NUM UINT32_MAX
#define MIR_NON_HARD_REG MIR_MAX_REG_NUM

/* Immediate in immediate moves.  */
typedef union {int64_t i; uint64_t u; float f; double d; long double ld;} MIR_imm_t;

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
  MIR_OP_UNDEF, MIR_OP_REG, MIR_OP_HARD_REG, MIR_OP_INT, MIR_OP_UINT,
  MIR_OP_FLOAT, MIR_OP_DOUBLE, MIR_OP_LDOUBLE,
  MIR_OP_REF, MIR_OP_STR, MIR_OP_MEM, MIR_OP_HARD_REG_MEM, MIR_OP_LABEL, MIR_OP_BOUND
} MIR_op_mode_t;

typedef struct MIR_item *MIR_item_t;

/* An insn operand */
typedef struct {
  void *data; /* Aux data  */
  MIR_op_mode_t mode;
  /* Defined after MIR_func_finish.  Only MIR_OP_INT, MIR_OP_UINT,
     MIR_OP_FLOAT, MIR_OP_DOUBLE, MIR_OP_LDOUBLE: */
  MIR_op_mode_t value_mode;
  union {
    MIR_reg_t reg;
    MIR_reg_t hard_reg; /* Used only internally */
    int64_t i;
    uint64_t u;
    float f;
    double d;
    long double ld;
    MIR_item_t ref; /* non-export/non-forward after simplification */
    const char *str;
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
  MIR_insn_code_t code : 32;
  unsigned int nops : 32; /* number of operands */
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
  uint32_t nres, nargs, last_temp_num, n_inlines;
  MIR_type_t *res_types;
  char vararg_p; /* flag of variable number of arguments */
  VARR (MIR_var_t) *vars; /* args and locals but temps */
} *MIR_func_t;

typedef struct MIR_proto {
  const char *name;
  uint32_t nres;
  MIR_type_t *res_types; /* != MIR_T_UNDEF */
  char vararg_p; /* flag of variable number of arguments */
  VARR (MIR_var_t) *args; /* args name can be NULL */
} *MIR_proto_t;

typedef struct MIR_data {
  const char *name; /* can be NULL */
  MIR_type_t el_type;
  size_t nel;
  union {
    long double d; /* for alignment of temporary literals */
    uint8_t els[1];
  } u;
} *MIR_data_t;

typedef struct MIR_bss {
  const char *name; /* can be NULL */
  uint64_t len;
} *MIR_bss_t;

typedef struct MIR_module *MIR_module_t;

/* Definition of link of double list of MIR_item_t type elements */
DEF_DLIST_LINK (MIR_item_t);

typedef enum {MIR_func_item, MIR_proto_item, MIR_import_item, MIR_export_item,
	      MIR_forward_item, MIR_data_item, MIR_bss_item} MIR_item_type_t;

/* MIR module items (function or import): */
struct MIR_item {
  void *data;
  MIR_module_t module;
  DLIST_LINK (MIR_item_t) item_link;
  MIR_item_type_t item_type; /* item type */
  /* Non-null only for export/forward items and import item after
     linking.  It forms a chain to the final definition. */
  MIR_item_t ref_def;
  /* address of loaded data/bss items, function to call the function
     item, imported definition or proto object */
  void *addr;
  void *machine_code; /* address of generated machine code */
  char export_p; /* true for export items (only func items) */
  union {
    MIR_func_t func;
    MIR_proto_t proto;
    MIR_name_t import;
    MIR_name_t export;
    MIR_name_t forward;
    MIR_data_t data;
    MIR_bss_t bss;
  } u;
};

/* Definition of double list of MIR_item_t type elements */
DEF_DLIST (MIR_item_t, item_link);

/* Definition of link of double list of MIR_module_t type elements */
DEF_DLIST_LINK (MIR_module_t);

/* MIR module: */
struct MIR_module {
  void *data;
  const char *name;
  DLIST (MIR_item_t) items; /* module items */
  DLIST_LINK (MIR_module_t) module_link;
  size_t temp_items_num;  /* Used only internally */
};

/* Definition of double list of MIR_item_t type elements */
DEF_DLIST (MIR_module_t, module_link);

extern DLIST (MIR_module_t) MIR_modules; /* List of all modules */

static inline int MIR_FP_branch_code_p (MIR_insn_code_t code) {
  return (code == MIR_FBEQ || code == MIR_DBEQ || code == MIR_LDBEQ
	  || code == MIR_FBNE || code == MIR_DBNE || code == MIR_LDBNE
	  || code == MIR_FBLT || code == MIR_DBLT || code == MIR_LDBLT
	  || code == MIR_FBLE || code == MIR_DBLE || code == MIR_LDBLE
	  || code == MIR_FBGT || code == MIR_DBGT || code == MIR_LDBGT
	  || code == MIR_FBGE || code == MIR_DBGE || code == MIR_LDBGE);
}

static inline int MIR_call_code_p (MIR_insn_code_t code) {
  return code == MIR_CALL || code == MIR_INLINE;
}

static inline int MIR_branch_code_p (MIR_insn_code_t code) {
  return (code == MIR_JMP || code == MIR_BT || code == MIR_BTS || code == MIR_BF || code == MIR_BFS
	  || code == MIR_BEQ || code == MIR_BEQS || code == MIR_BNE || code == MIR_BNES
	  || code == MIR_BLT || code == MIR_BLTS || code == MIR_UBLT || code == MIR_UBLTS
	  || code == MIR_BLE || code == MIR_BLES || code == MIR_UBLE || code == MIR_UBLES
	  || code == MIR_BGT || code == MIR_BGTS || code == MIR_UBGT || code == MIR_UBGTS
	  || code == MIR_BGE || code == MIR_BGES || code == MIR_UBGE || code == MIR_UBGES
	  || MIR_FP_branch_code_p (code));
}

/* Use only the following API to create MIR code.  */
extern int MIR_init (void);
extern void MIR_finish (void);

extern MIR_module_t MIR_new_module (const char *name);
extern MIR_item_t MIR_new_import (const char *name);
extern MIR_item_t MIR_new_export (const char *name);
extern MIR_item_t MIR_new_forward (const char *name);
extern MIR_item_t MIR_new_bss (const char *name, size_t len); /* name can be NULL */
extern MIR_item_t MIR_new_data (const char *name, MIR_type_t el_type,
				size_t nel, const void *els); /* name can be NULL */
extern MIR_item_t MIR_new_string_data (const char *name, const char *str); /* name can be NULL */
extern MIR_item_t MIR_new_proto_arr (const char *name, size_t nres, MIR_type_t *res_types,
				     size_t nargs, MIR_var_t *vars);
extern MIR_item_t MIR_new_proto (const char *name, size_t nres, MIR_type_t *res_types,
				 size_t nargs, ...);
extern MIR_item_t MIR_new_vararg_proto_arr (const char *name, size_t nres, MIR_type_t *res_types,
					    size_t nargs, MIR_var_t *vars);
extern MIR_item_t MIR_new_vararg_proto (const char *name, size_t nres, MIR_type_t *res_types,
					size_t nargs, ...);
extern MIR_item_t MIR_new_func_arr (const char *name, size_t nres, MIR_type_t *res_types,
				    size_t nargs, MIR_var_t *vars);
extern MIR_item_t MIR_new_func (const char *name, size_t nres, MIR_type_t *res_types,
				size_t nargs, ...);
extern MIR_item_t MIR_new_vararg_func_arr (const char *name, size_t nres, MIR_type_t *res_types,
					   size_t nargs, MIR_var_t *vars);
extern MIR_item_t MIR_new_vararg_func (const char *name, size_t nres, MIR_type_t *res_types,
				       size_t nargs, ...);
extern const char *MIR_item_name (MIR_item_t item);
extern MIR_reg_t MIR_new_func_reg (MIR_func_t func, MIR_type_t type, const char *name);
extern void MIR_finish_func (void);
extern void MIR_finish_module (void);

extern MIR_error_func_t MIR_get_error_func (void);
extern void MIR_set_error_func (MIR_error_func_t func);

extern MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops);
extern MIR_insn_t MIR_new_insn (MIR_insn_code_t code, ...);
extern MIR_insn_t MIR_new_call_insn (size_t nops, ...);
extern MIR_insn_t MIR_new_ret_insn (size_t nops, ...);
extern MIR_insn_t MIR_copy_insn (MIR_insn_t insn);

extern const char *MIR_insn_name (MIR_insn_code_t code);
extern size_t MIR_insn_nops (MIR_insn_t insn);
extern MIR_op_mode_t MIR_insn_op_mode (MIR_insn_t insn, size_t nop, int *out_p);

extern MIR_insn_t MIR_new_label (void);

extern MIR_reg_t MIR_reg (const char *reg_name, MIR_func_t func);
extern MIR_type_t MIR_reg_type (MIR_reg_t reg, MIR_func_t func);
extern const char *MIR_reg_name (MIR_reg_t reg, MIR_func_t func);

extern MIR_op_t MIR_new_reg_op (MIR_reg_t reg);
extern MIR_op_t MIR_new_int_op (int64_t v);
extern MIR_op_t MIR_new_uint_op (uint64_t v);
extern MIR_op_t MIR_new_float_op (float v);
extern MIR_op_t MIR_new_double_op (double v);
extern MIR_op_t MIR_new_ldouble_op (long double v);
extern MIR_op_t MIR_new_ref_op (MIR_item_t item);
extern MIR_op_t MIR_new_str_op (const char *str);
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

extern const char *MIR_type_str (MIR_type_t tp);
extern void MIR_output_op (FILE *f, MIR_op_t op, MIR_func_t func);
extern void MIR_output_insn (FILE *f, MIR_insn_t insn, MIR_func_t func, int newline_p);
extern void MIR_output (FILE *f);

extern void MIR_simplify_func (MIR_item_t func, int mem_float_p);
extern void MIR_inline (MIR_item_t func_item);

#if MIR_IO
extern void MIR_write (FILE *f);
extern void MIR_read (FILE *f);
#endif

#if MIR_SCAN
extern void MIR_scan_string (const char *str);
#endif

extern MIR_item_t MIR_get_global_item (const char *name);
extern void MIR_load_module (MIR_module_t m);
extern void MIR_load_external (const char *name, void *addr);
extern void MIR_link (void (*set_interface) (MIR_item_t item), void * (*import_resolver) (const char *));

/* For internal use only:  */
extern MIR_item_t _MIR_called_func;

extern const char *_MIR_uniq_string (const char *str);
extern int _MIR_reserved_ref_name_p (const char *name);
extern int _MIR_reserved_name_p (const char *name);
extern MIR_reg_t _MIR_new_temp_reg (MIR_type_t type, MIR_func_t func); /* for internal use only */
extern size_t _MIR_type_size (MIR_type_t type);
extern MIR_op_mode_t _MIR_insn_code_op_mode (MIR_insn_code_t code, size_t nop, int *out_p);
extern void _MIR_simplify_insn (MIR_item_t func_item, MIR_insn_t insn, int mem_float_p);

extern MIR_op_t _MIR_new_hard_reg_op (MIR_reg_t hard_reg);

extern MIR_op_t _MIR_new_hard_reg_mem_op (MIR_type_t type, MIR_disp_t disp, MIR_reg_t base,
					  MIR_reg_t index, MIR_scale_t scale);

extern MIR_item_t _MIR_builtin_proto (MIR_module_t module, const char *name,
				      size_t nres, MIR_type_t *res_types, size_t nargs, ...);
extern MIR_item_t _MIR_builtin_func (MIR_module_t module, const char *name, void *addr);

extern uint8_t *_MIR_publish_code (uint8_t *code, size_t code_len);

struct MIR_code_reloc {
  size_t offset;
  void *value;
};

typedef struct MIR_code_reloc *MIR_code_reloc_t;

extern void _MIR_update_code_arr (uint8_t *base, size_t nloc, MIR_code_reloc_t relocs);
extern void _MIR_update_code (uint8_t *base, size_t nloc, ...);

extern void *va_arg_builtin (void *p, uint64_t t);
extern void va_start_interp_builtin (void *p, void *a);
extern void va_end_interp_builtin (void *p);
  
extern void *_MIR_get_bstart_builtin (void);
extern void *_MIR_get_bend_builtin (void);

extern void *_MIR_get_ff_call (size_t nres, MIR_type_t *res_types, size_t nargs, MIR_type_t *arg_types);
extern void *_MIR_get_interp_shim (MIR_item_t func_item, void *handler);
extern void *_MIR_get_thunk (MIR_item_t item);
extern void _MIR_redirect_thunk (void *thunk, void *to);
extern void *_MIR_get_thunk_target (void *thunk);
extern MIR_item_t _MIR_get_thunk_func (void *thunk);

#endif /* #ifndef MIR_H */
