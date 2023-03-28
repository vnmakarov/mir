/* This file is a part of MIR project.
   Copyright (C) 2018-2021 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Optimization pipeline:                                 ---------------
                                                         | Global Value  |
           ----------     -----------     -----------    | Numbering,    |    ------------
   MIR -->| Simplify |-->| Build CFG |-->| Build SSA |-->| Constant      |-->| Copy       |
           ----------     -----------     -----------    | Propagation,  |   | Propagation|
                                                         | Redundant Load|    ------------
                                                         | Elimination   |         |
                                                          ---------------          |
                                                                                   V
    -----     -------                   ----     --------     -----------     -----------
   |Build|   |Finding|    ---------    |Jump|   | Out of |   |Dead Code  |   |Dead Store |
   |Live |<--| Loops |<--|Machinize|<--|opts|<--| SSA    |<--|Elimination|<--|Elimination|
   |Info |    -------     ---------     ----     --------     -----------     -----------
    -----
       |
       V
    ------                                                                      --------
   |Build |    --------     -------     -----     ---     -------     -----    |Generate|
   |Live  |-->|Coalesce|-->|Combine|-->| DCE |-->|RA |-->|Combine|-->| DCE |-->|Machine |--> Machine
   |Ranges|    --------     -------     -----     ---     -------     -----    | Insns  |     Insns
    ------                                                                      --------

   Simplify: Lowering MIR (in mir.c).  Always.
   Build CGF: Building Control Flow Graph (basic blocks and CFG edges).  Only for -O1 and above.
   Build SSA: Building Single Static Assignment Form by adding phi nodes and SSA edges
   Global Value Numbering: Removing redundant insns through GVN.  This includes constant
                           propagation and redundant load eliminations.  Only for -O2 and above.
   Copy Propagation: SSA copy propagation and removing redundant extension insns
   Dead code elimination: Removing insns with unused outputs.  Only for -O2 and above.
   Out of SSA: Making conventional SSA and removing phi nodes and SSA edges
   Machinize: Machine-dependent code (e.g. in mir-gen-x86_64.c)
              transforming MIR for calls ABI, 2-op insns, etc.  Always.
   Finding Loops: Building loop tree which is used in subsequent register allocation.
                  Only for -O1 and above.
   Building Live Info: Calculating live in and live out for the basic blocks.
   Build Live Ranges: Calculating program point ranges for registers.  Only for -O1 and above.
   Coalesce: Aggressive register coalescing
   Register Allocator (RA): Fast RA for -O0 or Priority-based linear scan RA for -O1 and above.
                            Output is MIR containing only hard regs and hard reg memory
   Combine: Code selection by merging data-depended insns into one.
            1st pass is done on vars to improve RA for fewer regs and
                to combine more as we have no spilled regs,
            2nd pass (can be optional for 3-op RISC targets) on hard regs to combine new RA
                live range splitting insns (r=slot;bcmp r => bcmp slot) and combining 2 ops
                (before RA: p1=mem;add p2,p0,p1,dead p1
                 after RA: hr1=mem; add hr0,hr0,hr1 -> add hr0,mem  when p2 and p0 got hr0)
   Dead code elimination (DCE): Removing insns with unused outputs.  Only for -O1 and above.
   Generate machine insns: Machine-dependent code (e.g. in
                           mir-gen-x86_64.c) creating machine insns. Always.

   -O0 is 2 times faster than -O1 but generates much slower code.

   Terminology:
   reg - MIR (pseudo-)register (their numbers are in MIR_OP_VAR and MIR_OP_VAR_MEM > MAX_HARD_REG)
   hard reg - MIR hard register (their numbers are in MIR_OP_VAR and MIR_OP_VAR_MEM
                                 and less or equal MAX_HARD_REG)
   var - pseudo and hard register (MIR_NON_VAR means no var)
   loc - hard register and stack locations (stack slot numbers start with MAX_HARD_REG + 1).

   Memory aliasing rules:

   * Memory has aliases and they are used for recognizing aliased memory

   * Memory has nloc attribute.  Memory with the same nloc always refer for the same memory
     although memory with different nloc still may refer for the same memory.  Memory with
     the same nloc has the same alias attributes

   * Memory found aliased with alias attributes can be recognized as non-aliased one by
     using alloca flags described below

   * Memory can have flags 'must alloca' and 'may alloca'.  'Must alloca' always goes
     with 'may alloca'.  'Must alloca' means that we guarantee memory can be allocated
     only alloca in the func. 'May alloca' means that it is not excluded that memory is
     allocated by alloca

   * Memory with 'must alloca' flag can have disp attribute.  We can define that
     'must alloca' memory refers the same memory using disp attribute

*/

#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include <assert.h>

#define gen_assert(cond) assert (cond)

typedef struct gen_ctx *gen_ctx_t;

static void util_error (gen_ctx_t gen_ctx, const char *message);
static void varr_error (const char *message) { util_error (NULL, message); }

#define MIR_VARR_ERROR varr_error

#include "mir.h"
#include "mir-dlist.h"
#include "mir-bitmap.h"
#include "mir-htab.h"
#include "mir-hash.h"
#include "mir-gen.h"

/* Functions used by target dependent code: */
static void *gen_malloc (gen_ctx_t gen_ctx, size_t size);
static MIR_reg_t gen_new_temp_reg (gen_ctx_t gen_ctx, MIR_type_t type, MIR_func_t func);
static void set_label_disp (gen_ctx_t gen_ctx, MIR_insn_t insn, size_t disp);
static size_t get_label_disp (gen_ctx_t gen_ctx, MIR_insn_t insn);
static void create_new_bb_insns (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t after,
                                 MIR_insn_t insn_for_bb);
static void gen_delete_insn (gen_ctx_t gen_ctx, MIR_insn_t insn);
static void gen_add_insn_before (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t insn);
static void gen_add_insn_after (gen_ctx_t gen_ctx, MIR_insn_t after, MIR_insn_t insn);
static void setup_call_hard_reg_args (gen_ctx_t gen_ctx, MIR_insn_t call_insn, MIR_reg_t hard_reg);
static uint64_t get_ref_value (gen_ctx_t gen_ctx, MIR_op_t *ref_op);

#define SWAP(v1, v2, temp) \
  do {                     \
    temp = v1;             \
    v1 = v2;               \
    v2 = temp;             \
  } while (0)

#ifndef MIR_GEN_CALL_TRACE
#define MIR_GEN_CALL_TRACE 0
#endif

#if MIR_NO_GEN_DEBUG
#define DEBUG(level, code)
#else
#define DEBUG(level, code)                                \
  {                                                       \
    if (debug_file != NULL && debug_level >= level) code; \
  }
#endif

typedef struct func_cfg *func_cfg_t;

struct target_ctx;
struct data_flow_ctx;
struct ssa_ctx;
struct gvn_ctx;
struct lr_ctx;
struct coalesce_ctx;
struct ra_ctx;
struct selection_ctx;
struct fg_ctx;

typedef struct loop_node *loop_node_t;
DEF_VARR (loop_node_t);

typedef struct dead_var *dead_var_t;
DEF_DLIST_LINK (dead_var_t);

struct dead_var {
  MIR_reg_t var;
  DLIST_LINK (dead_var_t) dead_var_link;
};
DEF_DLIST (dead_var_t, dead_var_link);

struct all_gen_ctx;

typedef struct bb_insn *bb_insn_t;
DEF_VARR (bb_insn_t);

typedef struct target_bb_version *target_bb_version_t;
DEF_VARR (target_bb_version_t);

typedef void *void_ptr_t;
DEF_VARR (void_ptr_t);

typedef struct {
  unsigned char alloca_flag;
  unsigned char disp_def_p;    /* can be true only for MUST_ALLOCA */
  MIR_type_t type;             /* memory type */
  MIR_alias_t alias, nonalias; /* memory aliases */
  MIR_insn_t def_insn;         /* base def insn: its value + disp form address */
  int64_t disp;                /* defined only when disp_def_p, otherwise disp is unknown */
} mem_attr_t;

DEF_VARR (mem_attr_t);

typedef struct spot_attr {
  uint32_t spot, prop;
  MIR_op_t *mem_ref; /* ref for memory if the spot is memory, NULL otherwise */
} spot_attr_t;

DEF_VARR (spot_attr_t);

DEF_VARR (MIR_op_t);

struct gen_ctx {
  struct all_gen_ctx *all_gen_ctx;
  int gen_num; /* always 1 for non-parallel generation */
#if MIR_PARALLEL_GEN
  pthread_t gen_thread;
  int busy_p;
#endif
  MIR_context_t ctx;
  unsigned optimize_level; /* 0:fast gen; 1:RA+combiner; 2: +GVN/CCP (default); >=3: everything  */
  MIR_item_t curr_func_item;
#if !MIR_NO_GEN_DEBUG
  FILE *debug_file;
  int debug_level;
#endif
  int addr_insn_p;    /* true if we have address insns in the input func */
  bitmap_t tied_regs; /* regs tied to hard reg */
  bitmap_t addr_regs; /* regs in addr insns as 2nd op */
  bitmap_t insn_to_consider, temp_bitmap, temp_bitmap2, temp_bitmap3;
  bitmap_t call_used_hard_regs[MIR_T_BOUND];
  bitmap_t func_used_hard_regs; /* before prolog: used hard regs except global var hard regs */
  func_cfg_t curr_cfg;
  uint32_t curr_bb_index, curr_loop_node_index;
  DLIST (dead_var_t) free_dead_vars;
  struct target_ctx *target_ctx;
  struct data_flow_ctx *data_flow_ctx;
  struct ssa_ctx *ssa_ctx;
  struct gvn_ctx *gvn_ctx;
  struct lr_ctx *lr_ctx;
  struct coalesce_ctx *coalesce_ctx;
  struct ra_ctx *ra_ctx;
  struct selection_ctx *selection_ctx;
  struct fg_ctx *fg_ctx;
  VARR (MIR_op_t) * temp_ops;
  VARR (bb_insn_t) * temp_bb_insns, *temp_bb_insns2;
  VARR (loop_node_t) * loop_nodes, *queue_nodes, *loop_entries; /* used in building loop tree */
  /* true when alloca memory escapes by assigning alloca address to memory: */
  unsigned char full_escape_p;
  VARR (mem_attr_t) * mem_attrs; /* nloc (> 0) => mem attributes */
  int max_int_hard_regs, max_fp_hard_regs;
  /* Slots num for variables.  Some variable can take several slots and can be aligned. */
  size_t func_stack_slots_num;
  VARR (target_bb_version_t) * target_succ_bb_versions;
  VARR (void_ptr_t) * succ_bb_addrs;
  void *bb_wrapper; /* to jump to lazy basic block generation */
  VARR (spot_attr_t) * spot_attrs, *spot2attr;
};

#define optimize_level gen_ctx->optimize_level
#define curr_func_item gen_ctx->curr_func_item
#define debug_file gen_ctx->debug_file
#define debug_level gen_ctx->debug_level
#define addr_insn_p gen_ctx->addr_insn_p
#define tied_regs gen_ctx->tied_regs
#define addr_regs gen_ctx->addr_regs
#define insn_to_consider gen_ctx->insn_to_consider
#define temp_bitmap gen_ctx->temp_bitmap
#define temp_bitmap2 gen_ctx->temp_bitmap2
#define temp_bitmap3 gen_ctx->temp_bitmap3
#define call_used_hard_regs gen_ctx->call_used_hard_regs
#define func_used_hard_regs gen_ctx->func_used_hard_regs
#define curr_cfg gen_ctx->curr_cfg
#define curr_bb_index gen_ctx->curr_bb_index
#define curr_loop_node_index gen_ctx->curr_loop_node_index
#define full_escape_p gen_ctx->full_escape_p
#define mem_attrs gen_ctx->mem_attrs
#define free_dead_vars gen_ctx->free_dead_vars
#define temp_ops gen_ctx->temp_ops
#define temp_bb_insns gen_ctx->temp_bb_insns
#define temp_bb_insns2 gen_ctx->temp_bb_insns2
#define loop_nodes gen_ctx->loop_nodes
#define queue_nodes gen_ctx->queue_nodes
#define loop_entries gen_ctx->loop_entries
#define max_int_hard_regs gen_ctx->max_int_hard_regs
#define max_fp_hard_regs gen_ctx->max_fp_hard_regs
#define func_stack_slots_num gen_ctx->func_stack_slots_num
#define target_succ_bb_versions gen_ctx->target_succ_bb_versions
#define succ_bb_addrs gen_ctx->succ_bb_addrs
#define bb_wrapper gen_ctx->bb_wrapper
#define spot_attrs gen_ctx->spot_attrs
#define spot2attr gen_ctx->spot2attr

#define LOOP_COST_FACTOR 5

typedef struct bb_version *bb_version_t;

struct func_or_bb {
  /* full_p is used only when func_p and means generation machine code for full func */
  char func_p, full_p;
  union {
    MIR_item_t func_item;
    bb_version_t bb_version;
  } u;
};

typedef struct func_or_bb func_or_bb_t;
DEF_VARR (func_or_bb_t);

#if MIR_PARALLEL_GEN
static struct func_or_bb null_func_or_bb = {TRUE, TRUE, {NULL}};
#endif

struct all_gen_ctx {
#if MIR_PARALLEL_GEN
  mir_mutex_t queue_mutex;
  mir_cond_t generate_signal, done_signal;
  size_t funcs_start;
  VARR (func_or_bb_t) * code_to_generate;
#endif
  MIR_context_t ctx;
  size_t gens_num; /* size of the following array: */
  unsigned long long overall_bbs_num, overall_gen_bbs_num;
  struct gen_ctx gen_ctx[1];
};

#if MIR_PARALLEL_GEN
#define queue_mutex all_gen_ctx->queue_mutex
#define generate_signal all_gen_ctx->generate_signal
#define done_signal all_gen_ctx->done_signal
#define funcs_start all_gen_ctx->funcs_start
#define code_to_generate all_gen_ctx->code_to_generate
#endif

static inline struct all_gen_ctx **all_gen_ctx_loc (MIR_context_t ctx) {
  return (struct all_gen_ctx **) ctx;
}

#if defined(__x86_64__) || defined(_M_AMD64)
#include "mir-gen-x86_64.c"
#elif defined(__aarch64__)
#include "mir-gen-aarch64.c"
#elif defined(__PPC64__)
#include "mir-gen-ppc64.c"
#elif defined(__s390x__)
#include "mir-gen-s390x.c"
#elif defined(__riscv)
#if __riscv_xlen != 64 || __riscv_flen < 64 || !__riscv_float_abi_double || !__riscv_mul \
  || !__riscv_div || !__riscv_compressed
#error "only 64-bit RISCV supported (at least rv64imafd)"
#endif
#if __riscv_flen == 128
#error "RISCV 128-bit floats (Q set) is not supported"
#endif
#include "mir-gen-riscv64.c"
#else
#error "undefined or unsupported generation target"
#endif

typedef struct bb_stub *bb_stub_t;
DEF_DLIST_LINK (bb_version_t);

struct bb_version {
  bb_stub_t bb_stub;
  DLIST_LINK (bb_version_t) bb_version_link;
  int call_p;
  void *addr; /* bb code address or generator creating and returning address */
  void *machine_code;
  struct target_bb_version target_data; /* data container for the target code */
  uint32_t n_attrs;
  spot_attr_t attrs[1];
};

/* Definition of double list of bb_version_t type elements */
DEF_DLIST (bb_version_t, bb_version_link);

struct bb_stub {
  DLIST (bb_version_t) bb_versions;
  MIR_item_t func_item;
  MIR_insn_t first_insn, last_insn;
};

static void MIR_NO_RETURN util_error (gen_ctx_t gen_ctx, const char *message) {
  (*MIR_get_error_func (gen_ctx->ctx)) (MIR_alloc_error, message);
}

static void *gen_malloc (gen_ctx_t gen_ctx, size_t size) {
  void *res = malloc (size);
  if (res == NULL) util_error (gen_ctx, "no memory");
  return res;
}

#define DEFAULT_INIT_BITMAP_BITS_NUM 256

typedef struct bb *bb_t;

DEF_DLIST_LINK (bb_t);

typedef struct insn_data *insn_data_t;

DEF_DLIST_LINK (bb_insn_t);

typedef struct edge *edge_t;

typedef edge_t in_edge_t;

typedef edge_t out_edge_t;

DEF_DLIST_LINK (in_edge_t);
DEF_DLIST_LINK (out_edge_t);

struct edge {
  bb_t src, dst;
  DLIST_LINK (in_edge_t) in_link;
  DLIST_LINK (out_edge_t) out_link;
  unsigned char fall_through_p, back_edge_p, flag1, flag2;
};

DEF_DLIST (in_edge_t, in_link);
DEF_DLIST (out_edge_t, out_link);

struct insn_data { /* used only for calls/labels in -O0 mode */
  bb_t bb;
  union {
    bitmap_t call_hard_reg_args; /* non-null for calls */
    size_t label_disp;           /* used for labels */
  } u;
};

#define MAY_ALLOCA 0x1
#define MUST_ALLOCA 0x2
struct bb_insn {
  MIR_insn_t insn;
  unsigned char gvn_val_const_p; /* true for int value, false otherwise */
  unsigned char alloca_flag;     /* true for value may and/or must be from alloca */
  uint32_t index, mem_index;
  int64_t gvn_val; /* used for GVN, it is negative index for non GVN expr insns */
  DLIST_LINK (bb_insn_t) bb_insn_link;
  bb_t bb;
  DLIST (dead_var_t) insn_dead_vars;
  bitmap_t call_hard_reg_args; /* non-null for calls */
  size_t label_disp;           /* for label */
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost, bfs; /* preorder, reverse post order, breadth first order */
  DLIST_LINK (bb_t) bb_link;
  DLIST (in_edge_t) in_edges;
  /* The out edges order: optional fall through bb, optional label bb,
     optional exit bb.  There is always at least one edge.  */
  DLIST (out_edge_t) out_edges;
  DLIST (bb_insn_t) bb_insns;
  unsigned char call_p;        /* used in mem avail calculation, true if there is a call in BB */
  unsigned char flag;          /* used in different calculation */
  bitmap_t in, out, gen, kill; /* var bitmaps for different data flow problems */
  bitmap_t dom_in, dom_out;    /* additional var bitmaps */
  loop_node_t loop_node;
  int max_int_pressure, max_fp_pressure;
};

DEF_DLIST (bb_t, bb_link);

DEF_DLIST_LINK (loop_node_t);
DEF_DLIST_TYPE (loop_node_t);

struct loop_node {
  uint32_t index; /* if BB != NULL, it is index of BB */
  bb_t bb;        /* NULL for internal tree node  */
  loop_node_t entry;
  loop_node_t parent;
  bb_t preheader; /* used in LICM */
  DLIST (loop_node_t) children;
  DLIST_LINK (loop_node_t) children_link;
  int max_int_pressure, max_fp_pressure;
};

DEF_DLIST_CODE (loop_node_t, children_link);

DEF_DLIST_LINK (func_cfg_t);

struct reg_info {
  long freq;
  /* The following members are defined and used only in RA */
  size_t live_length; /* # of program points where reg lives */
};

typedef struct reg_info reg_info_t;

DEF_VARR (reg_info_t);

typedef struct {
  int uns_p;
  union {
    int64_t i;
    uint64_t u;
  } u;
} const_t;

struct func_cfg {
  MIR_reg_t max_var;
  uint32_t curr_bb_insn_index;
  VARR (reg_info_t) * reg_info; /* regs */
  bitmap_t call_crossed_regs;
  DLIST (bb_t) bbs;
  loop_node_t root_loop_node;
};

static void init_dead_vars (gen_ctx_t gen_ctx) { DLIST_INIT (dead_var_t, free_dead_vars); }

static void free_dead_var (gen_ctx_t gen_ctx, dead_var_t dv) {
  DLIST_APPEND (dead_var_t, free_dead_vars, dv);
}

static dead_var_t get_dead_var (gen_ctx_t gen_ctx) {
  dead_var_t dv;

  if ((dv = DLIST_HEAD (dead_var_t, free_dead_vars)) == NULL)
    return gen_malloc (gen_ctx, sizeof (struct dead_var));
  DLIST_REMOVE (dead_var_t, free_dead_vars, dv);
  return dv;
}

static void finish_dead_vars (gen_ctx_t gen_ctx) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, free_dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, free_dead_vars, dv);
    free (dv);
  }
}

static void add_bb_insn_dead_var (gen_ctx_t gen_ctx, bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv;

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars); dv != NULL;
       dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var) return;
  dv = get_dead_var (gen_ctx);
  dv->var = var;
  DLIST_APPEND (dead_var_t, bb_insn->insn_dead_vars, dv);
}

static dead_var_t find_bb_insn_dead_var (bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv;

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars); dv != NULL;
       dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var) return dv;
  return NULL;
}

static void clear_bb_insn_dead_vars (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, bb_insn->insn_dead_vars, dv);
    free_dead_var (gen_ctx, dv);
  }
}

static void remove_bb_insn_dead_var (gen_ctx_t gen_ctx, bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv, next_dv;

  gen_assert (var != MIR_NON_VAR);
  for (dv = DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars); dv != NULL; dv = next_dv) {
    next_dv = DLIST_NEXT (dead_var_t, dv);
    if (dv->var != var) continue;
    DLIST_REMOVE (dead_var_t, bb_insn->insn_dead_vars, dv);
    free_dead_var (gen_ctx, dv);
  }
}

static void move_bb_insn_dead_vars (bb_insn_t bb_insn, bb_insn_t from_bb_insn) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, from_bb_insn->insn_dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, from_bb_insn->insn_dead_vars, dv);
    DLIST_APPEND (dead_var_t, bb_insn->insn_dead_vars, dv);
  }
}

static int insn_data_p (MIR_insn_t insn) {
  return insn->code == MIR_LABEL || MIR_call_code_p (insn->code);
}

static void setup_insn_data (gen_ctx_t gen_ctx, MIR_insn_t insn, bb_t bb) {
  insn_data_t insn_data;

  if (!insn_data_p (insn)) {
    insn->data = bb;
    return;
  }
  insn_data = insn->data = gen_malloc (gen_ctx, sizeof (struct insn_data));
  insn_data->bb = bb;
  insn_data->u.call_hard_reg_args = NULL;
}

static bb_t get_insn_data_bb (MIR_insn_t insn) {
  return insn_data_p (insn) ? ((insn_data_t) insn->data)->bb : (bb_t) insn->data;
}

static void delete_insn_data (MIR_insn_t insn) {
  insn_data_t insn_data = insn->data;

  if (insn_data == NULL || !insn_data_p (insn)) return;
  if (MIR_call_code_p (insn->code) && insn_data->u.call_hard_reg_args != NULL)
    bitmap_destroy (insn_data->u.call_hard_reg_args);
  free (insn_data);
}

static bb_insn_t create_bb_insn (gen_ctx_t gen_ctx, MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = gen_malloc (gen_ctx, sizeof (struct bb_insn));

  insn->data = bb_insn;
  bb_insn->bb = bb;
  bb_insn->insn = insn;
  bb_insn->gvn_val_const_p = FALSE;
  bb_insn->alloca_flag = insn->code == MIR_ALLOCA ? MAY_ALLOCA | MUST_ALLOCA : 0;
  bb_insn->call_hard_reg_args = NULL;
  gen_assert (curr_cfg->curr_bb_insn_index != (uint32_t) ~0ull);
  bb_insn->index = curr_cfg->curr_bb_insn_index++;
  bb_insn->mem_index = 0;
  bb_insn->gvn_val = bb_insn->index;
  DLIST_INIT (dead_var_t, bb_insn->insn_dead_vars);
  if (MIR_call_code_p (insn->code)) bb_insn->call_hard_reg_args = bitmap_create2 (MAX_HARD_REG + 1);
  return bb_insn;
}

static bb_insn_t add_new_bb_insn (gen_ctx_t gen_ctx, MIR_insn_t insn, bb_t bb, int append_p) {
  bb_insn_t bb_insn = create_bb_insn (gen_ctx, insn, bb);

  if (append_p)
    DLIST_APPEND (bb_insn_t, bb->bb_insns, bb_insn);
  else
    DLIST_PREPEND (bb_insn_t, bb->bb_insns, bb_insn);
  return bb_insn;
}

static void delete_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  DLIST_REMOVE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn);
  bb_insn->insn->data = NULL;
  clear_bb_insn_dead_vars (gen_ctx, bb_insn);
  if (bb_insn->call_hard_reg_args != NULL) bitmap_destroy (bb_insn->call_hard_reg_args);
  free (bb_insn);
}

static bb_t get_insn_bb (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  return optimize_level == 0 ? get_insn_data_bb (insn) : ((bb_insn_t) insn->data)->bb;
}

static void create_new_bb_insns (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t after,
                                 MIR_insn_t insn_for_bb) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, new_bb_insn;
  bb_t bb;

  /* Null insn_for_bb means it should be in the 1st block: skip entry and exit blocks: */
  bb = insn_for_bb == NULL ? DLIST_EL (bb_t, curr_cfg->bbs, 2) : get_insn_bb (gen_ctx, insn_for_bb);
  if (optimize_level == 0) {
    for (insn = (before == NULL ? DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns)
                                : DLIST_NEXT (MIR_insn_t, before));
         insn != after; insn = DLIST_NEXT (MIR_insn_t, insn))
      setup_insn_data (gen_ctx, insn, bb);
    return;
  }
  if (before != NULL && (bb_insn = before->data)->bb == bb) {
    for (insn = DLIST_NEXT (MIR_insn_t, before); insn != after;
         insn = DLIST_NEXT (MIR_insn_t, insn), bb_insn = new_bb_insn) {
      new_bb_insn = create_bb_insn (gen_ctx, insn, bb);
      DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
    }
  } else {
    gen_assert (after != NULL);
    bb_insn = after->data;
    insn = (before == NULL ? DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns)
                           : DLIST_NEXT (MIR_insn_t, before));
    for (; insn != after; insn = DLIST_NEXT (MIR_insn_t, insn)) {
      new_bb_insn = create_bb_insn (gen_ctx, insn, bb);
      if (bb == bb_insn->bb)
        DLIST_INSERT_BEFORE (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
      else
        DLIST_APPEND (bb_insn_t, bb->bb_insns, new_bb_insn);
    }
  }
}

static void gen_delete_insn (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  if (optimize_level == 0)
    delete_insn_data (insn);
  else
    delete_bb_insn (gen_ctx, insn->data);
  MIR_remove_insn (gen_ctx->ctx, curr_func_item, insn);
}

static void gen_add_insn_before (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t insn) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn_for_bb = before;

  gen_assert (!MIR_any_branch_code_p (insn->code) && insn->code != MIR_LABEL);
  if (before->code == MIR_LABEL) {
    insn_for_bb = DLIST_PREV (MIR_insn_t, before);
    gen_assert (insn_for_bb == NULL || !MIR_any_branch_code_p (insn_for_bb->code));
  }
  MIR_insert_insn_before (ctx, curr_func_item, before, insn);
  create_new_bb_insns (gen_ctx, DLIST_PREV (MIR_insn_t, insn), before, insn_for_bb);
}

static void gen_add_insn_after (gen_ctx_t gen_ctx, MIR_insn_t after, MIR_insn_t insn) {
  MIR_insn_t insn_for_bb = after;

  gen_assert (insn->code != MIR_LABEL);
  if (MIR_any_branch_code_p (insn_for_bb->code)) insn_for_bb = DLIST_NEXT (MIR_insn_t, insn_for_bb);
  gen_assert (!MIR_any_branch_code_p (insn_for_bb->code));
  MIR_insert_insn_after (gen_ctx->ctx, curr_func_item, after, insn);
  create_new_bb_insns (gen_ctx, after, DLIST_NEXT (MIR_insn_t, insn), insn_for_bb);
}

static void gen_move_insn_before (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t insn) {
  bb_insn_t bb_insn = insn->data, before_bb_insn = before->data;

  DLIST_REMOVE (MIR_insn_t, curr_func_item->u.func->insns, insn);
  MIR_insert_insn_before (gen_ctx->ctx, curr_func_item, before, insn);
  DLIST_REMOVE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn);
  DLIST_INSERT_BEFORE (bb_insn_t, before_bb_insn->bb->bb_insns, before_bb_insn, bb_insn);
  bb_insn->bb = before_bb_insn->bb;
}

static void MIR_UNUSED setup_call_hard_reg_args (gen_ctx_t gen_ctx, MIR_insn_t call_insn,
                                                 MIR_reg_t hard_reg) {
  insn_data_t insn_data;

  gen_assert (MIR_call_code_p (call_insn->code) && hard_reg <= MAX_HARD_REG);
  if (optimize_level != 0) {
    bitmap_set_bit_p (((bb_insn_t) call_insn->data)->call_hard_reg_args, hard_reg);
    return;
  }
  if ((insn_data = call_insn->data)->u.call_hard_reg_args == NULL)
    insn_data->u.call_hard_reg_args = (void *) bitmap_create2 (MAX_HARD_REG + 1);
  bitmap_set_bit_p (insn_data->u.call_hard_reg_args, hard_reg);
}

static void set_label_disp (gen_ctx_t gen_ctx, MIR_insn_t insn, size_t disp) {
  gen_assert (insn->code == MIR_LABEL);
  if (optimize_level == 0)
    ((insn_data_t) insn->data)->u.label_disp = disp;
  else
    ((bb_insn_t) insn->data)->label_disp = disp;
}
static size_t get_label_disp (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  gen_assert (insn->code == MIR_LABEL);
  return (optimize_level == 0 ? ((insn_data_t) insn->data)->u.label_disp
                              : ((bb_insn_t) insn->data)->label_disp);
}

static uint64_t get_ref_value (gen_ctx_t gen_ctx, MIR_op_t *ref_op) {
  gen_assert (ref_op->mode == MIR_OP_REF);
  return (ref_op->u.ref->item_type == MIR_data_item && ref_op->u.ref->u.data->name != NULL
              && _MIR_reserved_ref_name_p (gen_ctx->ctx, ref_op->u.ref->u.data->name)
            ? (uint64_t) ref_op->u.ref->u.data->u.els
            : (uint64_t) ref_op->u.ref->addr);
}

static void setup_used_hard_regs (gen_ctx_t gen_ctx, MIR_type_t type, MIR_reg_t hard_reg) {
  MIR_reg_t curr_hard_reg;
  int i, slots_num = target_locs_num (hard_reg, type);

  for (i = 0; i < slots_num; i++)
    if ((curr_hard_reg = target_nth_loc (hard_reg, type, i)) <= MAX_HARD_REG)
      bitmap_set_bit_p (func_used_hard_regs, curr_hard_reg);
}

static MIR_reg_t get_temp_hard_reg (MIR_type_t type, int first_p) {
  if (type == MIR_T_F) return first_p ? TEMP_FLOAT_HARD_REG1 : TEMP_FLOAT_HARD_REG2;
  if (type == MIR_T_D) return first_p ? TEMP_DOUBLE_HARD_REG1 : TEMP_DOUBLE_HARD_REG2;
  if (type == MIR_T_LD) return first_p ? TEMP_LDOUBLE_HARD_REG1 : TEMP_LDOUBLE_HARD_REG2;
  return first_p ? TEMP_INT_HARD_REG1 : TEMP_INT_HARD_REG2;
}

static bb_t create_bb (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  bb_t bb = gen_malloc (gen_ctx, sizeof (struct bb));

  bb->pre = bb->rpost = bb->bfs = 0;
  bb->loop_node = NULL;
  DLIST_INIT (bb_insn_t, bb->bb_insns);
  DLIST_INIT (in_edge_t, bb->in_edges);
  DLIST_INIT (out_edge_t, bb->out_edges);
  bb->call_p = bb->flag = FALSE;
  bb->in = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->out = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->gen = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->kill = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->dom_in = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->dom_out = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->max_int_pressure = bb->max_fp_pressure = 0;
  if (insn != NULL) {
    if (optimize_level == 0)
      setup_insn_data (gen_ctx, insn, bb);
    else
      add_new_bb_insn (gen_ctx, insn, bb, TRUE);
  }
  return bb;
}

static void add_new_bb (gen_ctx_t gen_ctx, bb_t bb) {
  DLIST_APPEND (bb_t, curr_cfg->bbs, bb);
  bb->index = curr_bb_index++;
}

static void insert_new_bb_after (gen_ctx_t gen_ctx, bb_t after, bb_t bb) {
  DLIST_INSERT_AFTER (bb_t, curr_cfg->bbs, after, bb);
  bb->index = curr_bb_index++;
}

static void insert_new_bb_before (gen_ctx_t gen_ctx, bb_t before, bb_t bb) {
  DLIST_INSERT_BEFORE (bb_t, curr_cfg->bbs, before, bb);
  bb->index = curr_bb_index++;
}

static edge_t create_edge (gen_ctx_t gen_ctx, bb_t src, bb_t dst, int fall_through_p,
                           int append_p) {
  edge_t e = gen_malloc (gen_ctx, sizeof (struct edge));

  e->src = src;
  e->dst = dst;
  if (append_p) {
    DLIST_APPEND (in_edge_t, dst->in_edges, e);
    DLIST_APPEND (out_edge_t, src->out_edges, e);
  } else {
    DLIST_PREPEND (in_edge_t, dst->in_edges, e);
    DLIST_PREPEND (out_edge_t, src->out_edges, e);
  }
  e->fall_through_p = fall_through_p;
  e->back_edge_p = e->flag1 = e->flag2 = FALSE;
  return e;
}

static void delete_edge (edge_t e) {
  DLIST_REMOVE (out_edge_t, e->src->out_edges, e);
  DLIST_REMOVE (in_edge_t, e->dst->in_edges, e);
  free (e);
}

static edge_t find_edge (bb_t src, bb_t dst) {
  for (edge_t e = DLIST_HEAD (out_edge_t, src->out_edges); e != NULL;
       e = DLIST_NEXT (out_edge_t, e))
    if (e->dst == dst) return e;
  return NULL;
}

static void delete_bb (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e, next_e;

  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = next_e) {
    next_e = DLIST_NEXT (out_edge_t, e);
    delete_edge (e);
  }
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = next_e) {
    next_e = DLIST_NEXT (in_edge_t, e);
    delete_edge (e);
  }
  if (bb->loop_node != NULL) {
    if (bb->loop_node->parent->entry == bb->loop_node) bb->loop_node->parent->entry = NULL;
    DLIST_REMOVE (loop_node_t, bb->loop_node->parent->children, bb->loop_node);
    free (bb->loop_node);
  }
  DLIST_REMOVE (bb_t, curr_cfg->bbs, bb);
  bitmap_destroy (bb->in);
  bitmap_destroy (bb->out);
  bitmap_destroy (bb->gen);
  bitmap_destroy (bb->kill);
  bitmap_destroy (bb->dom_in);
  bitmap_destroy (bb->dom_out);
  free (bb);
}

static void print_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn, int with_notes_p);

/* Return BB to put insns from edge E.  If necessary, split edge by creating new bb, bb enumeration
   and new bb bitmaps can be invalid after that.  Loop info is undefined for the new bb. */
static bb_t split_edge_if_necessary (gen_ctx_t gen_ctx, edge_t e, bitmap_t aux_bitmap) {
  MIR_context_t ctx = gen_ctx->ctx;
  int i;
  bb_t new_bb, src = e->src, dst = e->dst;
  edge_t e2;
  bb_insn_t last_bb_insn = DLIST_TAIL (bb_insn_t, src->bb_insns);
  bb_insn_t first_bb_insn = DLIST_HEAD (bb_insn_t, dst->bb_insns);
  MIR_insn_t insn, tail_insn, last_insn = last_bb_insn->insn, first_insn = first_bb_insn->insn;
  DEBUG (4, {
    fprintf (debug_file, "    Splitting bb%lu->bb%lu:\n", (unsigned long) src->index,
             (unsigned long) dst->index);
  });
  if (DLIST_HEAD (out_edge_t, src->out_edges) == DLIST_TAIL (out_edge_t, src->out_edges)
      || e->fall_through_p) { /* fall through or src with one dest */
    if (e->fall_through_p) {
      insn = MIR_new_insn_arr (ctx, MIR_USE, 0, NULL); /* just nop */
      MIR_insert_insn_after (ctx, curr_func_item, last_insn, insn);
    } else if (DLIST_HEAD (in_edge_t, src->in_edges) == DLIST_TAIL (in_edge_t, src->in_edges)) {
      return src;
    } else { /* jump with one dest only: move jmp to new fall-though block */
      gen_assert (last_insn->code == MIR_JMP || last_insn->code == MIR_RET
                  || last_insn->code == MIR_JRET);
      delete_bb_insn (gen_ctx, last_bb_insn);
      insn = last_insn;
    }
    new_bb = create_bb (gen_ctx, insn);
    insert_new_bb_after (gen_ctx, src, new_bb);
    DLIST_REMOVE (in_edge_t, dst->in_edges, e);
    e->dst = new_bb;
    DLIST_APPEND (in_edge_t, new_bb->in_edges, e);
    create_edge (gen_ctx, new_bb, dst, e->fall_through_p, TRUE);
    e->fall_through_p = TRUE;
    DEBUG (4, {
      fprintf (debug_file, "     creating fall through bb%lu after bb%lu, redirect the edge to it",
               (unsigned long) new_bb->index, (unsigned long) src->index);
      fprintf (debug_file, ", and create edge bb%lu->bb%lu:\n", (unsigned long) new_bb->index,
               (unsigned long) dst->index);
      fprintf (debug_file, "       new bb insn is ");
      print_bb_insn (gen_ctx, (bb_insn_t) insn->data, FALSE);
    });
  } else if (DLIST_HEAD (in_edge_t, dst->in_edges) == DLIST_TAIL (in_edge_t, dst->in_edges)) {
    gen_assert (first_insn->code == MIR_LABEL);
    if (first_bb_insn == DLIST_TAIL (bb_insn_t, dst->bb_insns)) return dst;
    /* non-fall through dest with one source only: move dest label to new block */
    delete_bb_insn (gen_ctx, first_bb_insn);
    new_bb = create_bb (gen_ctx, first_insn);
    insert_new_bb_before (gen_ctx, dst, new_bb);
    DLIST_REMOVE (in_edge_t, dst->in_edges, e);
    e->dst = new_bb;
    DLIST_APPEND (in_edge_t, new_bb->in_edges, e);
    create_edge (gen_ctx, new_bb, dst, TRUE, TRUE);
    DEBUG (4, {
      fprintf (debug_file, "     creating bb%lu before bb%lu, redirect the edge to it",
               (unsigned long) new_bb->index, (unsigned long) dst->index);
      fprintf (debug_file, ", and create fall-through edge bb%lu->bb%lu:\n",
               (unsigned long) new_bb->index, (unsigned long) dst->index);
      fprintf (debug_file, "       new bb insn is ");
      print_bb_insn (gen_ctx, (bb_insn_t) first_insn->data, FALSE);
    });
  } else { /* critical non-fall through edge: */
    gen_assert (first_insn->code == MIR_LABEL);
    for (e2 = DLIST_HEAD (in_edge_t, dst->in_edges); e2 != NULL; e2 = DLIST_NEXT (in_edge_t, e2)) {
      if (e2->fall_through_p) break;
      gen_assert (DLIST_TAIL (bb_insn_t, e2->src->bb_insns) != NULL
                  && MIR_any_branch_code_p (DLIST_TAIL (bb_insn_t, e2->src->bb_insns)->insn->code));
    }
    if (e2 != NULL) { /* make fall through edge to dst a jump edge */
      gen_assert (e2->dst == dst);
      insn = MIR_new_insn (ctx, MIR_JMP, MIR_new_label_op (ctx, first_insn));
      tail_insn = DLIST_TAIL (bb_insn_t, e2->src->bb_insns)->insn;
      if (DLIST_NEXT (out_edge_t, e2) == NULL && DLIST_PREV (out_edge_t, e2) == NULL) {
        /* e2->src with the only output edge: just put jump at the end of e2->src */
        gen_assert (!MIR_any_branch_code_p (tail_insn->code));
        gen_add_insn_after (gen_ctx, tail_insn, insn);
        e2->fall_through_p = FALSE;
        DEBUG (4, {
          fprintf (debug_file,
                   "     Make edge bb%lu->bb%lu a non-fall through, add new insn at the of bb%lu ",
                   (unsigned long) e2->src->index, (unsigned long) e2->dst->index,
                   (unsigned long) e2->src->index);
          print_bb_insn (gen_ctx, (bb_insn_t) insn->data, FALSE);
        });
      } else {
        MIR_insert_insn_after (ctx, curr_func_item, tail_insn, insn);
        new_bb = create_bb (gen_ctx, insn);
        insert_new_bb_after (gen_ctx, e2->src, new_bb);
        DLIST_REMOVE (in_edge_t, e2->dst->in_edges, e2);
        e2->dst = new_bb;
        DLIST_APPEND (in_edge_t, new_bb->in_edges, e2);
        create_edge (gen_ctx, new_bb, dst, FALSE, TRUE);
        DEBUG (4, {
          fprintf (debug_file,
                   "     creating bb%lu after bb%lu, redirect edge bb%lu->bb%lu to bb%lu",
                   (unsigned long) new_bb->index, (unsigned long) e2->src->index,
                   (unsigned long) e2->src->index, (unsigned long) dst->index,
                   (unsigned long) new_bb->index);
          fprintf (debug_file, ", and create jump edge bb%lu->bb%lu:\n",
                   (unsigned long) new_bb->index, (unsigned long) dst->index);
          fprintf (debug_file, "       new bb insn is ");
          print_bb_insn (gen_ctx, (bb_insn_t) insn->data, FALSE);
        });
      }
    }
    /* add fall through new block before dst */
    insn = _MIR_new_label (ctx);
    MIR_insert_insn_before (ctx, curr_func_item, first_insn, insn);
    new_bb = create_bb (gen_ctx, insn);
    insert_new_bb_before (gen_ctx, dst, new_bb);
    DLIST_REMOVE (in_edge_t, dst->in_edges, e);
    e->dst = new_bb;
    DLIST_APPEND (in_edge_t, new_bb->in_edges, e);
    create_edge (gen_ctx, new_bb, dst, TRUE, TRUE);
    DEBUG (4, {
      fprintf (debug_file, "     creating bb%lu before bb%lu, redirect the edge to it",
               (unsigned long) new_bb->index, (unsigned long) dst->index);
      fprintf (debug_file, ", and create fall-through edge bb%lu->bb%lu:\n",
               (unsigned long) new_bb->index, (unsigned long) dst->index);
      fprintf (debug_file, "       new bb insn is ");
      print_bb_insn (gen_ctx, (bb_insn_t) insn->data, FALSE);
      fprintf (debug_file, "       change src bb insn ");
      print_bb_insn (gen_ctx, last_bb_insn, FALSE);
    });
    /* change label first_insn to label insn in src */
    if (last_insn->code != MIR_SWITCH) {
      gen_assert (last_insn->ops[0].mode == MIR_OP_LABEL
                  && last_insn->ops[0].u.label == first_insn);
      last_insn->ops[0] = MIR_new_label_op (ctx, insn);
    } else {
      for (i = 1; i < last_insn->nops; i++)
        if (last_insn->ops[i].u.label == first_insn) break;
      gen_assert (i < last_insn->nops);
      last_insn->ops[i] = MIR_new_label_op (ctx, insn);
    }
    DEBUG (4, {
      fprintf (debug_file, "         to insn ");
      print_bb_insn (gen_ctx, last_bb_insn, FALSE);
    });
  }
  return new_bb;
}

static void DFS (bb_t bb, size_t *pre, size_t *rpost) {
  edge_t e;

  bb->pre = (*pre)++;
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    if (e->dst->pre == 0)
      DFS (e->dst, pre, rpost);
    else if (e->dst->rpost == 0)
      e->back_edge_p = TRUE;
  bb->rpost = (*rpost)--;
}

static void enumerate_bbs (gen_ctx_t gen_ctx) {
  size_t pre, rpost;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    bb->pre = bb->rpost = 0;
  pre = 1;
  rpost = DLIST_LENGTH (bb_t, curr_cfg->bbs);
  DFS (DLIST_HEAD (bb_t, curr_cfg->bbs), &pre, &rpost);
}

static loop_node_t top_loop_node (bb_t bb) {
  for (loop_node_t loop_node = bb->loop_node;; loop_node = loop_node->parent)
    if (loop_node->parent == NULL) return loop_node;
}

static loop_node_t create_loop_node (gen_ctx_t gen_ctx, bb_t bb) {
  loop_node_t loop_node = gen_malloc (gen_ctx, sizeof (struct loop_node));

  loop_node->index = curr_loop_node_index++;
  loop_node->bb = bb;
  if (bb != NULL) bb->loop_node = loop_node;
  loop_node->parent = NULL;
  loop_node->entry = NULL;
  loop_node->preheader = NULL;
  loop_node->max_int_pressure = loop_node->max_fp_pressure = 0;
  DLIST_INIT (loop_node_t, loop_node->children);
  return loop_node;
}

static int process_loop (gen_ctx_t gen_ctx, bb_t entry_bb) {
  edge_t e;
  loop_node_t loop_node, new_loop_node, queue_node;
  bb_t queue_bb;

  VARR_TRUNC (loop_node_t, loop_nodes, 0);
  VARR_TRUNC (loop_node_t, queue_nodes, 0);
  bitmap_clear (temp_bitmap);
  for (e = DLIST_HEAD (in_edge_t, entry_bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
    if (e->back_edge_p && e->src != entry_bb) {
      loop_node = top_loop_node (e->src);
      if (!bitmap_set_bit_p (temp_bitmap, loop_node->index)) continue;
      VARR_PUSH (loop_node_t, loop_nodes, loop_node);
      VARR_PUSH (loop_node_t, queue_nodes, loop_node);
    }
  while (VARR_LENGTH (loop_node_t, queue_nodes) != 0) {
    queue_node = VARR_POP (loop_node_t, queue_nodes);
    if ((queue_bb = queue_node->bb) == NULL) queue_bb = queue_node->entry->bb; /* subloop */
    /* entry block is achieved which means multiple entry loop -- just ignore */
    if (queue_bb == DLIST_HEAD (bb_t, curr_cfg->bbs)) return FALSE;
    for (e = DLIST_HEAD (in_edge_t, queue_bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
      if (e->src != entry_bb) {
        loop_node = top_loop_node (e->src);
        if (!bitmap_set_bit_p (temp_bitmap, loop_node->index)) continue;
        VARR_PUSH (loop_node_t, loop_nodes, loop_node);
        VARR_PUSH (loop_node_t, queue_nodes, loop_node);
      }
  }
  loop_node = entry_bb->loop_node;
  VARR_PUSH (loop_node_t, loop_nodes, loop_node);
  new_loop_node = create_loop_node (gen_ctx, NULL);
  new_loop_node->entry = loop_node;
  while (VARR_LENGTH (loop_node_t, loop_nodes) != 0) {
    loop_node = VARR_POP (loop_node_t, loop_nodes);
    DLIST_APPEND (loop_node_t, new_loop_node->children, loop_node);
    loop_node->parent = new_loop_node;
  }
  return TRUE;
}

static void setup_loop_pressure (gen_ctx_t gen_ctx, loop_node_t loop_node) {
  for (loop_node_t curr = DLIST_HEAD (loop_node_t, loop_node->children); curr != NULL;
       curr = DLIST_NEXT (loop_node_t, curr)) {
    if (curr->bb == NULL) {
      setup_loop_pressure (gen_ctx, curr);
    } else {
      curr->max_int_pressure = curr->bb->max_int_pressure;
      curr->max_fp_pressure = curr->bb->max_fp_pressure;
    }
    if (loop_node->max_int_pressure < curr->max_int_pressure)
      loop_node->max_int_pressure = curr->max_int_pressure;
    if (loop_node->max_fp_pressure < curr->max_fp_pressure)
      loop_node->max_fp_pressure = curr->max_fp_pressure;
  }
}

static int compare_bb_loop_nodes (const void *p1, const void *p2) {
  bb_t bb1 = (*(const loop_node_t *) p1)->bb, bb2 = (*(const loop_node_t *) p2)->bb;

  return bb1->rpost > bb2->rpost ? -1 : bb1->rpost < bb2->rpost ? 1 : 0;
}

static int build_loop_tree (gen_ctx_t gen_ctx) {
  loop_node_t loop_node;
  edge_t e;
  int loops_p = FALSE;

  curr_loop_node_index = 0;
  enumerate_bbs (gen_ctx);
  VARR_TRUNC (loop_node_t, loop_entries, 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    loop_node = create_loop_node (gen_ctx, bb);
    loop_node->entry = loop_node;
    for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
      if (e->back_edge_p) {
        VARR_PUSH (loop_node_t, loop_entries, loop_node);
        break;
      }
  }
  qsort (VARR_ADDR (loop_node_t, loop_entries), VARR_LENGTH (loop_node_t, loop_entries),
         sizeof (loop_node_t), compare_bb_loop_nodes);
  for (size_t i = 0; i < VARR_LENGTH (loop_node_t, loop_entries); i++)
    if (process_loop (gen_ctx, VARR_GET (loop_node_t, loop_entries, i)->bb)) loops_p = TRUE;
  curr_cfg->root_loop_node = create_loop_node (gen_ctx, NULL);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    if ((loop_node = top_loop_node (bb)) != curr_cfg->root_loop_node) {
      DLIST_APPEND (loop_node_t, curr_cfg->root_loop_node->children, loop_node);
      loop_node->parent = curr_cfg->root_loop_node;
    }
  setup_loop_pressure (gen_ctx, curr_cfg->root_loop_node);
  return loops_p;
}

static void destroy_loop_tree (gen_ctx_t gen_ctx, loop_node_t root) {
  loop_node_t node, next;

  if (root->bb != NULL) {
    root->bb->loop_node = NULL;
  } else {
    for (node = DLIST_HEAD (loop_node_t, root->children); node != NULL; node = next) {
      next = DLIST_NEXT (loop_node_t, node);
      destroy_loop_tree (gen_ctx, node);
    }
  }
  free (root);
}

static void update_max_var (gen_ctx_t gen_ctx, MIR_reg_t reg) {
  if (reg == MIR_NON_VAR) return;
  if (curr_cfg->max_var < reg) curr_cfg->max_var = reg;
}

static MIR_reg_t gen_new_temp_reg (gen_ctx_t gen_ctx, MIR_type_t type, MIR_func_t func) {
  MIR_reg_t reg = _MIR_new_temp_reg (gen_ctx->ctx, type, func) + MAX_HARD_REG;

  update_max_var (gen_ctx, reg);
  return reg;
}

static MIR_reg_t get_max_var (gen_ctx_t gen_ctx) { return curr_cfg->max_var; }

static int move_code_p (MIR_insn_code_t code) {
  return code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV || code == MIR_LDMOV;
}

static int move_p (MIR_insn_t insn) {
  return (move_code_p (insn->code) && insn->ops[0].mode == MIR_OP_VAR
          && insn->ops[1].mode == MIR_OP_VAR && insn->ops[0].u.var > MAX_HARD_REG
          && insn->ops[1].u.var > MAX_HARD_REG);
}

static int imm_move_p (MIR_insn_t insn) {
  return (move_code_p (insn->code) && insn->ops[0].mode == MIR_OP_VAR
          && insn->ops[0].u.var > MAX_HARD_REG
          && (insn->ops[1].mode == MIR_OP_INT || insn->ops[1].mode == MIR_OP_UINT
              || insn->ops[1].mode == MIR_OP_FLOAT || insn->ops[1].mode == MIR_OP_DOUBLE
              || insn->ops[1].mode == MIR_OP_LDOUBLE || insn->ops[1].mode == MIR_OP_REF));
}

typedef struct {
  MIR_insn_t insn;
  size_t nops, op_num, op_part_num;
} insn_var_iterator_t;

static inline void insn_var_iterator_init (gen_ctx_t gen_ctx, insn_var_iterator_t *iter,
                                           MIR_insn_t insn) {
  iter->insn = insn;
  iter->nops = MIR_insn_nops (gen_ctx->ctx, insn);
  iter->op_num = 0;
  iter->op_part_num = 0;
}

static inline int insn_var_iterator_next (gen_ctx_t gen_ctx, insn_var_iterator_t *iter,
                                          MIR_reg_t *var, int *op_num, int *out_p, int *mem_p) {
  MIR_op_t op;

  while (iter->op_num < iter->nops) {
    *op_num = iter->op_num;
    MIR_insn_op_mode (gen_ctx->ctx, iter->insn, iter->op_num, out_p);
    op = iter->insn->ops[iter->op_num];
    *mem_p = FALSE;
    while (iter->op_part_num < 2) {
      if (op.mode == MIR_OP_VAR_MEM) {
        *mem_p = TRUE;
        *out_p = FALSE;
        *var = iter->op_part_num == 0 ? op.u.var_mem.base : op.u.var_mem.index;
        if (*var == MIR_NON_VAR) {
          iter->op_part_num++;
          continue;
        }
      } else if (iter->op_part_num > 0) {
        break;
      } else if (op.mode == MIR_OP_VAR) {
        *var = op.u.var;
      } else
        break;
      iter->op_part_num++;
      return TRUE;
    }
    iter->op_num++;
    iter->op_part_num = 0;
  }
  return FALSE;
}

#define FOREACH_INSN_VAR(gen_ctx, iterator, insn, var, op_num, out_p, mem_p) \
  for (insn_var_iterator_init (gen_ctx, &iterator, insn);                    \
       insn_var_iterator_next (gen_ctx, &iterator, &var, &op_num, &out_p, &mem_p);)

#if !MIR_NO_GEN_DEBUG
static void output_in_edges (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  in edges:");
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    fprintf (debug_file, " %3lu%s%s", (unsigned long) e->src->index, e->fall_through_p ? "f" : "",
             e->back_edge_p ? "*" : "");
  }
  fprintf (debug_file, "\n");
}

static void output_out_edges (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  out edges:");
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e)) {
    fprintf (debug_file, " %3lu%s%s", (unsigned long) e->dst->index, e->fall_through_p ? "f" : "",
             e->back_edge_p ? "*" : "");
  }
  fprintf (debug_file, "\n");
}

/* When print_name_p, treat as reg bitmap. */
static void output_bitmap (gen_ctx_t gen_ctx, const char *head, bitmap_t bm, int print_name_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t reg;
  size_t nel;
  bitmap_iterator_t bi;

  if (bm == NULL || bitmap_empty_p (bm)) return;
  fprintf (debug_file, "%s", head);
  FOREACH_BITMAP_BIT (bi, bm, nel) {
    fprintf (debug_file, " %3lu", (unsigned long) nel);
    if (print_name_p && nel > MAX_HARD_REG) {
      reg = nel;
      fprintf (debug_file, "(%s:%s)",
               MIR_type_str (ctx, MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func)),
               MIR_reg_name (ctx, reg - MAX_HARD_REG, curr_func_item->u.func));
    }
  }
  fprintf (debug_file, "\n");
}

static void print_op_data (gen_ctx_t gen_ctx, void *op_data, bb_insn_t from);
static void print_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn, int with_notes_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_op_t op;
  int first_p;
  int flag;
  size_t nel;
  bitmap_iterator_t bi;

  MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
  for (size_t i = 0; i < bb_insn->insn->nops; i++) {
    op = bb_insn->insn->ops[i];
    if (op.mode == MIR_OP_VAR_MEM && op.u.var_mem.nloc != 0) {
      flag = VARR_GET (mem_attr_t, mem_attrs, op.u.var_mem.nloc).alloca_flag;
      fprintf (debug_file, " # m%lu%s", (unsigned long) op.u.var_mem.nloc,
               !flag                               ? ""
               : flag & (MAY_ALLOCA | MUST_ALLOCA) ? "au"
               : flag & MAY_ALLOCA                 ? "a"
                                                   : "u");
    }
  }
  fprintf (debug_file, " # indexes: ");
  for (size_t i = 0; i < bb_insn->insn->nops; i++) {
    if (i != 0) fprintf (debug_file, ",");
    print_op_data (gen_ctx, bb_insn->insn->ops[i].data, bb_insn);
  }
  if (with_notes_p) {
    for (dead_var_t dv = DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars); dv != NULL;
         dv = DLIST_NEXT (dead_var_t, dv)) {
      op.mode = MIR_OP_VAR;
      op.u.var = dv->var;
      fprintf (debug_file,
               dv == DLIST_HEAD (dead_var_t, bb_insn->insn_dead_vars) ? " # dead: " : " ");
      MIR_output_op (ctx, debug_file, op, curr_func_item->u.func);
    }
    if (MIR_call_code_p (bb_insn->insn->code)) {
      first_p = TRUE;
      FOREACH_BITMAP_BIT (bi, bb_insn->call_hard_reg_args, nel) {
        fprintf (debug_file, first_p ? " # call used: hr%ld" : " hr%ld", (unsigned long) nel);
        first_p = FALSE;
      }
    }
  }
  fprintf (debug_file, "\n");
}

static void print_CFG (gen_ctx_t gen_ctx, int bb_p, int pressure_p, int insns_p, int insn_index_p,
                       void (*bb_info_print_func) (gen_ctx_t, bb_t)) {
  bb_t bb, insn_bb;

  if (optimize_level == 0) {
    bb = NULL;
    for (MIR_insn_t insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
         insn = DLIST_NEXT (MIR_insn_t, insn)) {
      if (bb_p && (insn_bb = get_insn_data_bb (insn)) != bb) {
        bb = insn_bb;
        fprintf (debug_file, "BB %3lu:\n", (unsigned long) bb->index);
        output_in_edges (gen_ctx, bb);
        output_out_edges (gen_ctx, bb);
        if (bb_info_print_func != NULL) {
          bb_info_print_func (gen_ctx, bb);
          fprintf (debug_file, "\n");
        }
      }
      if (insns_p) MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
    }
    return;
  }
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb_p) {
      fprintf (debug_file, "BB %3lu", (unsigned long) bb->index);
      if (pressure_p)
        fprintf (debug_file, " (pressure: int=%d, fp=%d)", bb->max_int_pressure,
                 bb->max_fp_pressure);
      if (bb->loop_node == NULL)
        fprintf (debug_file, "\n");
      else
        fprintf (debug_file, " (loop%3lu):\n", (unsigned long) bb->loop_node->parent->index);
      output_in_edges (gen_ctx, bb);
      output_out_edges (gen_ctx, bb);
      if (bb_info_print_func != NULL) {
        bb_info_print_func (gen_ctx, bb);
        fprintf (debug_file, "\n");
      }
    }
    if (insns_p) {
      for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
           bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
        if (insn_index_p) fprintf (debug_file, "  %-5lu", (unsigned long) bb_insn->index);
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      }
      fprintf (debug_file, "\n");
    }
  }
}

static void print_varr_insns (gen_ctx_t gen_ctx, const char *title, VARR (bb_insn_t) * bb_insns) {
  fprintf (debug_file, "%s insns:\n", title);
  for (size_t i = 0; i < VARR_LENGTH (bb_insn_t, bb_insns); i++) {
    bb_insn_t bb_insn = VARR_GET (bb_insn_t, bb_insns, i);
    if (bb_insn == NULL) continue;
    fprintf (debug_file, "  %-5lu", (unsigned long) bb_insn->index);
    print_bb_insn (gen_ctx, bb_insn, TRUE);
  }
}

static void print_loop_subtree (gen_ctx_t gen_ctx, loop_node_t root, int level, int bb_p) {
  if (root->bb != NULL && !bb_p) return;
  for (int i = 0; i < 2 * level + 2; i++) fprintf (debug_file, " ");
  if (root->bb != NULL) {
    gen_assert (DLIST_HEAD (loop_node_t, root->children) == NULL);
    fprintf (debug_file, "BB%-3lu (pressure: int=%d, fp=%d)\n", (unsigned long) root->bb->index,
             root->max_int_pressure, root->max_fp_pressure);
    return;
  }
  fprintf (debug_file, "Loop%3lu (pressure: int=%d, fp=%d)", (unsigned long) root->index,
           root->max_int_pressure, root->max_fp_pressure);
  if (curr_cfg->root_loop_node == root || root->entry == NULL)
    fprintf (debug_file, ":\n");
  else {
    if (root->preheader != NULL)
      fprintf (debug_file, " (preheader - bb%lu)", (unsigned long) root->preheader->index);
    fprintf (debug_file, " (entry - bb%lu):\n", (unsigned long) root->entry->bb->index);
  }
  for (loop_node_t node = DLIST_HEAD (loop_node_t, root->children); node != NULL;
       node = DLIST_NEXT (loop_node_t, node))
    print_loop_subtree (gen_ctx, node, level + 1, bb_p);
}

static void print_loop_tree (gen_ctx_t gen_ctx, int bb_p) {
  if (curr_cfg->root_loop_node == NULL) return;
  fprintf (debug_file, "Loop Tree\n");
  print_loop_subtree (gen_ctx, curr_cfg->root_loop_node, 0, bb_p);
}

#endif

static void rename_op_reg (gen_ctx_t gen_ctx, MIR_op_t *op_ref, MIR_reg_t reg, MIR_reg_t new_reg,
                           MIR_insn_t insn, int print_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  int change_p = FALSE;

  gen_assert (reg > MAX_HARD_REG);
  if (op_ref->mode == MIR_OP_VAR && op_ref->u.var == reg) {
    op_ref->u.var = new_reg;
    change_p = TRUE;
  } else if (op_ref->mode == MIR_OP_VAR_MEM) {
    if (op_ref->u.var_mem.base == reg) {
      op_ref->u.var_mem.base = new_reg;
      change_p = TRUE;
    }
    if (op_ref->u.var_mem.index == reg) {
      op_ref->u.var_mem.index = new_reg;
      change_p = TRUE;
    }
  }
  if (!change_p || !print_p) return; /* definition was already changed from another use */
  DEBUG (2, {
    MIR_func_t func = curr_func_item->u.func;

    fprintf (debug_file, "    Change %s to %s in insn %-5lu",
             MIR_reg_name (ctx, reg - MAX_HARD_REG, func),
             MIR_reg_name (ctx, new_reg - MAX_HARD_REG, func),
             (long unsigned) ((bb_insn_t) insn->data)->index);
    print_bb_insn (gen_ctx, insn->data, FALSE);
  });
}

static void update_tied_regs (gen_ctx_t gen_ctx, MIR_reg_t reg) {
  gen_assert (reg > MAX_HARD_REG);
  if (reg == MIR_NON_VAR
      || MIR_reg_hard_reg_name (gen_ctx->ctx, reg - MAX_HARD_REG, curr_func_item->u.func) == NULL)
    return;
  bitmap_set_bit_p (tied_regs, reg);
}

static long remove_unreachable_bbs (gen_ctx_t gen_ctx);

static void build_func_cfg (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func = curr_func_item->u.func;
  MIR_insn_t insn, next_insn, ret_insn, use_insn;
  size_t i, nops;
  MIR_op_t *op;
  MIR_reg_t reg;
  MIR_var_t mir_var;
  bb_t bb, prev_bb, entry_bb, exit_bb, label_bb;

  DLIST_INIT (bb_t, curr_cfg->bbs);
  curr_cfg->curr_bb_insn_index = 0;
  curr_cfg->max_var = MAX_HARD_REG;
  curr_cfg->root_loop_node = NULL;
  curr_bb_index = 0;
  for (i = 0; i < VARR_LENGTH (MIR_var_t, func->vars); i++) {
    mir_var = VARR_GET (MIR_var_t, func->vars, i);
    update_max_var (gen_ctx, MIR_reg (ctx, mir_var.name, func) + MAX_HARD_REG);
  }
  entry_bb = create_bb (gen_ctx, NULL);
  add_new_bb (gen_ctx, entry_bb);
  exit_bb = create_bb (gen_ctx, NULL);
  add_new_bb (gen_ctx, exit_bb);
  insn = DLIST_HEAD (MIR_insn_t, func->insns);
  /* To deal with special cases like adding insns before call in
     machinize or moving invariant out of loop: */
  MIR_prepend_insn (ctx, curr_func_item, _MIR_new_label (ctx));
  insn = DLIST_HEAD (MIR_insn_t, func->insns);
  bb = create_bb (gen_ctx, NULL);
  add_new_bb (gen_ctx, bb);
  bitmap_clear (tied_regs);
  bitmap_clear (addr_regs);
  addr_insn_p = FALSE;
  for (ret_insn = NULL; insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    if (insn->code == MIR_ADDR) {
      addr_insn_p = TRUE;
      bitmap_set_bit_p (addr_regs, insn->ops[1].u.reg + MAX_HARD_REG);
    } else if (insn->code == MIR_RET) {
      if (ret_insn != NULL) { /* we should have only one ret insn before generator */
        gen_assert (ret_insn == insn);
      } else if (func->global_vars != NULL) {
        VARR_TRUNC (MIR_op_t, temp_ops, 0);
        for (i = 0; i < VARR_LENGTH (MIR_var_t, func->global_vars); i++) {
          reg = MIR_reg (ctx, VARR_GET (MIR_var_t, func->global_vars, i).name, func) + MAX_HARD_REG;
          VARR_PUSH (MIR_op_t, temp_ops, _MIR_new_var_op (ctx, reg));
        }
        use_insn = MIR_new_insn_arr (ctx, MIR_USE, VARR_LENGTH (MIR_op_t, temp_ops),
                                     VARR_ADDR (MIR_op_t, temp_ops));
        MIR_insert_insn_before (ctx, curr_func_item, insn, use_insn);
        next_insn = use_insn;
        ret_insn = insn;
        continue;
      }
    } else if (MIR_call_code_p (insn->code)) {
      bb->call_p = TRUE;
    }
    if (insn->data == NULL) {
      if (optimize_level != 0)
        add_new_bb_insn (gen_ctx, insn, bb, TRUE);
      else
        setup_insn_data (gen_ctx, insn, bb);
    }
    nops = MIR_insn_nops (ctx, insn);
    if (next_insn != NULL
        && (MIR_any_branch_code_p (insn->code) || insn->code == MIR_RET || insn->code == MIR_JRET
            || insn->code == MIR_PRBEQ || insn->code == MIR_PRBNE
            || next_insn->code == MIR_LABEL)) {
      prev_bb = bb;
      if (next_insn->code == MIR_LABEL && next_insn->data != NULL)
        bb = get_insn_bb (gen_ctx, next_insn);
      else
        bb = create_bb (gen_ctx, next_insn);
      add_new_bb (gen_ctx, bb);
      if (insn->code != MIR_JMP && insn->code != MIR_RET && insn->code != MIR_JRET
          && insn->code != MIR_SWITCH)
        create_edge (gen_ctx, prev_bb, bb, TRUE, TRUE); /* fall through */
    }
    for (i = 0; i < nops; i++) { /* Transform all ops to var ops */
      op = &insn->ops[i];
      if (op->mode == MIR_OP_REG) {
        op->mode = MIR_OP_VAR;
        op->u.var = op->u.reg == 0 ? MIR_NON_VAR : op->u.reg + MAX_HARD_REG;
      } else if (op->mode == MIR_OP_MEM) {
        op->mode = MIR_OP_VAR_MEM;
        op->u.var_mem.base = op->u.mem.base == 0 ? MIR_NON_VAR : op->u.mem.base + MAX_HARD_REG;
        op->u.var_mem.index = op->u.mem.index == 0 ? MIR_NON_VAR : op->u.mem.index + MAX_HARD_REG;
      }
      if (op->mode == MIR_OP_LABEL) {
        if (op->u.label->data == NULL) create_bb (gen_ctx, op->u.label);
        label_bb = get_insn_bb (gen_ctx, op->u.label);
        create_edge (gen_ctx, get_insn_bb (gen_ctx, insn), label_bb, FALSE, TRUE);
      } else if (op->mode == MIR_OP_VAR) {
        update_max_var (gen_ctx, op->u.var);
        update_tied_regs (gen_ctx, op->u.var);
      } else if (op->mode == MIR_OP_VAR_MEM) {
        update_max_var (gen_ctx, op->u.var_mem.base);
        update_tied_regs (gen_ctx, op->u.var_mem.base);
        update_max_var (gen_ctx, op->u.var_mem.index);
        update_tied_regs (gen_ctx, op->u.var_mem.index);
      }
    }
  }
  if (optimize_level > 0) remove_unreachable_bbs (gen_ctx);
  /* Add additional edges with entry and exit */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb != entry_bb && DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
      create_edge (gen_ctx, entry_bb, bb, FALSE, TRUE);
    if (bb != exit_bb && DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
      create_edge (gen_ctx, bb, exit_bb, FALSE, TRUE);
  }
  enumerate_bbs (gen_ctx);
  VARR_CREATE (reg_info_t, curr_cfg->reg_info, 128);
  curr_cfg->call_crossed_regs = bitmap_create2 (curr_cfg->max_var);
}

static void destroy_func_cfg (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t bb, next_bb;

  gen_assert (curr_func_item->item_type == MIR_func_item && curr_func_item->data != NULL);
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn))
    if (optimize_level == 0) {
      gen_assert (insn->data != NULL);
      delete_insn_data (insn);
    } else {
      bb_insn = insn->data;
      gen_assert (bb_insn != NULL);
      delete_bb_insn (gen_ctx, bb_insn);
    }
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    delete_bb (gen_ctx, bb);
  }
  VARR_DESTROY (reg_info_t, curr_cfg->reg_info);
  bitmap_destroy (curr_cfg->call_crossed_regs);
  free (curr_func_item->data);
  curr_func_item->data = NULL;
}

static int rpost_cmp (const void *a1, const void *a2) {
  return (*(const struct bb **) a1)->rpost - (*(const struct bb **) a2)->rpost;
}

static int post_cmp (const void *a1, const void *a2) { return -rpost_cmp (a1, a2); }

DEF_VARR (bb_t);

struct data_flow_ctx {
  VARR (bb_t) * worklist, *pending;
  bitmap_t bb_to_consider;
};

#define worklist gen_ctx->data_flow_ctx->worklist
#define pending gen_ctx->data_flow_ctx->pending
#define bb_to_consider gen_ctx->data_flow_ctx->bb_to_consider

static void solve_dataflow (gen_ctx_t gen_ctx, int forward_p, void (*con_func_0) (bb_t),
                            int (*con_func_n) (gen_ctx_t, bb_t),
                            int (*trans_func) (gen_ctx_t, bb_t)) {
  size_t i, iter;
  bb_t bb, *addr;
  VARR (bb_t) * t;

  VARR_TRUNC (bb_t, worklist, 0);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    VARR_PUSH (bb_t, worklist, bb);
  VARR_TRUNC (bb_t, pending, 0);
  iter = 0;
  while (VARR_LENGTH (bb_t, worklist) != 0) {
    VARR_TRUNC (bb_t, pending, 0);
    addr = VARR_ADDR (bb_t, worklist);
    qsort (addr, VARR_LENGTH (bb_t, worklist), sizeof (bb), forward_p ? rpost_cmp : post_cmp);
    bitmap_clear (bb_to_consider);
    for (i = 0; i < VARR_LENGTH (bb_t, worklist); i++) {
      int changed_p = iter == 0;
      edge_t e;

      bb = addr[i];
      if (forward_p) {
        if (DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
          con_func_0 (bb);
        else
          changed_p |= con_func_n (gen_ctx, bb);
      } else {
        if (DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
          con_func_0 (bb);
        else
          changed_p |= con_func_n (gen_ctx, bb);
      }
      if (changed_p && trans_func (gen_ctx, bb)) {
        if (forward_p) {
          for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL;
               e = DLIST_NEXT (out_edge_t, e))
            if (bitmap_set_bit_p (bb_to_consider, e->dst->index)) VARR_PUSH (bb_t, pending, e->dst);
        } else {
          for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
            if (bitmap_set_bit_p (bb_to_consider, e->src->index)) VARR_PUSH (bb_t, pending, e->src);
        }
      }
    }
    iter++;
    t = worklist;
    worklist = pending;
    pending = t;
  }
}

static void init_data_flow (gen_ctx_t gen_ctx) {
  gen_ctx->data_flow_ctx = gen_malloc (gen_ctx, sizeof (struct data_flow_ctx));
  VARR_CREATE (bb_t, worklist, 0);
  VARR_CREATE (bb_t, pending, 0);
  bb_to_consider = bitmap_create2 (512);
}

static void finish_data_flow (gen_ctx_t gen_ctx) {
  VARR_DESTROY (bb_t, worklist);
  VARR_DESTROY (bb_t, pending);
  bitmap_destroy (bb_to_consider);
  free (gen_ctx->data_flow_ctx);
  gen_ctx->data_flow_ctx = NULL;
}

/* New Page */

static MIR_insn_t get_insn_label (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t label;

  if (insn->code == MIR_LABEL) return insn;
  label = _MIR_new_label (ctx);
  MIR_insert_insn_before (ctx, curr_func_item, insn, label);
  add_new_bb_insn (gen_ctx, label, ((bb_insn_t) insn->data)->bb, FALSE);
  return label;
}

/* Clone hot BBs to cold ones (which are after ret insn) to improve
   optimization opportunities in hot part.  */
static int clone_bbs (gen_ctx_t gen_ctx) {
  const int max_bb_growth_factor = 3;
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t dst_insn, last_dst_insn, new_insn, label, next_insn, after;
  bb_t bb, dst, new_bb;
  edge_t e;
  bb_insn_t bb_insn, dst_bb_insn, next_bb_insn;
  MIR_func_t func = curr_func_item->u.func;
  size_t size, orig_size, len, last_orig_bound;
  int res;

  gen_assert (optimize_level != 0);
  bitmap_clear (temp_bitmap);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_set_bit_p (temp_bitmap, bb->index);
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL) continue;
    if (bb_insn->insn->code == MIR_RET || bb_insn->insn->code == MIR_JRET) break;
  }
  if (bb == NULL) return FALSE;
  VARR_TRUNC (bb_t, worklist, 0);
  for (bb = DLIST_NEXT (bb_t, bb); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
    gen_assert (bb_insn != NULL);
    if (bb_insn->insn->code == MIR_JMP && (e = DLIST_HEAD (out_edge_t, bb->out_edges)) != NULL
        && bitmap_bit_p (temp_bitmap, e->dst->index))
      VARR_PUSH (bb_t, worklist, bb);
  }
  res = FALSE;
  last_orig_bound = VARR_LENGTH (bb_t, worklist);
  orig_size = size = 0;
  while ((len = VARR_LENGTH (bb_t, worklist)) != 0) {
    if (last_orig_bound > len) {
      last_orig_bound = len;
      orig_size = size = DLIST_LENGTH (bb_insn_t, VARR_LAST (bb_t, worklist)->bb_insns);
    }
    bb = VARR_POP (bb_t, worklist);
    e = DLIST_HEAD (out_edge_t, bb->out_edges);
    gen_assert (DLIST_NEXT (out_edge_t, e) == NULL);
    if (e->back_edge_p) continue;
    bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
    gen_assert (bb_insn != NULL && bb_insn->insn->code == MIR_JMP);
    dst = e->dst;
    dst_bb_insn = DLIST_TAIL (bb_insn_t, dst->bb_insns);
    if (dst_bb_insn->insn->code == MIR_RET || dst_bb_insn->insn->code == MIR_JRET
        || dst_bb_insn->insn->code == MIR_SWITCH || size > max_bb_growth_factor * orig_size)
      continue;
    res = TRUE;
    DEBUG (2, {
      fprintf (debug_file, "  Cloning from BB%lu into BB%lu:\n", (unsigned long) dst->index,
               (unsigned long) bb->index);
    });
    last_dst_insn = DLIST_TAIL (bb_insn_t, dst->bb_insns)->insn;
    after = DLIST_PREV (MIR_insn_t, bb_insn->insn);
    gen_delete_insn (gen_ctx, bb_insn->insn);
    bb_insn = NULL;
    for (dst_bb_insn = DLIST_HEAD (bb_insn_t, dst->bb_insns); dst_bb_insn != NULL;
         dst_bb_insn = DLIST_NEXT (bb_insn_t, dst_bb_insn)) {
      dst_insn = dst_bb_insn->insn;
      if (dst_insn->code == MIR_LABEL) continue;
      new_insn = MIR_copy_insn (ctx, dst_insn);
      /* we can not use gen_add_insn_xxx becuase of some cases (e.g. bb_insn is the last insn): */
      MIR_insert_insn_after (ctx, curr_func_item, after, new_insn);
      add_new_bb_insn (gen_ctx, new_insn, bb, TRUE);
      after = new_insn;
      DEBUG (2, {
        fprintf (debug_file, "  Adding insn %-5lu",
                 (unsigned long) ((bb_insn_t) new_insn->data)->index);
        MIR_output_insn (ctx, debug_file, new_insn, func, TRUE);
      });
      size++;
    }
    delete_edge (e);
    gen_assert (last_dst_insn != NULL);
    if (last_dst_insn->code == MIR_JMP) {
      label = last_dst_insn->ops[0].u.label;
      create_edge (gen_ctx, bb, ((bb_insn_t) label->data)->bb, FALSE, TRUE);
      if (bitmap_bit_p (temp_bitmap, ((bb_insn_t) label->data)->index))
        VARR_PUSH (bb_t, worklist, bb);
    } else if (!MIR_branch_code_p (last_dst_insn->code)) {
      next_insn = DLIST_NEXT (MIR_insn_t, last_dst_insn);
      next_bb_insn = next_insn->data;
      gen_assert (next_insn->code == MIR_LABEL);
      new_insn = MIR_new_insn (ctx, MIR_JMP, MIR_new_label_op (ctx, next_insn));
      MIR_insert_insn_after (ctx, curr_func_item, after, new_insn);
      add_new_bb_insn (gen_ctx, new_insn, bb, TRUE);
      if (bitmap_bit_p (temp_bitmap, next_bb_insn->index)) VARR_PUSH (bb_t, worklist, bb);
      create_edge (gen_ctx, bb, ((bb_insn_t) next_insn->data)->bb, FALSE, TRUE);
    } else {
      label = get_insn_label (gen_ctx, DLIST_NEXT (MIR_insn_t, last_dst_insn)); /* fallthrough */
      new_insn = MIR_new_insn (ctx, MIR_JMP, MIR_new_label_op (ctx, label));
      MIR_insert_insn_after (ctx, curr_func_item, after, new_insn);
      new_bb = create_bb (gen_ctx, new_insn);
      insert_new_bb_after (gen_ctx, bb, new_bb);
      if (bitmap_bit_p (temp_bitmap, ((bb_insn_t) label->data)->bb->index))
        VARR_PUSH (bb_t, worklist, new_bb);
      create_edge (gen_ctx, bb, new_bb, TRUE, TRUE); /* fall through */
      create_edge (gen_ctx, bb, ((bb_insn_t) last_dst_insn->ops[0].u.label->data)->bb, FALSE,
                   TRUE); /* branch */
      create_edge (gen_ctx, new_bb, ((bb_insn_t) label->data)->bb, FALSE, TRUE);
    }
    DEBUG (2, {
      fprintf (debug_file, "  Result BB%lu:\n", (unsigned long) bb->index);
      output_in_edges (gen_ctx, bb);
      output_out_edges (gen_ctx, bb);
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
           bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
        fprintf (debug_file, "  %-5lu", (unsigned long) bb_insn->index);
        MIR_output_insn (ctx, debug_file, bb_insn->insn, func, TRUE);
      }
    });
  }
  if (res) enumerate_bbs (gen_ctx);
  return res;
}

/* New Page */

/* Building SSA.  First we build optimized maximal SSA, then we minimize it
   getting minimal SSA for reducible CFGs. There are two SSA representations:

   1. Def pointers only:

      phi|insn: out:v1, in, in
                       ^
                       |
      phi|insn: out, in:v1, ...

   2. Def-use chains (we don't use mir-lists to use less memory):

      phi|insn: out:v1, in, in
                    | (op.data)
                    V
                  ssa_edge (next_use)---------------> ssa_edge
                       ^                                ^
                       | (op.data)                      | (op.data)
      phi|insn: out, in:v1, ...        phi|insn: out, in:v1, ...

*/

typedef struct ssa_edge *ssa_edge_t;

struct ssa_edge {
  bb_insn_t use, def;
  char flag;
  uint16_t def_op_num;
  uint32_t use_op_num;
  ssa_edge_t prev_use, next_use; /* of the same def: we have only head in op.data */
};

typedef struct def_tab_el {
  bb_t bb;       /* table key */
  MIR_reg_t reg; /* another key */
  bb_insn_t def;
} def_tab_el_t;
DEF_HTAB (def_tab_el_t);

DEF_VARR (ssa_edge_t);
DEF_VARR (size_t);
DEF_VARR (char);

struct ssa_ctx {
  int def_use_repr_p; /* flag of def_use_chains */
  /* Different fake insns: defining undef, initial arg values. They are not in insn lists. */
  VARR (bb_insn_t) * arg_bb_insns, *undef_insns;
  VARR (bb_insn_t) * phis, *deleted_phis;
  HTAB (def_tab_el_t) * def_tab; /* reg,bb -> insn defining reg  */
  /* used for renaming: */
  VARR (ssa_edge_t) * ssa_edges_to_process;
  VARR (size_t) * curr_reg_indexes;
  VARR (char) * reg_name;
};

#define def_use_repr_p gen_ctx->ssa_ctx->def_use_repr_p
#define arg_bb_insns gen_ctx->ssa_ctx->arg_bb_insns
#define undef_insns gen_ctx->ssa_ctx->undef_insns
#define phis gen_ctx->ssa_ctx->phis
#define deleted_phis gen_ctx->ssa_ctx->deleted_phis
#define def_tab gen_ctx->ssa_ctx->def_tab
#define ssa_edges_to_process gen_ctx->ssa_ctx->ssa_edges_to_process
#define curr_reg_indexes gen_ctx->ssa_ctx->curr_reg_indexes
#define reg_name gen_ctx->ssa_ctx->reg_name

static htab_hash_t def_tab_el_hash (def_tab_el_t el, void *arg) {
  return mir_hash_finish (
    mir_hash_step (mir_hash_step (mir_hash_init (0x33), (uint64_t) el.bb), (uint64_t) el.reg));
}

static int def_tab_el_eq (def_tab_el_t el1, def_tab_el_t el2, void *arg) {
  return el1.reg == el2.reg && el1.bb == el2.bb;
}

static MIR_insn_code_t get_move_code (MIR_type_t type) {
  return (type == MIR_T_F    ? MIR_FMOV
          : type == MIR_T_D  ? MIR_DMOV
          : type == MIR_T_LD ? MIR_LDMOV
                             : MIR_MOV);
}

static bb_insn_t get_fake_insn (gen_ctx_t gen_ctx, VARR (bb_insn_t) * fake_insns, MIR_reg_t reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_type_t type;
  MIR_op_t op;
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); /* enter bb */

  gen_assert (bb->index == 0); /* enter bb */
  op = _MIR_new_var_op (ctx, reg);
  while (VARR_LENGTH (bb_insn_t, fake_insns) <= reg) VARR_PUSH (bb_insn_t, fake_insns, NULL);
  if ((bb_insn = VARR_GET (bb_insn_t, fake_insns, reg)) == NULL) {
    gen_assert (reg > MAX_HARD_REG);
    type = MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
    insn = MIR_new_insn (ctx, get_move_code (type), op, op);
    bb_insn = create_bb_insn (gen_ctx, insn, bb);
    VARR_SET (bb_insn_t, fake_insns, reg, bb_insn);
  }
  return bb_insn;
}

static int fake_insn_p (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  return bb_insn->bb->index == 0; /* enter bb */
  ;
}

static bb_insn_t redundant_phi_def (gen_ctx_t gen_ctx, bb_insn_t phi, int *def_op_num_ref) {
  bb_insn_t def, same = NULL;
  int op_num;

  *def_op_num_ref = 0;
  for (op_num = 1; op_num < phi->insn->nops; op_num++) { /* check input defs: */
    def = phi->insn->ops[op_num].data;
    if (def == same || def == phi) continue;
    if (same != NULL) return NULL;
    same = def;
  }
  gen_assert (phi->insn->ops[0].mode == MIR_OP_VAR);
  if (same == NULL) same = get_fake_insn (gen_ctx, undef_insns, phi->insn->ops[0].u.var);
  return same;
}

static bb_insn_t create_phi (gen_ctx_t gen_ctx, bb_t bb, MIR_op_t op) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t phi_insn;
  bb_insn_t bb_insn, phi;
  size_t len = DLIST_LENGTH (in_edge_t, bb->in_edges) + 1; /* output and inputs */

  VARR_TRUNC (MIR_op_t, temp_ops, 0);
  while (VARR_LENGTH (MIR_op_t, temp_ops) < len) VARR_PUSH (MIR_op_t, temp_ops, op);
  phi_insn = MIR_new_insn_arr (ctx, MIR_PHI, len, VARR_ADDR (MIR_op_t, temp_ops));
  bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
  if (bb_insn->insn->code == MIR_LABEL) {
    gen_add_insn_after (gen_ctx, bb_insn->insn, phi_insn);
  } else {
    gen_add_insn_before (gen_ctx, bb_insn->insn, phi_insn);
  }
  phi_insn->ops[0].data = phi = phi_insn->data;
  VARR_PUSH (bb_insn_t, phis, phi);
  return phi;
}

static MIR_insn_t get_last_bb_phi_insn (gen_ctx_t gen_ctx, MIR_insn_t phi_insn) {
  MIR_insn_t curr_insn, next_insn;
  bb_t bb = ((bb_insn_t) phi_insn->data)->bb;

  gen_assert (phi_insn->code == MIR_PHI);
  for (curr_insn = phi_insn;
       (next_insn = DLIST_NEXT (MIR_insn_t, curr_insn)) != NULL
       && ((bb_insn_t) next_insn->data)->bb == bb && next_insn->code == MIR_PHI;
       curr_insn = next_insn)
    ;
  return curr_insn;
}

static bb_insn_t get_def (gen_ctx_t gen_ctx, MIR_reg_t reg, bb_t bb) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t src;
  bb_insn_t def;
  def_tab_el_t el, tab_el;
  MIR_op_t op;

  el.bb = bb;
  el.reg = reg;
  if (HTAB_DO (def_tab_el_t, def_tab, el, HTAB_FIND, tab_el)) return tab_el.def;
  if (DLIST_LENGTH (in_edge_t, bb->in_edges) == 1) {
    if ((src = DLIST_HEAD (in_edge_t, bb->in_edges)->src)->index == 0) { /* start bb: args */
      return get_fake_insn (gen_ctx, arg_bb_insns, reg);
    }
    return get_def (gen_ctx, reg, DLIST_HEAD (in_edge_t, bb->in_edges)->src);
  }
  op = _MIR_new_var_op (ctx, reg);
  el.def = def = create_phi (gen_ctx, bb, op);
  HTAB_DO (def_tab_el_t, def_tab, el, HTAB_INSERT, tab_el);
  return el.def;
}

static void add_phi_operands (gen_ctx_t gen_ctx, MIR_reg_t reg, bb_insn_t phi) {
  size_t nop = 1;
  bb_insn_t def;
  edge_t in_edge;

  for (in_edge = DLIST_HEAD (in_edge_t, phi->bb->in_edges); in_edge != NULL;
       in_edge = DLIST_NEXT (in_edge_t, in_edge)) {
    def = get_def (gen_ctx, reg, in_edge->src);
    phi->insn->ops[nop++].data = def;
  }
}

static bb_insn_t skip_redundant_phis (bb_insn_t def) {
  while (def->insn->code == MIR_PHI && def != def->insn->ops[0].data) def = def->insn->ops[0].data;
  return def;
}

static void minimize_ssa (gen_ctx_t gen_ctx, size_t insns_num) {
  MIR_insn_t insn;
  bb_insn_t phi, def;
  size_t i, j, saved_bound;
  int op_num, change_p, out_p, mem_p;
  MIR_reg_t var;
  insn_var_iterator_t iter;

  VARR_TRUNC (bb_insn_t, deleted_phis, 0);
  do {
    change_p = FALSE;
    saved_bound = 0;
    for (i = 0; i < VARR_LENGTH (bb_insn_t, phis); i++) {
      phi = VARR_GET (bb_insn_t, phis, i);
      for (j = 1; j < phi->insn->nops; j++)
        phi->insn->ops[j].data = skip_redundant_phis (phi->insn->ops[j].data);
      if ((def = redundant_phi_def (gen_ctx, phi, &op_num)) == NULL) {
        VARR_SET (bb_insn_t, phis, saved_bound++, phi);
        continue;
      }
      phi->insn->ops[0].data = def;
      gen_assert (phi != def);
      VARR_PUSH (bb_insn_t, deleted_phis, phi);
      change_p = TRUE;
    }
    VARR_TRUNC (bb_insn_t, phis, saved_bound);
  } while (change_p);
  DEBUG (2, {
    fprintf (debug_file, "Minimizing SSA phis: from %ld to %ld phis (non-phi insns %ld)\n",
             (long) VARR_LENGTH (bb_insn_t, deleted_phis) + (long) VARR_LENGTH (bb_insn_t, phis),
             (long) VARR_LENGTH (bb_insn_t, phis), (long) insns_num);
  });
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
        if (out_p || insn->ops[op_num].data == NULL) continue;
        insn->ops[op_num].data = skip_redundant_phis (insn->ops[op_num].data);
      }
    }
  for (i = 0; i < VARR_LENGTH (bb_insn_t, deleted_phis); i++) {
    phi = VARR_GET (bb_insn_t, deleted_phis, i);
    gen_delete_insn (gen_ctx, phi->insn);
  }
  for (i = 0; i < VARR_LENGTH (bb_insn_t, phis); i++) {
    phi = VARR_GET (bb_insn_t, phis, i);
    phi->insn->ops[0].data = NULL;
  }
}

static void print_op_data (gen_ctx_t gen_ctx, void *op_data, bb_insn_t from) {
  ssa_edge_t se;

  if (op_data == NULL) {
    fprintf (debug_file, "_");
  } else if (!def_use_repr_p) {
    fprintf (debug_file, "%d", ((bb_insn_t) op_data)->index);
  } else if ((se = op_data)->def != from) {
    fprintf (debug_file, "%d", se->def->index);
  } else {
    for (; se != NULL; se = se->next_use)
      fprintf (debug_file, "%s%d", se == op_data ? "(" : ", ", se->use->index);
    fprintf (debug_file, ")");
  }
}

static void add_ssa_edge (gen_ctx_t gen_ctx, bb_insn_t def, int def_op_num, bb_insn_t use,
                          int use_op_num) {
  MIR_op_t *op_ref;
  ssa_edge_t ssa_edge = gen_malloc (gen_ctx, sizeof (struct ssa_edge));

  gen_assert (use_op_num >= 0 && def_op_num >= 0 && def_op_num < (1 << 16));
  ssa_edge->flag = FALSE;
  ssa_edge->def = def;
  ssa_edge->def_op_num = def_op_num;
  ssa_edge->use = use;
  ssa_edge->use_op_num = use_op_num;
  gen_assert (use->insn->ops[use_op_num].data == NULL);
  use->insn->ops[use_op_num].data = ssa_edge;
  op_ref = &def->insn->ops[def_op_num];
  ssa_edge->next_use = op_ref->data;
  if (ssa_edge->next_use != NULL) ssa_edge->next_use->prev_use = ssa_edge;
  ssa_edge->prev_use = NULL;
  op_ref->data = ssa_edge;
}

static void remove_ssa_edge (gen_ctx_t gen_ctx, ssa_edge_t ssa_edge) {
  if (ssa_edge->prev_use != NULL) {
    ssa_edge->prev_use->next_use = ssa_edge->next_use;
  } else {
    MIR_op_t *op_ref = &ssa_edge->def->insn->ops[ssa_edge->def_op_num];
    gen_assert (op_ref->data == ssa_edge);
    op_ref->data = ssa_edge->next_use;
  }
  if (ssa_edge->next_use != NULL) ssa_edge->next_use->prev_use = ssa_edge->prev_use;
  gen_assert (ssa_edge->use->insn->ops[ssa_edge->use_op_num].data == ssa_edge);
  ssa_edge->use->insn->ops[ssa_edge->use_op_num].data = NULL;
  free (ssa_edge);
}

static void remove_insn_ssa_edges (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  ssa_edge_t ssa_edge;
  for (size_t i = 0; i < insn->nops; i++) {
    /* output operand refers to chain of ssa edges -- remove them all: */
    while ((ssa_edge = insn->ops[i].data) != NULL) remove_ssa_edge (gen_ctx, ssa_edge);
  }
}

static void change_ssa_edge_list_def (ssa_edge_t list, bb_insn_t new_bb_insn,
                                      unsigned new_def_op_num, MIR_reg_t reg, MIR_reg_t new_reg) {
  gen_assert (new_reg > MAX_HARD_REG);
  for (ssa_edge_t se = list; se != NULL; se = se->next_use) {
    se->def = new_bb_insn;
    se->def_op_num = new_def_op_num;
    if (new_reg != MIR_NON_VAR) {
      MIR_op_t *op_ref = &se->use->insn->ops[se->use_op_num];
      if (op_ref->mode == MIR_OP_VAR) {
        op_ref->u.var = new_reg;
      } else {
        gen_assert (op_ref->mode == MIR_OP_VAR_MEM && op_ref->u.var_mem.base == reg);
        op_ref->u.var_mem.base = new_reg;
      }
    }
  }
}

static void redirect_def (gen_ctx_t gen_ctx, MIR_insn_t insn, MIR_insn_t by, int def_use_ssa_p) {
  int out_p, by_out_p;

  MIR_insn_op_mode (gen_ctx->ctx, insn, 0, &out_p);
  MIR_insn_op_mode (gen_ctx->ctx, by, 0, &by_out_p);
  gen_assert (insn->ops[0].mode == MIR_OP_VAR && by->ops[0].mode == MIR_OP_VAR
              && (def_use_ssa_p || insn->ops[0].u.var == by->ops[0].u.var)
              && !MIR_call_code_p (insn->code) && out_p && by_out_p);
  by->ops[0].data = insn->ops[0].data;
  insn->ops[0].data = NULL; /* make redundant insn having no uses */
  change_ssa_edge_list_def (by->ops[0].data, by->data, 0, insn->ops[0].u.var, by->ops[0].u.var);
  if (def_use_ssa_p) {
    gen_assert (move_p (by) && insn->ops[0].mode == MIR_OP_VAR && by->ops[1].mode == MIR_OP_VAR
                && insn->ops[0].u.var == by->ops[1].u.var);
    add_ssa_edge (gen_ctx, insn->data, 0, by->data, 1);
  }
}

static int get_var_def_op_num (gen_ctx_t gen_ctx, MIR_reg_t var, MIR_insn_t insn) {
  int op_num, out_p, mem_p;
  MIR_reg_t insn_var;
  insn_var_iterator_t iter;

  FOREACH_INSN_VAR (gen_ctx, iter, insn, insn_var, op_num, out_p, mem_p) {
    if (out_p && var == insn_var) return op_num;
  }
  gen_assert (FALSE);
  return -1;
}

static void process_insn_inputs_for_ssa_def_use_repr (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  MIR_insn_t insn = bb_insn->insn;
  bb_insn_t def;
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  insn_var_iterator_t iter;

  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
    if (out_p || var <= MAX_HARD_REG) continue;
    def = insn->ops[op_num].data;
    gen_assert (def != NULL);
    insn->ops[op_num].data = NULL;
    add_ssa_edge (gen_ctx, def, get_var_def_op_num (gen_ctx, var, def->insn), bb_insn, op_num);
  }
}

static void make_ssa_def_use_repr (gen_ctx_t gen_ctx) {
  bb_insn_t bb_insn;

  if (def_use_repr_p) return;
  def_use_repr_p = TRUE;
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      process_insn_inputs_for_ssa_def_use_repr (gen_ctx, bb_insn);
}

static void ssa_delete_insn (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  insn_var_iterator_t iter;

  gen_assert (def_use_repr_p);  // ??remove !def_use_repr as we dont use it at all
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
    if (insn->ops[op_num].data != NULL) remove_ssa_edge (gen_ctx, insn->ops[op_num].data);
  }
  gen_delete_insn (gen_ctx, insn);
}

static MIR_reg_t get_new_reg (gen_ctx_t gen_ctx, MIR_reg_t old_reg, int sep, size_t index) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func = curr_func_item->u.func;
  MIR_type_t type = MIR_reg_type (ctx, old_reg - MAX_HARD_REG, func);
  const char *name = MIR_reg_name (ctx, old_reg - MAX_HARD_REG, func);
  const char *hard_reg_name = MIR_reg_hard_reg_name (ctx, old_reg - MAX_HARD_REG, func);
  char ind_str[30];
  MIR_reg_t new_reg;

  VARR_TRUNC (char, reg_name, 0);
  VARR_PUSH_ARR (char, reg_name, name, strlen (name));
  VARR_PUSH (char, reg_name, sep);
  sprintf (ind_str, "%lu", (unsigned long) index); /* ??? should be enough to unique */
  VARR_PUSH_ARR (char, reg_name, ind_str, strlen (ind_str) + 1);
  if (hard_reg_name == NULL) {
    new_reg = _MIR_new_func_reg (ctx, func, type, VARR_ADDR (char, reg_name)) + MAX_HARD_REG;
  } else {
    new_reg = (_MIR_new_global_func_reg (ctx, func, type, VARR_ADDR (char, reg_name), hard_reg_name)
               + MAX_HARD_REG);
    bitmap_set_bit_p (tied_regs, new_reg);
  }
  update_max_var (gen_ctx, new_reg);
  return new_reg;
}

static int push_to_rename (gen_ctx_t gen_ctx, ssa_edge_t ssa_edge) {
  if (ssa_edge->flag) return FALSE;
  VARR_PUSH (ssa_edge_t, ssa_edges_to_process, ssa_edge);
  ssa_edge->flag = TRUE;
  DEBUG (2, {
    fprintf (debug_file, "     Adding ssa edge: def %lu:%d -> use %lu:%d:\n      ",
             (unsigned long) ssa_edge->def->index, ssa_edge->def_op_num,
             (unsigned long) ssa_edge->use->index, ssa_edge->use_op_num);
    print_bb_insn (gen_ctx, ssa_edge->def, FALSE);
    fprintf (debug_file, "     ");
    print_bb_insn (gen_ctx, ssa_edge->use, FALSE);
  });
  return TRUE;
}

static int pop_to_rename (gen_ctx_t gen_ctx, ssa_edge_t *ssa_edge) {
  if (VARR_LENGTH (ssa_edge_t, ssa_edges_to_process) == 0) return FALSE;
  *ssa_edge = VARR_POP (ssa_edge_t, ssa_edges_to_process);
  return TRUE;
}

static void process_insn_to_rename (gen_ctx_t gen_ctx, MIR_insn_t insn, int op_num) {
  for (ssa_edge_t curr_edge = insn->ops[op_num].data; curr_edge != NULL;
       curr_edge = curr_edge->next_use)
    push_to_rename (gen_ctx, curr_edge);
}

static MIR_reg_t get_new_ssa_reg (gen_ctx_t gen_ctx, MIR_reg_t reg, int sep, int new_p) {
  size_t reg_index;

  while (VARR_LENGTH (size_t, curr_reg_indexes) <= reg) VARR_PUSH (size_t, curr_reg_indexes, 0);
  reg_index = VARR_GET (size_t, curr_reg_indexes, reg);
  VARR_SET (size_t, curr_reg_indexes, reg, reg_index + 1);
  return reg_index == 0 && !new_p ? MIR_NON_VAR : get_new_reg (gen_ctx, reg, sep, reg_index);
}

static void rename_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  int op_num, out_p, mem_p;
  MIR_reg_t var, reg, new_reg;
  MIR_insn_t insn, def_insn, use_insn;
  ssa_edge_t ssa_edge;
  insn_var_iterator_t iter;

  insn = bb_insn->insn;
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
    if (!out_p || var <= MAX_HARD_REG) continue;
    ssa_edge = insn->ops[op_num].data;
    if (ssa_edge != NULL && ssa_edge->flag) continue; /* already processed */
    DEBUG (2, {
      fprintf (debug_file, "  Start def insn %-5lu", (long unsigned) bb_insn->index);
      print_bb_insn (gen_ctx, bb_insn, FALSE);
    });
    reg = var;
    new_reg = get_new_ssa_reg (gen_ctx, reg, '@', FALSE);
    if (ssa_edge == NULL) { /* special case: unused output */
      if (new_reg != MIR_NON_VAR)
        rename_op_reg (gen_ctx, &insn->ops[op_num], reg, new_reg, insn, TRUE);
      continue;
    }
    VARR_TRUNC (ssa_edge_t, ssa_edges_to_process, 0);
    process_insn_to_rename (gen_ctx, insn, op_num);
    if (new_reg != MIR_NON_VAR) {
      while (pop_to_rename (gen_ctx, &ssa_edge)) {
        def_insn = ssa_edge->def->insn;
        use_insn = ssa_edge->use->insn;
        rename_op_reg (gen_ctx, &def_insn->ops[ssa_edge->def_op_num], reg, new_reg, def_insn, TRUE);
        rename_op_reg (gen_ctx, &use_insn->ops[ssa_edge->use_op_num], reg, new_reg, use_insn, TRUE);
      }
    }
  }
}

static void rename_regs (gen_ctx_t gen_ctx) {
  bb_insn_t bb_insn;
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  MIR_insn_t insn;
  ssa_edge_t ssa_edge;
  insn_var_iterator_t iter;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) { /* clear all ssa edge flags */
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
        if (out_p || var <= MAX_HARD_REG || insn->code == MIR_ADDR) continue;
        ssa_edge = insn->ops[op_num].data;
        ssa_edge->flag = FALSE;
      }
    }
  /* Process arg insns first to have first use of reg in the program with zero index.
     We need this because machinize for args will use reg with zero index: */
  for (size_t i = 0; i < VARR_LENGTH (bb_insn_t, arg_bb_insns); i++)
    if ((bb_insn = VARR_GET (bb_insn_t, arg_bb_insns, i)) != NULL)
      rename_bb_insn (gen_ctx, bb_insn);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      rename_bb_insn (gen_ctx, bb_insn);
}

static void process_bb_insn_for_ssa (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  bb_t bb = bb_insn->bb;
  bb_insn_t def;
  int op_num, out_p, mem_p;
  MIR_reg_t var, reg;
  def_tab_el_t el;
  insn_var_iterator_t iter;

  FOREACH_INSN_VAR (gen_ctx, iter, bb_insn->insn, var, op_num, out_p, mem_p) {
    gen_assert (var > MAX_HARD_REG);
    if (out_p) continue;
    reg = var;
    def = get_def (gen_ctx, reg, bb);
    bb_insn->insn->ops[op_num].data = def;
  }
  FOREACH_INSN_VAR (gen_ctx, iter, bb_insn->insn, var, op_num, out_p, mem_p) {
    if (!out_p) continue;
    reg = var;
    el.bb = bb;
    el.reg = reg;
    el.def = bb_insn;
    HTAB_DO (def_tab_el_t, def_tab, el, HTAB_REPLACE, el);
  }
}

static void build_ssa (gen_ctx_t gen_ctx, int rename_p) {
  bb_t bb;
  bb_insn_t bb_insn, phi;
  size_t i, insns_num;

  gen_assert (VARR_LENGTH (bb_insn_t, arg_bb_insns) == 0
              && VARR_LENGTH (bb_insn_t, undef_insns) == 0);
  def_use_repr_p = FALSE;
  HTAB_CLEAR (def_tab_el_t, def_tab);
  VARR_TRUNC (bb_t, worklist, 0);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    VARR_PUSH (bb_t, worklist, bb);
  qsort (VARR_ADDR (bb_t, worklist), VARR_LENGTH (bb_t, worklist), sizeof (bb_t), rpost_cmp);
  VARR_TRUNC (bb_insn_t, phis, 0);
  insns_num = 0;
  for (i = 0; i < VARR_LENGTH (bb_t, worklist); i++) {
    bb = VARR_GET (bb_t, worklist, i);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      if (bb_insn->insn->code != MIR_PHI) {
        insns_num++;
        process_bb_insn_for_ssa (gen_ctx, bb_insn);
      }
  }
  for (i = 0; i < VARR_LENGTH (bb_insn_t, phis); i++) {
    phi = VARR_GET (bb_insn_t, phis, i);
    add_phi_operands (gen_ctx, phi->insn->ops[0].u.var, phi);
  }
  /* minimization can not be switched off for def_use representation
     building as it clears ops[0].data: */
  minimize_ssa (gen_ctx, insns_num);
  make_ssa_def_use_repr (gen_ctx);
  if (rename_p) {
    VARR_TRUNC (size_t, curr_reg_indexes, 0);
    rename_regs (gen_ctx);
  }
}

static void make_conventional_ssa (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_type_t type;
  MIR_reg_t reg, new_reg;
  MIR_insn_code_t move_code;
  MIR_insn_t insn, new_insn;
  bb_t bb, prev_bb;
  bb_insn_t bb_insn, next_bb_insn, tail, new_bb_insn, after;
  edge_t e;
  ssa_edge_t se;
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if ((insn = bb_insn->insn)->code == MIR_LABEL) continue;
      if (insn->code != MIR_PHI) break;
      gen_assert (insn->ops[0].mode == MIR_OP_VAR && insn->ops[0].u.var > MAX_HARD_REG);
      reg = insn->ops[0].u.var;
      type = MIR_reg_type (gen_ctx->ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
      move_code = get_move_code (type);
      new_reg = get_new_ssa_reg (gen_ctx, reg, '%', TRUE);
      gen_assert (new_reg != MIR_NON_VAR);
      new_insn
        = MIR_new_insn (ctx, move_code, _MIR_new_var_op (ctx, reg), _MIR_new_var_op (ctx, new_reg));
      gen_add_insn_after (gen_ctx, insn, new_insn);
      new_insn->ops[0].data = insn->ops[0].data;
      insn->ops[0] = new_insn->ops[1];
      change_ssa_edge_list_def (new_insn->ops[0].data, new_insn->data, 0, MIR_NON_VAR, MIR_NON_VAR);
      add_ssa_edge (gen_ctx, bb_insn, 0, new_insn->data, 1);
      e = DLIST_HEAD (in_edge_t, bb->in_edges);
      for (size_t i = 1; i < insn->nops; i++) {
        se = insn->ops[i].data;
        insn->ops[i].data = NULL;
        new_insn = MIR_new_insn (ctx, move_code, _MIR_new_var_op (ctx, new_reg), insn->ops[i]);
        if ((tail = DLIST_TAIL (bb_insn_t, e->src->bb_insns)) == NULL) {
          for (prev_bb = DLIST_PREV (bb_t, e->src), after = NULL;
               prev_bb != NULL && (after = DLIST_TAIL (bb_insn_t, prev_bb->bb_insns)) == NULL;
               prev_bb = DLIST_PREV (bb_t, prev_bb))
            ;
          if (after != NULL)
            MIR_insert_insn_after (ctx, curr_func_item, after->insn, new_insn);
          else
            MIR_prepend_insn (ctx, curr_func_item, new_insn);
          new_bb_insn = create_bb_insn (gen_ctx, new_insn, e->src);
          DLIST_APPEND (bb_insn_t, e->src->bb_insns, new_bb_insn);
        } else if (MIR_any_branch_code_p (tail->insn->code)) {
          gen_add_insn_before (gen_ctx, tail->insn, new_insn);
          for (size_t j = 0; j < tail->insn->nops; j++) {
            /* remove a conflict: we have new_reg = p; b ..p.. => new_reg = p; b .. new_reg .. */
            if (tail->insn->ops[j].mode != MIR_OP_VAR
                || tail->insn->ops[j].u.var != new_insn->ops[1].u.var)
              continue;
            tail->insn->ops[j].u.var = new_reg;
            remove_ssa_edge (gen_ctx, tail->insn->ops[j].data);
            add_ssa_edge (gen_ctx, new_insn->data, 0, tail, j);
          }
        } else {
          gen_add_insn_after (gen_ctx, tail->insn, new_insn);
        }
        new_insn->ops[1].data = se;
        se->use = new_insn->data;
        se->use_op_num = 1;
        add_ssa_edge (gen_ctx, new_insn->data, 0, bb_insn, i);
        insn->ops[i].mode = MIR_OP_VAR;
        insn->ops[i].u.var = new_reg;
        e = DLIST_NEXT (in_edge_t, e);
      }
    }
}

static void free_bb_insns (gen_ctx_t gen_ctx, VARR (bb_insn_t) * bb_insns) {
  bb_insn_t bb_insn;

  while (VARR_LENGTH (bb_insn_t, bb_insns) != 0)
    if ((bb_insn = VARR_POP (bb_insn_t, bb_insns)) != NULL) {  // ??? specialized free funcs
      free (bb_insn->insn);
      free (bb_insn);
    }
}

static void undo_build_ssa (gen_ctx_t gen_ctx) {
  bb_t bb;
  bb_insn_t bb_insn, next_bb_insn;
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  MIR_insn_t insn;
  insn_var_iterator_t iter;

  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
        if (insn->ops[op_num].data == NULL) continue;
        if (!def_use_repr_p)
          insn->ops[op_num].data = NULL;
        else
          remove_ssa_edge (gen_ctx, insn->ops[op_num].data);
      }
    }
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (bb_insn->insn->code == MIR_PHI) gen_delete_insn (gen_ctx, bb_insn->insn);
    }
  free_bb_insns (gen_ctx, arg_bb_insns);
  free_bb_insns (gen_ctx, undef_insns);
}

static void init_ssa (gen_ctx_t gen_ctx) {
  gen_ctx->ssa_ctx = gen_malloc (gen_ctx, sizeof (struct ssa_ctx));
  VARR_CREATE (bb_insn_t, arg_bb_insns, 0);
  VARR_CREATE (bb_insn_t, undef_insns, 0);
  VARR_CREATE (bb_insn_t, phis, 0);
  VARR_CREATE (bb_insn_t, deleted_phis, 0);
  HTAB_CREATE (def_tab_el_t, def_tab, 1024, def_tab_el_hash, def_tab_el_eq, gen_ctx);
  VARR_CREATE (ssa_edge_t, ssa_edges_to_process, 512);
  VARR_CREATE (size_t, curr_reg_indexes, 4096);
  VARR_CREATE (char, reg_name, 20);
}

static void finish_ssa (gen_ctx_t gen_ctx) {
  VARR_DESTROY (bb_insn_t, arg_bb_insns);
  VARR_DESTROY (bb_insn_t, undef_insns);
  VARR_DESTROY (bb_insn_t, phis);
  VARR_DESTROY (bb_insn_t, deleted_phis);
  HTAB_DESTROY (def_tab_el_t, def_tab);
  VARR_DESTROY (ssa_edge_t, ssa_edges_to_process);
  VARR_DESTROY (size_t, curr_reg_indexes);
  VARR_DESTROY (char, reg_name);
  free (gen_ctx->ssa_ctx);
  gen_ctx->ssa_ctx = NULL;
}

/* New Page */

/* If we have addr insns we transforming addressable pseudos to memory if the addr insn can not be
   elimnated and memory of addressable pseudos to pseudos otherwise.  */

/* Add all copies which are uses of bb_insn to temp_bb_insns2.  Return TRUE if all bb_insn uses
   (skipping moves) are memory address.  Collect insns which bb_insn uses are memory in
   bb_mem_insns. */
static int collect_addr_uses (gen_ctx_t gen_ctx, bb_insn_t bb_insn,
                              VARR (bb_insn_t) * bb_mem_insns) {
  int res = TRUE;

  gen_assert (bb_insn->insn->code == MIR_ADDR || move_p (bb_insn->insn));
  for (ssa_edge_t se = bb_insn->insn->ops[0].data; se != NULL; se = se->next_use) {
    if (se->use->insn->ops[se->use_op_num].mode == MIR_OP_VAR_MEM) {
      gen_assert (move_code_p (se->use->insn->code) && se->use_op_num <= 1);
      if (bb_mem_insns != NULL) VARR_PUSH (bb_insn_t, bb_mem_insns, se->use);
      continue;
    }
    if (!move_p (se->use->insn)) {
      res = FALSE;
    } else if (bitmap_set_bit_p (temp_bitmap2, se->use->index)) {
      VARR_PUSH (bb_insn_t, temp_bb_insns2, se->use);
    }
  }
  return res;
}

/* Return TRUE if all addr insn (bb_insn) uses (skipping moves) are memory address.
   Collect insns which addr uses are memory in bb_mem_insns. */
static int addr_eliminable_p (gen_ctx_t gen_ctx, bb_insn_t bb_insn,
                              VARR (bb_insn_t) * bb_mem_insns) {
  int res = TRUE;

  bitmap_clear (temp_bitmap2);
  VARR_TRUNC (bb_insn_t, temp_bb_insns2, 0);
  if (bb_mem_insns != NULL) VARR_TRUNC (bb_insn_t, bb_mem_insns, 0);
  if (!collect_addr_uses (gen_ctx, bb_insn, bb_mem_insns)) res = FALSE;
  while (VARR_LENGTH (bb_insn_t, temp_bb_insns2) != 0) {
    bb_insn_t bb_insn = VARR_POP (bb_insn_t, temp_bb_insns2);
    if (!collect_addr_uses (gen_ctx, bb_insn, bb_mem_insns)) res = FALSE;
  }
  return res;
}

// aliasing, loc ???
static void transform_addrs (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  int op_num, out_p, mem_p, ssa_rebuild_p = FALSE;
  MIR_type_t type;
  MIR_insn_code_t move_code;
  MIR_reg_t var, reg, addr_reg, new_reg;
  MIR_insn_t insn, addr_insn, new_insn;
  bb_insn_t bb_insn, next_bb_insn;
  insn_var_iterator_t iter;
  ssa_edge_t se;
  MIR_func_t func = curr_func_item->u.func;

  gen_assert (addr_insn_p);
  bitmap_clear (addr_regs);
  VARR_TRUNC (bb_insn_t, temp_bb_insns, 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      if (bb_insn->insn->code == MIR_ADDR) {
        VARR_PUSH (bb_insn_t, temp_bb_insns, bb_insn);
      } else if (move_p (bb_insn->insn)) {
        gen_assert (bb_insn->insn->ops[1].data != NULL);
      }
  if (VARR_LENGTH (bb_insn_t, temp_bb_insns) == 0)
    return; /* all addr insns can be unreachable and removed */
  for (size_t i = 0; i < VARR_LENGTH (bb_insn_t, temp_bb_insns); i++) {
    bb_insn = VARR_GET (bb_insn_t, temp_bb_insns, i);
    insn = bb_insn->insn;
    gen_assert (insn->code == MIR_ADDR && insn->ops[0].mode == MIR_OP_VAR
                && insn->ops[1].mode == MIR_OP_VAR);
    if (!addr_eliminable_p (gen_ctx, bb_insn, NULL))
      bitmap_set_bit_p (addr_regs, insn->ops[1].u.var);
  }
  addr_insn = NULL;       /* to remove warning */
  addr_reg = MIR_NON_VAR; /* to remove warning */
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      insn = bb_insn->insn;
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (insn->code == MIR_PHI) {
        /* we keep conventional SSA -- do nothing when we keep pseudo */
        if (!bitmap_bit_p (addr_regs, insn->ops[0].u.var)) continue;
        DEBUG (2, {
          fprintf (debug_file, "  deleting phi for pseudo transformed into memory ");
          print_bb_insn (gen_ctx, insn->data, TRUE);
        });
        remove_insn_ssa_edges (gen_ctx, insn);
        gen_delete_insn (gen_ctx, insn);
      } else if (insn->code == MIR_USE) {
        int change_p = FALSE;
        /* we keep conventional SSA -- do nothing */
        for (size_t i = 0; i < insn->nops; i++) {
          gen_assert (insn->ops[i].mode == MIR_OP_VAR);
          if (!bitmap_bit_p (addr_regs, insn->ops[i].u.var)) continue;
          remove_ssa_edge (gen_ctx, insn->ops[i].data);
          for (size_t j = i; j + 1 < insn->nops; j++) insn->ops[j] = insn->ops[j + 1];
          change_p = TRUE;
          i--;
          insn->nops--;
        }
        if (change_p) {
          DEBUG (2, {
            fprintf (debug_file, "  modifying use to ");
            print_bb_insn (gen_ctx, insn->data, TRUE);
          });
        }
      } else if (insn->code != MIR_ADDR) { /* change reg to memory */
        MIR_reg_t prev_reg = 0;
        FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
          gen_assert (var > MAX_HARD_REG);
          reg = var;
          if (!bitmap_bit_p (addr_regs, reg)) continue;
          DEBUG (2, {
            fprintf (debug_file, "  ");
            print_bb_insn (gen_ctx, bb_insn, TRUE);
          });
          if (reg != prev_reg) {
            addr_reg = gen_new_temp_reg (gen_ctx, MIR_T_I64, func);
            addr_insn = MIR_new_insn (ctx, MIR_ADDR, _MIR_new_var_op (ctx, addr_reg),
                                      _MIR_new_var_op (ctx, reg));
            gen_add_insn_before (gen_ctx, insn, addr_insn);
            prev_reg = reg;
            DEBUG (2, {
              fprintf (debug_file, "    adding before: ");
              print_bb_insn (gen_ctx, addr_insn->data, TRUE);
            });
          }
          type = MIR_reg_type (ctx, reg - MAX_HARD_REG, func);
          move_code = get_move_code (type);
          new_reg = gen_new_temp_reg (gen_ctx, type, func);
          if (out_p) { /* p = ... => addr t2, p (no edge for p); t = ...; mem[t2] = t */
            new_insn = MIR_new_insn (ctx, move_code,
                                     _MIR_new_var_mem_op (ctx, type, 0, addr_reg, MIR_NON_VAR, 0),
                                     _MIR_new_var_op (ctx, new_reg));
            gen_add_insn_after (gen_ctx, insn, new_insn);
            gen_assert (insn->ops[op_num].mode == MIR_OP_VAR);
            insn->ops[op_num].u.var = new_reg;
            while ((se = insn->ops[op_num].data) != NULL) remove_ssa_edge (gen_ctx, se);
            if (!ssa_rebuild_p) {
              add_ssa_edge (gen_ctx, addr_insn->data, 0, new_insn->data, 0);
              add_ssa_edge (gen_ctx, bb_insn, op_num, new_insn->data, 1);
            }
          } else { /* ... = p => addr t2, p (no edge for p); t = mem[t2]; ... = t */
            new_insn = MIR_new_insn (ctx, move_code, _MIR_new_var_op (ctx, new_reg),
                                     _MIR_new_var_mem_op (ctx, type, 0, addr_reg, MIR_NON_VAR, 0));
            gen_add_insn_before (gen_ctx, insn, new_insn);
            if (insn->ops[op_num].mode == MIR_OP_VAR) {
              insn->ops[op_num].u.var = new_reg;
            } else {
              gen_assert (insn->ops[op_num].mode == MIR_OP_VAR_MEM
                          && insn->ops[op_num].u.var_mem.base == reg);
              insn->ops[op_num].u.var_mem.base = new_reg;
            }
            if (insn->ops[op_num].data != NULL) remove_ssa_edge (gen_ctx, insn->ops[op_num].data);
            if (!ssa_rebuild_p) {
              add_ssa_edge (gen_ctx, addr_insn->data, 0, new_insn->data, 1);
              add_ssa_edge (gen_ctx, new_insn->data, 0, bb_insn, op_num);
            }
          }
          DEBUG (2, {
            fprintf (debug_file, "    adding %s: ", out_p ? "after" : "before");
            print_bb_insn (gen_ctx, new_insn->data, TRUE);
            fprintf (debug_file, "    changing to ");
            print_bb_insn (gen_ctx, bb_insn, TRUE);
          });
        }
      } else if (!bitmap_bit_p (addr_regs, insn->ops[1].u.var)) {
        /* addr a, p: change reg mem to reg */
        MIR_UNUSED int res = addr_eliminable_p (gen_ctx, bb_insn, temp_bb_insns);
        se = insn->ops[1].data;
        gen_assert (res);
        while (VARR_LENGTH (bb_insn_t, temp_bb_insns) != 0) {
          /* ... = m[a] => ... = p; m[a] = ... => p = ... */
          bb_insn_t use_bb_insn = VARR_POP (bb_insn_t, temp_bb_insns);
          MIR_insn_t use_insn = use_bb_insn->insn;
          gen_assert (move_code_p (use_insn->code));
          op_num = use_insn->ops[0].mode == MIR_OP_VAR_MEM ? 0 : 1;
          ssa_rebuild_p = TRUE;
          switch (use_insn->ops[op_num].u.var_mem.type) {
          case MIR_T_I8: use_insn->code = MIR_EXT8; break;
          case MIR_T_U8: use_insn->code = MIR_UEXT8; break;
          case MIR_T_I16: use_insn->code = MIR_EXT16; break;
          case MIR_T_U16: use_insn->code = MIR_UEXT16; break;
          case MIR_T_I32: use_insn->code = MIR_EXT32; break;
          case MIR_T_U32: use_insn->code = MIR_UEXT32; break;
          default: break;
          }
          if (use_insn->ops[op_num].data != NULL)
            remove_ssa_edge (gen_ctx, use_insn->ops[op_num].data);
          use_insn->ops[op_num].mode = MIR_OP_VAR;
          use_insn->ops[op_num].u.var = insn->ops[1].u.var;
          if (!ssa_rebuild_p) add_ssa_edge (gen_ctx, se->def, se->def_op_num, use_bb_insn, op_num);
        }
        DEBUG (2, {
          fprintf (debug_file, "  deleting ");
          print_bb_insn (gen_ctx, insn->data, TRUE);
        });
        remove_insn_ssa_edges (gen_ctx, insn);
        gen_delete_insn (gen_ctx, insn);
      }
    }
}

/* New Page */

/* Copy propagation */

static int64_t int_log2 (int64_t i) {
  int64_t n;

  if (i <= 0) return -1;
  for (n = 0; (i & 1) == 0; n++, i >>= 1)
    ;
  return i == 1 ? n : -1;
}

static int power2_int_op (ssa_edge_t se, MIR_op_t **op_ref) {
  MIR_op_t *op;

  *op_ref = NULL;
  if (se->def->insn->code != MIR_MOV) return -1;
  *op_ref = op = &se->def->insn->ops[1];
  if (op->mode != MIR_OP_INT && op->mode != MIR_OP_UINT) return -1;
  return int_log2 (op->u.i);
}

static MIR_insn_t transform_mul_div (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t new_insns[7];
  MIR_op_t temp[6], *op_ref;
  MIR_func_t func = curr_func_item->u.func;
  MIR_insn_code_t new_code;
  int sh;
  ssa_edge_t se;
  int n;

  switch (insn->code) {
  case MIR_MUL: new_code = MIR_LSH; break;
  case MIR_MULS: new_code = MIR_LSHS; break;
  case MIR_UDIV: new_code = MIR_URSH; break;
  case MIR_UDIVS: new_code = MIR_URSHS; break;
  case MIR_DIV: new_code = MIR_RSH; break;
  case MIR_DIVS: new_code = MIR_RSHS; break;
  default: return insn;
  }
  sh = power2_int_op (insn->ops[2].data, &op_ref);
  if (sh < 0 && (insn->code == MIR_MUL || insn->code == MIR_MULS)
      && (sh = power2_int_op (insn->ops[1].data, &op_ref)) >= 0) {
    temp[0] = insn->ops[1];
    insn->ops[1] = insn->ops[2];
    insn->ops[2] = temp[0];
    ((ssa_edge_t) insn->ops[1].data)->use_op_num = 1;
    ((ssa_edge_t) insn->ops[2].data)->use_op_num = 2;
  }
  if (sh < 0) return insn;
  if (sh == 0) {
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], insn->ops[1]);
    new_insns[0]->ops[1].data = NULL;
    gen_add_insn_before (gen_ctx, insn, new_insns[0]);
    redirect_def (gen_ctx, insn, new_insns[0], FALSE);
    se = insn->ops[1].data;
    add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_insns[0]->data, 1);
    n = 1;
  } else if (insn->code != MIR_DIV && insn->code != MIR_DIVS) {
    temp[0] = _MIR_new_var_op (ctx, gen_new_temp_reg (gen_ctx, MIR_T_I64, func));
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, temp[0], MIR_new_int_op (ctx, sh));
    gen_add_insn_before (gen_ctx, insn, new_insns[0]);
    new_insns[1] = MIR_new_insn (ctx, new_code, insn->ops[0], insn->ops[1], temp[0]);
    new_insns[1]->ops[1].data = NULL;
    gen_add_insn_before (gen_ctx, insn, new_insns[1]);
    redirect_def (gen_ctx, insn, new_insns[1], FALSE);
    se = insn->ops[1].data;
    add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_insns[1]->data, 1);
    add_ssa_edge (gen_ctx, new_insns[0]->data, 0, new_insns[1]->data, 2);
    n = 2;
  } else {
    for (int i = 0; i < 6; i++)
      temp[i] = _MIR_new_var_op (ctx, gen_new_temp_reg (gen_ctx, MIR_T_I64, func));
    if (insn->code == MIR_DIV) {
      new_insns[0] = MIR_new_insn (ctx, MIR_MOV, temp[0], MIR_new_int_op (ctx, 63));
      new_insns[1] = MIR_new_insn (ctx, MIR_RSH, temp[1], insn->ops[1], temp[0]);
      new_insns[2] = MIR_new_insn (ctx, MIR_MOV, temp[2], MIR_new_int_op (ctx, op_ref->u.i - 1));
      new_insns[3] = MIR_new_insn (ctx, MIR_AND, temp[3], temp[1], temp[2]);
      new_insns[4] = MIR_new_insn (ctx, MIR_ADD, temp[4], temp[3], insn->ops[1]);
    } else {
      new_insns[0] = MIR_new_insn (ctx, MIR_MOV, temp[0], MIR_new_int_op (ctx, 31));
      new_insns[1] = MIR_new_insn (ctx, MIR_RSHS, temp[1], insn->ops[1], temp[0]);
      new_insns[2] = MIR_new_insn (ctx, MIR_MOV, temp[2], MIR_new_int_op (ctx, op_ref->u.i - 1));
      new_insns[3] = MIR_new_insn (ctx, MIR_ANDS, temp[3], temp[1], temp[2]);
      new_insns[4] = MIR_new_insn (ctx, MIR_ADDS, temp[4], temp[3], insn->ops[1]);
    }
    new_insns[1]->ops[1].data = NULL;
    new_insns[4]->ops[2].data = NULL;
    new_insns[5] = MIR_new_insn (ctx, MIR_MOV, temp[5], MIR_new_int_op (ctx, sh));
    new_insns[6] = MIR_new_insn (ctx, new_code, insn->ops[0], temp[4], temp[5]);
    for (int i = 0; i < 7; i++) gen_add_insn_before (gen_ctx, insn, new_insns[i]);
    add_ssa_edge (gen_ctx, new_insns[0]->data, 0, new_insns[1]->data, 2);
    add_ssa_edge (gen_ctx, new_insns[1]->data, 0, new_insns[3]->data, 1);
    add_ssa_edge (gen_ctx, new_insns[2]->data, 0, new_insns[3]->data, 2);
    add_ssa_edge (gen_ctx, new_insns[3]->data, 0, new_insns[4]->data, 1);
    add_ssa_edge (gen_ctx, new_insns[4]->data, 0, new_insns[6]->data, 1);
    add_ssa_edge (gen_ctx, new_insns[5]->data, 0, new_insns[6]->data, 2);
    se = insn->ops[1].data;
    add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_insns[1]->data, 1);
    add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_insns[4]->data, 2);
    redirect_def (gen_ctx, insn, new_insns[6], FALSE);
    n = 7;
  }
  DEBUG (2, {
    for (int i = 0; i < n; i++) {
      fprintf (debug_file, i == 0 ? "      adding " : "        and ");
      print_bb_insn (gen_ctx, new_insns[i]->data, TRUE);
    }
    fprintf (debug_file, "        and deleting ");
    print_bb_insn (gen_ctx, insn->data, TRUE);
  });
  remove_insn_ssa_edges (gen_ctx, insn);
  gen_delete_insn (gen_ctx, insn);
  return new_insns[n - 1];
}

static int get_ext_params (MIR_insn_code_t code, int *sign_p) {
  *sign_p = code == MIR_EXT8 || code == MIR_EXT16 || code == MIR_EXT32;
  switch (code) {
  case MIR_EXT8:
  case MIR_UEXT8: return 8;
  case MIR_EXT16:
  case MIR_UEXT16: return 16;
  case MIR_EXT32:
  case MIR_UEXT32: return 32;
  default: return 0;
  }
}

static int cmp_res64_p (MIR_insn_code_t cmp_code) {
  switch (cmp_code) {
#define REP_SEP :
#define CASE_EL(e) case MIR_##e
    REP4 (CASE_EL, EQ, FEQ, DEQ, LDEQ)
      : REP4 (CASE_EL, NE, FNE, DNE, LDNE)
      : REP5 (CASE_EL, LT, ULT, FLT, DLT, LDLT)
      : REP5 (CASE_EL, LE, ULE, FLE, DLE, LDLE)
      : REP5 (CASE_EL, GT, UGT, FGT, DGT, LDGT)
      : REP5 (CASE_EL, GE, UGE, FGE, DGE, LDGE) : return TRUE;
#undef REP_SEP
  default: return FALSE;
  }
}

static void copy_prop (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func = curr_func_item->u.func;
  MIR_insn_t insn, def_insn, new_insn, mov_insn;
  MIR_op_t temp_op;
  bb_insn_t bb_insn, next_bb_insn, def;
  ssa_edge_t se, se2;
  int op_num, out_p, mem_p, w, w2, sign_p, sign2_p;
  MIR_reg_t var, reg, new_reg, src_reg;
  insn_var_iterator_t iter;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      if (insn->code == MIR_ADDR) {
        continue; /* no input reg propagation */
      }
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
        if (out_p || var <= MAX_HARD_REG) continue;
        reg = var;
        for (int n = 0; n < 30; n++) { /* unreachable code can create loops in copies */
          se = insn->ops[op_num].data;
          def = se->def;
          if (def->bb->index == 0) break; /* arg init or undef insn */
          def_insn = def->insn;
          if (!move_p (def_insn) || def_insn->ops[0].u.var == def_insn->ops[1].u.var) break;
          src_reg = def_insn->ops[1].u.var;
          gen_assert (src_reg > MAX_HARD_REG);
          if (MIR_reg_hard_reg_name (ctx, def_insn->ops[0].u.var - MAX_HARD_REG, func)
              != MIR_reg_hard_reg_name (ctx, src_reg - MAX_HARD_REG, func))
            break;
          DEBUG (2, {
            fprintf (debug_file, "  Propagate from copy insn ");
            print_bb_insn (gen_ctx, def, FALSE);
          });
          new_reg = def_insn->ops[1].u.var;
          gen_assert (reg > MAX_HARD_REG && new_reg > MAX_HARD_REG);
          remove_ssa_edge (gen_ctx, se);
          se = def_insn->ops[1].data;
          add_ssa_edge (gen_ctx, se->def, se->def_op_num, bb_insn, op_num);
          rename_op_reg (gen_ctx, &insn->ops[op_num], reg, new_reg, insn, TRUE);
          reg = new_reg;
        }
      }
      if (move_p (insn) && insn->ops[0].data != NULL && (se = insn->ops[1].data) != NULL
          && se->def == DLIST_PREV (bb_insn_t, bb_insn)
          && (se = se->def->insn->ops[se->def_op_num].data) != NULL && se->next_use != NULL
          && se->next_use->next_use == NULL
          && (se->use == DLIST_NEXT (bb_insn_t, bb_insn)
              || se->next_use->use == DLIST_NEXT (bb_insn_t, bb_insn))) {
        /* a = ...; non-dead insn: b = a; ... = a & only two uses of a =>  b = ...; ... = b */
        MIR_op_t *def_op_ref = &se->def->insn->ops[se->def_op_num];
        remove_ssa_edge (gen_ctx, insn->ops[1].data);
        se = def_op_ref->data;
        gen_assert (se != NULL && se->next_use == NULL
                    && se->use == DLIST_NEXT (bb_insn_t, bb_insn));
        def_op_ref->u.var = insn->ops[0].u.var;
        MIR_op_t *use_op_ref = &se->use->insn->ops[se->use_op_num];
        gen_assert (use_op_ref->mode == MIR_OP_VAR || use_op_ref->mode == MIR_OP_VAR_MEM);
        if (use_op_ref->mode == MIR_OP_VAR)
          use_op_ref->u.var = def_op_ref->u.var;
        else
          use_op_ref->u.var_mem.base = def_op_ref->u.var;
        change_ssa_edge_list_def (insn->ops[0].data, se->def, se->def_op_num, MIR_NON_VAR,
                                  MIR_NON_VAR);
        se->next_use = insn->ops[0].data;
        se->next_use->prev_use = se;
        insn->ops[0].data = insn->ops[1].data = NULL;
        DEBUG (2, {
          fprintf (debug_file, "    Remove move %-5lu", (unsigned long) bb_insn->index);
          print_bb_insn (gen_ctx, bb_insn, FALSE);
        });
        gen_delete_insn (gen_ctx, insn);
        continue;
      }
      insn = transform_mul_div (gen_ctx, insn);
      bb_insn = insn->data;
      w = get_ext_params (insn->code, &sign_p);
      if (w == 0 || insn->ops[1].mode != MIR_OP_VAR) continue;
      se = insn->ops[1].data;
      def_insn = se->def->insn;
      if (cmp_res64_p (def_insn->code)) {
        DEBUG (2, {
          fprintf (debug_file, "    Change code of insn %lu ", (unsigned long) bb_insn->index);
          MIR_output_insn (ctx, debug_file, insn, func, FALSE);
          fprintf (debug_file, "    to move\n");
        });
        insn->code = MIR_MOV;
        next_bb_insn = bb_insn; /* process the new move */
        continue;
      }
      w2 = get_ext_params (def_insn->code, &sign2_p);
      if (w2 != 0 && sign_p == sign2_p && w2 <= w) { /* ext a,...; ext b,... */
        DEBUG (2, {
          fprintf (debug_file, "    Change code of insn %lu: before",
                   (unsigned long) bb_insn->index);
          MIR_output_insn (ctx, debug_file, insn, func, FALSE);
        });
        insn->code = MIR_MOV;
        DEBUG (2, {
          fprintf (debug_file, "    after ");
          print_bb_insn (gen_ctx, bb_insn, FALSE);
        });
        next_bb_insn = bb_insn; /* process the new move */
        continue;
      }
      if (!sign_p && (def_insn->code == MIR_AND || def_insn->code == MIR_ANDS)) {
        if ((se2 = def_insn->ops[1].data) != NULL && (mov_insn = se2->def->insn)->code == MIR_MOV
            && (mov_insn->ops[1].mode == MIR_OP_INT || mov_insn->ops[1].mode == MIR_OP_UINT))
          SWAP (def_insn->ops[1], def_insn->ops[2], temp_op);
        if ((se2 = def_insn->ops[2].data) == NULL || (mov_insn = se2->def->insn)->code != MIR_MOV
            || (mov_insn->ops[1].mode != MIR_OP_INT && mov_insn->ops[1].mode != MIR_OP_UINT))
          continue;
        uint64_t c1 = mov_insn->ops[1].u.u;
        uint64_t c2 = w == 8 ? 0xff : w == 16 ? 0xffff : 0xffffffff;
        /* and r1,r2,c1; ... uext r, r1 => and r1,r2,c1; ... mov t, c1 & c2; and r, r2, t */
        DEBUG (2, {
          fprintf (debug_file, "    Change code of insn %lu ", (unsigned long) bb_insn->index);
          MIR_output_insn (ctx, debug_file, insn, func, FALSE);
        });
        new_reg = gen_new_temp_reg (gen_ctx, MIR_T_I64, func);
        mov_insn = MIR_new_insn (ctx, MIR_MOV, _MIR_new_var_op (ctx, new_reg),
                                 MIR_new_int_op (ctx, c1 & c2));
        gen_add_insn_before (gen_ctx, insn, mov_insn);
        new_insn = MIR_new_insn (ctx, MIR_AND, insn->ops[0], /* include ssa def list */
                                 _MIR_new_var_op (ctx, def_insn->ops[1].u.var),
                                 _MIR_new_var_op (ctx, new_reg));
        gen_add_insn_before (gen_ctx, insn, new_insn);
        remove_ssa_edge (gen_ctx, se);                                /* r1 */
        add_ssa_edge (gen_ctx, mov_insn->data, 0, new_insn->data, 2); /* t */
        se = def_insn->ops[1].data;
        add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_insn->data, 1); /* r2 */
        insn->ops[0].data = NULL;
        change_ssa_edge_list_def (new_insn->ops[0].data, new_insn->data, 0, MIR_NON_VAR,
                                  MIR_NON_VAR); /* r */
        remove_insn_ssa_edges (gen_ctx, insn);
        gen_delete_insn (gen_ctx, insn);
        DEBUG (2, {
          fprintf (debug_file, " on ");
          MIR_output_insn (ctx, debug_file, mov_insn, func, FALSE);
          fprintf (debug_file, " and ");
          MIR_output_insn (ctx, debug_file, new_insn, func, TRUE);
        });
      }
    }
  }
}

/* New Page */

/* Removing redundant insns through GVN.  */

typedef struct expr {
  MIR_insn_t insn;
  uint32_t num;       /* the expression number (0, 1 ...) */
  MIR_reg_t temp_reg; /* 0 initially and reg used to remove redundant expr */
} *expr_t;

DEF_VARR (expr_t);
DEF_HTAB (expr_t);

typedef struct mem_expr {
  MIR_insn_t insn;    /* load or store */
  uint32_t mem_num;   /* the memory expression number (0, 1 ...) */
  MIR_reg_t temp_reg; /* 0 initially and reg used to remove redundant load/store */
  struct mem_expr *next;
} *mem_expr_t;

DEF_VARR (mem_expr_t);
DEF_HTAB (mem_expr_t);

struct insn_nop_pair {
  bb_insn_t bb_insn;
  size_t nop;
};
typedef struct insn_nop_pair insn_nop_pair_t;

DEF_VARR (insn_nop_pair_t);

struct gvn_ctx {
  MIR_insn_t temp_mem_insn;
  VARR (expr_t) * exprs; /* the expr number -> expression */
  VARR (mem_expr_t) * mem_exprs;
  HTAB (expr_t) * expr_tab; /* keys: insn code and input operands */
  /* keys: gvn val of memory address -> list of mem exprs: last added is the first */
  HTAB (mem_expr_t) * mem_expr_tab;
  VARR (insn_nop_pair_t) * insn_nop_pairs;
};

#define temp_mem_insn gen_ctx->gvn_ctx->temp_mem_insn
#define exprs gen_ctx->gvn_ctx->exprs
#define mem_exprs gen_ctx->gvn_ctx->mem_exprs
#define expr_tab gen_ctx->gvn_ctx->expr_tab
#define mem_expr_tab gen_ctx->gvn_ctx->mem_expr_tab
#define insn_nop_pairs gen_ctx->gvn_ctx->insn_nop_pairs

static void dom_con_func_0 (bb_t bb) { bitmap_clear (bb->dom_in); }

static int dom_con_func_n (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e, head;
  bitmap_t prev_dom_in = temp_bitmap;

  bitmap_copy (prev_dom_in, bb->dom_in);
  head = DLIST_HEAD (in_edge_t, bb->in_edges);
  bitmap_copy (bb->dom_in, head->src->dom_out);
  for (e = DLIST_NEXT (in_edge_t, head); e != NULL; e = DLIST_NEXT (in_edge_t, e))
    bitmap_and (bb->dom_in, bb->dom_in, e->src->dom_out); /* dom_in &= dom_out */
  return !bitmap_equal_p (bb->dom_in, prev_dom_in);
}

static int dom_trans_func (gen_ctx_t gen_ctx, bb_t bb) {
  bitmap_clear (temp_bitmap);
  bitmap_set_bit_p (temp_bitmap, bb->index);
  return bitmap_ior (bb->dom_out, bb->dom_in, temp_bitmap);
}

static void calculate_dominators (gen_ctx_t gen_ctx) {
  bb_t entry_bb = DLIST_HEAD (bb_t, curr_cfg->bbs);

  bitmap_clear (entry_bb->dom_out);
  for (bb_t bb = DLIST_NEXT (bb_t, entry_bb); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    bitmap_set_bit_range_p (bb->dom_out, 0, curr_bb_index);
  solve_dataflow (gen_ctx, TRUE, dom_con_func_0, dom_con_func_n, dom_trans_func);
}

#define mem_av_in in
#define mem_av_out out

static int may_alias_p (MIR_alias_t alias1, MIR_alias_t alias2, MIR_alias_t nonalias1,
                        MIR_alias_t nonalias2) {
  return (alias1 == 0 || alias2 == 0 || alias1 == alias2)
         && (nonalias1 == 0 || nonalias2 == 0 || nonalias1 != nonalias2);
}

static int may_mem_alias_p (const MIR_op_t *mem1, const MIR_op_t *mem2) {
  gen_assert (mem1->mode == MIR_OP_VAR_MEM && mem2->mode == MIR_OP_VAR_MEM);
  return may_alias_p (mem1->u.var_mem.alias, mem2->u.var_mem.alias, mem1->u.var_mem.nonalias,
                      mem2->u.var_mem.nonalias);
}

static void mem_av_con_func_0 (bb_t bb) { bitmap_clear (bb->mem_av_in); }

static int mem_av_con_func_n (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e, head;
  bitmap_t prev_mem_av_in = temp_bitmap;

  bitmap_copy (prev_mem_av_in, bb->mem_av_in);
  head = DLIST_HEAD (in_edge_t, bb->in_edges);
  bitmap_copy (bb->mem_av_in, head->src->mem_av_out);
  for (e = DLIST_NEXT (in_edge_t, head); e != NULL; e = DLIST_NEXT (in_edge_t, e))
    bitmap_and (bb->mem_av_in, bb->mem_av_in, e->src->mem_av_out); /* mem_av_in &= mem_av_out */
  return !bitmap_equal_p (bb->mem_av_in, prev_mem_av_in);
}

static int mem_av_trans_func (gen_ctx_t gen_ctx, bb_t bb) {
  int alias_p;
  size_t nel, nel2;
  MIR_insn_t insn, mem_insn;
  MIR_op_t *mem_ref;
  bitmap_iterator_t bi, bi2;
  bitmap_t prev_mem_av_out = temp_bitmap;

  bitmap_copy (prev_mem_av_out, bb->mem_av_out);
  bitmap_copy (bb->mem_av_out, bb->gen);
  if (!bb->call_p) {
    FOREACH_BITMAP_BIT (bi, bb->mem_av_in, nel) {
      alias_p = FALSE;
      insn = VARR_GET (mem_expr_t, mem_exprs, nel)->insn;
      mem_ref = insn->ops[0].mode == MIR_OP_VAR_MEM ? &insn->ops[0] : &insn->ops[1];
      FOREACH_BITMAP_BIT (bi2, bb->gen, nel2) { /* consider only stores */
        mem_insn = VARR_GET (mem_expr_t, mem_exprs, nel2)->insn;
        if (mem_insn->ops[0].mode == MIR_OP_VAR_MEM
            && may_mem_alias_p (mem_ref, &mem_insn->ops[0])) {
          alias_p = TRUE;
          break;
        }
      }
      if (!alias_p) bitmap_set_bit_p (bb->mem_av_out, nel);
    }
  }
  return !bitmap_equal_p (bb->mem_av_out, prev_mem_av_out);
}

static void update_mem_availability (gen_ctx_t gen_ctx, bitmap_t mem_av, bb_insn_t mem_bb_insn) {
  size_t nel;
  bitmap_iterator_t bi;
  MIR_insn_t mem_insn;
  MIR_op_t *mem_ref = &mem_bb_insn->insn->ops[0];
  int ld_p;

  gen_assert (move_code_p (mem_bb_insn->insn->code));
  if ((ld_p = mem_ref->mode != MIR_OP_VAR_MEM)) mem_ref = &mem_bb_insn->insn->ops[1];
  gen_assert (mem_ref->mode == MIR_OP_VAR_MEM);
  FOREACH_BITMAP_BIT (bi, mem_av, nel) {
    mem_insn = VARR_GET (mem_expr_t, mem_exprs, nel)->insn;
    if (!ld_p
        && may_mem_alias_p (&mem_insn->ops[mem_insn->ops[0].mode == MIR_OP_VAR_MEM ? 0 : 1],
                            mem_ref))
      bitmap_clear_bit_p (mem_av, nel);
  }
  bitmap_set_bit_p (mem_av, mem_bb_insn->mem_index);
}

static void calculate_memory_availability (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;

  DEBUG (2, { fprintf (debug_file, "Calculate memory availability:\n"); });
  gen_assert (VARR_LENGTH (mem_expr_t, mem_exprs) == 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    DEBUG (2, { fprintf (debug_file, "  BB%lu:\n", (unsigned long) bb->index); });
    bitmap_clear (bb->gen);
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      MIR_insn_t insn = bb_insn->insn;
      mem_expr_t e;
      size_t mem_num;

      if (MIR_call_code_p (insn->code)) { /* ??? improving */
        bitmap_clear (bb->gen);
        continue;
      }
      if (!move_code_p (insn->code)) continue;
      if (insn->ops[0].mode != MIR_OP_VAR_MEM && insn->ops[1].mode != MIR_OP_VAR_MEM) continue;
      bb_insn->mem_index = mem_num = VARR_LENGTH (mem_expr_t, mem_exprs);
      DEBUG (2, {
        fprintf (debug_file, "     Adding mem insn %-5lu:", mem_num);
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
      });
      e = gen_malloc (gen_ctx, sizeof (struct mem_expr));
      e->insn = bb_insn->insn;
      e->temp_reg = MIR_NON_VAR;
      e->mem_num = mem_num;
      e->next = NULL;
      VARR_PUSH (mem_expr_t, mem_exprs, e);
      if (insn->ops[0].mode == MIR_OP_VAR_MEM || insn->ops[1].mode == MIR_OP_VAR_MEM)
        update_mem_availability (gen_ctx, bb->gen, bb_insn);
    }
    DEBUG (2, { output_bitmap (gen_ctx, "   Mem availabilty gen:", bb->gen, FALSE); });
  }
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    bitmap_set_bit_range_p (bb->mem_av_out, 0, VARR_LENGTH (mem_expr_t, mem_exprs));
  solve_dataflow (gen_ctx, TRUE, mem_av_con_func_0, mem_av_con_func_n, mem_av_trans_func);
  DEBUG (2, {
    fprintf (debug_file, "BB mem availability in/out:\n");
    for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
      fprintf (debug_file, "  BB%lu:\n", (unsigned long) bb->index);
      output_bitmap (gen_ctx, "    mem av in:", bb->mem_av_in, FALSE);
      output_bitmap (gen_ctx, "    mem av out:", bb->mem_av_out, FALSE);
    }
  });
}

#undef mem_av_in
#undef mem_av_out

static int op_eq (gen_ctx_t gen_ctx, MIR_op_t op1, MIR_op_t op2) {
  return MIR_op_eq_p (gen_ctx->ctx, op1, op2);
}

static int multi_out_insn_p (MIR_insn_t insn) {
  if (!MIR_call_code_p (insn->code)) return FALSE;
  gen_assert (insn->ops[0].u.ref->item_type == MIR_proto_item);
  return insn->ops[0].u.ref->u.proto->nres > 1;
}

static int expr_eq (expr_t e1, expr_t e2, void *arg) {
  gen_ctx_t gen_ctx = arg;
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn1 = e1->insn, insn2 = e2->insn;
  size_t i, nops;
  int out_p;
  ssa_edge_t ssa_edge1, ssa_edge2;

  if (insn1->code != insn2->code) return FALSE;
  nops = MIR_insn_nops (gen_ctx->ctx, insn1);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (ctx, insn1, i, &out_p);
    if (out_p && insn1->ops[i].mode != MIR_OP_VAR_MEM) continue;
    if ((insn1->ops[i].mode != MIR_OP_VAR || insn2->ops[i].mode != MIR_OP_VAR)
        && (insn1->ops[i].mode != MIR_OP_VAR_MEM || insn2->ops[i].mode != MIR_OP_VAR_MEM)
        && !op_eq (gen_ctx, insn1->ops[i], insn2->ops[i]))
      return FALSE;
    ssa_edge1 = insn1->ops[i].data;
    ssa_edge2 = insn2->ops[i].data;
    if (ssa_edge1 != NULL && ssa_edge2 != NULL
        && (ssa_edge1->def->gvn_val_const_p != ssa_edge2->def->gvn_val_const_p
            || ssa_edge1->def->gvn_val != ssa_edge2->def->gvn_val
            /* we can not be sure what definition we use in multi-output insn: */
            || multi_out_insn_p (ssa_edge1->def->insn) || multi_out_insn_p (ssa_edge2->def->insn)))
      return FALSE;
  }
  return TRUE;
}

static htab_hash_t expr_hash (expr_t e, void *arg) {
  gen_ctx_t gen_ctx = arg;
  MIR_context_t ctx = gen_ctx->ctx;
  size_t i, nops;
  int out_p;
  ssa_edge_t ssa_edge;
  htab_hash_t h = mir_hash_init (0x42);

  h = mir_hash_step (h, (uint64_t) e->insn->code);
  nops = MIR_insn_nops (ctx, e->insn);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (ctx, e->insn, i, &out_p);
    if (out_p && e->insn->ops[i].mode != MIR_OP_VAR_MEM) continue;
    if (e->insn->ops[i].mode != MIR_OP_VAR && e->insn->ops[i].mode != MIR_OP_VAR_MEM)
      h = MIR_op_hash_step (ctx, h, e->insn->ops[i]);
    if ((ssa_edge = e->insn->ops[i].data) != NULL) {
      h = mir_hash_step (h, (uint64_t) ssa_edge->def->gvn_val_const_p);
      h = mir_hash_step (h, (uint64_t) ssa_edge->def->gvn_val);
    }
  }
  return mir_hash_finish (h);
}

static int find_expr (gen_ctx_t gen_ctx, MIR_insn_t insn, expr_t *e) {
  struct expr es;

  es.insn = insn;
  return HTAB_DO (expr_t, expr_tab, &es, HTAB_FIND, *e);
}

static void insert_expr (gen_ctx_t gen_ctx, expr_t e) {
  expr_t MIR_UNUSED e2;

  gen_assert (!find_expr (gen_ctx, e->insn, &e2));
  HTAB_DO (expr_t, expr_tab, e, HTAB_INSERT, e);
}

static void replace_expr (gen_ctx_t gen_ctx, expr_t e) {
  expr_t MIR_UNUSED e2;

  gen_assert (find_expr (gen_ctx, e->insn, &e2));
  HTAB_DO (expr_t, expr_tab, e, HTAB_REPLACE, e);
}

static expr_t add_expr (gen_ctx_t gen_ctx, MIR_insn_t insn, int replace_p) {
  expr_t e = gen_malloc (gen_ctx, sizeof (struct expr));

  /* can not be calls, rets, stores */
  gen_assert (!MIR_call_code_p (insn->code) && insn->code != MIR_RET && insn->code != MIR_JRET
              && (!move_code_p (insn->code) || insn->ops[0].mode != MIR_OP_VAR_MEM));
  e->insn = insn;
  e->num = ((bb_insn_t) insn->data)->index;
  e->temp_reg = MIR_NON_VAR;
  VARR_PUSH (expr_t, exprs, e);
  if (replace_p)
    replace_expr (gen_ctx, e);
  else
    insert_expr (gen_ctx, e);
  return e;
}

static MIR_type_t canonic_type (MIR_type_t type) {
  switch (type) {
  case MIR_T_U8: return MIR_T_I8;
  case MIR_T_U16: return MIR_T_I16;
  case MIR_T_U32: return MIR_T_I32;
  case MIR_T_U64: return MIR_T_I64;
#ifdef MIR_PTR32
  case MIR_T_P: return MIR_T_I32;
#else
  case MIR_T_P: return MIR_T_I64;
#endif
  default: return type;
  }
}

static int mem_expr_eq (mem_expr_t e1, mem_expr_t e2, void *arg) {
  MIR_insn_t st1 = e1->insn, st2 = e2->insn;
  MIR_op_t *op_ref1 = &st1->ops[0], *op_ref2 = &st2->ops[0];
  ssa_edge_t ssa_edge1, ssa_edge2;

  gen_assert (move_code_p (st1->code) && move_code_p (st2->code));
  if (op_ref1->mode != MIR_OP_VAR_MEM) op_ref1 = &st1->ops[1];
  if (op_ref2->mode != MIR_OP_VAR_MEM) op_ref2 = &st2->ops[1];
  gen_assert (op_ref1->mode == MIR_OP_VAR_MEM && op_ref2->mode == MIR_OP_VAR_MEM);
  ssa_edge1 = op_ref1->data;
  ssa_edge2 = op_ref2->data;
  return (ssa_edge1 != NULL && ssa_edge2 != NULL
          && ssa_edge1->def->gvn_val_const_p == ssa_edge2->def->gvn_val_const_p
          && ssa_edge1->def->gvn_val == ssa_edge2->def->gvn_val
          && canonic_type (op_ref1->u.var_mem.type) == canonic_type (op_ref2->u.var_mem.type)
          && op_ref1->u.var_mem.alias == op_ref2->u.var_mem.alias
          && op_ref1->u.var_mem.nonalias == op_ref2->u.var_mem.nonalias);
}

static htab_hash_t mem_expr_hash (mem_expr_t e, void *arg) {
  MIR_insn_t st = e->insn;
  MIR_op_t *op_ref;
  ssa_edge_t ssa_edge;
  htab_hash_t h = mir_hash_init (0x23);

  gen_assert (move_code_p (st->code));
  op_ref = st->ops[0].mode == MIR_OP_VAR_MEM ? &st->ops[0] : &st->ops[1];
  gen_assert (op_ref->mode == MIR_OP_VAR_MEM);
  if ((ssa_edge = op_ref->data) != NULL) {
    h = mir_hash_step (h, (uint64_t) ssa_edge->def->gvn_val_const_p);
    h = mir_hash_step (h, (uint64_t) ssa_edge->def->gvn_val);
  }
  h = mir_hash_step (h, (uint64_t) canonic_type (op_ref->u.var_mem.type));
  h = mir_hash_step (h, (uint64_t) op_ref->u.var_mem.alias);
  h = mir_hash_step (h, (uint64_t) op_ref->u.var_mem.nonalias);
  return mir_hash_finish (h);
}

static mem_expr_t find_mem_expr (gen_ctx_t gen_ctx, MIR_insn_t mem_insn) {
  mem_expr_t tab_e, e;

  gen_assert (
    move_code_p (mem_insn->code)
    && (mem_insn->ops[0].mode == MIR_OP_VAR_MEM || mem_insn->ops[1].mode == MIR_OP_VAR_MEM));
  e = VARR_GET (mem_expr_t, mem_exprs, ((bb_insn_t) mem_insn->data)->mem_index);
  if (HTAB_DO (mem_expr_t, mem_expr_tab, e, HTAB_FIND, tab_e)) return tab_e;
  return NULL;
}

static mem_expr_t add_mem_insn (gen_ctx_t gen_ctx, MIR_insn_t mem_insn) {
  bb_insn_t bb_insn = mem_insn->data;
  mem_expr_t tab_e, e;

  gen_assert (
    move_code_p (mem_insn->code)
    && (mem_insn->ops[0].mode == MIR_OP_VAR_MEM || mem_insn->ops[1].mode == MIR_OP_VAR_MEM));
  e = VARR_GET (mem_expr_t, mem_exprs, bb_insn->mem_index);
  e->next = NULL;
  if (HTAB_DO (mem_expr_t, mem_expr_tab, e, HTAB_FIND, tab_e)) e->next = tab_e;
  HTAB_DO (mem_expr_t, mem_expr_tab, e, HTAB_REPLACE, tab_e);
  return e;
}

static MIR_type_t mode2type (MIR_op_mode_t mode) {
  return (mode == MIR_OP_FLOAT     ? MIR_T_F
          : mode == MIR_OP_DOUBLE  ? MIR_T_D
          : mode == MIR_OP_LDOUBLE ? MIR_T_LD
                                   : MIR_T_I64);
}

static MIR_op_mode_t type2mode (MIR_type_t type) {
  return (type == MIR_T_F    ? MIR_OP_FLOAT
          : type == MIR_T_D  ? MIR_OP_DOUBLE
          : type == MIR_T_LD ? MIR_OP_LDOUBLE
                             : MIR_OP_INT);
}

static MIR_reg_t get_expr_temp_reg (gen_ctx_t gen_ctx, MIR_insn_t insn, MIR_reg_t *temp_reg) {
  int out_p;
  MIR_op_mode_t mode;

  if (*temp_reg != MIR_NON_VAR) return *temp_reg;
  mode = MIR_insn_op_mode (gen_ctx->ctx, insn, 0, &out_p);
  *temp_reg = gen_new_temp_reg (gen_ctx, mode2type (mode), curr_func_item->u.func);
  return *temp_reg;
}

static int gvn_insn_p (MIR_insn_t insn) {
  return (insn->code != MIR_RET && insn->code != MIR_JRET && insn->code != MIR_SWITCH
          && insn->code != MIR_LABEL && !MIR_call_code_p (insn->code) && insn->code != MIR_ALLOCA
          && insn->code != MIR_BSTART && insn->code != MIR_BEND && insn->code != MIR_VA_START
          && insn->code != MIR_VA_ARG && insn->code != MIR_VA_END);
}

#if !MIR_NO_GEN_DEBUG
static void print_expr (gen_ctx_t gen_ctx, expr_t e, const char *title) {
  MIR_context_t ctx = gen_ctx->ctx;
  size_t nops;

  fprintf (debug_file, "  %s %3lu: ", title, (unsigned long) e->num);
  fprintf (debug_file, "%s _", MIR_insn_name (ctx, e->insn->code));
  nops = MIR_insn_nops (ctx, e->insn);
  for (size_t j = 1; j < nops; j++) {
    fprintf (debug_file, ", ");
    MIR_output_op (ctx, debug_file, e->insn->ops[j], curr_func_item->u.func);
  }
  fprintf (debug_file, "\n");
}
#endif

static int add_sub_const_insn_p (MIR_insn_t insn, int64_t *val) { /* check r1 = r0 +- const */
  ssa_edge_t ssa_edge;
  bb_insn_t def_bb_insn;
  // ??? , minimal gvn->val
  if (insn->code != MIR_ADD && insn->code != MIR_SUB && insn->code != MIR_ADDS
      && insn->code != MIR_SUBS)
    return FALSE;
  if ((ssa_edge = insn->ops[2].data) == NULL || !(def_bb_insn = ssa_edge->def)->gvn_val_const_p)
    return FALSE;
  *val = insn->code == MIR_SUB || insn->code == MIR_SUBS ? -def_bb_insn->gvn_val
                                                         : def_bb_insn->gvn_val;
  return TRUE;
}

static MIR_insn_t skip_moves (MIR_insn_t insn) {
  ssa_edge_t se;

  while (insn->code == MIR_MOV && insn->ops[1].mode == MIR_OP_VAR) {
    if ((se = insn->ops[1].data) == NULL) return insn;
    insn = se->def->insn;
  }
  return insn;
}

static void print_bb_insn_value (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  MIR_context_t ctx = gen_ctx->ctx;

  DEBUG (2, {
    fprintf (debug_file, "%s%s=%lld for insn %lu:",
             !bb_insn->alloca_flag                               ? ""
             : bb_insn->alloca_flag & (MAY_ALLOCA | MUST_ALLOCA) ? "may/must alloca "
             : bb_insn->alloca_flag & MAY_ALLOCA                 ? "may alloca"
                                                                 : "must alloca",
             bb_insn->gvn_val_const_p ? "const val" : "val", (long long) bb_insn->gvn_val,
             (unsigned long) bb_insn->index);
    MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, TRUE);
  });
}

static int get_gvn_op (gen_ctx_t gen_ctx, MIR_insn_t insn, size_t nop, int64_t *val) {
  MIR_op_t *op_ref = &insn->ops[nop];
  ssa_edge_t ssa_edge;
  bb_insn_t def_bb_insn;

  if ((ssa_edge = op_ref->data) != NULL && (def_bb_insn = ssa_edge->def)->gvn_val_const_p) {
    *val = def_bb_insn->gvn_val;
    return TRUE;
  }
  return FALSE;
}

static int get_gvn_2ops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *val1) {
  return get_gvn_op (gen_ctx, insn, 1, val1);
}

static int get_gvn_3ops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *val1, int64_t *val2) {
  if (get_gvn_op (gen_ctx, insn, 1, val1) && get_gvn_op (gen_ctx, insn, 2, val2)) return TRUE;
  return FALSE;
}

static int get_gvn_2iops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *p) {
  int64_t val;

  if (!get_gvn_2ops (gen_ctx, insn, &val)) return FALSE;
  *p = val;
  return TRUE;
}

static int get_gvn_2isops (gen_ctx_t gen_ctx, MIR_insn_t insn, int32_t *p) {
  int64_t val;

  if (!get_gvn_2ops (gen_ctx, insn, &val)) return FALSE;
  *p = val;
  return TRUE;
}

static int MIR_UNUSED get_gvn_2usops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint32_t *p) {
  int64_t val;

  if (!get_gvn_2ops (gen_ctx, insn, &val)) return FALSE;
  *p = val;
  return TRUE;
}

static int get_gvn_3iops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *p1, int64_t *p2) {
  int64_t val1, val2;

  if (!get_gvn_3ops (gen_ctx, insn, &val1, &val2)) return FALSE;
  *p1 = val1;
  *p2 = val2;
  return TRUE;
}

static int get_gvn_3isops (gen_ctx_t gen_ctx, MIR_insn_t insn, int32_t *p1, int32_t *p2) {
  int64_t val1, val2;

  if (!get_gvn_3ops (gen_ctx, insn, &val1, &val2)) return FALSE;
  *p1 = val1;
  *p2 = val2;
  return TRUE;
}

static int get_gvn_3uops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint64_t *p1, uint64_t *p2) {
  int64_t val1, val2;

  if (!get_gvn_3ops (gen_ctx, insn, &val1, &val2)) return FALSE;
  *p1 = val1;
  *p2 = val2;
  return TRUE;
}

static int get_gvn_3usops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint32_t *p1, uint32_t *p2) {
  int64_t val1, val2;

  if (!get_gvn_3ops (gen_ctx, insn, &val1, &val2)) return FALSE;
  *p1 = val1;
  *p2 = val2;
  return TRUE;
}

#define GVN_EXT(tp)                                                  \
  do {                                                               \
    int64_t p;                                                       \
    if ((const_p = get_gvn_2iops (gen_ctx, insn, &p))) val = (tp) p; \
  } while (0)

#define GVN_IOP2(op)                                               \
  do {                                                             \
    int64_t p;                                                     \
    if ((const_p = get_gvn_2iops (gen_ctx, insn, &p))) val = op p; \
  } while (0)

#define GVN_IOP2S(op)                                               \
  do {                                                              \
    int32_t p;                                                      \
    if ((const_p = get_gvn_2isops (gen_ctx, insn, &p))) val = op p; \
  } while (0)

#define GVN_IOP3(op)                                                         \
  do {                                                                       \
    int64_t p1, p2;                                                          \
    if ((const_p = get_gvn_3iops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_IOP3S(op)                                                         \
  do {                                                                        \
    int32_t p1, p2;                                                           \
    if ((const_p = get_gvn_3isops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_UOP3(op)                                                         \
  do {                                                                       \
    uint64_t p1, p2;                                                         \
    if ((const_p = get_gvn_3uops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_UOP3S(op)                                                         \
  do {                                                                        \
    uint32_t p1, p2;                                                          \
    if ((const_p = get_gvn_3usops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_IOP30(op)                                                   \
  do {                                                                  \
    if (get_gvn_op (gen_ctx, insn, 2, &val) && val != 0) GVN_IOP3 (op); \
  } while (0)

#define GVN_IOP3S0(op)                                                   \
  do {                                                                   \
    if (get_gvn_op (gen_ctx, insn, 2, &val) && val != 0) GVN_IOP3S (op); \
  } while (0)

#define GVN_UOP30(op)                                                   \
  do {                                                                  \
    if (get_gvn_op (gen_ctx, insn, 2, &val) && val != 0) GVN_UOP3 (op); \
  } while (0)

#define GVN_UOP3S0(op)                                                   \
  do {                                                                   \
    if (get_gvn_op (gen_ctx, insn, 2, &val) && val != 0) GVN_UOP3S (op); \
  } while (0)

#define GVN_ICMP(op)                                                         \
  do {                                                                       \
    int64_t p1, p2;                                                          \
    if ((const_p = get_gvn_3iops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_ICMPS(op)                                                         \
  do {                                                                        \
    int32_t p1, p2;                                                           \
    if ((const_p = get_gvn_3isops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_UCMP(op)                                                         \
  do {                                                                       \
    uint64_t p1, p2;                                                         \
    if ((const_p = get_gvn_3uops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

#define GVN_UCMPS(op)                                                         \
  do {                                                                        \
    uint32_t p1, p2;                                                          \
    if ((const_p = get_gvn_3usops (gen_ctx, insn, &p1, &p2))) val = p1 op p2; \
  } while (0)

static int gvn_phi_val (gen_ctx_t gen_ctx, bb_insn_t phi, int64_t *val) {
  MIR_insn_t phi_insn = phi->insn;
  bb_t bb = phi->bb;
  bb_insn_t def_bb_insn;
  edge_t e;
  size_t nop;
  ssa_edge_t se;
  int const_p = TRUE, same_p = TRUE;

  nop = 1;
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e), nop++) {
    /* Update phi value: */
    gen_assert (nop < phi_insn->nops);
    if (same_p) {
      if ((se = phi_insn->ops[nop].data) == NULL || (def_bb_insn = se->def) == NULL) {
        same_p = FALSE;
      } else if (nop == 1) {
        const_p = def_bb_insn->gvn_val_const_p;
        *val = def_bb_insn->gvn_val;
      } else if (const_p != def_bb_insn->gvn_val_const_p || *val != def_bb_insn->gvn_val) {
        same_p = FALSE;
      }
    }
    if ((se = phi_insn->ops[nop].data) != NULL) {
      phi->alloca_flag = nop == 1 ? se->def->alloca_flag
                                  : ((phi->alloca_flag | se->def->alloca_flag) & MAY_ALLOCA)
                                      | (phi->alloca_flag & se->def->alloca_flag & MUST_ALLOCA);
    }
  }
  if (!same_p) *val = phi->index;
  return same_p && const_p;
}

static void remove_edge_phi_ops (gen_ctx_t gen_ctx, edge_t e) {
  size_t i, nop;
  edge_t e2;
  MIR_insn_t insn;
  ssa_edge_t se;

  for (nop = 1, e2 = DLIST_HEAD (in_edge_t, e->dst->in_edges); e2 != NULL && e2 != e;
       e2 = DLIST_NEXT (in_edge_t, e2), nop++)
    ;
  gen_assert (e2 != NULL);
  for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, e->dst->bb_insns); bb_insn != NULL;
       bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
    if ((insn = bb_insn->insn)->code == MIR_LABEL) continue;
    if (insn->code != MIR_PHI) break;
    if ((se = insn->ops[nop].data) != NULL) remove_ssa_edge (gen_ctx, se);
    for (i = nop; i + 1 < insn->nops; i++) {
      insn->ops[i] = insn->ops[i + 1];
      /* se can be null from some previously removed BB insn: */
      if ((se = insn->ops[i].data) != NULL) {
        gen_assert (se->use_op_num == i + 1);
        se->use_op_num = i;
      }
    }
    insn->nops--;
  }
}

static void MIR_UNUSED remove_dest_phi_ops (gen_ctx_t gen_ctx, bb_t bb) {
  for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    remove_edge_phi_ops (gen_ctx, e);
}

static void set_alloca_based_flag (gen_ctx_t gen_ctx, bb_insn_t bb_insn, int must_p) {
  MIR_insn_t insn = bb_insn->insn;
  ssa_edge_t se;

  gen_assert (insn->nops >= 2);
  if (must_p) {
    if (((se = insn->ops[1].data) != NULL && (se->def->alloca_flag & MUST_ALLOCA))
        || (insn->nops == 3 && (se = insn->ops[2].data) != NULL
            && (se->def->alloca_flag & MUST_ALLOCA)))
      bb_insn->alloca_flag |= MUST_ALLOCA;
  }
  if (((se = insn->ops[1].data) != NULL && (se->def->alloca_flag & MAY_ALLOCA))
      || (insn->nops == 3 && (se = insn->ops[2].data) != NULL
          && (se->def->alloca_flag & MAY_ALLOCA)))
    bb_insn->alloca_flag |= MAY_ALLOCA;
}

static ssa_edge_t skip_move_ssa_edges (ssa_edge_t se, MIR_insn_t *def_insn) {
  for (;;) {
    gen_assert (se != NULL);
    *def_insn = se->def->insn;
    if (!move_p (*def_insn)) return se;
    se = (*def_insn)->ops[1].data;
  }
}

static MIR_insn_t get_def_disp (ssa_edge_t se, int64_t *disp) {
  MIR_insn_t def_insn;

  *disp = 0;
  for (;;) {
    se = skip_move_ssa_edges (se, &def_insn);
    if ((def_insn->code != MIR_ADD && def_insn->code != MIR_ADDS && def_insn->code != MIR_SUB
         && def_insn->code != MIR_SUBS)
        || (se = def_insn->ops[2].data) == NULL || !se->def->gvn_val_const_p)
      return def_insn;
    int add_p = def_insn->code == MIR_ADD || def_insn->code == MIR_ADDS;
    *disp += add_p ? se->def->gvn_val : -se->def->gvn_val;
    se = def_insn->ops[1].data; /* new base */
  }
}

static void new_mem_loc (gen_ctx_t gen_ctx, MIR_op_t *mem_op_ref, int flag) {
  /* zero loc is fixed: */
  int64_t disp;
  mem_attr_t mem_attr;

  if ((mem_op_ref->u.var_mem.nloc = VARR_LENGTH (mem_attr_t, mem_attrs)) == 0)
    mem_op_ref->u.var_mem.nloc = 1;
  mem_attr.alloca_flag = flag;
  mem_attr.type = mem_op_ref->u.var_mem.type;
  mem_attr.alias = mem_op_ref->u.var_mem.alias;
  mem_attr.nonalias = mem_op_ref->u.var_mem.nonalias;
  mem_attr.disp_def_p = FALSE;
  mem_attr.disp = 0;
  mem_attr.def_insn = NULL;
  if ((flag & MUST_ALLOCA) != 0) {
    mem_attr.def_insn = get_def_disp (mem_op_ref->data, &disp);
    mem_attr.disp_def_p = TRUE;
    mem_attr.disp = disp;
  }
  if (VARR_LENGTH (mem_attr_t, mem_attrs) == 0) VARR_PUSH (mem_attr_t, mem_attrs, mem_attr);
  DEBUG (2, {
    fprintf (debug_file, "    new m%lu", (unsigned long) mem_op_ref->u.var_mem.nloc);
    if (mem_attr.def_insn != NULL)
      fprintf (debug_file, "(def_insn=%u)", ((bb_insn_t) mem_attr.def_insn->data)->index);
    if (mem_attr.disp_def_p) fprintf (debug_file, "(disp=%lld)", (long long) mem_attr.disp);
    if (flag)
      fprintf (debug_file, " is %s alloca based",
               flag & (MAY_ALLOCA | MUST_ALLOCA) ? "may/must"
               : flag & MAY_ALLOCA               ? "may"
                                                 : "must");
    fprintf (debug_file, "\n");
  });
  VARR_PUSH (mem_attr_t, mem_attrs, mem_attr);
}

static void update_mem_loc_alloca_flag (gen_ctx_t gen_ctx, size_t nloc, int flag) {
  int old_flag;
  mem_attr_t *mem_attr_ref;

  gen_assert (VARR_LENGTH (mem_attr_t, mem_attrs) > nloc);
  mem_attr_ref = &VARR_ADDR (mem_attr_t, mem_attrs)[nloc];
  old_flag = mem_attr_ref->alloca_flag;
  mem_attr_ref->alloca_flag = ((old_flag | flag) & MAY_ALLOCA) | (old_flag & flag & MUST_ALLOCA);
  DEBUG (2, {
    if (flag != old_flag) {
      fprintf (debug_file, "    m%lu ", (unsigned long) nloc);
      if (!flag)
        fprintf (debug_file, "is no more alloca based\n");
      else
        fprintf (debug_file, "becomes %s alloca based\n",
                 flag & (MAY_ALLOCA | MUST_ALLOCA) ? "may/must"
                 : flag & MAY_ALLOCA               ? "may"
                                                   : "must");
    }
  });
}

static long remove_bb (gen_ctx_t gen_ctx, bb_t bb) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, next_bb_insn;
  long deleted_insns_num = 0;

  gen_assert (bb->index != 2);
  DEBUG (2, {
    fprintf (debug_file, "  BB%lu is unreachable and removed\n", (unsigned long) bb->index);
  });
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
    next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
    insn = bb_insn->insn;
    gen_delete_insn (gen_ctx, insn);
    deleted_insns_num++;
  }
  delete_bb (gen_ctx, bb);
  return deleted_insns_num;
}

static long remove_unreachable_bbs (gen_ctx_t gen_ctx) {
  long deleted_insns_num = 0;
  bb_t next_bb, bb = DLIST_EL (bb_t, curr_cfg->bbs, 2);

  if (bb == NULL) return 0;
  gen_assert (bb->index == 2);
  bitmap_clear (temp_bitmap);
  VARR_TRUNC (bb_t, worklist, 0);
  VARR_PUSH (bb_t, worklist, bb);
  bitmap_set_bit_p (temp_bitmap, bb->index);
  while (VARR_LENGTH (bb_t, worklist) != 0) {
    bb = VARR_POP (bb_t, worklist);
    for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL;
         e = DLIST_NEXT (out_edge_t, e))
      if (bitmap_set_bit_p (temp_bitmap, e->dst->index)) VARR_PUSH (bb_t, worklist, e->dst);
  }
  for (bb_t bb = DLIST_EL (bb_t, curr_cfg->bbs, 2); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    if (!bitmap_bit_p (temp_bitmap, bb->index)) deleted_insns_num += remove_bb (gen_ctx, bb);
  }
  return deleted_insns_num;
}

static void copy_gvn_info (bb_insn_t to, bb_insn_t from) {
  to->gvn_val_const_p = from->gvn_val_const_p;
  to->gvn_val = from->gvn_val;
  to->alloca_flag = from->alloca_flag;
}

static void remove_copy (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  ssa_edge_t se, last_se;
  bb_insn_t def;
  int def_op_num;

  gen_assert (move_p (insn) || (insn->code == MIR_PHI && insn->nops == 2));
  se = insn->ops[1].data;
  def = se->def;
  def_op_num = se->def_op_num;
  remove_ssa_edge (gen_ctx, se);
  if ((last_se = def->insn->ops[def_op_num].data) != NULL)
    while (last_se->next_use != NULL) last_se = last_se->next_use;
  change_ssa_edge_list_def (insn->ops[0].data, def, def_op_num, insn->ops[0].u.var,
                            insn->ops[1].u.var);
  if (last_se != NULL)
    last_se->next_use = insn->ops[0].data;
  else
    def->insn->ops[def_op_num].data = insn->ops[0].data;
  if (insn->ops[0].data != NULL) ((ssa_edge_t) insn->ops[0].data)->prev_use = last_se;
  insn->ops[0].data = NULL;
  DEBUG (2, {
    fprintf (debug_file, "    Remove copy %-5lu", (unsigned long) ((bb_insn_t) insn->data)->index);
    print_bb_insn (gen_ctx, insn->data, FALSE);
  });
  gen_delete_insn (gen_ctx, insn);
}

/* we are at curr bb from start, return true if can go to start avoiding dst */
static int reachable_without_visiting_bb_p (gen_ctx_t gen_ctx, bb_t curr, bb_t start,
                                            bb_t exclude) {
  if (curr == exclude || !bitmap_set_bit_p (temp_bitmap2, curr->index)) return FALSE;
  for (edge_t e = DLIST_HEAD (out_edge_t, curr->out_edges); e != NULL;
       e = DLIST_NEXT (out_edge_t, e))
    if (e->dst == start || reachable_without_visiting_bb_p (gen_ctx, e->dst, start, exclude))
      return TRUE;
  return FALSE;
}

static int cycle_without_bb_visit_p (gen_ctx_t gen_ctx, bb_t start, bb_t exclude) {
  bitmap_clear (temp_bitmap2);
  return reachable_without_visiting_bb_p (gen_ctx, start, start, exclude);
}

static mem_expr_t find_first_available_mem_expr (mem_expr_t list, bitmap_t available_mem,
                                                 int any_p) {
  for (mem_expr_t curr = list; curr != NULL; curr = curr->next)
    if (bitmap_bit_p (available_mem, ((bb_insn_t) curr->insn->data)->mem_index)
        && (any_p || curr->insn->ops[0].mode == MIR_OP_VAR_MEM))
      return curr;
  return NULL;
}

/* Memory displacement to prefer for memory address recalculation instead.  */
#ifndef TARGET_MAX_MEM_DISP
#define TARGET_MAX_MEM_DISP 127
#endif

#ifndef TARGET_MIN_MEM_DISP
#define TARGET_MIN_MEM_DISP -128
#endif

static void remove_unreachable_bb_edges (gen_ctx_t gen_ctx, bb_t bb, VARR (bb_t) * bbs) {
  bb_t dst;
  edge_t e, next_e;

  VARR_TRUNC (bb_t, bbs, 0);
  VARR_PUSH (bb_t, bbs, bb);
  while (VARR_LENGTH (bb_t, bbs) != 0) {
    bb = VARR_POP (bb_t, bbs);
    DEBUG (2, {
      fprintf (debug_file, "  Deleting output edges of unreachable bb%lu\n",
               (unsigned long) bb->index);
    });
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = next_e) {
      next_e = DLIST_NEXT (out_edge_t, e);
      remove_edge_phi_ops (gen_ctx, e);
      dst = e->dst;
      dst->flag = TRUE; /* to recalculate dst mem_av_in */
      delete_edge (e);
      if (dst->index > 2 && DLIST_HEAD (in_edge_t, dst->in_edges) == NULL)
        VARR_PUSH (bb_t, bbs, dst);
    }
  }
}

static void gvn_modify (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t bb;
  bb_insn_t bb_insn, mem_bb_insn, new_bb_insn, new_bb_insn2, next_bb_insn, expr_bb_insn;
  MIR_reg_t temp_reg;
  long gvn_insns_num = 0, ccp_insns_num = 0, deleted_branches_num = 0;
  bitmap_t curr_available_mem = temp_bitmap, removed_mem = temp_bitmap3;
  MIR_func_t func = curr_func_item->u.func;

  full_escape_p = FALSE;
  VARR_TRUNC (mem_attr_t, mem_attrs, 0);
  bitmap_clear (removed_mem);
  for (size_t i = 0; i < VARR_LENGTH (bb_t, worklist); i++)
    VARR_GET (bb_t, worklist, i)->flag = FALSE;
  while (VARR_LENGTH (bb_t, worklist) != 0) {
    bb = VARR_POP (bb_t, worklist);
    DEBUG (2, { fprintf (debug_file, "  BB%lu:\n", (unsigned long) bb->index); });
    if (bb->index > 2 && DLIST_HEAD (in_edge_t, bb->in_edges) == NULL) {
      /* Unreachable bb because of branch transformation: remove output edges
         recursively as it shorten phis in successors and this creates more opportunity for
         optimizations. But don't remove insns as their output can be used in unreachable loops
         (unreachable loops will be removed in jump optimization pass). */
      remove_unreachable_bb_edges (gen_ctx, bb, pending);
      continue;
    }
    /* Recalculate mem_avin and mem_av_out: */
    if (DLIST_HEAD (in_edge_t, bb->in_edges) != NULL && bb->flag
        && mem_av_con_func_n (gen_ctx, bb)) {
      DEBUG (2, { fprintf (debug_file, "   changed mem_avin\n"); });
      bitmap_and_compl (bb->in, bb->in, removed_mem);
      if (mem_av_trans_func (gen_ctx, bb)) {
        DEBUG (2, { fprintf (debug_file, "   changed mem_avout\n"); });
        for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL;
             e = DLIST_NEXT (out_edge_t, e))
          e->dst->flag = TRUE;
      }
    }
    bitmap_and_compl (curr_available_mem, bb->in, removed_mem);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      expr_t e, new_e;
      mem_expr_t prev_mem_expr, mem_expr;
      MIR_op_t op;
      int add_def_p, const_p, cont_p;
      MIR_type_t type;
      MIR_insn_code_t move_code;
      MIR_insn_t mem_insn, new_insn, new_insn2, def_insn, after, insn = bb_insn->insn;
      ssa_edge_t se, se2;
      bb_insn_t def_bb_insn, new_bb_copy_insn;
      int64_t val = 0, val2;

      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (insn->code == MIR_MOV
          && (insn->ops[1].mode == MIR_OP_INT || insn->ops[1].mode == MIR_OP_UINT)) {
        bb_insn->gvn_val_const_p = TRUE;
        bb_insn->gvn_val = insn->ops[1].u.i;
        print_bb_insn_value (gen_ctx, bb_insn);
        continue;
      }
      if (MIR_call_code_p (insn->code)) bitmap_clear (curr_available_mem);
      if (!gvn_insn_p (insn)) continue;
      const_p = FALSE;
      switch (insn->code) {
      case MIR_PHI:
        const_p = gvn_phi_val (gen_ctx, bb_insn, &val);
        if (const_p) break;
        if (insn->nops == 2 && insn->ops[0].mode == MIR_OP_VAR && insn->ops[1].mode == MIR_OP_VAR
            && MIR_reg_hard_reg_name (ctx, insn->ops[0].u.var - MAX_HARD_REG, func) == NULL
            && MIR_reg_hard_reg_name (ctx, insn->ops[1].u.var - MAX_HARD_REG, func) == NULL) {
          remove_copy (gen_ctx, insn);
          continue;
        }
        bb_insn->gvn_val_const_p = FALSE;
        bb_insn->gvn_val = val;
        print_bb_insn_value (gen_ctx, bb_insn);
        continue;
      case MIR_EXT8: GVN_EXT (int8_t); break;
      case MIR_EXT16: GVN_EXT (int16_t); break;
      case MIR_EXT32: GVN_EXT (int32_t); break;
      case MIR_UEXT8: GVN_EXT (uint8_t); break;
      case MIR_UEXT16: GVN_EXT (uint16_t); break;
      case MIR_UEXT32: GVN_EXT (uint32_t); break;

      case MIR_NEG: GVN_IOP2 (-); break;
      case MIR_NEGS: GVN_IOP2S (-); break;

      case MIR_MUL: GVN_IOP3 (*); break;
      case MIR_MULS: GVN_IOP3S (*); break;

      case MIR_MULO: GVN_IOP3 (*); break;
      case MIR_MULOS: GVN_IOP3S (*); break;
      case MIR_UMULO: GVN_UOP3 (*); break;
      case MIR_UMULOS: GVN_UOP3S (*); break;

      case MIR_DIV: GVN_IOP30 (/); break;
      case MIR_DIVS: GVN_IOP3S0 (/); break;
      case MIR_UDIV: GVN_UOP30 (/); break;
      case MIR_UDIVS: GVN_UOP3S0 (/); break;

      case MIR_MOD: GVN_IOP30 (%); break;
      case MIR_MODS: GVN_IOP3S0 (%); break;
      case MIR_UMOD: GVN_UOP30 (%); break;
      case MIR_UMODS:
        GVN_UOP3S0 (%);
        break;

        /* The following insn can be involved in addres calculation too: */
      case MIR_AND: GVN_IOP3 (&); goto set_alloca_flag;
      case MIR_ANDS: GVN_IOP3S (&); goto set_alloca_flag;
      case MIR_OR: GVN_IOP3 (|); goto set_alloca_flag;
      case MIR_ORS: GVN_IOP3S (|); goto set_alloca_flag;
      case MIR_XOR: GVN_IOP3 (^); goto set_alloca_flag;
      case MIR_XORS:
        GVN_IOP3S (^);
      set_alloca_flag:
        set_alloca_based_flag (gen_ctx, bb_insn, FALSE);
        break;

      case MIR_LSH: GVN_IOP3 (<<); break;
      case MIR_LSHS: GVN_IOP3S (<<); break;
      case MIR_RSH: GVN_IOP3 (>>); break;
      case MIR_RSHS: GVN_IOP3S (>>); break;
      case MIR_URSH: GVN_UOP3 (>>); break;
      case MIR_URSHS: GVN_UOP3S (>>); break;

      case MIR_EQ: GVN_ICMP (==); break;
      case MIR_EQS: GVN_ICMPS (==); break;
      case MIR_NE: GVN_ICMP (!=); break;
      case MIR_NES: GVN_ICMPS (!=); break;

      case MIR_LT: GVN_ICMP (<); break;
      case MIR_LTS: GVN_ICMPS (<); break;
      case MIR_ULT: GVN_UCMP (<); break;
      case MIR_ULTS: GVN_UCMPS (<); break;
      case MIR_LE: GVN_ICMP (<=); break;
      case MIR_LES: GVN_ICMPS (<=); break;
      case MIR_ULE: GVN_UCMP (<=); break;
      case MIR_ULES: GVN_UCMPS (<=); break;
      case MIR_GT: GVN_ICMP (>); break;
      case MIR_GTS: GVN_ICMPS (>); break;
      case MIR_UGT: GVN_UCMP (>); break;
      case MIR_UGTS: GVN_UCMPS (>); break;
      case MIR_GE: GVN_ICMP (>=); break;
      case MIR_GES: GVN_ICMPS (>=); break;
      case MIR_UGE: GVN_UCMP (>=); break;
      case MIR_UGES:
        GVN_UCMPS (>=);
        break;
        /* special treatement for address canonization: */
      case MIR_ADD:
      case MIR_ADDO:
        set_alloca_based_flag (gen_ctx, bb_insn, TRUE);
        GVN_IOP3 (+);
        if (!const_p) goto canon_expr;
        break;
      case MIR_ADDS:
      case MIR_ADDOS:
        set_alloca_based_flag (gen_ctx, bb_insn, TRUE);
        GVN_IOP3S (+);
        if (!const_p) goto canon_expr;
        break;
      case MIR_SUB:
      case MIR_SUBO:
        set_alloca_based_flag (gen_ctx, bb_insn, TRUE);
        GVN_IOP3 (-);
        if (!const_p) goto canon_expr;
        break;
      case MIR_SUBS:
      case MIR_SUBOS:
        set_alloca_based_flag (gen_ctx, bb_insn, TRUE);
        GVN_IOP3S (-);
        if (!const_p) goto canon_expr;
        break;
      canon_expr:
        cont_p = TRUE;
        if ((insn->code == MIR_ADD || insn->code == MIR_ADDS) && (se = insn->ops[1].data) != NULL
            && se->def->gvn_val_const_p
            && ((se2 = insn->ops[2].data) == NULL || !se2->def->gvn_val_const_p)) {
          MIR_op_t temp = insn->ops[2];
          insn->ops[2] = insn->ops[1];
          insn->ops[1] = temp;
          se->use_op_num = 2;
          se2->use_op_num = 1;
          DEBUG (2, {
            fprintf (debug_file, "  exchange ops of insn");
            MIR_output_insn (ctx, debug_file, insn, func, TRUE);
          });
        }
        if (add_sub_const_insn_p (insn, &val2) && (se = insn->ops[1].data) != NULL
            && (def_insn = skip_moves (se->def->insn)) != NULL
            && add_sub_const_insn_p (def_insn, &val)) {
          /* r1=r0+const; ... r2=r1+const2 =>
             temp = r0; r1=r0+const; ... r2=r1+const2;r2=temp+(const+const2): */
          temp_reg = gen_new_temp_reg (gen_ctx, MIR_T_I64, func);
          op = _MIR_new_var_op (ctx, temp_reg);
          new_insn = MIR_new_insn (ctx, MIR_MOV, op, def_insn->ops[1]);
          new_insn->ops[1].data = NULL;
          gen_add_insn_before (gen_ctx, def_insn, new_insn);
          new_bb_copy_insn = new_insn->data;
          add_ssa_edge (gen_ctx, ((ssa_edge_t) def_insn->ops[1].data)->def, 0, new_bb_copy_insn, 1);
          def_bb_insn = ((ssa_edge_t) def_insn->ops[1].data)->def; /* ops[1] def */
          copy_gvn_info (new_bb_copy_insn, def_bb_insn);
          DEBUG (2, {
            fprintf (debug_file, "  adding insn ");
            MIR_output_insn (ctx, debug_file, new_insn, func, FALSE);
            fprintf (debug_file, "  before def insn ");
            MIR_output_insn (ctx, debug_file, def_insn, func, TRUE);
          });
          print_bb_insn_value (gen_ctx, new_bb_copy_insn);
          new_insn2 = NULL;
          if (insn->code == MIR_ADDS || insn->code == MIR_SUBS) {
            if ((int32_t) val + (int32_t) val2 == 0) {
              new_insn = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], op);
            } else {
              temp_reg = gen_new_temp_reg (gen_ctx, MIR_T_I64, func);
              new_insn = MIR_new_insn (ctx, MIR_MOV, _MIR_new_var_op (ctx, temp_reg),
                                       MIR_new_int_op (ctx, (int32_t) val + (int32_t) val2));
              new_insn2
                = MIR_new_insn (ctx, MIR_ADDS, insn->ops[0], op, _MIR_new_var_op (ctx, temp_reg));
            }
          } else {
            if (val + val2 == 0) {
              new_insn = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], op);
            } else {
              temp_reg = gen_new_temp_reg (gen_ctx, MIR_T_I64, func);
              new_insn = MIR_new_insn (ctx, MIR_MOV, _MIR_new_var_op (ctx, temp_reg),
                                       MIR_new_int_op (ctx, val + val2));
              new_insn2
                = MIR_new_insn (ctx, MIR_ADD, insn->ops[0], op, _MIR_new_var_op (ctx, temp_reg));
            }
          }
          new_bb_insn2 = NULL;
          if (new_insn2 != NULL) {
            gen_add_insn_after (gen_ctx, insn, new_insn2);
            new_bb_insn2 = new_insn2->data;
          }
          gen_add_insn_after (gen_ctx, insn, new_insn);
          new_bb_insn = new_insn->data;
          if (new_insn2 != NULL) {
            new_bb_insn->gvn_val_const_p = TRUE;
            new_bb_insn->gvn_val = new_insn->ops[1].u.i;
            add_ssa_edge (gen_ctx, new_bb_insn, 0, new_bb_insn2, 2);
          }
          redirect_def (gen_ctx, insn, (new_insn2 != NULL ? new_insn2 : new_insn), FALSE);
          add_ssa_edge (gen_ctx, new_bb_copy_insn, 0,
                        (new_insn2 != NULL ? new_bb_insn2 : new_bb_insn), 1);
          DEBUG (2, {
            fprintf (debug_file, "  adding insn after:");
            MIR_output_insn (ctx, debug_file, new_insn, func, TRUE);
            if (new_insn2 != NULL) {
              fprintf (debug_file, "  adding 2nd insn after:");
              MIR_output_insn (ctx, debug_file, new_insn2, func, TRUE);
            }
          });
          if (new_insn2 != NULL) { /* start with modified add */
            next_bb_insn = new_bb_insn;
            continue;
          }
          set_alloca_based_flag (gen_ctx, new_bb_copy_insn, TRUE);
          cont_p = new_insn->code != MIR_MOV || new_insn->ops[1].mode != MIR_OP_VAR;
          if (!cont_p) set_alloca_based_flag (gen_ctx, new_bb_insn, TRUE);
          insn = new_insn; /* to consider new insn next */
          bb_insn = new_bb_insn;
          next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
        }
        if (cont_p) break;
        /* fall through */
      case MIR_MOV:
      case MIR_FMOV:
      case MIR_DMOV:
      case MIR_LDMOV:
        if (insn->ops[0].mode == MIR_OP_VAR_MEM) { /* store */
          if ((se = insn->ops[1].data) != NULL && se->def->alloca_flag) full_escape_p = TRUE;
          se = insn->ops[0].data; /* address def actually */
          mem_expr = find_mem_expr (gen_ctx, insn);
          prev_mem_expr = find_first_available_mem_expr (mem_expr, curr_available_mem, FALSE);
          /* If we can reach prev available store bb from itself w/o going through given bb then
             it means it can be stores with different addresses and we just have the same
             memory only for the last store and can not make dead store in prev expr bb.  It
             is also not worth to reuse stored value as it will create a move from some loop
             containing prev expr bb and not containing given bb.  Make new memory for such
             case.  */
          int new_mem_p
            = (prev_mem_expr != NULL
               && cycle_without_bb_visit_p (gen_ctx, ((bb_insn_t) prev_mem_expr->insn->data)->bb,
                                            bb));
          prev_mem_expr = find_first_available_mem_expr (mem_expr, curr_available_mem, TRUE);
          def_bb_insn = ((ssa_edge_t) insn->ops[1].data)->def;
          if (new_mem_p || prev_mem_expr == NULL) {
            new_mem_loc (gen_ctx, &insn->ops[0], se->def->alloca_flag);
          } else if (prev_mem_expr->insn->ops[0].mode
                     == MIR_OP_VAR_MEM) { /* mem = x; ... ; mem=y */
            insn->ops[0].u.var_mem.nloc = prev_mem_expr->insn->ops[0].u.var_mem.nloc;
            update_mem_loc_alloca_flag (gen_ctx, insn->ops[0].u.var_mem.nloc, se->def->alloca_flag);
          } else { /* x = mem; ...; mem = y */
            gen_assert (prev_mem_expr->insn->ops[1].mode == MIR_OP_VAR_MEM);
            insn->ops[0].u.var_mem.nloc = prev_mem_expr->insn->ops[1].u.var_mem.nloc;
            update_mem_loc_alloca_flag (gen_ctx, insn->ops[0].u.var_mem.nloc, se->def->alloca_flag);
            bb_insn_t prev_bb_insn = prev_mem_expr->insn->data;
            if (def_bb_insn->gvn_val_const_p == prev_bb_insn->gvn_val_const_p
                && def_bb_insn->gvn_val == prev_bb_insn->gvn_val) { /* x == y: remove insn */
              gen_assert (def_bb_insn->alloca_flag == prev_bb_insn->alloca_flag);
              DEBUG (2, {
                fprintf (debug_file, "  deleting ");
                print_bb_insn (gen_ctx, insn->data, TRUE);
              });
              bitmap_clear_bit_p (curr_available_mem, bb_insn->mem_index);
              bitmap_set_bit_p (removed_mem, bb_insn->mem_index);
              remove_insn_ssa_edges (gen_ctx, insn);
              gen_delete_insn (gen_ctx, insn);
              continue;
            }
          }
          add_mem_insn (gen_ctx, insn);
          update_mem_availability (gen_ctx, curr_available_mem, bb_insn);
          copy_gvn_info (bb_insn, def_bb_insn);
          print_bb_insn_value (gen_ctx, bb_insn);
          continue;
        } else if (insn->ops[1].mode == MIR_OP_VAR_MEM) { /* load */
          if (insn->ops[0].data == NULL) continue;        /* dead load */
          se = insn->ops[1].data;                         /* address def actually */
          mem_expr = find_mem_expr (gen_ctx, insn);
          mem_expr = find_first_available_mem_expr (mem_expr, curr_available_mem, TRUE);
          if (mem_expr == NULL) {
            new_mem_loc (gen_ctx, &insn->ops[1], se->def->alloca_flag);
            add_mem_insn (gen_ctx, insn);
          } else {
            MIR_op_t *op_ref;
            mem_insn = mem_expr->insn;
            op_ref
              = mem_insn->ops[0].mode == MIR_OP_VAR_MEM ? &mem_insn->ops[0] : &mem_insn->ops[1];
            insn->ops[1].u.var_mem.nloc = op_ref->u.var_mem.nloc;
            update_mem_loc_alloca_flag (gen_ctx, op_ref->u.var_mem.nloc, se->def->alloca_flag);
            if (!bitmap_bit_p (curr_available_mem, (mem_bb_insn = mem_insn->data)->mem_index)
                /* last available load can become dead: */
                || (mem_insn->ops[1].mode == MIR_OP_VAR_MEM && mem_insn->ops[0].data == NULL)) {
              add_mem_insn (gen_ctx, insn);
            } else { /* (mem=x|x=mem); ...; r=mem => (mem=x|x=mem); t=x; ...; r=t */
              copy_gvn_info (bb_insn, mem_bb_insn);
              print_bb_insn_value (gen_ctx, bb_insn);
              temp_reg = mem_expr->temp_reg;
              add_def_p = temp_reg == MIR_NON_VAR;
              if (add_def_p) {
                mem_expr->temp_reg = temp_reg
                  = get_expr_temp_reg (gen_ctx, mem_expr->insn, &mem_expr->temp_reg);
                new_insn = MIR_new_insn (ctx, insn->code, _MIR_new_var_op (ctx, temp_reg),
                                         op_ref == &mem_insn->ops[0] ? mem_insn->ops[1]
                                                                     : mem_insn->ops[0]);
                new_insn->ops[1].data = NULL; /* remove ssa edge taken from load/store op */
                gen_add_insn_after (gen_ctx, mem_insn, new_insn);
                new_bb_insn = new_insn->data;
                copy_gvn_info (new_bb_insn, mem_bb_insn);
                se = op_ref == &mem_insn->ops[0] ? mem_insn->ops[1].data : mem_insn->ops[0].data;
                add_ssa_edge (gen_ctx, se->def, se->def_op_num, new_bb_insn, 1);
                DEBUG (2, {
                  fprintf (debug_file, "  adding insn ");
                  MIR_output_insn (ctx, debug_file, new_insn, func, FALSE);
                  fprintf (debug_file, "  after def insn ");
                  MIR_output_insn (ctx, debug_file, mem_insn, func, TRUE);
                });
              }
              bitmap_clear_bit_p (curr_available_mem, bb_insn->mem_index);
              bitmap_set_bit_p (removed_mem, bb_insn->mem_index);
              remove_ssa_edge (gen_ctx, (ssa_edge_t) insn->ops[1].data);
              insn->ops[1] = _MIR_new_var_op (ctx, temp_reg); /* changing mem */
              def_insn = DLIST_NEXT (MIR_insn_t, mem_insn);
              add_ssa_edge (gen_ctx, def_insn->data, 0, bb_insn, 1);
              gvn_insns_num++;
              DEBUG (2, {
                fprintf (debug_file, "  changing curr insn to ");
                MIR_output_insn (ctx, debug_file, insn, func, TRUE);
              });
              continue;
            }
          }
          update_mem_availability (gen_ctx, curr_available_mem, bb_insn);
        } else if (move_p (insn) && (se = insn->ops[1].data) != NULL
                   && !fake_insn_p (gen_ctx, se->def)
                   && (se = se->def->insn->ops[se->def_op_num].data) != NULL && se->next_use == NULL
                   && MIR_reg_hard_reg_name (ctx, insn->ops[0].u.var - MAX_HARD_REG, func) == NULL
                   && MIR_reg_hard_reg_name (ctx, insn->ops[1].u.var - MAX_HARD_REG, func)
                        == NULL) {
          /* one source for definition: remove copy */
          gen_assert (se->use == bb_insn && se->use_op_num == 1);
          remove_copy (gen_ctx, insn);
          continue;
        }
        break;
      case MIR_BT:
      case MIR_BTS: const_p = get_gvn_op (gen_ctx, insn, 1, &val); break;
      case MIR_BF:
      case MIR_BFS:
        const_p = get_gvn_op (gen_ctx, insn, 1, &val);
        if (const_p) val = !val;
        break;
      case MIR_BEQ: GVN_ICMP (==); break;
      case MIR_BEQS: GVN_ICMPS (==); break;
      case MIR_BNE: GVN_ICMP (!=); break;
      case MIR_BNES: GVN_ICMPS (!=); break;

      case MIR_BLT: GVN_ICMP (<); break;
      case MIR_BLTS: GVN_ICMPS (<); break;
      case MIR_UBLT: GVN_UCMP (<); break;
      case MIR_UBLTS: GVN_UCMPS (<); break;
      case MIR_BLE: GVN_ICMP (<=); break;
      case MIR_BLES: GVN_ICMPS (<=); break;
      case MIR_UBLE: GVN_UCMP (<=); break;
      case MIR_UBLES: GVN_UCMPS (<=); break;
      case MIR_BGT: GVN_ICMP (>); break;
      case MIR_BGTS: GVN_ICMPS (>); break;
      case MIR_UBGT: GVN_UCMP (>); break;
      case MIR_UBGTS: GVN_UCMPS (>); break;
      case MIR_BGE: GVN_ICMP (>=); break;
      case MIR_BGES: GVN_ICMPS (>=); break;
      case MIR_UBGE: GVN_UCMP (>=); break;
      case MIR_UBGES: GVN_UCMPS (>=); break;
      default: break;
      }
      if (const_p) {
        ccp_insns_num++;
        print_bb_insn_value (gen_ctx, bb_insn);
        if (MIR_any_branch_code_p (insn->code)) {
          gen_assert (insn->code != MIR_SWITCH);
          if (val == 0) {
            DEBUG (2, {
              fprintf (debug_file, "  removing branch insn ");
              MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
              fprintf (debug_file, "\n");
            });
            remove_insn_ssa_edges (gen_ctx, insn);
            gen_delete_insn (gen_ctx, insn);
            edge_t edge = DLIST_EL (out_edge_t, bb->out_edges, 1);
            remove_edge_phi_ops (gen_ctx, edge);
            edge->dst->flag = TRUE; /* to recalculate dst mem_av_in */
            delete_edge (edge);
            deleted_branches_num++;
          } else {
            new_insn = MIR_new_insn (ctx, MIR_JMP, insn->ops[0]); /* label is always 0-th op */
            DEBUG (2, {
              fprintf (debug_file, "  changing branch insn ");
              MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
              fprintf (debug_file, " onto jump insn ");
              MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
              fprintf (debug_file, "\n");
            });
            MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
            remove_insn_ssa_edges (gen_ctx, insn);
            MIR_remove_insn (ctx, curr_func_item, insn);
            new_insn->data = bb_insn;
            bb_insn->insn = new_insn;
            edge_t edge = DLIST_EL (out_edge_t, bb->out_edges, 0);
            remove_edge_phi_ops (gen_ctx, edge);
            edge->dst->flag = TRUE; /* to recalculate dst mem_av_in */
            delete_edge (edge);
          }
        } else { /* x=... and x is const => x=...; x=const */
          new_insn = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], MIR_new_int_op (ctx, val));
          after = insn->code == MIR_PHI ? get_last_bb_phi_insn (gen_ctx, insn) : insn;
          gen_add_insn_after (gen_ctx, after, new_insn);
          new_bb_insn = new_insn->data;
          redirect_def (gen_ctx, insn, new_insn, FALSE);
          new_bb_insn->gvn_val_const_p = TRUE;
          new_bb_insn->gvn_val = val;
          gvn_insns_num++;
          DEBUG (2, {
            fprintf (debug_file, "  Adding insn after:");
            MIR_output_insn (ctx, debug_file, new_insn, func, TRUE);
          });
          print_bb_insn_value (gen_ctx, new_bb_insn);
        }
        continue;
      }
      if (MIR_any_branch_code_p (insn->code) || insn->code == MIR_PHI) continue;
      e = NULL;
      if (move_p (insn)) {
        def_bb_insn = ((ssa_edge_t) insn->ops[1].data)->def;
        copy_gvn_info (bb_insn, def_bb_insn);
      } else if (!MIR_overflow_insn_code_p (insn->code)) {
        /* r=e; ...; x=e => r=e; t=r; ...; x=e; x=t */
        if (!find_expr (gen_ctx, insn, &e)) {
          e = add_expr (gen_ctx, insn, FALSE);
          DEBUG (2, { print_expr (gen_ctx, e, "Adding"); });
        } else if (move_code_p (insn->code) && insn->ops[1].mode == MIR_OP_VAR_MEM
                   && !bitmap_bit_p (curr_available_mem, ((bb_insn_t) e->insn->data)->mem_index)) {
          e = add_expr (gen_ctx, insn, TRUE);
          DEBUG (2, { print_expr (gen_ctx, e, "Replacing"); });
        }
        bb_insn->gvn_val_const_p = FALSE;
        bb_insn->gvn_val = e->num;
        bb_insn->alloca_flag = ((bb_insn_t) e->insn->data)->alloca_flag;
      }
      print_bb_insn_value (gen_ctx, bb_insn);
      if (e == NULL || e->insn == insn || (imm_move_p (insn) && insn->ops[1].mode != MIR_OP_REF))
        continue;
      if (insn->code == MIR_ADDR) {
        continue;
      } else if ((insn->code == MIR_ADD || insn->code == MIR_SUB)
                 && (se = insn->ops[0].data) != NULL && se->next_use == NULL
                 && se->use->insn->ops[se->use_op_num].mode == MIR_OP_VAR_MEM
                 && (((se2 = insn->ops[2].data) != NULL && imm_move_p (se2->def->insn))
                     || (insn->code == MIR_ADD && (se2 = insn->ops[1].data) != NULL
                         && imm_move_p (se2->def->insn)))) {
        /* Do not recalculate reg + const if it is only used in address: */
        int64_t disp = se2->def->insn->ops[1].u.i;
        if (insn->code == MIR_SUB) disp = -disp;
        if (TARGET_MIN_MEM_DISP <= disp && disp <= TARGET_MAX_MEM_DISP) continue;
      }
      expr_bb_insn = e->insn->data;
      if (bb->index != expr_bb_insn->bb->index
          && !bitmap_bit_p (bb->dom_in, expr_bb_insn->bb->index))
        continue;
      add_def_p = e->temp_reg == MIR_NON_VAR;
      temp_reg = get_expr_temp_reg (gen_ctx, e->insn, &e->temp_reg);
      op = _MIR_new_var_op (ctx, temp_reg);
      type = MIR_reg_type (ctx, temp_reg - MAX_HARD_REG, func);
#ifndef NDEBUG
      int out_p;
      MIR_insn_op_mode (ctx, insn, 0, &out_p); /* result here is always 0-th op */
      gen_assert (out_p);
#endif
      move_code = get_move_code (type);
      if (add_def_p) {
        gen_assert (e->insn->ops[0].mode == MIR_OP_VAR);
        new_insn = MIR_new_insn (ctx, move_code, op, _MIR_new_var_op (ctx, e->insn->ops[0].u.var));
        gen_add_insn_after (gen_ctx, e->insn, new_insn);
        new_bb_insn = new_insn->data;
        redirect_def (gen_ctx, e->insn, new_insn, TRUE);
        if (!find_expr (gen_ctx, new_insn, &new_e)) new_e = add_expr (gen_ctx, new_insn, FALSE);
        new_bb_insn->gvn_val_const_p = FALSE;
        new_bb_insn->gvn_val = e->num;
        new_bb_insn->alloca_flag = ((bb_insn_t) e->insn->data)->alloca_flag;
        DEBUG (2, {
          fprintf (debug_file, "  adding insn ");
          MIR_output_insn (ctx, debug_file, new_insn, func, FALSE);
          fprintf (debug_file, "  after def insn ");
          MIR_output_insn (ctx, debug_file, e->insn, func, TRUE);
        });
      }
      new_insn = MIR_new_insn (ctx, move_code, insn->ops[0], op);
      gen_add_insn_after (gen_ctx, insn, new_insn);
      new_bb_insn = new_insn->data;
      redirect_def (gen_ctx, insn, new_insn, FALSE);
      def_insn = DLIST_NEXT (MIR_insn_t, e->insn);
      add_ssa_edge (gen_ctx, def_insn->data, 0, new_insn->data, 1);
      if (!find_expr (gen_ctx, new_insn, &new_e)) new_e = add_expr (gen_ctx, new_insn, FALSE);
      new_bb_insn->gvn_val_const_p = FALSE;
      new_bb_insn->gvn_val = e->num;
      new_bb_insn->alloca_flag = ((bb_insn_t) e->insn->data)->alloca_flag;
      gvn_insns_num++;
      DEBUG (2, {
        fprintf (debug_file, "  adding insn ");
        MIR_output_insn (ctx, debug_file, new_insn, func, FALSE);
        fprintf (debug_file, "  after use insn ");
        MIR_output_insn (ctx, debug_file, insn, func, TRUE);
      });
    }
  }
  DEBUG (1, {
    fprintf (debug_file,
             "%5ld found GVN redundant insns, %ld ccp insns, %ld deleted "
             "branches\n",
             gvn_insns_num, ccp_insns_num, deleted_branches_num);
  });
}

static void gvn (gen_ctx_t gen_ctx) {
  calculate_memory_availability (gen_ctx);
  calculate_dominators (gen_ctx);
  VARR_TRUNC (bb_t, worklist, 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    VARR_PUSH (bb_t, worklist, bb);
  qsort (VARR_ADDR (bb_t, worklist), VARR_LENGTH (bb_t, worklist), sizeof (bb_t), post_cmp);
  gvn_modify (gen_ctx);
}

static void gvn_clear (gen_ctx_t gen_ctx) {
  HTAB_CLEAR (expr_t, expr_tab);
  while (VARR_LENGTH (expr_t, exprs) != 0) free (VARR_POP (expr_t, exprs));
  HTAB_CLEAR (mem_expr_t, mem_expr_tab);
  while (VARR_LENGTH (mem_expr_t, mem_exprs) != 0) free (VARR_POP (mem_expr_t, mem_exprs));
}

static void init_gvn (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;

  gen_ctx->gvn_ctx = gen_malloc (gen_ctx, sizeof (struct gvn_ctx));
  VARR_CREATE (expr_t, exprs, 512);
  HTAB_CREATE (expr_t, expr_tab, 1024, expr_hash, expr_eq, gen_ctx);
  temp_mem_insn
    = MIR_new_insn (ctx, MIR_MOV,
                    _MIR_new_var_mem_op (ctx, MIR_T_I64, 0, MIR_NON_VAR, MIR_NON_VAR, 0),
                    _MIR_new_var_op (ctx, 0));
  VARR_CREATE (mem_expr_t, mem_exprs, 256);
  HTAB_CREATE (mem_expr_t, mem_expr_tab, 512, mem_expr_hash, mem_expr_eq, gen_ctx);
  VARR_CREATE (insn_nop_pair_t, insn_nop_pairs, 16);
}

static void finish_gvn (gen_ctx_t gen_ctx) {
  VARR_DESTROY (expr_t, exprs);
  HTAB_DESTROY (expr_t, expr_tab);
  free (temp_mem_insn); /* ??? */
  VARR_DESTROY (mem_expr_t, mem_exprs);
  HTAB_DESTROY (mem_expr_t, mem_expr_tab);
  VARR_DESTROY (insn_nop_pair_t, insn_nop_pairs);
  free (gen_ctx->gvn_ctx);
  gen_ctx->gvn_ctx = NULL;
}

/* New page */

/* Dead store elimination */

#define mem_live_in in
#define mem_live_out out
#define mem_live_gen gen
#define mem_live_kill kill

static void mem_live_con_func_0 (bb_t bb) {
  if (bb->index != 1) bitmap_clear (bb->mem_live_in);
}

static int mem_live_con_func_n (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;
  int change_p = FALSE;

  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    change_p |= bitmap_ior (bb->mem_live_out, bb->mem_live_out, e->dst->mem_live_in);
  return change_p;
}

static int mem_live_trans_func (gen_ctx_t gen_ctx, bb_t bb) {
  return bitmap_ior_and_compl (bb->mem_live_in, bb->mem_live_gen, bb->mem_live_out,
                               bb->mem_live_kill);
}

static int alloca_arg_p (gen_ctx_t gen_ctx, MIR_insn_t call_insn) {
  MIR_proto_t proto;
  ssa_edge_t se;

  gen_assert (MIR_call_code_p (call_insn->code) && call_insn->ops[0].mode == MIR_OP_REF
              && call_insn->ops[0].u.ref->item_type == MIR_proto_item);
  proto = call_insn->ops[0].u.ref->u.proto;
  for (size_t i = proto->nres + 1; i < call_insn->nops; i++) {
    if (call_insn->ops[i].mode != MIR_OP_VAR && call_insn->ops[i].mode != MIR_OP_VAR_MEM) continue;
    if ((se = call_insn->ops[i].data) == NULL) continue;
    if ((se->def->alloca_flag & MUST_ALLOCA) || (se->def->alloca_flag & MAY_ALLOCA)) return TRUE;
  }
  return FALSE;
}

static void update_call_mem_live (gen_ctx_t gen_ctx, bitmap_t mem_live, MIR_insn_t call_insn) {
  gen_assert (MIR_call_code_p (call_insn->code));
  gen_assert (call_insn->ops[0].mode == MIR_OP_REF
              && call_insn->ops[0].u.ref->item_type == MIR_proto_item);
  if (full_escape_p || alloca_arg_p (gen_ctx, call_insn)) {
    bitmap_set_bit_range_p (mem_live, 1, VARR_LENGTH (mem_attr_t, mem_attrs));
  } else {
    mem_attr_t *mem_attr_addr = VARR_ADDR (mem_attr_t, mem_attrs);

    for (size_t i = 1; i < VARR_LENGTH (mem_attr_t, mem_attrs); i++)
      if (!mem_attr_addr[i].alloca_flag) bitmap_set_bit_p (mem_live, i);
  }
}

static int alloca_mem_intersect_p (gen_ctx_t gen_ctx, uint32_t nloc1, MIR_type_t type1,
                                   uint32_t nloc2, MIR_type_t type2) {
  MIR_context_t ctx = gen_ctx->ctx;
  mem_attr_t *mem_attr_ref1 = &VARR_ADDR (mem_attr_t, mem_attrs)[nloc1];
  mem_attr_t *mem_attr_ref2 = &VARR_ADDR (mem_attr_t, mem_attrs)[nloc2];
  int64_t disp1, disp2, size1, size2;

  gen_assert (nloc1 != 0 && nloc2 != 0);
  if (!mem_attr_ref1->disp_def_p || !mem_attr_ref2->disp_def_p) return TRUE;
  if (mem_attr_ref1->def_insn == NULL || mem_attr_ref1->def_insn != mem_attr_ref2->def_insn)
    return TRUE;
  disp1 = mem_attr_ref1->disp;
  disp2 = mem_attr_ref2->disp;
  size1 = _MIR_type_size (ctx, type1);
  size2 = _MIR_type_size (ctx, type2);
  if (disp2 <= disp1 && disp1 < disp2 + size2) return TRUE;
  return disp1 <= disp2 && disp2 < disp1 + size1;
}

static void make_live_from_mem (gen_ctx_t gen_ctx, MIR_op_t *mem_ref, bitmap_t gen, bitmap_t kill,
                                int must_alloca_p) {
  mem_attr_t *mem_attr_addr = VARR_ADDR (mem_attr_t, mem_attrs);

  gen_assert (mem_ref->mode == MIR_OP_VAR_MEM);
  for (size_t i = 1; i < VARR_LENGTH (mem_attr_t, mem_attrs); i++) {
    if (!may_alias_p (mem_ref->u.var_mem.alias, mem_attr_addr[i].alias, mem_ref->u.var_mem.nonalias,
                      mem_attr_addr[i].nonalias))
      continue;
    if (must_alloca_p && (mem_attr_addr[i].alloca_flag & MUST_ALLOCA)
        && !alloca_mem_intersect_p (gen_ctx, mem_ref->u.var_mem.nloc, mem_ref->u.var_mem.type, i,
                                    mem_attr_addr[i].type))
      continue;
    /* all aliased but unintersected must alloca: */
    bitmap_set_bit_p (gen, i);
    if (kill != NULL) bitmap_clear_bit_p (kill, i);
  }
}

static MIR_insn_t initiate_bb_mem_live_info (gen_ctx_t gen_ctx, MIR_insn_t bb_tail_insn) {
  bb_t bb = get_insn_bb (gen_ctx, bb_tail_insn);
  MIR_insn_t insn;
  ssa_edge_t se;
  uint32_t nloc;

  for (insn = bb_tail_insn; insn != NULL && get_insn_bb (gen_ctx, insn) == bb;
       insn = DLIST_PREV (MIR_insn_t, insn)) {
    if (MIR_call_code_p (insn->code)) update_call_mem_live (gen_ctx, bb->mem_live_gen, insn);
    if (!move_code_p (insn->code)) continue;
    if (insn->ops[0].mode == MIR_OP_VAR_MEM) { /* store */
      if ((nloc = insn->ops[0].u.var_mem.nloc) != 0) {
        bitmap_clear_bit_p (bb->mem_live_gen, nloc);
        bitmap_set_bit_p (bb->mem_live_kill, nloc);
      }
    } else if (insn->ops[1].mode == MIR_OP_VAR_MEM) { /* load */
      if ((nloc = insn->ops[1].u.var_mem.nloc) != 0) {
        bitmap_set_bit_p (bb->mem_live_gen, nloc);
        bitmap_clear_bit_p (bb->mem_live_kill, nloc);
        se = insn->ops[1].data;
        make_live_from_mem (gen_ctx, &insn->ops[1], bb->mem_live_gen, bb->mem_live_kill,
                            se != NULL && (se->def->alloca_flag & MUST_ALLOCA));
      } else {
        bitmap_set_bit_range_p (bb->mem_live_gen, 1, VARR_LENGTH (mem_attr_t, mem_attrs));
      }
    }
  }
  return insn;
}

static void initiate_mem_live_info (gen_ctx_t gen_ctx) {
  bb_t exit_bb = DLIST_EL (bb_t, curr_cfg->bbs, 1);
  mem_attr_t *mem_attr_addr;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    gen_assert (bb->mem_live_in != NULL && bb->mem_live_out != NULL && bb->mem_live_gen != NULL
                && bb->mem_live_kill != NULL);
    bitmap_clear (bb->mem_live_in);
    bitmap_clear (bb->mem_live_out);
    bitmap_clear (bb->mem_live_gen);
    bitmap_clear (bb->mem_live_kill);
  }
  for (MIR_insn_t tail = DLIST_TAIL (MIR_insn_t, curr_func_item->u.func->insns); tail != NULL;)
    tail = initiate_bb_mem_live_info (gen_ctx, tail);
  mem_attr_addr = VARR_ADDR (mem_attr_t, mem_attrs);
  for (size_t i = 1; i < VARR_LENGTH (mem_attr_t, mem_attrs); i++) {
    if (mem_attr_addr[i].alloca_flag & MUST_ALLOCA) continue; /* skip alloca memory */
    bitmap_set_bit_p (exit_bb->mem_live_in, i);
    bitmap_set_bit_p (exit_bb->mem_live_out, i);
  }
}

static void print_mem_bb_live_info (gen_ctx_t gen_ctx, bb_t bb) {
  fprintf (debug_file, "BB %3lu:\n", (unsigned long) bb->index);
  output_bitmap (gen_ctx, "   Mem live in:", bb->mem_live_in, FALSE);
  output_bitmap (gen_ctx, "   Mem live out:", bb->mem_live_out, FALSE);
  output_bitmap (gen_ctx, "   Mem live gen:", bb->mem_live_gen, FALSE);
  output_bitmap (gen_ctx, "   Mem live kill:", bb->mem_live_kill, FALSE);
}

static void calculate_mem_live_info (gen_ctx_t gen_ctx) {
  initiate_mem_live_info (gen_ctx);
  solve_dataflow (gen_ctx, FALSE, mem_live_con_func_0, mem_live_con_func_n, mem_live_trans_func);
  DEBUG (2, {
    for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
      print_mem_bb_live_info (gen_ctx, bb);
  });
}

static void dse (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  uint32_t nloc;
  long dead_stores_num = 0;
  ssa_edge_t se;
  bb_insn_t bb_insn, prev_bb_insn;
  bitmap_t live = temp_bitmap;

  calculate_mem_live_info (gen_ctx);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->mem_live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      if (MIR_call_code_p (insn->code)) update_call_mem_live (gen_ctx, live, insn);
      if (!move_code_p (insn->code)) continue;
      if (insn->ops[0].mode == MIR_OP_VAR_MEM) { /* store */
        if ((nloc = insn->ops[0].u.var_mem.nloc) != 0) {
          if (!bitmap_clear_bit_p (live, nloc)) {
            DEBUG (2, {
              fprintf (debug_file, "Removing dead store ");
              print_bb_insn (gen_ctx, bb_insn, FALSE);
            });
            remove_ssa_edge (gen_ctx, insn->ops[0].data);
            remove_ssa_edge (gen_ctx, insn->ops[1].data);
            gen_delete_insn (gen_ctx, insn);
            dead_stores_num++;
          }
        }
      } else if (insn->ops[1].mode == MIR_OP_VAR_MEM) { /* load */
        if ((nloc = insn->ops[1].u.var_mem.nloc) != 0) {
          bitmap_set_bit_p (live, nloc);
          se = insn->ops[1].data;
          make_live_from_mem (gen_ctx, &insn->ops[1], live, NULL,
                              se != NULL && (se->def->alloca_flag & MUST_ALLOCA));
        } else {
          bitmap_set_bit_range_p (live, 1, VARR_LENGTH (mem_attr_t, mem_attrs));
        }
      }
    }
  }
  DEBUG (1, { fprintf (debug_file, "%5ld removed dead stores\n", dead_stores_num); });
}

#undef mem_live_in
#undef mem_live_out
#undef mem_live_gen
#undef mem_live_kill

/* New Page */

/* Loop invariant motion */

static edge_t find_loop_entry_edge (gen_ctx_t gen_ctx, bb_t loop_entry) {
  edge_t e, entry_e = NULL;
  bb_insn_t head, tail;

  for (e = DLIST_HEAD (in_edge_t, loop_entry->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    if (e->back_edge_p) continue;
    if (entry_e != NULL) return NULL;
    entry_e = e;
  }
  if (entry_e == NULL) return NULL; /* unreachable loop */
  tail = DLIST_TAIL (bb_insn_t, entry_e->src->bb_insns);
  head = DLIST_HEAD (bb_insn_t, entry_e->dst->bb_insns);
  if (tail != NULL && head != NULL && DLIST_NEXT (MIR_insn_t, tail->insn) != head->insn)
    return NULL; /* not fall through */
  return entry_e;
}

static void create_preheader_from_edge (gen_ctx_t gen_ctx, edge_t e, loop_node_t loop) {
  bb_t new_bb = create_bb (gen_ctx, NULL);
  loop_node_t bb_loop_node = create_loop_node (gen_ctx, new_bb), parent = loop->parent;

  add_new_bb (gen_ctx, new_bb);
  DLIST_REMOVE (bb_t, curr_cfg->bbs, new_bb);
  DLIST_INSERT_BEFORE (bb_t, curr_cfg->bbs, e->dst, new_bb); /* insert before loop entry */
  create_edge (gen_ctx, e->src, new_bb, TRUE, FALSE); /* fall through should be the 1st edge */
  create_edge (gen_ctx, new_bb, e->dst, TRUE, FALSE);
  delete_edge (e);
  gen_assert (parent != NULL);
  DLIST_APPEND (loop_node_t, parent->children, bb_loop_node);
  bb_loop_node->parent = parent;
  loop->preheader = new_bb;
}

static void licm_add_loop_preheaders (gen_ctx_t gen_ctx, loop_node_t loop) {
  int subloop_p = FALSE;
  bb_insn_t bb_insn;
  edge_t e;

  for (loop_node_t node = DLIST_HEAD (loop_node_t, loop->children); node != NULL;
       node = DLIST_NEXT (loop_node_t, node))
    if (node->bb == NULL) {
      subloop_p = TRUE;
      licm_add_loop_preheaders (gen_ctx, node); /* process sub-loops */
    }
  /* See loop_licm where we process only the nested loops: */
  if (subloop_p || loop == curr_cfg->root_loop_node) return;
  loop->preheader = NULL;
  if ((e = find_loop_entry_edge (gen_ctx, loop->entry->bb)) == NULL) return;
  if ((bb_insn = DLIST_TAIL (bb_insn_t, e->src->bb_insns)) == NULL
      || !MIR_any_branch_code_p (bb_insn->insn->code))
    loop->preheader = e->src; /* The preheader already exists */
  else
    create_preheader_from_edge (gen_ctx, e, loop);
}

static int loop_invariant_p (gen_ctx_t gen_ctx, loop_node_t loop, bb_insn_t bb_insn) {
  MIR_insn_t insn = bb_insn->insn;
  bb_t bb = bb_insn->bb;
  loop_node_t curr_loop;
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  ssa_edge_t se;
  insn_var_iterator_t iter;

  if (MIR_any_branch_code_p (insn->code) || insn->code == MIR_RET || insn->code == MIR_JRET
      || insn->code == MIR_LABEL || MIR_call_code_p (insn->code) || insn->code == MIR_ALLOCA
      || insn->code == MIR_BSTART || insn->code == MIR_BEND || insn->code == MIR_VA_START
      || insn->code == MIR_VA_ARG || insn->code == MIR_VA_END
      || (insn->code == MIR_MOV
          && (insn->ops[1].mode != MIR_OP_REF
              || (get_ref_value (gen_ctx, &insn->ops[1]) >> 32) != 0)))
    return FALSE;
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
    if (mem_p) return FALSE;
    if (out_p) continue;
    se = insn->ops[op_num].data;
    gen_assert (se != NULL);
    bb_insn = se->def;
    bb = bb_insn->bb;
    for (curr_loop = loop->parent; curr_loop != NULL; curr_loop = curr_loop->parent)
      if (curr_loop == bb->loop_node) break;
    if (curr_loop == NULL) return FALSE;
  }
  return TRUE;
}

static void licm_move_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn, bb_t to, bb_insn_t before) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t bb = bb_insn->bb;
  MIR_insn_t insn = bb_insn->insn;

  gen_assert (before != NULL);
  DLIST_REMOVE (bb_insn_t, bb->bb_insns, bb_insn);
  DLIST_APPEND (bb_insn_t, to->bb_insns, bb_insn);
  bb_insn->bb = to;
  DLIST_REMOVE (MIR_insn_t, curr_func_item->u.func->insns, insn);
  MIR_insert_insn_before (ctx, curr_func_item, before->insn, insn);
}

static int loop_licm (gen_ctx_t gen_ctx, loop_node_t loop) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  loop_node_t node;
  int subloop_p = FALSE, move_p = FALSE, op_num, out_p, mem_p;
  MIR_reg_t var;
  insn_var_iterator_t iter;
  bitmap_t loop_invariant_bb_insn_bitmap = temp_bitmap;
  VARR (bb_insn_t) *loop_invariant_bb_insns = temp_bb_insns;

  for (node = DLIST_HEAD (loop_node_t, loop->children); node != NULL;
       node = DLIST_NEXT (loop_node_t, node))
    if (node->bb == NULL) {
      subloop_p = TRUE;
      if (loop_licm (gen_ctx, node)) move_p = TRUE; /* process sub-loops first */
    }
  if (subloop_p || curr_cfg->root_loop_node == loop || loop->preheader == NULL)
    return move_p; /* e.g. root or unreachable root */
  DEBUG (2, {
    fprintf (debug_file, "Processing Loop%3lu for loop invariant motion:\n",
             (unsigned long) loop->index);
  });
  VARR_TRUNC (bb_insn_t, loop_invariant_bb_insns, 0);
  bitmap_clear (loop_invariant_bb_insn_bitmap);
  for (node = DLIST_HEAD (loop_node_t, loop->children); node != NULL;
       node = DLIST_NEXT (loop_node_t, node)) {
    if (node->bb == NULL) continue; /* skip subloops */
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, node->bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      if (loop_invariant_p (gen_ctx, loop, bb_insn))
        VARR_PUSH (bb_insn_t, loop_invariant_bb_insns, bb_insn);
  }
  while (VARR_LENGTH (bb_insn_t, loop_invariant_bb_insns) != 0) {
    bb_insn = VARR_POP (bb_insn_t, loop_invariant_bb_insns);
    insn = bb_insn->insn;
    DEBUG (2, {
      fprintf (debug_file, "  Move invariant ");
      print_bb_insn (gen_ctx, bb_insn, FALSE);
    });
    move_p = TRUE;
    licm_move_insn (gen_ctx, bb_insn, loop->preheader,
                    DLIST_HEAD (bb_insn_t, loop->entry->bb->bb_insns));
    FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
      if (!out_p) continue;
      for (ssa_edge_t se = insn->ops[op_num].data; se != NULL; se = se->next_use) {
        if (loop_invariant_p (gen_ctx, loop, se->use)
            && bitmap_set_bit_p (loop_invariant_bb_insn_bitmap, se->use->index))
          VARR_PUSH (bb_insn_t, loop_invariant_bb_insns, se->use);
      }
    }
  }
  return move_p;
}

static int licm (gen_ctx_t gen_ctx) {
  loop_node_t node;
  for (node = DLIST_HEAD (loop_node_t, curr_cfg->root_loop_node->children); node != NULL;
       node = DLIST_NEXT (loop_node_t, node))
    if (node->bb == NULL) break;
  if (node == NULL) return FALSE; /* no loops */
  licm_add_loop_preheaders (gen_ctx, curr_cfg->root_loop_node);
  return loop_licm (gen_ctx, curr_cfg->root_loop_node);
}

/* New Page */

/* Pressure relief */

static int pressure_relief (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func = curr_func_item->u.func;
  MIR_insn_t insn;
  bb_insn_t bb_insn, next_bb_insn, use;
  loop_node_t loop;
  ssa_edge_t se;
  int moved_p = FALSE;

  DEBUG (2, { fprintf (debug_file, "+++++++++++++Pressure Relief:\n"); });
  gen_assert (def_use_repr_p);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      if (!move_code_p (insn->code) || insn->ops[0].mode != MIR_OP_VAR
          || insn->ops[1].mode == MIR_OP_VAR || insn->ops[1].mode == MIR_OP_VAR_MEM
          || (se = insn->ops[0].data) == NULL || se->next_use != NULL || (use = se->use)->bb == bb
          || use->insn->code == MIR_PHI)
        continue;
      if ((loop = use->bb->loop_node) != NULL) {
        for (loop = loop->parent; loop != NULL; loop = loop->parent)
          if (loop == bb->loop_node->parent) break;
        if (loop != NULL) continue; /* avoid move into a loop */
      }
      /* One use in another BB: move closer */
      DEBUG (2, {
        fprintf (debug_file, "  Move insn %-5lu", (unsigned long) bb_insn->index);
        MIR_output_insn (ctx, debug_file, insn, func, FALSE);
        fprintf (debug_file, "  before insn %-5lu", (unsigned long) use->index);
        MIR_output_insn (ctx, debug_file, use->insn, func, TRUE);
      });
      gen_move_insn_before (gen_ctx, use->insn, insn);
      moved_p = TRUE;
    }
  return moved_p;
}

/* New page */

/* Jump optimizations */

/* Remove empty blocks, branches to next insn, change branches to
   jumps.  ??? consider switch as a branch. */
static void jump_opt (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t bb, next_bb;
  int maybe_unreachable_bb_p = FALSE;
  long bb_deleted_insns_num;

  if ((bb_deleted_insns_num = remove_unreachable_bbs (gen_ctx)) != 0) {
    DEBUG (1, { fprintf (debug_file, "%ld deleted unrechable bb insns\n", bb_deleted_insns_num); });
  }
  bitmap_clear (temp_bitmap);
  for (bb = DLIST_EL (bb_t, curr_cfg->bbs, 2); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bb_insn_t bb_insn;
    int i, start_nop, bound_nop;

    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL) continue;
    if (bb_insn->insn->code == MIR_SWITCH) {
      start_nop = 1;
      bound_nop = bb_insn->insn->nops;
    } else if (MIR_branch_code_p (bb_insn->insn->code)) {
      start_nop = 0;
      bound_nop = 1;
    } else {
      continue;
    }
    for (i = start_nop; i < bound_nop; i++)
      bitmap_set_bit_p (temp_bitmap, bb_insn->insn->ops[i].u.label->ops[0].u.u);
  }
  for (bb = DLIST_EL (bb_t, curr_cfg->bbs, 2); bb != NULL; bb = next_bb) {
    edge_t e, out_e;
    bb_insn_t label_bb_insn, last_label_bb_insn, bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
    MIR_insn_t insn, next_insn, last_label;

    next_bb = DLIST_NEXT (bb_t, bb);
    if (bb->index != 2 /* BB2 will be used for machinize */
        && (e = DLIST_HEAD (in_edge_t, bb->in_edges)) != NULL && DLIST_NEXT (in_edge_t, e) == NULL
        && (bb_insn == NULL
            || ((insn = bb_insn->insn)->code == MIR_LABEL && DLIST_NEXT (bb_insn_t, bb_insn) == NULL
                && DLIST_PREV (bb_insn_t, bb_insn) == NULL
                && !bitmap_bit_p (temp_bitmap, insn->ops[0].u.u)))) {
      /* empty bb or bb with the only label which can be removed. we can have more one the same
         dest edge (e.g. when removed cond branch to the next insn). */
      out_e = DLIST_HEAD (out_edge_t, bb->out_edges);
      gen_assert (out_e != NULL);
      e->dst = out_e->dst;
      DLIST_REMOVE (in_edge_t, bb->in_edges, e);
      DLIST_INSERT_BEFORE (in_edge_t, out_e->dst->in_edges, out_e, e);
      gen_assert (DLIST_HEAD (in_edge_t, bb->in_edges) == NULL);
      /* Don't shorten phis in dest bbs. We don't care about SSA in this kind of bb. */
      remove_bb (gen_ctx, bb);
      continue;
    }
    if (bb_insn == NULL) continue;
    insn = bb_insn->insn;
    if (!MIR_branch_code_p (insn->code)) continue;
    DEBUG (2, { fprintf (debug_file, "  BB%lu:\n", (unsigned long) bb->index); });
    gen_assert (insn->ops[0].mode == MIR_OP_LABEL);
    if ((next_insn = DLIST_NEXT (MIR_insn_t, insn)) != NULL && next_insn->code == MIR_LABEL
        && next_insn == insn->ops[0].u.label) {
      DEBUG (2, {
        fprintf (debug_file, "  Removing trivial branch insn ");
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
      });
      out_e = DLIST_HEAD (out_edge_t, bb->out_edges);
      out_e->fall_through_p = TRUE;
      e = DLIST_NEXT (out_edge_t, out_e);
      gen_assert (e == NULL || DLIST_NEXT (out_edge_t, e) == NULL);
      if (e != NULL) delete_edge (e);
      gen_delete_insn (gen_ctx, insn);
      next_bb = bb; /* bb can became empty after removing jump.  */
    } else {
      for (;;) {
        for (last_label = insn->ops[0].u.label;
             (next_insn = DLIST_NEXT (MIR_insn_t, last_label)) != NULL
             && next_insn->code == MIR_LABEL;)
          last_label = next_insn;
        if ((next_insn = DLIST_NEXT (MIR_insn_t, last_label)) != NULL
            && next_insn->code == MIR_JMP) {
          last_label = next_insn->ops[0].u.label;
        }
        if (insn->ops[0].u.label == last_label) break;
        DEBUG (2, {
          fprintf (debug_file, "  Changing label in branch insn ");
          MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
        });
        label_bb_insn = insn->ops[0].u.label->data;
        insn->ops[0].u.label = last_label;
        last_label_bb_insn = last_label->data;
        gen_assert (label_bb_insn->bb != last_label_bb_insn->bb);
        e = find_edge (bb, label_bb_insn->bb);
        e->dst = last_label_bb_insn->bb;
        DLIST_REMOVE (in_edge_t, label_bb_insn->bb->in_edges, e);
        /* We don't need to keep the edge order as we are already off SSA: */
        DLIST_APPEND (in_edge_t, e->dst->in_edges, e);
        DEBUG (2, {
          fprintf (debug_file, "  , result insn ");
          MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        });
        maybe_unreachable_bb_p = TRUE;
      }
    }
  }
  /* Don't shorten phis in dest bbs. We don't care about SSA for new trivial unreachable bbs. */
  if (maybe_unreachable_bb_p) remove_unreachable_bbs (gen_ctx);
  enumerate_bbs (gen_ctx);
}

/* New Page */

#define live_in in
#define live_out out
#define live_kill kill
#define live_gen gen

/* Life analysis */
static void live_con_func_0 (bb_t bb) {}

static int live_con_func_n (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;
  int change_p = FALSE;

  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    change_p |= bitmap_ior (bb->live_out, bb->live_out, e->dst->live_in);
  return change_p;
}

static int live_trans_func (gen_ctx_t gen_ctx, bb_t bb) {
  return bitmap_ior_and_compl (bb->live_in, bb->live_gen, bb->live_out, bb->live_kill);
}

static int bb_loop_level (bb_t bb) {
  loop_node_t loop_node;
  int level = -1;

  for (loop_node = bb->loop_node; loop_node->parent != NULL; loop_node = loop_node->parent) level++;
  gen_assert (level >= 0);
  return level;
}

static void increase_pressure (int int_p, bb_t bb, int *int_pressure, int *fp_pressure) {
  if (int_p) {
    if (bb->max_int_pressure < ++(*int_pressure)) bb->max_int_pressure = *int_pressure;
  } else {
    if (bb->max_fp_pressure < ++(*fp_pressure)) bb->max_fp_pressure = *fp_pressure;
  }
}

static int int_var_type_p (gen_ctx_t gen_ctx, MIR_reg_t var) {
  if (var <= MAX_HARD_REG) return target_hard_reg_type_ok_p (var, MIR_T_I32);
  return MIR_int_type_p (MIR_reg_type (gen_ctx->ctx, var - MAX_HARD_REG, curr_func_item->u.func));
}

static MIR_insn_t initiate_bb_live_info (gen_ctx_t gen_ctx, MIR_insn_t bb_tail_insn, int freq_p) {
  bb_t bb = get_insn_bb (gen_ctx, bb_tail_insn);
  MIR_insn_t insn;
  size_t niter, bb_freq;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, mem_p, int_p = FALSE;
  int bb_int_pressure, bb_fp_pressure;
  reg_info_t *reg_infos;
  insn_var_iterator_t insn_var_iter;
  bitmap_t global_hard_regs
    = _MIR_get_module_global_var_hard_regs (gen_ctx->ctx, curr_func_item->module);

  reg_infos = VARR_ADDR (reg_info_t, curr_cfg->reg_info);
  bb_freq = 1;
  if (optimize_level != 0 && freq_p)
    for (int i = bb_loop_level (bb); i > 0; i--)
      if (bb_freq < SIZE_MAX / 8) bb_freq *= LOOP_COST_FACTOR;
  bb->max_int_pressure = bb_int_pressure = bb->max_fp_pressure = bb_fp_pressure = 0;
  for (insn = bb_tail_insn; insn != NULL && get_insn_bb (gen_ctx, insn) == bb;
       insn = DLIST_PREV (MIR_insn_t, insn)) {
    if (MIR_call_code_p (insn->code)) {
      bitmap_ior (bb->live_kill, bb->live_kill, call_used_hard_regs[MIR_T_UNDEF]);
      if (global_hard_regs != NULL)
        bitmap_ior_and_compl (bb->live_gen, global_hard_regs, bb->live_gen,
                              call_used_hard_regs[MIR_T_UNDEF]);
      else
        bitmap_and_compl (bb->live_gen, bb->live_gen, call_used_hard_regs[MIR_T_UNDEF]);
    }
    /* Process output ops on 0-th iteration, then input ops. */
    for (niter = 0; niter <= 1; niter++) {
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
        if (!out_p && niter != 0) {
          if (bitmap_set_bit_p (bb->live_gen, var) && optimize_level != 0)
            increase_pressure (int_var_type_p (gen_ctx, var), bb, &bb_int_pressure,
                               &bb_fp_pressure);
        } else if (niter == 0) {
          if (bitmap_clear_bit_p (bb->live_gen, var) && optimize_level != 0)
            (int_var_type_p (gen_ctx, var) ? bb_int_pressure-- : bb_fp_pressure--);
          bitmap_set_bit_p (bb->live_kill, var);
        }
        if (freq_p && var > MAX_HARD_REG) {
          if (reg_infos[var].freq < LONG_MAX - bb_freq)
            reg_infos[var].freq += bb_freq;
          else
            reg_infos[var].freq = LONG_MAX;
        }
      }
    }
    target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                          &early_clobbered_hard_reg2);
    if (early_clobbered_hard_reg1 != MIR_NON_VAR) {
      if (optimize_level != 0) {
        int_p = int_var_type_p (gen_ctx, early_clobbered_hard_reg1);
        increase_pressure (int_p, bb, &bb_int_pressure, &bb_fp_pressure);
      }
      bitmap_clear_bit_p (bb->live_gen, early_clobbered_hard_reg1);
      bitmap_set_bit_p (bb->live_kill, early_clobbered_hard_reg1);
      if (optimize_level != 0) (int_p ? bb_int_pressure-- : bb_fp_pressure--);
    }
    if (early_clobbered_hard_reg2 != MIR_NON_VAR) {
      if (optimize_level != 0) {
        int_p = int_var_type_p (gen_ctx, early_clobbered_hard_reg2);
        increase_pressure (int_p, bb, &bb_int_pressure, &bb_fp_pressure);
      }
      bitmap_clear_bit_p (bb->live_gen, early_clobbered_hard_reg2);
      bitmap_set_bit_p (bb->live_kill, early_clobbered_hard_reg2);
      if (optimize_level != 0) (int_p ? bb_int_pressure-- : bb_fp_pressure--);
    }
    if (MIR_call_code_p (insn->code)) {
      bitmap_t reg_args;

      if (optimize_level != 0)
        bitmap_ior (bb->live_gen, bb->live_gen, ((bb_insn_t) insn->data)->call_hard_reg_args);
      else if ((reg_args = ((insn_data_t) insn->data)->u.call_hard_reg_args) != NULL)
        bitmap_ior (bb->live_gen, bb->live_gen, reg_args);
    }
  }
  return insn;
}

static void initiate_live_info (gen_ctx_t gen_ctx, int freq_p) {
  MIR_reg_t max_var, n;
  reg_info_t ri;
  bitmap_t global_hard_regs
    = _MIR_get_module_global_var_hard_regs (gen_ctx->ctx, curr_func_item->module);

  VARR_TRUNC (reg_info_t, curr_cfg->reg_info, 0);
  max_var = get_max_var (gen_ctx);
  for (n = 0; n <= max_var; n++) {
    ri.freq = 0;
    ri.live_length = 0;
    VARR_PUSH (reg_info_t, curr_cfg->reg_info, ri);
  }
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    gen_assert (bb != NULL && bb->live_in != NULL && bb->live_out != NULL && bb->live_gen != NULL
                && bb->live_kill != NULL);
    bitmap_clear (bb->live_in);
    bitmap_clear (bb->live_out);
    bitmap_clear (bb->live_gen);
    bitmap_clear (bb->live_kill);
  }
  if (global_hard_regs != NULL)
    bitmap_copy (DLIST_EL (bb_t, curr_cfg->bbs, 1)->live_out, global_hard_regs); /* exit bb */
  for (MIR_insn_t tail = DLIST_TAIL (MIR_insn_t, curr_func_item->u.func->insns); tail != NULL;)
    tail = initiate_bb_live_info (gen_ctx, tail, freq_p);
}

static void update_bb_pressure (gen_ctx_t gen_ctx) {
  size_t nel;
  bitmap_iterator_t bi;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    int int_pressure = bb->max_int_pressure, fp_pressure = bb->max_fp_pressure;

    FOREACH_BITMAP_BIT (bi, bb->live_out, nel) {
      increase_pressure (int_var_type_p (gen_ctx, (MIR_reg_t) nel), bb, &int_pressure,
                         &fp_pressure);
    }
  }
}

static void calculate_func_cfg_live_info (gen_ctx_t gen_ctx, int freq_p) {
  initiate_live_info (gen_ctx, freq_p);
  solve_dataflow (gen_ctx, FALSE, live_con_func_0, live_con_func_n, live_trans_func);
  if (optimize_level != 0) update_bb_pressure (gen_ctx);
}

static void add_bb_insn_dead_vars (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, mem_p;
  bitmap_t live;
  insn_var_iterator_t insn_var_iter;

  gen_assert (optimize_level > 0); /* we need bb insns to keep dead var info */
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      clear_bb_insn_dead_vars (gen_ctx, bb_insn);
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
        if (out_p) bitmap_clear_bit_p (live, var);
      }
      if (MIR_call_code_p (insn->code))
        bitmap_and_compl (live, live, call_used_hard_regs[MIR_T_UNDEF]);
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
        if (out_p) continue;
        if (bitmap_set_bit_p (live, var)) add_bb_insn_dead_var (gen_ctx, bb_insn, var);
      }
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_VAR)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_VAR)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg2);
      if (MIR_call_code_p (insn->code)) bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
}

#if !MIR_NO_GEN_DEBUG
static void output_bb_border_live_info (gen_ctx_t gen_ctx, bb_t bb) {
  output_bitmap (gen_ctx, "  live_in:", bb->live_in, TRUE);
  output_bitmap (gen_ctx, "  live_out:", bb->live_out, TRUE);
}

static void output_bb_live_info (gen_ctx_t gen_ctx, bb_t bb) {
  output_bb_border_live_info (gen_ctx, bb);
  output_bitmap (gen_ctx, "  live_gen:", bb->live_gen, TRUE);
  output_bitmap (gen_ctx, "  live_kill:", bb->live_kill, TRUE);
}
#endif

#undef live_kill
#undef live_gen

typedef struct lr_bb *lr_bb_t;
struct lr_bb {
  bb_t bb;
  lr_bb_t next;
};

typedef struct live_range *live_range_t; /* vars */
struct live_range {
  lr_bb_t lr_bb; /* first BB which is entirely in this range, NULL otherwise */
  int start, finish;
  int ref_cost;
  /* to smaller start and finish, but still this start can be equal to the next finish: */
  live_range_t next;
};

DEF_VARR (live_range_t);

struct lr_ctx {
  live_range_t free_lr_list;
  lr_bb_t free_lr_bb_list;
  int curr_point;
  bitmap_t live_vars, referenced_vars;
  bitmap_t points_with_born_vars, points_with_dead_vars, points_with_born_or_dead_vars;
  VARR (live_range_t) * var_live_ranges;
  VARR (int) * point_map;
};

#define free_lr_list gen_ctx->lr_ctx->free_lr_list
#define free_lr_bb_list gen_ctx->lr_ctx->free_lr_bb_list
#define curr_point gen_ctx->lr_ctx->curr_point
#define live_vars gen_ctx->lr_ctx->live_vars
#define referenced_vars gen_ctx->lr_ctx->referenced_vars
#define points_with_born_vars gen_ctx->lr_ctx->points_with_born_vars
#define points_with_dead_vars gen_ctx->lr_ctx->points_with_dead_vars
#define points_with_born_or_dead_vars gen_ctx->lr_ctx->points_with_born_or_dead_vars
#define var_live_ranges gen_ctx->lr_ctx->var_live_ranges
#define point_map gen_ctx->lr_ctx->point_map

static lr_bb_t create_lr_bb (gen_ctx_t gen_ctx, bb_t bb, lr_bb_t next) {
  lr_bb_t lr_bb;
  if ((lr_bb = free_lr_bb_list) != NULL) {
    free_lr_bb_list = free_lr_bb_list->next;
  } else {
    lr_bb = gen_malloc (gen_ctx, sizeof (struct lr_bb));
  }
  lr_bb->bb = bb;
  lr_bb->next = next;
  return lr_bb;
}

static void free_lr_bbs (gen_ctx_t gen_ctx, lr_bb_t list) {
  for (lr_bb_t lr_bb = list; lr_bb != NULL; lr_bb = list) {
    list = lr_bb->next;
    lr_bb->next = free_lr_bb_list;
    free_lr_bb_list = lr_bb;
  }
}

static void init_lr_bbs (gen_ctx_t gen_ctx) { free_lr_bb_list = NULL; }
static void finish_lr_bbs (gen_ctx_t gen_ctx) {
  for (lr_bb_t lr_bb = free_lr_bb_list; lr_bb != NULL; lr_bb = free_lr_bb_list) {
    free_lr_bb_list = lr_bb->next;
    free (lr_bb);
  }
}

static void free_one_live_range (gen_ctx_t gen_ctx, live_range_t lr) {
  free_lr_bbs (gen_ctx, lr->lr_bb);
  lr->next = free_lr_list;
  free_lr_list = lr;
}

static void free_live_ranges (gen_ctx_t gen_ctx, live_range_t list) {
  for (live_range_t lr = list; lr != NULL; lr = list) {
    list = lr->next;
    free_one_live_range (gen_ctx, lr);
  }
}

static live_range_t create_live_range (gen_ctx_t gen_ctx, int start, int finish,
                                       live_range_t next) {
  live_range_t lr;
  if ((lr = free_lr_list) != NULL) {
    free_lr_list = free_lr_list->next;
  } else {
    lr = gen_malloc (gen_ctx, sizeof (struct live_range));
  }
  gen_assert (start >= 0);
  gen_assert (finish < 0 || start <= finish);
  lr->start = start;
  lr->finish = finish;
  lr->ref_cost = 1;
  lr->next = next;
  lr->lr_bb = NULL;
  return lr;
}

static void move_lr_bbs (gen_ctx_t gen_ctx, live_range_t from, live_range_t to) {
  lr_bb_t lr_bb, next_lr_bb;
  for (lr_bb = from->lr_bb; lr_bb != NULL; lr_bb = from->lr_bb) {
    next_lr_bb = lr_bb->next;
    lr_bb->next = to->lr_bb;
    to->lr_bb = lr_bb;
    from->lr_bb = next_lr_bb;
  }
}

static void init_lrs (gen_ctx_t gen_ctx) { free_lr_list = NULL; }
static void finish_lrs (gen_ctx_t gen_ctx) {
  for (live_range_t lr = free_lr_list; lr != NULL; lr = free_lr_list) {
    free_lr_list = lr->next;
    free (lr);
  }
}

static inline int make_var_dead (gen_ctx_t gen_ctx, MIR_reg_t var, int point, int insn_p,
                                 bitmap_t coalesce_vars) {
  live_range_t lr;
  if (coalesce_vars != NULL && !bitmap_bit_p (coalesce_vars, var)) return FALSE;
  if (insn_p) bitmap_set_bit_p (referenced_vars, var);
  lr = VARR_GET (live_range_t, var_live_ranges, var);
  if (bitmap_clear_bit_p (live_vars, var)) {
    lr->finish = point;
  } else {
    /* insn with unused result: result still needs a hard register */
    VARR_SET (live_range_t, var_live_ranges, var, create_live_range (gen_ctx, point, point, lr));
  }
  return TRUE;
}

static inline int make_var_live (gen_ctx_t gen_ctx, MIR_reg_t var, int point, int insn_p,
                                 bitmap_t coalesce_vars) {
  live_range_t lr;
  if (coalesce_vars != NULL && !bitmap_bit_p (coalesce_vars, var)) return FALSE;
  lr = VARR_GET (live_range_t, var_live_ranges, var);
  if (insn_p) bitmap_set_bit_p (referenced_vars, var);
  if (!bitmap_set_bit_p (live_vars, var)) return FALSE;
  /* Always start new live range for starting living at bb end or if
     the last live range is covering a whole bb: */
  if (!insn_p || lr == NULL || lr->lr_bb != NULL
      || (lr->finish != point && lr->finish + 1 != point)) {
    VARR_SET (live_range_t, var_live_ranges, var, create_live_range (gen_ctx, point, -1, lr));
  }
  return TRUE;
}

static void add_lr_bb (gen_ctx_t gen_ctx, MIR_reg_t var, bb_t bb) {
  live_range_t lr = VARR_GET (live_range_t, var_live_ranges, var);
  gen_assert (lr != NULL && lr->lr_bb == NULL);
  lr->lr_bb = create_lr_bb (gen_ctx, bb, NULL);
}

#if !MIR_NO_GEN_DEBUG
static void print_live_range (gen_ctx_t gen_ctx, live_range_t lr) {
  fprintf (debug_file, " [%d..%d]", lr->start, lr->finish);
  if (lr->lr_bb == NULL) return;
  for (lr_bb_t lr_bb = lr->lr_bb; lr_bb != NULL; lr_bb = lr_bb->next)
    fprintf (debug_file, "%cbb%lu", lr_bb == lr->lr_bb ? '(' : ' ',
             (long unsigned) lr_bb->bb->index);
  fprintf (debug_file, ")");
}

static void print_live_ranges (gen_ctx_t gen_ctx, live_range_t lr) {
  for (; lr != NULL; lr = lr->next) print_live_range (gen_ctx, lr);
  fprintf (debug_file, "\n");
}

static void print_all_live_ranges (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  live_range_t lr;

  fprintf (debug_file, "+++++++++++++Live ranges:\n");
  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    if ((lr = VARR_GET (live_range_t, var_live_ranges, i)) == NULL) continue;
    fprintf (debug_file, "%lu", (unsigned long) i);
    if (i > MAX_HARD_REG)
      fprintf (debug_file, " (%s:%s)",
               MIR_type_str (ctx, MIR_reg_type (ctx, i - MAX_HARD_REG, curr_func_item->u.func)),
               MIR_reg_name (ctx, i - MAX_HARD_REG, curr_func_item->u.func));
    fprintf (debug_file, ":");
    print_live_ranges (gen_ctx, lr);
  }
}
#endif

static void shrink_live_ranges (gen_ctx_t gen_ctx) {
  size_t p;
  long int pn, rn, old_rn;
  live_range_t lr, prev_lr, next_lr;
  int born_p, dead_p, prev_dead_p;
  bitmap_iterator_t bi;

  bitmap_clear (points_with_born_vars);
  bitmap_clear (points_with_dead_vars);
  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    for (prev_lr = NULL, lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL;
         lr = lr->next) {
      gen_assert (lr->start <= lr->finish);
      bitmap_set_bit_p (points_with_born_vars, lr->start);
      bitmap_set_bit_p (points_with_dead_vars, lr->finish);
    }
  }

  VARR_TRUNC (int, point_map, 0);
  for (size_t i = 0; i <= curr_point; i++) VARR_PUSH (int, point_map, 0);
  bitmap_ior (points_with_born_or_dead_vars, points_with_born_vars, points_with_dead_vars);
  pn = -1;
  prev_dead_p = TRUE;
  FOREACH_BITMAP_BIT (bi, points_with_born_or_dead_vars, p) {
    born_p = bitmap_bit_p (points_with_born_vars, p);
    dead_p = bitmap_bit_p (points_with_dead_vars, p);
    assert (born_p || dead_p);
    if (!prev_dead_p || !born_p) /* 1st point is always a born */
      VARR_SET (int, point_map, p, pn);
    else
      VARR_SET (int, point_map, p, ++pn);
    prev_dead_p = dead_p;
  }
  pn++;

  old_rn = rn = 0;
  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i), prev_lr = NULL; lr != NULL;
         lr = next_lr) {
      old_rn++;
      next_lr = lr->next;
      lr->start = VARR_GET (int, point_map, lr->start);
      lr->finish = VARR_GET (int, point_map, lr->finish);
      if (prev_lr == NULL || (prev_lr->start != lr->finish && prev_lr->start != lr->finish + 1)
          || (prev_lr->lr_bb != NULL && lr->lr_bb == NULL)
          || (prev_lr->lr_bb == NULL && lr->lr_bb != NULL)) {
        rn++;
        prev_lr = lr;
        continue;
      }
      prev_lr->start = lr->start;
      prev_lr->next = next_lr;
      move_lr_bbs (gen_ctx, lr, prev_lr);
      free_one_live_range (gen_ctx, lr);
    }
  }
  DEBUG (2, {
    fprintf (debug_file, "Compressing live range points: from %d to %ld - %ld%%\n", curr_point, pn,
             curr_point == 0 ? 100 : 100 * pn / curr_point);
    if (rn != old_rn)
      fprintf (debug_file, "Compressing live ranges: from %ld to %ld - %ld%%\n", old_rn, rn,
               rn == 0 ? 100 : 100 * rn / old_rn);
  });
  curr_point = pn;
  DEBUG (2, {
    fprintf (debug_file, "Ranges after the compression:\n");
    print_all_live_ranges (gen_ctx);
  });
}

/* Merge *non-intersected* ranges R1 and R2 *without live range bb info* and returns the result. The
   function maintains the order of ranges and tries to minimize size of the result range list.
   Ranges R1 and R2 may not be used after the call.  */
static live_range_t merge_live_ranges (gen_ctx_t gen_ctx, live_range_t r1, live_range_t r2) {
  live_range_t first, last, temp;

  if (r1 == NULL) return r2;
  if (r2 == NULL) return r1;
  gen_assert (r1->lr_bb == NULL && r2->lr_bb == NULL);
  DEBUG (3, {
    fprintf (debug_file, "  Merging range:");
    print_live_ranges (gen_ctx, r1);
    fprintf (debug_file, "      and range:");
    print_live_ranges (gen_ctx, r2);
  });
  for (first = last = NULL; r1 != NULL && r2 != NULL;) {
    if (r1->start < r2->start) SWAP (r1, r2, temp);
    if (r1->start == r2->finish + 1) {
      /* Joint ranges: merge r1 and r2 into r1.  */
      DEBUG (4, {
        fprintf (debug_file, "        merging");
        print_live_range (gen_ctx, r1);
        fprintf (debug_file, " and");
        print_live_range (gen_ctx, r2);
        fprintf (debug_file, "\n");
      });
      r1->start = r2->start;
      temp = r2;
      r2 = r2->next;
      free_one_live_range (gen_ctx, temp);
    } else {
      gen_assert (r2->finish + 1 < r1->start);
      /* Add r1 to the result.  */
      if (first == NULL) {
        first = last = r1;
      } else {
        last->next = r1;
        last = r1;
      }
      r1 = r1->next;
    }
  }
  if (r1 != NULL) {
    if (first == NULL)
      first = r1;
    else
      last->next = r1;
  } else {
    gen_assert (r2 != NULL);
    if (first == NULL)
      first = r2;
    else
      last->next = r2;
  }
  DEBUG (3, {
    fprintf (debug_file, "    result: ");
    print_live_ranges (gen_ctx, first);
  });
  return first;
}

/* Return TRUE if live ranges R1 and R2 intersect.  */
static int live_range_intersect_p (live_range_t r1, live_range_t r2) {
  /* Remember the live ranges are always kept ordered.	*/
  while (r1 != NULL && r2 != NULL) {
    if (r1->start > r2->finish)
      r1 = r1->next;
    else if (r2->start > r1->finish)
      r2 = r2->next;
    else
      return TRUE;
  }
  return FALSE;
}

#define spill_gen gen   /* pseudo regs fully spilled in BB */
#define spill_kill kill /* pseudo regs referenced in the BB */

static void process_bb_ranges (gen_ctx_t gen_ctx, bb_t bb, MIR_insn_t start_insn,
                               MIR_insn_t tail_insn, bitmap_t coalesce_vars) {
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  size_t nel;
  int op_num, incr_p, out_p, mem_p;
  bitmap_iterator_t bi;
  insn_var_iterator_t insn_var_iter;

  DEBUG (2, {
    fprintf (debug_file, "  ------BB%u end: point=%d\n", (unsigned) bb->index, curr_point);
  });
  bitmap_clear (referenced_vars);
  bitmap_clear (live_vars);
  if (bb->live_out != NULL) FOREACH_BITMAP_BIT (bi, bb->live_out, nel) {
      make_var_live (gen_ctx, nel, curr_point, FALSE, coalesce_vars);
    }
  for (MIR_insn_t insn = tail_insn;; insn = DLIST_PREV (MIR_insn_t, insn)) {
    DEBUG (2, {
      fprintf (debug_file, "  p%-5d", curr_point);
      MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
    });
    incr_p = FALSE;
    FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
      if (out_p) incr_p |= make_var_dead (gen_ctx, var, curr_point, TRUE, coalesce_vars);
    }
    if (coalesce_vars == NULL && MIR_call_code_p (insn->code)) {
      if (incr_p) curr_point++;
      incr_p = FALSE;
      FOREACH_BITMAP_BIT (bi, call_used_hard_regs[MIR_T_UNDEF], nel) {
        make_var_dead (gen_ctx, nel, curr_point, TRUE, coalesce_vars);
        incr_p = TRUE;
      }
      bitmap_t args = (optimize_level > 0 ? ((bb_insn_t) insn->data)->call_hard_reg_args
                                          : ((insn_data_t) insn->data)->u.call_hard_reg_args);
      if (args != NULL) {
        FOREACH_BITMAP_BIT (bi, args, nel) {
          make_var_live (gen_ctx, nel, curr_point, TRUE, coalesce_vars);
        }
      }
      FOREACH_BITMAP_BIT (bi, live_vars, nel) {
        MIR_reg_t reg;

        if (nel <= MAX_HARD_REG) continue;
        reg = nel;
        bitmap_set_bit_p (curr_cfg->call_crossed_regs, reg);
      }
    }
    if (incr_p) curr_point++;
    incr_p = FALSE;
    FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
      if (!out_p) incr_p |= make_var_live (gen_ctx, var, curr_point, TRUE, coalesce_vars);
    }
    if (coalesce_vars == NULL) {
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_VAR) {
        incr_p |= make_var_live (gen_ctx, early_clobbered_hard_reg1, curr_point, TRUE, NULL);
        incr_p |= make_var_dead (gen_ctx, early_clobbered_hard_reg1, curr_point, TRUE, NULL);
      }
      if (early_clobbered_hard_reg2 != MIR_NON_VAR) {
        incr_p |= make_var_live (gen_ctx, early_clobbered_hard_reg2, curr_point, TRUE, NULL);
        incr_p |= make_var_dead (gen_ctx, early_clobbered_hard_reg2, curr_point, TRUE, NULL);
      }
    }
    if (incr_p) curr_point++;
    if (insn == start_insn) break;
  }
#ifndef NDEBUG
  if (coalesce_vars == NULL) {
    gen_assert (bitmap_equal_p (bb->live_in, live_vars));
  } else {
    bitmap_and (temp_bitmap, bb->live_in, coalesce_vars);
    gen_assert (bitmap_equal_p (temp_bitmap, live_vars));
  }
#endif
  FOREACH_BITMAP_BIT (bi, bb->live_in, nel) {
    make_var_dead (gen_ctx, nel, curr_point, FALSE, coalesce_vars);
    if (coalesce_vars == NULL && !bitmap_bit_p (referenced_vars, nel)) add_lr_bb (gen_ctx, nel, bb);
  }
  if (coalesce_vars == NULL) { /* setup spill info for RA */
    bitmap_clear (bb->spill_gen);
    bitmap_clear (bb->spill_kill);
    FOREACH_BITMAP_BIT (bi, referenced_vars, nel) {
      if (nel > MAX_HARD_REG) bitmap_set_bit_p (bb->spill_kill, nel);
    }
  }
  if (!bitmap_empty_p (bb->live_in)) curr_point++;
}

#undef spill_gen
#undef spill_kill

/* Build live ranges for coalescing if coalesce_vars != NULL, othewise for RA */
static void build_live_ranges (gen_ctx_t gen_ctx, bitmap_t coalesce_vars) {
  size_t i;
  MIR_reg_t max_var;
  MIR_insn_t insn, next_insn, head_insn;
  bb_t bb;

  curr_point = 0;
  max_var = get_max_var (gen_ctx);
  gen_assert (VARR_LENGTH (live_range_t, var_live_ranges) == 0);
  for (i = 0; i <= max_var; i++) VARR_PUSH (live_range_t, var_live_ranges, NULL);
  if (optimize_level == 0) {
    for (head_insn = insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
         insn = next_insn) {
      next_insn = DLIST_NEXT (MIR_insn_t, insn);
      bb = get_insn_bb (gen_ctx, head_insn);
      if (next_insn == NULL || bb != get_insn_bb (gen_ctx, next_insn)) {
        process_bb_ranges (gen_ctx, bb, head_insn, insn, coalesce_vars);
        head_insn = next_insn;
      }
    }
  } else {
    VARR_TRUNC (bb_t, worklist, 0);
    for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
      VARR_PUSH (bb_t, worklist, bb);
    if (optimize_level <= 1) /* arrange BBs in PO (post order) for more compact ranges: */
      qsort (VARR_ADDR (bb_t, worklist), VARR_LENGTH (bb_t, worklist), sizeof (bb), post_cmp);
    for (i = 0; i < VARR_LENGTH (bb_t, worklist); i++) {
      bb = VARR_GET (bb_t, worklist, i);
      if (DLIST_HEAD (bb_insn_t, bb->bb_insns) == NULL) continue;
      process_bb_ranges (gen_ctx, bb, DLIST_HEAD (bb_insn_t, bb->bb_insns)->insn,
                         DLIST_TAIL (bb_insn_t, bb->bb_insns)->insn, coalesce_vars);
    }
  }
  DEBUG (2, { print_all_live_ranges (gen_ctx); });
  shrink_live_ranges (gen_ctx);
}

static void free_func_live_ranges (gen_ctx_t gen_ctx) {
  size_t i;

  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++)
    free_live_ranges (gen_ctx, VARR_GET (live_range_t, var_live_ranges, i));
  VARR_TRUNC (live_range_t, var_live_ranges, 0);
}

static void init_live_ranges (gen_ctx_t gen_ctx) {
  gen_ctx->lr_ctx = gen_malloc (gen_ctx, sizeof (struct lr_ctx));
  init_lr_bbs (gen_ctx);
  init_lrs (gen_ctx);
  VARR_CREATE (live_range_t, var_live_ranges, 0);
  VARR_CREATE (int, point_map, 1024);
  live_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  referenced_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  points_with_born_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  points_with_dead_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  points_with_born_or_dead_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
}

static void finish_live_ranges (gen_ctx_t gen_ctx) {
  VARR_DESTROY (live_range_t, var_live_ranges);
  VARR_DESTROY (int, point_map);
  bitmap_destroy (live_vars);
  bitmap_destroy (referenced_vars);
  bitmap_destroy (points_with_born_vars);
  bitmap_destroy (points_with_dead_vars);
  bitmap_destroy (points_with_born_or_dead_vars);
  finish_lrs (gen_ctx);
  finish_lr_bbs (gen_ctx);
  free (gen_ctx->lr_ctx);
  gen_ctx->lr_ctx = NULL;
}

/* New Page */

/* Aggressive register coalescing */

typedef struct mv {
  bb_insn_t bb_insn;
  size_t freq;
} mv_t;

DEF_VARR (mv_t);

DEF_VARR (MIR_reg_t);

struct coalesce_ctx {
  VARR (mv_t) * moves;
  bitmap_t move_vars; /* vars which are in the moves above */
  /* the first and the next res in the coalesced regs group */
  VARR (MIR_reg_t) * first_coalesced_reg, *next_coalesced_reg;
};

#define moves gen_ctx->coalesce_ctx->moves
#define move_vars gen_ctx->coalesce_ctx->move_vars
#define first_coalesced_reg gen_ctx->coalesce_ctx->first_coalesced_reg
#define next_coalesced_reg gen_ctx->coalesce_ctx->next_coalesced_reg

static int substitute_reg (gen_ctx_t gen_ctx, MIR_reg_t *reg) {
  if (*reg == MIR_NON_VAR || VARR_GET (MIR_reg_t, first_coalesced_reg, *reg) == *reg) return FALSE;
  *reg = VARR_GET (MIR_reg_t, first_coalesced_reg, *reg);
  return TRUE;
}

static int mv_freq_cmp (const void *v1p, const void *v2p) {
  const mv_t *mv1 = (const mv_t *) v1p;
  const mv_t *mv2 = (const mv_t *) v2p;

  if (mv1->freq < mv2->freq) return -1;
  if (mv1->freq > mv2->freq) return 1;
  return (long) mv1->bb_insn->index - (long) mv2->bb_insn->index;
}

/* Merge two sets of coalesced regs given correspondingly by regs REG1 and REG2.  Set up
   COALESCED_REGS_BITMAP.  */
static void merge_regs (gen_ctx_t gen_ctx, MIR_reg_t reg1, MIR_reg_t reg2) {
  MIR_reg_t reg, first, first2, last, next, first_var, first2_var, temp;

  first = VARR_GET (MIR_reg_t, first_coalesced_reg, reg1);
  if ((first2 = VARR_GET (MIR_reg_t, first_coalesced_reg, reg2)) == first) return;
  if (MIR_reg_hard_reg_name (gen_ctx->ctx, first2 - MAX_HARD_REG, curr_func_item->u.func) != NULL
      || (MIR_reg_hard_reg_name (gen_ctx->ctx, first - MAX_HARD_REG, curr_func_item->u.func) == NULL
          && first2 < first)) {
    SWAP (first, first2, temp);
    SWAP (reg1, reg2, temp);
  }
  for (last = reg2, reg = VARR_GET (MIR_reg_t, next_coalesced_reg, reg2);;
       reg = VARR_GET (MIR_reg_t, next_coalesced_reg, reg)) {
    VARR_SET (MIR_reg_t, first_coalesced_reg, reg, first);
    if (reg == reg2) break;
    last = reg;
  }
  next = VARR_GET (MIR_reg_t, next_coalesced_reg, first);
  VARR_SET (MIR_reg_t, next_coalesced_reg, first, reg2);
  VARR_SET (MIR_reg_t, next_coalesced_reg, last, next);
  first_var = first;
  first2_var = first2;
  live_range_t list = VARR_GET (live_range_t, var_live_ranges, first_var);
  live_range_t list2 = VARR_GET (live_range_t, var_live_ranges, first2_var);
  VARR_SET (live_range_t, var_live_ranges, first2_var, NULL);
  VARR_SET (live_range_t, var_live_ranges, first_var, merge_live_ranges (gen_ctx, list, list2));
}

static void update_bitmap_after_coalescing (gen_ctx_t gen_ctx, bitmap_t bm) {
  MIR_reg_t reg, first_reg;
  size_t nel;
  bitmap_iterator_t bi;

  FOREACH_BITMAP_BIT (bi, bm, nel) {
    reg = nel;
    if (reg <= MAX_HARD_REG) continue;
    if ((first_reg = VARR_GET (MIR_reg_t, first_coalesced_reg, reg)) == reg) continue;
    bitmap_clear_bit_p (bm, reg);
    bitmap_set_bit_p (bm, first_reg);
  }
}

static void coalesce (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t reg, sreg, dreg, first_reg, first_sreg, first_dreg, sreg_var, dreg_var;
  MIR_insn_t insn, new_insn, next_insn;
  bb_t bb;
  bb_insn_t bb_insn;
  mv_t mv;
  size_t nops;
  int coalesced_moves = 0, change_p;

  gen_assert (optimize_level > 0);
  VARR_TRUNC (mv_t, moves, 0);
  VARR_TRUNC (MIR_reg_t, first_coalesced_reg, 0);
  VARR_TRUNC (MIR_reg_t, next_coalesced_reg, 0);
  for (MIR_reg_t i = 0; i <= curr_cfg->max_var; i++) {
    VARR_PUSH (MIR_reg_t, first_coalesced_reg, i);
    VARR_PUSH (MIR_reg_t, next_coalesced_reg, i);
  }
  bitmap_clear (move_vars);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      if (move_p (insn) && insn->ops[0].mode == MIR_OP_VAR && insn->ops[1].mode == MIR_OP_VAR) {
        mv.bb_insn = bb_insn;
        mv.freq = 1;
        for (int i = bb_loop_level (bb); i > 0; i--)
          if (mv.freq < SIZE_MAX / 8) mv.freq *= LOOP_COST_FACTOR;
        VARR_PUSH (mv_t, moves, mv);
        bitmap_set_bit_p (move_vars, insn->ops[0].u.var);
        bitmap_set_bit_p (move_vars, insn->ops[1].u.var);
      }
    }
  }
  qsort (VARR_ADDR (mv_t, moves), VARR_LENGTH (mv_t, moves), sizeof (mv_t), mv_freq_cmp);
  build_live_ranges (gen_ctx, move_vars);
  /* Coalesced moves, most frequently executed first. */
  for (size_t i = 0; i < VARR_LENGTH (mv_t, moves); i++) {
    mv = VARR_GET (mv_t, moves, i);
    bb_insn = mv.bb_insn;
    insn = bb_insn->insn;
    dreg = insn->ops[0].u.var;
    sreg = insn->ops[1].u.var;
    gen_assert (sreg > MAX_HARD_REG && dreg > MAX_HARD_REG);
    first_sreg = VARR_GET (MIR_reg_t, first_coalesced_reg, sreg);
    first_dreg = VARR_GET (MIR_reg_t, first_coalesced_reg, dreg);
    if (first_sreg == first_dreg) {
      coalesced_moves++;
      DEBUG (2, {
        fprintf (debug_file, "Coalescing move r%d-r%d (freq=%llud):", sreg, dreg,
                 (unsigned long long) mv.freq);
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      });
    } else {
      sreg_var = first_sreg;
      dreg_var = first_dreg;
      if (!live_range_intersect_p (VARR_GET (live_range_t, var_live_ranges, sreg_var),
                                   VARR_GET (live_range_t, var_live_ranges, dreg_var))
          && (MIR_reg_hard_reg_name (ctx, first_sreg - MAX_HARD_REG, curr_func_item->u.func) == NULL
              || MIR_reg_hard_reg_name (ctx, first_dreg, curr_func_item->u.func) == NULL)) {
        coalesced_moves++;
        DEBUG (2, {
          fprintf (debug_file, "Coalescing move r%d-r%d (freq=%llu):", sreg, dreg,
                   (unsigned long long) mv.freq);
          print_bb_insn (gen_ctx, bb_insn, TRUE);
        });
        merge_regs (gen_ctx, sreg, dreg);
      }
    }
  }
  reg_info_t *reg_infos = VARR_ADDR (reg_info_t, curr_cfg->reg_info);
  for (reg = MAX_HARD_REG + 1; reg <= curr_cfg->max_var; reg++) {
    if ((first_reg = VARR_GET (MIR_reg_t, first_coalesced_reg, reg)) == reg) continue;
    reg_infos[first_reg].freq += reg_infos[reg].freq;
    reg_infos[reg].freq = 0;
  }
  for (size_t i = 0; i < VARR_LENGTH (mv_t, moves); i++) {
    mv = VARR_GET (mv_t, moves, i);
    bb_insn = mv.bb_insn;
    bb = bb_insn->bb;
    insn = bb_insn->insn;
    dreg = insn->ops[0].u.var;
    sreg = insn->ops[1].u.var;
    gen_assert (sreg > MAX_HARD_REG && dreg > MAX_HARD_REG);
    first_reg = VARR_GET (MIR_reg_t, first_coalesced_reg, sreg);
    if (first_reg != VARR_GET (MIR_reg_t, first_coalesced_reg, dreg)) continue;
    if (DLIST_TAIL (bb_insn_t, bb->bb_insns) == bb_insn
        && DLIST_HEAD (bb_insn_t, bb->bb_insns) == bb_insn) { /* bb is becoming empty */
      new_insn = _MIR_new_label (ctx);
      MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
      add_new_bb_insn (gen_ctx, new_insn, bb, FALSE);
      DEBUG (2, {
        fprintf (debug_file, "Adding label for becoming empty BB ");
        MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
      });
    }
    DEBUG (2, {
      fprintf (debug_file, "Deleting coalesced move ");
      MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
    });
    gen_delete_insn (gen_ctx, insn);
  }
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
       insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    nops = MIR_insn_nops (ctx, insn);
    change_p = FALSE;
    for (size_t i = 0; i < nops; i++) {
      MIR_op_t *op = &insn->ops[i];
      switch (op->mode) {
      case MIR_OP_VAR: change_p = substitute_reg (gen_ctx, &op->u.var) || change_p; break;
      case MIR_OP_VAR_MEM:
        change_p = substitute_reg (gen_ctx, &op->u.var_mem.base) || change_p;
        change_p = substitute_reg (gen_ctx, &op->u.var_mem.index) || change_p;
        break;
      default: /* do nothing */ break;
      }
    }
    if (change_p)
      for (dead_var_t dv = DLIST_HEAD (dead_var_t, ((bb_insn_t) insn->data)->insn_dead_vars);
           dv != NULL; dv = DLIST_NEXT (dead_var_t, dv)) {
        if (dv->var <= MAX_HARD_REG) continue;
        reg = dv->var;
        if ((first_reg = VARR_GET (MIR_reg_t, first_coalesced_reg, reg)) != reg)
          dv->var = first_reg;
      }
  }
  /* Update live_in & live_out */
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    update_bitmap_after_coalescing (gen_ctx, bb->live_in);
    update_bitmap_after_coalescing (gen_ctx, bb->live_out);
  }
  DEBUG (1, {
    int moves_num = (int) VARR_LENGTH (mv_t, moves);
    if (coalesced_moves != 0) {
      fprintf (debug_file, "Coalesced Moves = %d out of %d moves (%.1f%%)\n", coalesced_moves,
               moves_num, 100.0 * coalesced_moves / moves_num);
      fprintf (debug_file, "Ranges after the coalescing:\n");
      print_all_live_ranges (gen_ctx);
    }
  });
  free_func_live_ranges (gen_ctx);
}
#undef live_in
#undef live_out

static void init_coalesce (gen_ctx_t gen_ctx) {
  gen_ctx->coalesce_ctx = gen_malloc (gen_ctx, sizeof (struct coalesce_ctx));
  VARR_CREATE (mv_t, moves, 0);
  move_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  VARR_CREATE (MIR_reg_t, first_coalesced_reg, 0);
  VARR_CREATE (MIR_reg_t, next_coalesced_reg, 0);
}

static void finish_coalesce (gen_ctx_t gen_ctx) {
  VARR_DESTROY (mv_t, moves);
  bitmap_destroy (move_vars);
  VARR_DESTROY (MIR_reg_t, first_coalesced_reg);
  VARR_DESTROY (MIR_reg_t, next_coalesced_reg);
  free (gen_ctx->coalesce_ctx);
  gen_ctx->coalesce_ctx = NULL;
}

/* New page */

static void add_reload (gen_ctx_t gen_ctx, MIR_insn_t anchor, MIR_op_t *op1, MIR_op_t *op2,
                        MIR_type_t type, int to_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t new_insn;
  MIR_insn_code_t move_code = get_move_code (type);
  if (to_p) {
    new_insn = MIR_new_insn (ctx, move_code, *op1, *op2);
    gen_add_insn_after (gen_ctx, anchor, new_insn);
  } else {
    new_insn = MIR_new_insn (ctx, move_code, *op2, *op1);
    gen_add_insn_before (gen_ctx, anchor, new_insn);
  }
  DEBUG (2, {
    fprintf (debug_file, "    Add %s insn", (to_p ? "after" : "before"));
    MIR_output_insn (ctx, debug_file, anchor, curr_func_item->u.func, FALSE);
    fprintf (debug_file, ": ");
    MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
  });
}

static void add_inout_reloads (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  MIR_context_t ctx = gen_ctx->ctx;
  int out_p;
  MIR_op_mode_t mode;
  MIR_type_t type;
  MIR_reg_t temp_reg;
  MIR_op_t temp_op;

  gen_assert (MIR_insn_nops (ctx, insn) >= 2 && !MIR_call_code_p (insn->code)
              && insn->code != MIR_RET);
  MIR_insn_op_mode (ctx, insn, 1, &out_p);
  gen_assert (!out_p);
  mode = MIR_insn_op_mode (ctx, insn, 0, &out_p);
  gen_assert (out_p && mode == MIR_insn_op_mode (ctx, insn, 1, &out_p) && !out_p);
  type = mode2type (mode);
  temp_reg = gen_new_temp_reg (gen_ctx, type, curr_func_item->u.func);
  temp_op = _MIR_new_var_op (ctx, temp_reg);
  add_reload (gen_ctx, insn, &insn->ops[1], &temp_op, type, FALSE);
  add_reload (gen_ctx, insn, &insn->ops[0], &temp_op, type, TRUE);
  insn->ops[0] = insn->ops[1] = temp_op;
}

static void make_io_dup_op_insns (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func;
  MIR_insn_t insn, next_insn;
  MIR_insn_code_t code;
  MIR_op_t temp_op, mem_op;
  MIR_op_mode_t mode;
  MIR_type_t type;
  MIR_reg_t temp_reg, type_regs[MIR_T_BOUND];
  size_t i;
  int out_p;

  gen_assert (curr_func_item->item_type == MIR_func_item);
  func = curr_func_item->u.func;
  for (i = 0; target_io_dup_op_insn_codes[i] != MIR_INSN_BOUND; i++)
    bitmap_set_bit_p (insn_to_consider, target_io_dup_op_insn_codes[i]);
  for (type = 0; type < MIR_T_BOUND; type++) type_regs[type] = MIR_NON_VAR;
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    code = insn->code;
    if (code == MIR_LABEL || code == MIR_ADDR || code == MIR_USE) continue;
    if (bitmap_bit_p (insn_to_consider, code) && !MIR_op_eq_p (ctx, insn->ops[0], insn->ops[1]))
      add_inout_reloads (gen_ctx, insn);
    if (target_insn_ok_p (gen_ctx, insn, TRUE)) continue;
    int change_p = FALSE;
    for (i = 0; i < insn->nops; i++) { /* try to change one non-dup mem op to reg */
      if (insn->ops[i].mode != MIR_OP_VAR_MEM) continue;
      if (bitmap_bit_p (insn_to_consider, code) && (i == 0 || i == 1)) continue;
      mode = MIR_insn_op_mode (ctx, insn, i, &out_p);
      type = mode2type (mode);
      /* we don't use hard regs for this type: */
      if (get_temp_hard_reg (type, TRUE) == MIR_NON_VAR) continue;
      change_p = TRUE;
      if (type_regs[type] == MIR_NON_VAR)
        type_regs[type] = gen_new_temp_reg (gen_ctx, type, curr_func_item->u.func);
      mem_op = insn->ops[i];
      insn->ops[i] = _MIR_new_var_op (ctx, type_regs[type]);
      if (target_insn_ok_p (gen_ctx, insn, TRUE)) {
        add_reload (gen_ctx, insn, &mem_op, &insn->ops[i], type, out_p);
        type_regs[type] = MIR_NON_VAR;
        break;
      }
      insn->ops[i] = mem_op;
    }
    if (i < insn->nops) continue;
    if (bitmap_bit_p (insn_to_consider, code) && insn->ops[0].mode == MIR_OP_VAR_MEM) {
      add_inout_reloads (gen_ctx, insn);
      if (target_insn_ok_p (gen_ctx, insn, TRUE)) continue;
    }
    for (i = 0; i < insn->nops; i++) { /* change all non-dup mem ops to pseudo */
      if (insn->ops[i].mode != MIR_OP_VAR_MEM) continue;
      if (bitmap_bit_p (insn_to_consider, code) && (i == 0 || i == 1)) continue;
      mode = MIR_insn_op_mode (ctx, insn, i, &out_p);
      type = mode2type (mode);
      /* we don't use hard regs for this type: */
      if (get_temp_hard_reg (type, TRUE) == MIR_NON_VAR) continue;
      temp_reg = gen_new_temp_reg (gen_ctx, type, curr_func_item->u.func);
      mem_op = insn->ops[i];
      insn->ops[i] = _MIR_new_var_op (ctx, temp_reg);
      add_reload (gen_ctx, insn, &mem_op, &insn->ops[i], type, out_p);
    }
    gen_assert (target_insn_ok_p (gen_ctx, insn, TRUE));
  }
}

/* New Page */

/* Register allocation */

typedef struct allocno_info {
  MIR_reg_t reg;
  int tied_reg_p;
  reg_info_t *reg_infos;
} allocno_info_t;

DEF_VARR (allocno_info_t);

typedef struct spill_cache_el {
  uint32_t age;
  MIR_reg_t slot;
} spill_cache_el_t;

DEF_VARR (spill_cache_el_t);

DEF_VARR (bitmap_t);

typedef struct lr_gap {
  int16_t hreg;    /* key, hard reg assigned to reg */
  int16_t type;    /* type of reg */
  MIR_reg_t reg;   /* reg of the gap lr */
  live_range_t lr; /* the gap lr, lr->finish is another key */
} lr_gap_t;

DEF_VARR (lr_gap_t);
DEF_HTAB (lr_gap_t);

typedef struct spill_el {
  MIR_reg_t reg;
  signed char spill_p, edge_p, bb_end_p /* used only for !edge_p */;
  union {
    edge_t e;
    bb_t bb;
  } u;
} spill_el_t;

DEF_VARR (spill_el_t);

typedef struct insn_reload {
  MIR_type_t type;
  MIR_reg_t var, hreg;
} insn_reload_t;

#define MAX_INSN_RELOADS (2 * 4) /* 2 temp regs * 4 types */
struct ra_ctx {
  MIR_reg_t start_mem_loc;
  VARR (MIR_reg_t) * reg_renumber;
  VARR (allocno_info_t) * sorted_regs;
  VARR (bitmap_t) * used_locs, *busy_used_locs; /* indexed by bb or point */
  VARR (bitmap_t) * var_bbs;
  VARR (lr_gap_t) * spill_gaps, *curr_gaps; /* used to find live ranges to spill */
  bitmap_t lr_gap_bitmaps[MAX_HARD_REG + 1];
  HTAB (lr_gap_t) * lr_gap_tab;
  VARR (spill_el_t) * spill_els;
  VARR (spill_cache_el_t) * spill_cache;
  uint32_t spill_cache_age;
  bitmap_t conflict_locs1;
  reg_info_t *curr_reg_infos;
  int in_reloads_num, out_reloads_num;
  insn_reload_t in_reloads[MAX_INSN_RELOADS], out_reloads[MAX_INSN_RELOADS];
};

#define start_mem_loc gen_ctx->ra_ctx->start_mem_loc
#define reg_renumber gen_ctx->ra_ctx->reg_renumber
#define sorted_regs gen_ctx->ra_ctx->sorted_regs
#define used_locs gen_ctx->ra_ctx->used_locs
#define busy_used_locs gen_ctx->ra_ctx->busy_used_locs
#define var_bbs gen_ctx->ra_ctx->var_bbs
#define spill_gaps gen_ctx->ra_ctx->spill_gaps
#define curr_gaps gen_ctx->ra_ctx->curr_gaps
#define lr_gap_bitmaps gen_ctx->ra_ctx->lr_gap_bitmaps
#define lr_gap_tab gen_ctx->ra_ctx->lr_gap_tab
#define spill_els gen_ctx->ra_ctx->spill_els
#define spill_cache gen_ctx->ra_ctx->spill_cache
#define spill_cache_age gen_ctx->ra_ctx->spill_cache_age
#define conflict_locs1 gen_ctx->ra_ctx->conflict_locs1
#define curr_reg_infos gen_ctx->ra_ctx->curr_reg_infos
#define in_reloads_num gen_ctx->ra_ctx->in_reloads_num
#define out_reloads_num gen_ctx->ra_ctx->out_reloads_num
#define in_reloads gen_ctx->ra_ctx->in_reloads
#define out_reloads gen_ctx->ra_ctx->out_reloads

/* Priority RA */

#define live_in in
#define live_out out
#define spill_gen gen   /* pseudo regs fully spilled in BB, for them spill_kill is false */
#define spill_kill kill /* pseudo regs referenced in the BB and should use assigned hreg */

static htab_hash_t lr_gap_hash (lr_gap_t el, void *arg) {
  return mir_hash_finish (mir_hash_step (mir_hash_step (mir_hash_init (0x88), (uint64_t) el.hreg),
                                         (uint64_t) el.lr->start));
}

static int lr_gap_eq (lr_gap_t el1, lr_gap_t el2, void *arg) {
  return el1.hreg == el2.hreg && el1.lr->start == el2.lr->start;
}

static void insert_lr_gap (gen_ctx_t gen_ctx, int hreg, MIR_type_t type, MIR_reg_t reg,
                           live_range_t lr) {
  lr_gap_t el = {hreg, type, reg, lr}, tab_el;
  gen_assert (lr->lr_bb != NULL);
  if (lr_gap_bitmaps[hreg] == NULL) lr_gap_bitmaps[hreg] = bitmap_create2 (3 * lr->start / 2);
  bitmap_set_bit_p (lr_gap_bitmaps[hreg], lr->start);
  HTAB_DO (lr_gap_t, lr_gap_tab, el, HTAB_INSERT, tab_el);
}

static void delete_lr_gap (gen_ctx_t gen_ctx, int hreg, live_range_t lr) {
  lr_gap_t el, tab_el;
  gen_assert (lr->lr_bb != NULL && lr_gap_bitmaps[hreg] != NULL);
  bitmap_clear_bit_p (lr_gap_bitmaps[hreg], lr->start);
  el.hreg = hreg;
  el.lr = lr;
  HTAB_DO (lr_gap_t, lr_gap_tab, el, HTAB_DELETE, tab_el);
}

static inline int find_lr_gap (gen_ctx_t gen_ctx, int hreg, int point, lr_gap_t *tab_el) {
  struct live_range lr;
  lr_gap_t el;
  if (lr_gap_bitmaps[hreg] == NULL || !bitmap_bit_p (lr_gap_bitmaps[hreg], point)) return FALSE;
  el.hreg = hreg;
  lr.start = point;
  el.lr = &lr;
  return HTAB_DO (lr_gap_t, lr_gap_tab, el, HTAB_FIND, *tab_el);
}

static void init_lr_gap_tab (gen_ctx_t gen_ctx) {
  for (int i = 0; i <= MAX_HARD_REG; i++) lr_gap_bitmaps[i] = NULL;
  HTAB_CREATE (lr_gap_t, lr_gap_tab, 1024, lr_gap_hash, lr_gap_eq, NULL);
}

static void finish_lr_gap_tab (gen_ctx_t gen_ctx) {
  for (int i = 0; i <= MAX_HARD_REG; i++)
    if (lr_gap_bitmaps[i] != NULL) bitmap_destroy (lr_gap_bitmaps[i]);
  HTAB_DESTROY (lr_gap_t, lr_gap_tab);
}

static int allocno_info_compare_func (const void *a1, const void *a2) {
  const allocno_info_t *allocno_info1 = (const allocno_info_t *) a1,
                       *allocno_info2 = (const allocno_info_t *) a2;
  MIR_reg_t reg1 = allocno_info1->reg, reg2 = allocno_info2->reg;
  reg_info_t *reg_infos = allocno_info1->reg_infos;
  long diff;

  gen_assert (reg_infos == allocno_info2->reg_infos);
  if (allocno_info1->tied_reg_p) {
    if (allocno_info2->tied_reg_p) return -1;
  } else if (allocno_info2->tied_reg_p) {
    return 1;
  }
  if ((diff = reg_infos[reg2].freq - reg_infos[reg1].freq) != 0) return diff;
  if (reg_infos[reg2].live_length < reg_infos[reg1].live_length) return -1;
  if (reg_infos[reg1].live_length < reg_infos[reg2].live_length) return 1;
  return reg1 < reg2 ? -1 : 1; /* make sort stable */
}

static int hreg_in_bitmap_p (int hreg, MIR_type_t type, int nregs, bitmap_t bm) {
  for (int i = 0; i < nregs; i++)
    if (bitmap_bit_p (bm, target_nth_loc (hreg, type, i))) return TRUE;
  return FALSE;
}

static MIR_reg_t get_hard_reg (gen_ctx_t gen_ctx, MIR_reg_t type, bitmap_t conflict_locs) {
  MIR_reg_t hreg, curr_hreg, best_hreg = MIR_NON_VAR;
  int n, k, nregs, best_saved_p = FALSE;
  for (n = 0; n <= MAX_HARD_REG; n++) {
#ifdef TARGET_HARD_REG_ALLOC_ORDER
    hreg = TARGET_HARD_REG_ALLOC_ORDER (n);
#else
    hreg = n;
#endif
    if (bitmap_bit_p (conflict_locs, hreg)) continue;
    if (!target_hard_reg_type_ok_p (hreg, type) || target_fixed_hard_reg_p (hreg)) continue;
    if ((nregs = target_locs_num (hreg, type)) > 1) {
      if (target_nth_loc (hreg, type, nregs - 1) > MAX_HARD_REG) break;
      for (k = nregs - 1; k > 0; k--) {
        curr_hreg = target_nth_loc (hreg, type, k);
        if (target_fixed_hard_reg_p (curr_hreg) || bitmap_bit_p (conflict_locs, curr_hreg)) break;
      }
      if (k > 0) continue;
    }
    if (best_hreg == MIR_NON_VAR
        || (best_saved_p && bitmap_bit_p (call_used_hard_regs[MIR_T_UNDEF], hreg))) {
      best_hreg = hreg;
      best_saved_p = !bitmap_bit_p (call_used_hard_regs[MIR_T_UNDEF], hreg);
    }
  }
  return best_hreg;
}

static int availabe_hreg_p (gen_ctx_t gen_ctx, int hreg, MIR_reg_t type, int nregs,
                            bitmap_t *conflict_locs, live_range_t lr) {
  for (int j = lr->start; j <= lr->finish; j++) {
    if (bitmap_bit_p (conflict_locs[j], hreg)) return FALSE;
    if (nregs > 1) {
      if (target_nth_loc (hreg, type, nregs - 1) > MAX_HARD_REG) return FALSE;
      for (int k = nregs - 1; k > 0; k--) {
        MIR_reg_t curr_hreg = target_nth_loc (hreg, type, k);
        if (bitmap_bit_p (conflict_locs[j], curr_hreg)) return FALSE;
      }
    }
  }
  return TRUE;
}

/* Return cost spill of given lr */
static int gap_lr_spill_cost (gen_ctx_t gen_ctx, live_range_t lr) {
  int cost_factor = LOOP_COST_FACTOR / 2;
  bitmap_clear (temp_bitmap);
  for (lr_bb_t lr_bb = lr->lr_bb; lr_bb != NULL; lr_bb = lr_bb->next)
    bitmap_set_bit_p (temp_bitmap, lr_bb->bb->index);
  int cost = 0;
  for (lr_bb_t lr_bb = lr->lr_bb; lr_bb != NULL; lr_bb = lr_bb->next) {
    bb_t bb = lr_bb->bb;
    int level, max_level, bb_level = bb_loop_level (bb) + 1;
    edge_t e;
    max_level = -1;
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
      if (!bitmap_bit_p (temp_bitmap, e->dst->index)
          && (level = bb_loop_level (e->dst) + 1) > max_level)
        max_level = level;
    if (max_level >= 0) cost += (max_level < bb_level ? max_level : bb_level) * cost_factor;
    max_level = -1;
    for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
      if (!bitmap_bit_p (temp_bitmap, e->src->index)
          && (level = bb_loop_level (e->src) + 1) > max_level)
        max_level = level;
    if (max_level >= 0) cost += (max_level < bb_level ? max_level : bb_level) * cost_factor;
  }
  return cost;
}

static void find_lr_gaps (gen_ctx_t gen_ctx, live_range_t for_lr, MIR_reg_t hreg, MIR_type_t type,
                          int nregs, int *spill_cost, VARR (lr_gap_t) * lr_gaps) {
  MIR_reg_t curr_hreg;
  int i, j, cont, slots_num = target_locs_num (hreg, type);
  int found_p MIR_UNUSED;
  lr_gap_t lr_gap, last_lr_gap;
  for (i = 0; i < slots_num; i++) {
    curr_hreg = target_nth_loc (hreg, type, i);
    gen_assert (curr_hreg <= MAX_HARD_REG);
    if (VARR_LENGTH (lr_gap_t, lr_gaps) == 0) {
      last_lr_gap.lr = NULL;
    } else {
      last_lr_gap = VARR_LAST (lr_gap_t, lr_gaps);
    }
    *spill_cost = 0;
    for (j = for_lr->start; j >= 0; j--)
      if (find_lr_gap (gen_ctx, curr_hreg, j, &lr_gap)) break;
    cont = for_lr->start + 1;
    if (j >= 0 && lr_gap.lr->finish >= for_lr->start) { /* found the leftmost interesecting */
      cont = lr_gap.lr->finish + 1;
      if (last_lr_gap.lr != lr_gap.lr) {
        VARR_PUSH (lr_gap_t, lr_gaps, lr_gap);
        *spill_cost = gap_lr_spill_cost (gen_ctx, lr_gap.lr);
        last_lr_gap = lr_gap;
      }
    }
    for (j = cont; j <= for_lr->finish; j++) {
      if (!find_lr_gap (gen_ctx, curr_hreg, j, &lr_gap)) continue;
      if (last_lr_gap.lr != lr_gap.lr) {
        VARR_PUSH (lr_gap_t, lr_gaps, lr_gap);
        *spill_cost += gap_lr_spill_cost (gen_ctx, lr_gap.lr);
        last_lr_gap = lr_gap;
      }
      j = lr_gap.lr->finish;
    }
  }
}

/* If we find a hard reg then info about spilled lrs will in spill_gaps */
static MIR_reg_t get_hard_reg_with_split (gen_ctx_t gen_ctx, MIR_reg_t reg, MIR_reg_t type,
                                          live_range_t start_lr) {
  MIR_reg_t hreg, curr_hreg, best_hreg = MIR_NON_VAR;
  int n, k, nregs, profit, cost, best_profit = 0, gap_size, best_gap_size = 0;
  int clobbered_p, best_saved_p = FALSE;
  live_range_t lr;
  bitmap_t *all_locs = VARR_ADDR (bitmap_t, used_locs);
  bitmap_t *busy_locs = VARR_ADDR (bitmap_t, busy_used_locs);
  VARR (lr_gap_t) * temp_gaps;
  for (n = 0; n <= MAX_HARD_REG; n++) {
#ifdef TARGET_HARD_REG_ALLOC_ORDER
    hreg = TARGET_HARD_REG_ALLOC_ORDER (n);
#else
    hreg = n;
#endif
    if (!target_hard_reg_type_ok_p (hreg, type) || target_fixed_hard_reg_p (hreg)) continue;
    if ((nregs = target_locs_num (hreg, type)) > 1) {
      if (target_nth_loc (hreg, type, nregs - 1) > MAX_HARD_REG) break;
      for (k = nregs - 1; k > 0; k--) {
        curr_hreg = target_nth_loc (hreg, type, k);
        if (target_fixed_hard_reg_p (curr_hreg)) break;
      }
      if (k > 0) continue;
    }
    VARR_TRUNC (lr_gap_t, curr_gaps, 0);
    profit = curr_reg_infos[reg].freq;
    gap_size = 0;
    for (lr = start_lr; lr != NULL; lr = lr->next) {
      if (availabe_hreg_p (gen_ctx, hreg, type, nregs, all_locs, lr)) {
      } else if (availabe_hreg_p (gen_ctx, hreg, type, nregs, busy_locs, lr)) {
        /* spill other pseudo regs in their gap */
        find_lr_gaps (gen_ctx, lr, hreg, type, nregs, &cost, curr_gaps);
        profit -= cost;
        gap_size += (lr->finish - lr->start + 1);
      } else if (lr->lr_bb == NULL) { /* not a gap */
        break;
      } else { /* spill this pseudo reg gap */
        lr_gap_t lr_gap = {hreg, type, reg, lr};
        cost = gap_lr_spill_cost (gen_ctx, lr_gap.lr);
        profit -= cost;
        VARR_PUSH (lr_gap_t, curr_gaps, lr_gap);
      }
    }
    if (lr != NULL || profit < 0) continue;
    clobbered_p = bitmap_bit_p (call_used_hard_regs[MIR_T_UNDEF], hreg);
    if (best_hreg == MIR_NON_VAR || profit > best_profit
        || (profit == best_profit && best_saved_p && clobbered_p)
        || (profit == best_profit && best_saved_p == !clobbered_p && gap_size > best_gap_size)) {
      best_hreg = hreg;
      best_profit = profit;
      best_saved_p = !clobbered_p;
      best_gap_size = gap_size;
      SWAP (spill_gaps, curr_gaps, temp_gaps);
    }
  }
  return best_hreg;
}

static MIR_reg_t get_new_stack_slot (gen_ctx_t gen_ctx, MIR_reg_t type, int *slots_num_ref) {
  MIR_reg_t best_loc;
  int k, slots_num = 1;

  for (k = 0; k < slots_num; k++) {
    if (k == 0) {
      best_loc = func_stack_slots_num + MAX_HARD_REG + 1;
      slots_num = target_locs_num (best_loc, type);
    }
    func_stack_slots_num++;
    if (k == 0 && (best_loc - MAX_HARD_REG - 1) % slots_num != 0) k--; /* align */
  }
  *slots_num_ref = slots_num;
  return best_loc;
}

static MIR_reg_t get_stack_loc (gen_ctx_t gen_ctx, MIR_reg_t start_loc, MIR_type_t type,
                                bitmap_t conflict_locs, int *slots_num_ref) {
  MIR_reg_t loc, curr_loc, best_loc = MIR_NON_VAR;
  int k, slots_num = 1;
  for (loc = start_loc; loc <= func_stack_slots_num + MAX_HARD_REG; loc++) {
    slots_num = target_locs_num (loc, type);
    if (target_nth_loc (loc, type, slots_num - 1) > func_stack_slots_num + MAX_HARD_REG) break;
    for (k = 0; k < slots_num; k++) {
      curr_loc = target_nth_loc (loc, type, k);
      if (bitmap_bit_p (conflict_locs, curr_loc)) break;
    }
    if (k < slots_num) continue;
    if ((loc - MAX_HARD_REG - 1) % slots_num != 0)
      continue; /* we align stack slots according to the type size */
    if (best_loc == MIR_NON_VAR) best_loc = loc;
  }
  if (best_loc == MIR_NON_VAR) best_loc = get_new_stack_slot (gen_ctx, type, &slots_num);
  *slots_num_ref = slots_num;
  return best_loc;
}

#define ONLY_SIMPLIFIED_RA FALSE

static void assign (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t best_loc, i, reg, var, max_var = get_max_var (gen_ctx);
  MIR_type_t type;
  int slots_num;
  int j, k, simple_loc_update_p, reserve_p, nregs;
  live_range_t start_lr, lr;
  bitmap_t bm;
  size_t length;
  bitmap_t *used_locs_addr, *busy_used_locs_addr;
  allocno_info_t allocno_info;
  MIR_func_t func = curr_func_item->u.func;
  bitmap_t global_hard_regs = _MIR_get_module_global_var_hard_regs (ctx, curr_func_item->module);
  const char *msg;
  const int simplified_p = ONLY_SIMPLIFIED_RA || optimize_level < 2;
  bitmap_t conflict_locs = conflict_locs1, spill_lr_starts = temp_bitmap2;

  func_stack_slots_num = 0;
  curr_reg_infos = VARR_ADDR (reg_info_t, curr_cfg->reg_info);
  VARR_TRUNC (MIR_reg_t, reg_renumber, 0);
  for (i = 0; i <= max_var; i++) {
    VARR_PUSH (MIR_reg_t, reg_renumber, MIR_NON_VAR);
  }
  /* max_var for func */
  VARR_TRUNC (allocno_info_t, sorted_regs, 0);
  allocno_info.reg_infos = curr_reg_infos;
  start_mem_loc = MAX_HARD_REG + 1;
  for (reg = MAX_HARD_REG + 1; reg <= max_var; reg++) {
    allocno_info.reg = reg;
    allocno_info.tied_reg_p = bitmap_bit_p (tied_regs, reg);
    if (bitmap_bit_p (addr_regs, reg)) {
      type = MIR_reg_type (gen_ctx->ctx, reg - MAX_HARD_REG, func);
      best_loc = get_new_stack_slot (gen_ctx, type, &slots_num);
      VARR_SET (MIR_reg_t, reg_renumber, reg, best_loc);
      start_mem_loc = best_loc + slots_num;
      DEBUG (2, {
        fprintf (debug_file, " Assigning to addressable %s:reg=%3u (freq %-3ld) -- %lu\n",
                 MIR_reg_name (gen_ctx->ctx, reg - MAX_HARD_REG, func), reg,
                 curr_reg_infos[reg].freq, (unsigned long) best_loc);
      });
      continue;
    }
    VARR_PUSH (allocno_info_t, sorted_regs, allocno_info);
    for (length = 0, lr = VARR_GET (live_range_t, var_live_ranges, reg); lr != NULL; lr = lr->next)
      length += lr->finish - lr->start + 1;
    curr_reg_infos[reg].live_length = length;
  }
  for (size_t n = 0; n <= curr_point && n < VARR_LENGTH (bitmap_t, used_locs); n++)
    if (global_hard_regs == NULL) {
      bitmap_clear (VARR_GET (bitmap_t, used_locs, n));
      if (!simplified_p) bitmap_clear (VARR_GET (bitmap_t, busy_used_locs, n));
    } else {
      bitmap_copy (VARR_GET (bitmap_t, used_locs, n), global_hard_regs);
      if (!simplified_p) bitmap_copy (VARR_GET (bitmap_t, busy_used_locs, n), global_hard_regs);
    }
  while (VARR_LENGTH (bitmap_t, used_locs) <= curr_point) {
    bm = bitmap_create2 (MAX_HARD_REG + 1);
    if (global_hard_regs != NULL) bitmap_copy (bm, global_hard_regs);
    VARR_PUSH (bitmap_t, used_locs, bm);
    if (!simplified_p) {
      bm = bitmap_create2 (MAX_HARD_REG + 1);
      if (global_hard_regs != NULL) bitmap_copy (bm, global_hard_regs);
      VARR_PUSH (bitmap_t, busy_used_locs, bm);
    }
  }
  nregs = VARR_LENGTH (allocno_info_t, sorted_regs);
  qsort (VARR_ADDR (allocno_info_t, sorted_regs), nregs, sizeof (allocno_info_t),
         allocno_info_compare_func);
  used_locs_addr = VARR_ADDR (bitmap_t, used_locs);
  busy_used_locs_addr = VARR_ADDR (bitmap_t, busy_used_locs);
  /* Mark ranges used by hard regs for pseudo reg splitting: */
  for (i = 0; i <= MAX_HARD_REG; i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++) {
        bitmap_set_bit_p (used_locs_addr[j], i);
        if (!simplified_p) bitmap_set_bit_p (busy_used_locs_addr[j], i);
      }
  }
  bitmap_clear (func_used_hard_regs);
  if (!simplified_p) HTAB_CLEAR (lr_gap_t, lr_gap_tab);
  for (i = 0; i < nregs; i++) { /* hard reg and stack slot assignment */
    reg = VARR_GET (allocno_info_t, sorted_regs, i).reg;
    if (VARR_GET (MIR_reg_t, reg_renumber, reg) != MIR_NON_VAR) continue;
    type = MIR_reg_type (gen_ctx->ctx, reg - MAX_HARD_REG, func);
    if (VARR_GET (allocno_info_t, sorted_regs, i).tied_reg_p) {
      const char *hard_reg_name = MIR_reg_hard_reg_name (ctx, reg - MAX_HARD_REG, func);
      int hard_reg = _MIR_get_hard_reg (ctx, hard_reg_name);
      gen_assert (hard_reg >= 0 && hard_reg <= MAX_HARD_REG
                  && target_locs_num (hard_reg, type) == 1);
      VARR_SET (MIR_reg_t, reg_renumber, reg, hard_reg);
#ifndef NDEBUG
      for (lr = VARR_GET (live_range_t, var_live_ranges, reg); lr != NULL; lr = lr->next)
        for (j = lr->start; j <= lr->finish; j++)
          gen_assert (bitmap_bit_p (used_locs_addr[j], hard_reg));
#endif
      if (hard_reg_name == NULL) setup_used_hard_regs (gen_ctx, type, hard_reg);
      DEBUG (2, {
        fprintf (debug_file, " Assigning to global %s:reg=%3u (freq %-3ld) -- %lu\n",
                 MIR_reg_name (gen_ctx->ctx, reg - MAX_HARD_REG, func), reg,
                 curr_reg_infos[reg].freq, (unsigned long) hard_reg);
      });
      continue;
    }
    var = reg;
    if ((start_lr = VARR_GET (live_range_t, var_live_ranges, var)) == NULL) continue;
    bitmap_clear (conflict_locs);
    for (lr = start_lr; lr != NULL; lr = lr->next) {
      for (j = lr->start; j <= lr->finish; j++)
        bitmap_ior (conflict_locs, conflict_locs, used_locs_addr[j]);
    }
    msg = "";
    VARR_TRUNC (lr_gap_t, spill_gaps, 0);
    if ((best_loc = get_hard_reg (gen_ctx, type, conflict_locs)) != MIR_NON_VAR) {
      setup_used_hard_regs (gen_ctx, type, best_loc);
    } else if (!simplified_p
               && ((best_loc = get_hard_reg_with_split (gen_ctx, reg, type, start_lr))
                   != MIR_NON_VAR)) {
      /* try to use gaps in already allocated pseudos or given pseudo: */
      setup_used_hard_regs (gen_ctx, type, best_loc);
      msg = "(with splitting live ranges)";
    } else {
      best_loc = get_stack_loc (gen_ctx, start_mem_loc, type, conflict_locs, &slots_num);
    }
    DEBUG (2, {
      fprintf (debug_file, " Assigning %s to %s:reg=%3u (freq %-3ld) -- %lu\n", msg,
               MIR_reg_name (gen_ctx->ctx, reg - MAX_HARD_REG, func), reg, curr_reg_infos[reg].freq,
               (unsigned long) best_loc);
      fprintf (debug_file, "  live range: ");
      print_live_ranges (gen_ctx, start_lr);
    });
    bitmap_clear (spill_lr_starts);
    while (VARR_LENGTH (lr_gap_t, spill_gaps) != 0) {
      lr_gap_t lr_gap = VARR_POP (lr_gap_t, spill_gaps);
      DEBUG (4, {
        fprintf (debug_file, "   Splitting lr gap: r%d%s, h%d [%d..%d]\n", lr_gap.reg,
                 lr_gap.reg == reg ? "*" : "", lr_gap.hreg, lr_gap.lr->start, lr_gap.lr->finish);
      });
      for (lr_bb_t lr_bb = lr_gap.lr->lr_bb; lr_bb != NULL; lr_bb = lr_bb->next)
        bitmap_set_bit_p (lr_bb->bb->spill_gen, lr_gap.reg);
      if (lr_gap.reg == reg) {
        bitmap_set_bit_p (spill_lr_starts, lr_gap.lr->start);
        continue; /* spilled gap of the current reg */
      }
      slots_num = target_locs_num (lr_gap.hreg, lr_gap.type);
      for (k = 0; k < slots_num; k++) {
        MIR_reg_t curr_hr = target_nth_loc (lr_gap.hreg, lr_gap.type, k);
        delete_lr_gap (gen_ctx, curr_hr, lr_gap.lr);
        for (j = lr_gap.lr->start; j <= lr_gap.lr->finish; j++)
          bitmap_clear_bit_p (used_locs_addr[j], curr_hr);
      }
    }
    VARR_SET (MIR_reg_t, reg_renumber, reg, best_loc);
    slots_num = target_locs_num (best_loc, type);
    simple_loc_update_p = simplified_p || best_loc > MAX_HARD_REG;
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next) {
      if ((reserve_p = simple_loc_update_p || !bitmap_bit_p (spill_lr_starts, lr->start))) {
        for (j = lr->start; j <= lr->finish; j++)
          for (k = 0; k < slots_num; k++)
            bitmap_set_bit_p (used_locs_addr[j], target_nth_loc (best_loc, type, k));
      }
      if (simple_loc_update_p) continue;
      if (lr->lr_bb == NULL) {
        for (j = lr->start; j <= lr->finish; j++)
          for (k = 0; k < slots_num; k++)
            bitmap_set_bit_p (busy_used_locs_addr[j], target_nth_loc (best_loc, type, k));
      } else if (reserve_p) {
        for (k = 0; k < slots_num; k++) {
          MIR_reg_t hr = target_nth_loc (best_loc, type, k);
          DEBUG (4, {
            fprintf (debug_file, "    Adding lr gap: r%d, h%d [%d..%d]\n", reg, hr, lr->start,
                     lr->finish);
          });
          insert_lr_gap (gen_ctx, hr, type, reg, lr);
        }
      }
    }
  }
}

/* Add store (st_p) or load of hard_reg with data mode to/from memory
   loc using temp_hard_reg for addressing an put it before after anchor.  */
static MIR_reg_t add_ld_st (gen_ctx_t gen_ctx, MIR_op_t *mem_op, MIR_reg_t loc, MIR_reg_t base_reg,
                            MIR_op_mode_t data_mode, MIR_reg_t hard_reg, int st_p,
                            MIR_reg_t temp_hard_reg, MIR_insn_t anchor, int after_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_disp_t offset;
  MIR_insn_code_t code;
  MIR_insn_t new_insn, new_insns[3];
  MIR_type_t type;
  bb_insn_t bb_insn, new_bb_insn;
  MIR_op_t hard_reg_op;
  size_t n;

  gen_assert (temp_hard_reg != MIR_NON_VAR);
  type = mode2type (data_mode);
  code = (type == MIR_T_I64 ? MIR_MOV
          : type == MIR_T_F ? MIR_FMOV
          : type == MIR_T_D ? MIR_DMOV
                            : MIR_LDMOV);
  if (hard_reg != MIR_NON_VAR) setup_used_hard_regs (gen_ctx, type, hard_reg);
  offset = target_get_stack_slot_offset (gen_ctx, type, loc - MAX_HARD_REG - 1);
  n = 0;
  if (target_valid_mem_offset_p (gen_ctx, type, offset)) {
    *mem_op = _MIR_new_var_mem_op (ctx, type, offset, base_reg, MIR_NON_VAR, 0);
  } else {
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, _MIR_new_var_op (ctx, temp_hard_reg),
                                 MIR_new_int_op (ctx, offset));
    new_insns[1]
      = MIR_new_insn (ctx, MIR_ADD, _MIR_new_var_op (ctx, temp_hard_reg),
                      _MIR_new_var_op (ctx, temp_hard_reg), _MIR_new_var_op (ctx, base_reg));
    n = 2;
    *mem_op = _MIR_new_var_mem_op (ctx, type, 0, temp_hard_reg, MIR_NON_VAR, 0);
  }
  if (hard_reg == MIR_NON_VAR) return hard_reg; /* LD vars can be always kept in memory */
  hard_reg_op = _MIR_new_var_op (ctx, hard_reg);
  if (!st_p) {
    new_insns[n++] = MIR_new_insn (ctx, code, hard_reg_op, *mem_op);
  } else {
    new_insns[n++] = MIR_new_insn (ctx, code, *mem_op, hard_reg_op);
  }
  DEBUG (2, {
    bb_t bb = get_insn_bb (gen_ctx, anchor);
    fprintf (debug_file, "    Adding %s insn ", after_p ? "after" : "before");
    fprintf (debug_file, " (in BB %lu", (unsigned long) bb->index);
    if (optimize_level == 0 || bb->loop_node == NULL)
      fprintf (debug_file, ") ");
    else
      fprintf (debug_file, ", level %d) ", bb_loop_level (bb));
    MIR_output_insn (ctx, debug_file, anchor, curr_func_item->u.func, FALSE);
    fprintf (debug_file, ":\n");
    for (size_t i = 0; i < n; i++) {
      fprintf (debug_file, "      ");
      MIR_output_insn (ctx, debug_file, new_insns[i], curr_func_item->u.func, TRUE);
    }
  });
  if (after_p) {
    for (size_t i = 0, j = n - 1; i < j; i++, j--) { /* reverse for subsequent correct insertion: */
      new_insn = new_insns[i];
      new_insns[i] = new_insns[j];
      new_insns[j] = new_insn;
    }
  }
  for (size_t i = 0; i < n; i++) {
    new_insn = new_insns[i];
    if (after_p)
      MIR_insert_insn_after (ctx, curr_func_item, anchor, new_insn);
    else
      MIR_insert_insn_before (ctx, curr_func_item, anchor, new_insn);
    if (optimize_level == 0) {
      new_insn->data = get_insn_data_bb (anchor);
    } else {
      bb_insn = anchor->data;
      new_bb_insn = create_bb_insn (gen_ctx, new_insn, bb_insn->bb);
      if (after_p)
        DLIST_INSERT_AFTER (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
      else
        DLIST_INSERT_BEFORE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
    }
  }
  return hard_reg;
}

static MIR_reg_t get_reload_hreg (gen_ctx_t gen_ctx, MIR_reg_t var, MIR_reg_t type, int out_p) {
  MIR_reg_t hr;
  insn_reload_t *reloads = out_p ? out_reloads : in_reloads;
  int rld_num = 0, *reloads_num = out_p ? &out_reloads_num : &in_reloads_num;

  for (int i = 0; i < *reloads_num; i++) {
    if (var != MIR_NON_VAR && reloads[i].var == var) return reloads[i].hreg;
    if (rld_num == 0 && reloads[i].hreg == get_temp_hard_reg (type, TRUE))
      rld_num = 1;
    else if (reloads[i].hreg == get_temp_hard_reg (type, FALSE))
      rld_num = 2;
  }
  gen_assert (rld_num <= 1);
  hr = get_temp_hard_reg (type, rld_num == 0);
  rld_num = (*reloads_num)++;
  gen_assert (rld_num < MAX_INSN_RELOADS);
  reloads[rld_num].var = var;
  reloads[rld_num].type = type;
  reloads[rld_num].hreg = hr;
  return hr;
}

/* Return hard reg to use in insn instead of pseudo (reg) with given data_mode.
   If reg got a stack slot (will be in *mem_op after the call), add load or store insn
   from this slot depending on out_p using base_reg and possibly a temp hard reg
   depending on out_p.  */
static MIR_reg_t change_reg (gen_ctx_t gen_ctx, MIR_op_t *mem_op, MIR_reg_t reg, MIR_reg_t base_reg,
                             MIR_op_mode_t data_mode, MIR_insn_t insn, int out_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t loc = VARR_GET (MIR_reg_t, reg_renumber, reg);
  if (loc <= MAX_HARD_REG) return loc;
  MIR_type_t type = MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
  MIR_reg_t reload_hreg = get_reload_hreg (gen_ctx, reg, type, out_p);
  MIR_reg_t temp_addr_hreg
    = (out_p || type != MIR_T_I64 ? get_reload_hreg (gen_ctx, MIR_NON_VAR, MIR_T_I64, out_p)
                                  : reload_hreg);
  gen_assert (insn->code != MIR_ADDR);
  return add_ld_st (gen_ctx, mem_op, loc, base_reg, data_mode, reload_hreg, out_p, temp_addr_hreg,
                    insn, out_p);
}

static void update_live (gen_ctx_t gen_ctx, MIR_reg_t var, int out_p, bitmap_t live) {
  if (out_p) {
    bitmap_clear_bit_p (live, var);
  } else {
    bitmap_set_bit_p (live, var);
  }
}

static int get_spill_mem_loc (gen_ctx_t gen_ctx, MIR_reg_t reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  int slots_num;
  MIR_type_t type;
  MIR_reg_t var, slot;
  live_range_t lr;
  bitmap_t conflict_locs = conflict_locs1;
  bitmap_t *used_locs_addr = VARR_ADDR (bitmap_t, used_locs);
  spill_cache_el_t *spill_cache_addr = VARR_ADDR (spill_cache_el_t, spill_cache);
  gen_assert (reg != MIR_NON_VAR && reg < VARR_LENGTH (spill_cache_el_t, spill_cache));
  if (spill_cache_addr[reg].age == spill_cache_age) return spill_cache_addr[reg].slot;
  bitmap_clear (conflict_locs);
  var = reg;
  for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
    for (int j = lr->start; j <= lr->finish; j++)
      bitmap_ior (conflict_locs, conflict_locs, used_locs_addr[j]);
  type = MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
  spill_cache_addr[reg].slot = slot
    = get_stack_loc (gen_ctx, start_mem_loc, type, conflict_locs, &slots_num);
  spill_cache_addr[reg].age = spill_cache_age;
  for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
    for (int j = lr->start; j <= lr->finish; j++)
      for (int k = 0; k < slots_num; k++)
        bitmap_set_bit_p (used_locs_addr[j], target_nth_loc (slot, type, k));
  return slot;
}

/* Add spill or restore (restore_p) of pseudo (reg) assigned to hard reg and
   put the insns after anchor.  Use base_reg to address the stack lot.  */
static void spill_restore_reg (gen_ctx_t gen_ctx, MIR_reg_t reg, MIR_reg_t base_reg,
                               MIR_insn_t anchor, int after_p, int restore_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t mem_loc;
  MIR_op_t mem_op;
  MIR_type_t type = MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
  MIR_op_mode_t data_mode = type2mode (type);
  MIR_reg_t hard_reg = VARR_GET (MIR_reg_t, reg_renumber, reg);
  gen_assert (hard_reg <= MAX_HARD_REG);
  mem_loc = get_spill_mem_loc (gen_ctx, reg);
  DEBUG (2, { fprintf (debug_file, "    %s r%d:", restore_p ? "Restore" : "Spill", reg); });
  add_ld_st (gen_ctx, &mem_op, mem_loc, base_reg, data_mode, hard_reg, !restore_p,
             TEMP_INT_HARD_REG1, anchor, after_p);
}

static void reload_addr (gen_ctx_t gen_ctx, MIR_insn_t insn, int in_mem_op_num, int out_mem_op_num,
                         MIR_reg_t base_reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_op_t mem_op, temp_op1, temp_op2, *ops = insn->ops;
  gen_assert (in_mem_op_num >= 0 || out_mem_op_num >= 0);
  int op_num = out_mem_op_num >= 0 ? out_mem_op_num : in_mem_op_num;
  MIR_reg_t base = ops[op_num].u.var_mem.base, index = ops[op_num].u.var_mem.index;
  MIR_insn_t new_insn;
  gen_assert (in_mem_op_num < 0 || out_mem_op_num < 0
              || MIR_op_eq_p (ctx, ops[in_mem_op_num], ops[out_mem_op_num]));
  add_ld_st (gen_ctx, &mem_op, VARR_GET (MIR_reg_t, reg_renumber, base), base_reg, MIR_OP_INT,
             TEMP_INT_HARD_REG1, FALSE, TEMP_INT_HARD_REG1, insn, FALSE);
  add_ld_st (gen_ctx, &mem_op, VARR_GET (MIR_reg_t, reg_renumber, index), base_reg, MIR_OP_INT,
             TEMP_INT_HARD_REG2, FALSE, TEMP_INT_HARD_REG2, insn, FALSE);
  temp_op1 = _MIR_new_var_op (ctx, TEMP_INT_HARD_REG1);
  temp_op2 = _MIR_new_var_op (ctx, TEMP_INT_HARD_REG2);
  if (ops[op_num].u.var_mem.scale != 1) {
    new_insn = MIR_new_insn (ctx, MIR_LSH, temp_op2, temp_op2,
                             MIR_new_int_op (ctx, int_log2 (ops[op_num].u.var_mem.scale)));
    gen_add_insn_before (gen_ctx, insn, new_insn);
    /* continuation of debug output in add_ld_st: */
    DEBUG (2, {
      fprintf (debug_file, "      ");
      MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
    });
  }
  new_insn = MIR_new_insn (ctx, MIR_ADD, temp_op1, temp_op1, temp_op2);
  gen_add_insn_before (gen_ctx, insn, new_insn);
  DEBUG (2, {
    fprintf (debug_file, "      ");
    MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
  });
  if (out_mem_op_num >= 0) {
    ops[out_mem_op_num].u.var_mem.base = TEMP_INT_HARD_REG1;
    ops[out_mem_op_num].u.var_mem.index = MIR_NON_VAR;
  }
  if (in_mem_op_num >= 0) {
    ops[in_mem_op_num].u.var_mem.base = TEMP_INT_HARD_REG1;
    ops[in_mem_op_num].u.var_mem.index = MIR_NON_VAR;
  }
}

struct rewrite_data {
  bb_t bb;
  bitmap_t live, regs_to_save;
};

#define MAX_INSN_RELOAD_MEM_OPS 2
static int try_spilled_reg_mem (gen_ctx_t gen_ctx, MIR_insn_t insn, int nop, MIR_reg_t loc,
                                MIR_reg_t base_reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_op_t *op = &insn->ops[nop];
  MIR_type_t type = MIR_reg_type (ctx, op->u.var - MAX_HARD_REG, curr_func_item->u.func);
  MIR_disp_t offset = target_get_stack_slot_offset (gen_ctx, type, loc - MAX_HARD_REG - 1);
  if (!target_valid_mem_offset_p (gen_ctx, type, offset)) return FALSE;
  MIR_reg_t reg = op->u.var;
  MIR_op_t saved_op = *op;
  MIR_op_t mem_op = _MIR_new_var_mem_op (ctx, type, offset, base_reg, MIR_NON_VAR, 0);
  int n = 0, op_nums[MAX_INSN_RELOAD_MEM_OPS];
  for (int i = nop; i < (int) insn->nops; i++)
    if (insn->ops[i].mode == MIR_OP_VAR && insn->ops[i].u.var == reg) {
      insn->ops[i] = mem_op;
      gen_assert (n < MAX_INSN_RELOAD_MEM_OPS);
      op_nums[n++] = i;
    }
  if (target_insn_ok_p (gen_ctx, insn, TRUE)) return TRUE;
  for (int i = 0; i < n; i++) insn->ops[op_nums[i]] = saved_op;
  return FALSE;
}

static void transform_addr (gen_ctx_t gen_ctx, MIR_insn_t insn, MIR_reg_t base_reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t reg, temp_hard_reg, loc;
  MIR_type_t type;
  MIR_disp_t offset;
  MIR_insn_t new_insn1, new_insn2;
  gen_assert (insn->code == MIR_ADDR);
  gen_assert (insn->ops[1].mode == MIR_OP_VAR);
  reg = insn->ops[1].u.reg;
  gen_assert (reg > MAX_HARD_REG && reg != MIR_NON_VAR);
  loc = VARR_GET (MIR_reg_t, reg_renumber, reg);
  type = MIR_reg_type (ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
  gen_assert (loc > MAX_HARD_REG);
  offset = target_get_stack_slot_offset (gen_ctx, type, loc - MAX_HARD_REG - 1);
  temp_hard_reg = get_reload_hreg (gen_ctx, MIR_NON_VAR, MIR_T_I64, FALSE);
  new_insn1 = MIR_new_insn (ctx, MIR_MOV, _MIR_new_var_op (ctx, temp_hard_reg),
                            MIR_new_int_op (ctx, offset));
  new_insn2 = MIR_new_insn (ctx, MIR_ADD, _MIR_new_var_op (ctx, temp_hard_reg),
                            _MIR_new_var_op (ctx, temp_hard_reg), _MIR_new_var_op (ctx, base_reg));
  DEBUG (2, {
    bb_t bb = get_insn_bb (gen_ctx, insn);
    fprintf (debug_file, "    Adding before insn (in BB %lu) ", (unsigned long) bb->index);
    MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
    fprintf (debug_file, ":\n      ");
    MIR_output_insn (ctx, debug_file, new_insn1, curr_func_item->u.func, TRUE);
    fprintf (debug_file, "      ");
    MIR_output_insn (ctx, debug_file, new_insn2, curr_func_item->u.func, TRUE);
  });
  gen_add_insn_before (gen_ctx, insn, new_insn1);
  gen_add_insn_before (gen_ctx, insn, new_insn2);
  DEBUG (2, {
    fprintf (debug_file, "Changing ");
    MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
  });
  insn->code = MIR_MOV;
  insn->ops[1] = _MIR_new_var_op (ctx, temp_hard_reg);
  DEBUG (2, {
    fprintf (debug_file, " to ");
    MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
  });
}

static int rewrite_insn (gen_ctx_t gen_ctx, MIR_insn_t insn, MIR_reg_t base_reg,
                         struct rewrite_data *data) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_type_t type;
  size_t nops, i;
  MIR_op_t *op, mem_op;
#if !MIR_NO_GEN_DEBUG
  MIR_op_t in_op = MIR_new_int_op (ctx, 0),
           out_op = MIR_new_int_op (ctx, 0); /* To remove unitilized warning */
#endif
  MIR_op_mode_t data_mode;
  MIR_reg_t hard_reg, reg;
  int out_p, call_p, addr_reload_p, rld_in_num;
  int out_mem_op_num, in_mem_op_num, other_mem_op_num;
  nops = MIR_insn_nops (ctx, insn);
  out_mem_op_num = in_mem_op_num = -1;
  rld_in_num = 0;
  /* Update live info, save/restore regs living across calls, and check do we need addr reload: */
  for (int niter = 0; niter <= 1; niter++) {
    for (i = 0; i < nops; i++) {
      op = &insn->ops[i];
      data_mode = MIR_insn_op_mode (ctx, insn, i, &out_p);
      if (niter == 0 && (!out_p || op->mode == MIR_OP_VAR_MEM)) continue;
      if (niter == 1 && (out_p && op->mode != MIR_OP_VAR_MEM)) continue;
      switch (op->mode) {
      case MIR_OP_VAR:
        if (op->u.var <= MAX_HARD_REG) {
          bitmap_set_bit_p (func_used_hard_regs, op->u.var);
          if (data != NULL) update_live (gen_ctx, op->u.var, out_p, data->live);
        } else {
          if (!out_p && VARR_GET (MIR_reg_t, reg_renumber, op->u.var) > MAX_HARD_REG
              && mode2type (data_mode) == MIR_T_I64)
            rld_in_num++;
          if (data != NULL) {
            update_live (gen_ctx, op->u.var, out_p, data->live);
            if (bitmap_clear_bit_p (data->regs_to_save, op->u.var)) /* put (slot<-hr) after insn */
              spill_restore_reg (gen_ctx, op->u.var, base_reg, insn, TRUE, FALSE);
          }
        }
        break;
      case MIR_OP_VAR_MEM:
        if (op->u.var_mem.base <= MAX_HARD_REG)
          bitmap_set_bit_p (func_used_hard_regs, op->u.var_mem.base);
        if (op->u.var_mem.index <= MAX_HARD_REG)
          bitmap_set_bit_p (func_used_hard_regs, op->u.var_mem.index);
        if (op->u.var_mem.base != MIR_NON_VAR && op->u.var_mem.index != MIR_NON_VAR
            && op->u.var_mem.base > MAX_HARD_REG && op->u.var_mem.index > MAX_HARD_REG
            && VARR_GET (MIR_reg_t, reg_renumber, op->u.var_mem.base) > MAX_HARD_REG
            && VARR_GET (MIR_reg_t, reg_renumber, op->u.var_mem.index) > MAX_HARD_REG) {
          other_mem_op_num = -1;
          if (out_p) {
            gen_assert (out_mem_op_num < 0);
            out_mem_op_num = (int) i;
            if (in_mem_op_num >= 0) other_mem_op_num = in_mem_op_num;
          } else {
            gen_assert (in_mem_op_num < 0);
            in_mem_op_num = (int) i;
            if (out_mem_op_num >= 0) other_mem_op_num = out_mem_op_num;
          }
          if (other_mem_op_num < 0
              || op->u.var_mem.base != insn->ops[other_mem_op_num].u.var_mem.base
              || op->u.var_mem.index != insn->ops[other_mem_op_num].u.var_mem.index)
            rld_in_num += 2;
        }
        if (data != NULL) {
          if (op->u.var_mem.base != MIR_NON_VAR) {
            update_live (gen_ctx, op->u.var_mem.base, FALSE, data->live);
            if (op->u.var_mem.base > MAX_HARD_REG) {
              if (bitmap_clear_bit_p (data->regs_to_save,
                                      op->u.var_mem.base)) /* put slot<-hr after */
                spill_restore_reg (gen_ctx, op->u.var_mem.base, base_reg, insn, TRUE, FALSE);
            }
          }
          if (op->u.var_mem.index != MIR_NON_VAR) {
            update_live (gen_ctx, op->u.var_mem.index, FALSE, data->live);
            if (op->u.var_mem.index > MAX_HARD_REG) {
              if (bitmap_clear_bit_p (data->regs_to_save,
                                      op->u.var_mem.index)) /* put slot<-hr after */
                spill_restore_reg (gen_ctx, op->u.var_mem.index, base_reg, insn, TRUE, FALSE);
            }
          }
        }
        break;
      default: /* do nothing */ break;
      }
    }
    if (data != NULL && niter == 0) { /* right after processing outputs */
      MIR_reg_t early_clobbered_hard_reg1, early_clobbered_hard_reg2;
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_VAR)
        update_live (gen_ctx, early_clobbered_hard_reg1, TRUE, data->live);
      if (early_clobbered_hard_reg2 != MIR_NON_VAR)
        update_live (gen_ctx, early_clobbered_hard_reg2, TRUE, data->live);
      if (MIR_call_code_p (insn->code)) {
        size_t nel;
        bb_insn_t bb_insn = insn->data;
        bitmap_iterator_t bi;
        FOREACH_BITMAP_BIT (bi, call_used_hard_regs[MIR_T_UNDEF], nel) {
          update_live (gen_ctx, nel, TRUE, data->live);
        }
        FOREACH_BITMAP_BIT (bi, bb_insn->call_hard_reg_args, nel) {
          update_live (gen_ctx, nel, FALSE, data->live);
        }
        FOREACH_BITMAP_BIT (bi, data->live, nel) {
          if (nel <= MAX_HARD_REG) continue;
          reg = nel;
          if (bitmap_bit_p (data->bb->spill_gen, reg)) continue; /* will be spilled in split */
          MIR_reg_t loc = VARR_GET (MIR_reg_t, reg_renumber, reg);
          if (loc > MAX_HARD_REG) continue;
          MIR_type_t type = MIR_reg_type (gen_ctx->ctx, reg - MAX_HARD_REG, curr_func_item->u.func);
          int nregs = target_locs_num (loc, type);
          if (hreg_in_bitmap_p (loc, type, nregs, call_used_hard_regs[MIR_T_UNDEF])
              && bitmap_set_bit_p (data->regs_to_save, reg)) /* put (hr<-slot) after call */
            spill_restore_reg (gen_ctx, reg, base_reg, insn, TRUE, TRUE);
        }
      }
    }
  }
  addr_reload_p = rld_in_num > 2;
  out_reloads_num = in_reloads_num = 0;
  if (addr_reload_p) { /* not enough 2 temp int hard regs: address reload: */
    reload_addr (gen_ctx, insn, in_mem_op_num, out_mem_op_num, base_reg);
    get_reload_hreg (gen_ctx, MIR_NON_VAR, MIR_T_I64,
                     FALSE); /* reserve the 1st int temp hard reg */
  }
  if (insn->code == MIR_ADDR) transform_addr (gen_ctx, insn, base_reg);
  call_p = MIR_call_code_p (insn->code);
  for (i = 0; i < nops; i++) {
    op = &insn->ops[i];
    data_mode = MIR_insn_op_mode (ctx, insn, i, &out_p);
    DEBUG (2, {
      if (out_p)
        out_op = *op; /* we don't care about multiple call outputs here */
      else
        in_op = *op;
    });
    switch (op->mode) {
    case MIR_OP_VAR:
      if (op->u.var <= MAX_HARD_REG) break;
      if (data_mode == MIR_OP_VAR) {
        gen_assert (insn->code == MIR_USE || (insn->code == MIR_ADDR && i == 1));
        type = MIR_reg_type (ctx, op->u.var - MAX_HARD_REG, curr_func_item->u.func);
        data_mode = type == MIR_T_F    ? MIR_OP_FLOAT
                    : type == MIR_T_D  ? MIR_OP_DOUBLE
                    : type == MIR_T_LD ? MIR_OP_LDOUBLE
                                       : MIR_OP_INT;
      }
      MIR_reg_t loc = VARR_GET (MIR_reg_t, reg_renumber, op->u.var);
      if (insn->code != MIR_ADDR && i == 0 && loc > MAX_HARD_REG
          && try_spilled_reg_mem (gen_ctx, insn, i, loc, base_reg))
        break;
      hard_reg = change_reg (gen_ctx, &mem_op, op->u.var, base_reg, data_mode, insn, out_p);
      if (hard_reg == MIR_NON_VAR) { /* we don't use hard regs for this type reg (e.g. ldouble) */
        *op = mem_op;
      } else {
        op->u.var = hard_reg;
      }
      break;
    case MIR_OP_VAR_MEM:
      if (call_p && MIR_blk_type_p (op->u.var_mem.type)) break;
      if (op->u.var_mem.base > MAX_HARD_REG && op->u.var_mem.base != MIR_NON_VAR) {
        op->u.var_mem.base
          = change_reg (gen_ctx, &mem_op, op->u.var_mem.base, base_reg, MIR_OP_INT, insn, FALSE);
        gen_assert (op->u.var_mem.base != MIR_NON_VAR); /* we can always use GP regs */
      }
      if (op->u.var_mem.index > MAX_HARD_REG && op->u.var_mem.index != MIR_NON_VAR) {
        op->u.var_mem.index
          = change_reg (gen_ctx, &mem_op, op->u.var_mem.index, base_reg, MIR_OP_INT, insn, FALSE);
        gen_assert (op->u.var_mem.index != MIR_NON_VAR); /* we can always use GP regs */
      }
      break;
    default: /* do nothing */ break;
    }
  }
  if (move_code_p (insn->code)) {
    if (MIR_op_eq_p (ctx, insn->ops[0], insn->ops[1])) {
      DEBUG (2, {
        fprintf (debug_file, "Deleting noop move ");
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
        fprintf (debug_file, " which was ");
        insn->ops[0] = out_op;
        insn->ops[1] = in_op;
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
      });
      bb_insn_t bb_insn;
      if (optimize_level > 0 && (bb_insn = insn->data) != NULL
          && DLIST_HEAD (bb_insn_t, bb_insn->bb->bb_insns) == bb_insn
          && DLIST_TAIL (bb_insn_t, bb_insn->bb->bb_insns) == bb_insn) { /* avoid empty bb */
        MIR_insn_t nop = MIR_new_insn_arr (gen_ctx->ctx, MIR_USE, 0, NULL);
        MIR_insert_insn_before (gen_ctx->ctx, curr_func_item, bb_insn->insn, nop);
        add_new_bb_insn (gen_ctx, nop, bb_insn->bb, FALSE);
      }
      gen_delete_insn (gen_ctx, insn);
      return 1;
    }
  }
  return 0;
}

static void rewrite (gen_ctx_t gen_ctx) {
  MIR_insn_t insn, next_insn, head_insn;
  MIR_reg_t base_reg = target_get_stack_slot_base_reg (gen_ctx);
  size_t insns_num = 0, movs_num = 0, deleted_movs_num = 0;
  bitmap_t global_hard_regs
    = _MIR_get_module_global_var_hard_regs (gen_ctx->ctx, curr_func_item->module);
  const int simplified_p = ONLY_SIMPLIFIED_RA || optimize_level < 2;

  if (simplified_p) {
    for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
         insn = next_insn) {
      next_insn = DLIST_NEXT (MIR_insn_t, insn);
      if (move_code_p (insn->code)) movs_num++;
      deleted_movs_num += rewrite_insn (gen_ctx, insn, base_reg, NULL);
      insns_num++;
    }
  } else {
    MIR_reg_t reg;
    bb_insn_t prev_bb_insn;
    bitmap_t live = temp_bitmap, regs_to_save = temp_bitmap2;
    bitmap_iterator_t bi;
    size_t nel;
    spill_cache_el_t spill_cache_el = {0, 0};
    spill_cache_age++;
    VARR_TRUNC (spill_cache_el_t, spill_cache, 0);
    while (VARR_LENGTH (spill_cache_el_t, spill_cache) <= curr_cfg->max_var)
      VARR_PUSH (spill_cache_el_t, spill_cache, spill_cache_el);
    for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
      struct rewrite_data data = {bb, live, regs_to_save};
      bitmap_copy (live, bb->live_out);
      bitmap_clear (regs_to_save);
      for (bb_insn_t bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL;
           bb_insn = prev_bb_insn) {
        prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
        insn = bb_insn->insn;
        if (move_code_p (insn->code)) movs_num++;
        deleted_movs_num += rewrite_insn (gen_ctx, insn, base_reg, &data);
        insns_num++;
      }
      gen_assert (bitmap_equal_p (live, bb->live_in));
      FOREACH_BITMAP_BIT (bi, regs_to_save, nel) {
        gen_assert (nel > MAX_HARD_REG);
        reg = nel;
        gen_assert (bitmap_bit_p (bb->spill_kill, reg));
        head_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns)->insn;
        spill_restore_reg (gen_ctx, reg, base_reg, head_insn, head_insn->code == MIR_LABEL, FALSE);
      }
    }
  }
  DEBUG (1, {
    fprintf (debug_file,
             "%5lu deleted RA noop moves out of %lu all moves (%.1f%%), out of %lu all insns "
             "(%.1f%%)\n",
             (unsigned long) deleted_movs_num, (unsigned long) movs_num,
             deleted_movs_num * 100.0 / movs_num, (unsigned long) insns_num,
             deleted_movs_num * 100.0 / insns_num);
  });
  if (global_hard_regs != NULL) /* we should not save/restore hard regs used by globals */
    bitmap_and_compl (func_used_hard_regs, func_used_hard_regs, global_hard_regs);
}

#if !MIR_NO_GEN_DEBUG
static void output_bb_spill_info (gen_ctx_t gen_ctx, bb_t bb) {
  output_bitmap (gen_ctx, "  live_in:", bb->live_in, TRUE);
  output_bitmap (gen_ctx, "  live_out:", bb->live_out, TRUE);
  output_bitmap (gen_ctx, "  spill_gen:", bb->spill_gen, TRUE);
  output_bitmap (gen_ctx, "  spill_kill:", bb->spill_kill, TRUE);
}
#endif

static void collect_spill_els (gen_ctx_t gen_ctx) {
  bb_t bb;
  edge_t e;
  size_t nel;
  bitmap_iterator_t bi;
  spill_el_t spill_el;

  VARR_TRUNC (spill_el_t, spill_els, 0); /* collect spill elements */
  for (bb = DLIST_EL (bb_t, curr_cfg->bbs, 2); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    /* we need non-empty BBs for splitting. we can not remove empty BB as a reg can be splitted
       around the BB and we need to generate spills/restores in this BB. */
    gen_assert (DLIST_HEAD (bb_insn_t, bb->bb_insns) != NULL);
    /* skip entry/exit bbs and split bbs */
    DEBUG (2, {
      fprintf (debug_file, " Process BB%lu(level %d) for splitting\n", (unsigned long) bb->index,
               bb_loop_level (bb));
    });
    /* Process out edges for spills: */
    spill_el.edge_p = spill_el.bb_end_p = TRUE;
    for (e = DLIST_TAIL (out_edge_t, bb->out_edges); e != NULL; e = DLIST_PREV (out_edge_t, e)) {
      bitmap_and_compl (temp_bitmap, e->dst->spill_gen, bb->spill_gen);
      if (bitmap_empty_p (temp_bitmap)) continue;
      FOREACH_BITMAP_BIT (bi, temp_bitmap, nel) {
        gen_assert (nel > MAX_HARD_REG);
        spill_el.reg = nel;
        spill_el.spill_p = TRUE;
        spill_el.u.e = e;
        VARR_PUSH (spill_el_t, spill_els, spill_el);
      }
    }
    /* Process input edges for restores: */
    for (e = DLIST_TAIL (in_edge_t, bb->in_edges); e != NULL; e = DLIST_PREV (in_edge_t, e)) {
      bitmap_clear (temp_bitmap);
      FOREACH_BITMAP_BIT (bi, e->src->spill_gen, nel) {
        if (bitmap_bit_p (bb->spill_gen, nel) || !bitmap_bit_p (bb->live_in, nel)) continue;
        bitmap_set_bit_p (temp_bitmap, nel);
      }
      if (bitmap_empty_p (temp_bitmap)) continue;
      FOREACH_BITMAP_BIT (bi, temp_bitmap, nel) {
        gen_assert (nel > MAX_HARD_REG);
        spill_el.reg = nel;
        spill_el.spill_p = FALSE;
        spill_el.u.e = e;
        VARR_PUSH (spill_el_t, spill_els, spill_el);
      }
    }
  }
}

#undef live_in
#undef live_out
#undef spill_gen
#undef spill_kill

static int spill_el_cmp (const spill_el_t *e1, const spill_el_t *e2) {
  if (e1->edge_p != e2->edge_p) return e1->edge_p - e2->edge_p; /* put bb first */
  if (e1->edge_p && e1->u.e != e2->u.e) return e1->u.e < e2->u.e ? -1 : 1;
  if (!e1->edge_p && e1->u.bb != e2->u.bb) return e1->u.bb->index < e2->u.bb->index ? -1 : 1;
  if (!e1->edge_p && e1->bb_end_p != e2->bb_end_p)
    return e1->bb_end_p - e2->bb_end_p; /* start first */
  if (e1->spill_p != e2->spill_p)       /* load first for bb start, store first otherwise: */
    return !e1->edge_p && !e1->bb_end_p ? e1->spill_p - e2->spill_p : e2->spill_p - e1->spill_p;
  return e1->reg == e2->reg ? 0 : e1->reg < e2->reg ? -1 : 1; /* smaller reg first */
}

static int spill_el_sort_cmp (const void *e1, const void *e2) { return spill_el_cmp (e1, e2); }

static void make_uniq_spill_els (gen_ctx_t gen_ctx) {
  size_t i, last, len = VARR_LENGTH (spill_el_t, spill_els);
  spill_el_t *els = VARR_ADDR (spill_el_t, spill_els);
  if (len == 0) return;
  for (last = 0, i = 1; i < len; i++) {
    if (spill_el_cmp (&els[last], &els[i]) == 0) continue;
    els[++last] = els[i];
  }
  VARR_TRUNC (spill_el_t, spill_els, last + 1);
}

#define at_start gen
#define at_end kill
#define at_src_p flag1
#define at_dst_p flag2
static void transform_edge_to_bb_placement (gen_ctx_t gen_ctx) {
  size_t i, j;
  MIR_insn_t insn;
  bb_t bb;
  edge_t e, e2, first_e;
  bitmap_t edge_regs = temp_bitmap;
  spill_el_t *spill_els_addr = VARR_ADDR (spill_el_t, spill_els);

  if (VARR_LENGTH (spill_el_t, spill_els) == 0) return;
  /* Initialize: */
  for (bb = DLIST_EL (bb_t, curr_cfg->bbs, 2); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_clear (bb->at_end);
    bitmap_clear (bb->at_start);
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
      e->at_src_p = e->at_dst_p = FALSE;
  }
  /* Setup common at_{start,end} and initial at_{src,dst}_p: */
  for (i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) {
    gen_assert (spill_els_addr[i].edge_p);
    e = spill_els_addr[i].u.e;
    insn = DLIST_TAIL (bb_insn_t, e->src->bb_insns)->insn;
    /* remember restores sorted after spills: */
    e->at_src_p
      = spill_els_addr[i].spill_p || !MIR_any_branch_code_p (insn->code) || insn->code == MIR_JMP;
    e->at_dst_p = TRUE;
    bitmap_set_bit_p (e->src->at_end, spill_els_addr[i].reg);
    bitmap_set_bit_p (e->dst->at_start, spill_els_addr[i].reg);
  }
  /* Check edge spills/restores and with common one at src end and dst start and refine
     at_{src,dst}_p: */
  for (i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i = j) {
    e = spill_els_addr[i].u.e;
    bitmap_clear (edge_regs);
    for (j = i; j < VARR_LENGTH (spill_el_t, spill_els) && e == spill_els_addr[j].u.e; j++)
      bitmap_set_bit_p (edge_regs, spill_els_addr[j].reg);
    if (e->at_src_p) {
      first_e = e2 = DLIST_HEAD (out_edge_t, e->src->out_edges);
      while (e2 != NULL && e2->at_src_p) e2 = DLIST_NEXT (out_edge_t, e2);
      if (e2 != NULL || !bitmap_equal_p (edge_regs, e->src->at_end))
        for (e2 = first_e; e2 != NULL; e2 = DLIST_NEXT (out_edge_t, e2)) e2->at_src_p = FALSE;
    }
    if (e->at_dst_p) {
      first_e = e2 = DLIST_HEAD (in_edge_t, e->dst->in_edges);
      while (e2 != NULL && e2->at_dst_p) e2 = DLIST_NEXT (in_edge_t, e2);
      if (e2 != NULL || !bitmap_equal_p (edge_regs, e->dst->at_start))
        for (e2 = first_e; e2 != NULL; e2 = DLIST_NEXT (in_edge_t, e2)) e2->at_dst_p = FALSE;
    }
  }
  for (size_t i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) {
    e = spill_els_addr[i].u.e;
    if (!e->at_src_p || !e->at_dst_p) continue;
    if (DLIST_HEAD (out_edge_t, e->src->out_edges) == DLIST_TAIL (out_edge_t, e->src->out_edges))
      e->at_src_p = FALSE;
    else if (DLIST_HEAD (in_edge_t, e->dst->in_edges) == DLIST_TAIL (in_edge_t, e->dst->in_edges))
      e->at_dst_p = FALSE;
  }
  uint32_t start_split_bb_index = curr_bb_index;
  /* Changing to BB placement with splitting edges if necessary */
  for (size_t i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) {
    gen_assert (spill_els_addr[i].edge_p);
    e = spill_els_addr[i].u.e;
    spill_els_addr[i].edge_p = FALSE;
    spill_els_addr[i].bb_end_p = FALSE;
    if (e->at_src_p) {
      spill_els_addr[i].u.bb = e->src;
      spill_els_addr[i].bb_end_p = TRUE;
    } else if (e->at_dst_p) {
      spill_els_addr[i].u.bb = e->dst;
    } else if (e->src->index >= start_split_bb_index) {  // ??? split_bb
      gen_assert (DLIST_LENGTH (out_edge_t, e->src->out_edges) == 1
                  && DLIST_LENGTH (in_edge_t, e->src->in_edges) == 1);
      spill_els_addr[i].u.bb = e->src;
    } else if (e->dst->index >= start_split_bb_index) {  // ?? split_bb
      gen_assert (DLIST_LENGTH (out_edge_t, e->dst->out_edges) == 1
                  && DLIST_LENGTH (in_edge_t, e->dst->in_edges) == 1);
      spill_els_addr[i].u.bb = e->dst;
    } else {
      /* put at split bb start, as we reuse existing edge to connect split bb, we will put
         next spill at the same split bb -- see processing order above */
      // ??? check reuse existing edge (start,end) in split_edge_if_necessary
      bb = split_edge_if_necessary (gen_ctx, e, temp_bitmap);
      spill_els_addr[i].u.bb = bb;
    }
  }
}

#undef at_start
#undef at_end
#undef at_src_p
#undef at_dst_p

static void split (gen_ctx_t gen_ctx) { /* split by putting spill/restore insns */
  int restore_p, after_p;
  bb_t bb;
  bb_insn_t bb_insn = NULL;
  MIR_reg_t reg, base_hreg = target_get_stack_slot_base_reg (gen_ctx);
  spill_el_t *spill_els_addr;

  collect_spill_els (gen_ctx);
  spill_els_addr = VARR_ADDR (spill_el_t, spill_els);
  qsort (spill_els_addr, VARR_LENGTH (spill_el_t, spill_els), sizeof (spill_el_t),
         spill_el_sort_cmp);
  DEBUG (2, {
    fprintf (debug_file, " Spills on edges:\n");
    for (size_t i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) {
      gen_assert (spill_els_addr[i].edge_p);
      fprintf (debug_file, "  %s r%d on %s of edge bb%lu->bb%lu\n",
               spill_els_addr[i].spill_p ? "spill" : "restore", spill_els_addr[i].reg,
               spill_els_addr[i].bb_end_p ? "end" : "start",
               (unsigned long) spill_els_addr[i].u.e->src->index,
               (unsigned long) spill_els_addr[i].u.e->dst->index);
    }
  });
  transform_edge_to_bb_placement (gen_ctx);
  qsort (spill_els_addr, VARR_LENGTH (spill_el_t, spill_els), sizeof (spill_el_t),
         spill_el_sort_cmp);
  make_uniq_spill_els (gen_ctx);
  spill_els_addr = VARR_ADDR (spill_el_t, spill_els);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after splitting edges:\n");
    print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, NULL);
    fprintf (debug_file, "  Spills on BBs:\n");
    for (size_t i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) {
      gen_assert (!spill_els_addr[i].edge_p);
      fprintf (debug_file, "    %s r%d on %s of bb%lu\n",
               spill_els_addr[i].spill_p ? "spill" : "restore", spill_els_addr[i].reg,
               spill_els_addr[i].bb_end_p ? "end" : "start",
               (unsigned long) spill_els_addr[i].u.bb->index);
    }
  });
  /* place spills and restores: */
  for (size_t i = 0; i < VARR_LENGTH (spill_el_t, spill_els); i++) { /* ??? debug info */
    bb = spill_els_addr[i].u.bb;
    reg = spill_els_addr[i].reg;
    gen_assert (reg > MAX_HARD_REG);
    restore_p = !spill_els_addr[i].spill_p;
    after_p = FALSE;
    if (spill_els_addr[i].bb_end_p) {
      bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
      if (!MIR_any_branch_code_p (bb_insn->insn->code)) after_p = TRUE;
    } else {
      bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
      if (bb_insn->insn->code == MIR_LABEL) after_p = TRUE;
    }
    spill_restore_reg (gen_ctx, reg, base_hreg, bb_insn->insn, after_p, restore_p);
  }
}

static void reg_alloc (gen_ctx_t gen_ctx) {
  MIR_reg_t reg, max_var = get_max_var (gen_ctx);
  const int simplified_p = ONLY_SIMPLIFIED_RA || optimize_level < 2;

  build_live_ranges (gen_ctx, NULL);
  assign (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++Disposition after assignment:");
    for (reg = MAX_HARD_REG + 1; reg <= max_var; reg++) {
      if ((reg - MAX_HARD_REG + 1) % 8 == 0) fprintf (debug_file, "\n");
      fprintf (debug_file, " %3u=>", reg);
      if (VARR_LENGTH (live_range_t, var_live_ranges) <= reg
          || VARR_GET (live_range_t, var_live_ranges, reg) == NULL)
        fprintf (debug_file, "UA");
      else
        fprintf (debug_file, "%-2u", VARR_GET (MIR_reg_t, reg_renumber, reg));
    }
    fprintf (debug_file, "\n");
  });
  rewrite (gen_ctx); /* After rewrite the BB live info is invalid as it is used for spill info */
  if (!simplified_p) {
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++Spill info:\n");
      print_CFG (gen_ctx, TRUE, FALSE, FALSE, FALSE, output_bb_spill_info);
    });
    split (gen_ctx);
  }
  free_func_live_ranges (gen_ctx);
}

static void init_ra (gen_ctx_t gen_ctx) {
  gen_ctx->ra_ctx = gen_malloc (gen_ctx, sizeof (struct ra_ctx));
  VARR_CREATE (MIR_reg_t, reg_renumber, 0);
  VARR_CREATE (allocno_info_t, sorted_regs, 0);
  VARR_CREATE (bitmap_t, used_locs, 0);
  VARR_CREATE (bitmap_t, busy_used_locs, 0);
  VARR_CREATE (bitmap_t, var_bbs, 0);
  VARR_CREATE (lr_gap_t, spill_gaps, 0);
  VARR_CREATE (lr_gap_t, curr_gaps, 0);
  VARR_CREATE (spill_el_t, spill_els, 0);
  init_lr_gap_tab (gen_ctx);
  VARR_CREATE (spill_cache_el_t, spill_cache, 0);
  spill_cache_age = 0;
  conflict_locs1 = bitmap_create2 (3 * MAX_HARD_REG / 2);
}

static void finish_ra (gen_ctx_t gen_ctx) {
  VARR_DESTROY (MIR_reg_t, reg_renumber);
  VARR_DESTROY (allocno_info_t, sorted_regs);
  while (VARR_LENGTH (bitmap_t, used_locs) != 0) bitmap_destroy (VARR_POP (bitmap_t, used_locs));
  VARR_DESTROY (bitmap_t, used_locs);
  while (VARR_LENGTH (bitmap_t, busy_used_locs) != 0)
    bitmap_destroy (VARR_POP (bitmap_t, busy_used_locs));
  VARR_DESTROY (bitmap_t, busy_used_locs);
  while (VARR_LENGTH (bitmap_t, var_bbs) != 0) bitmap_destroy (VARR_POP (bitmap_t, var_bbs));
  VARR_DESTROY (bitmap_t, var_bbs);
  VARR_DESTROY (lr_gap_t, spill_gaps);
  VARR_DESTROY (lr_gap_t, curr_gaps);
  VARR_DESTROY (spill_el_t, spill_els);
  finish_lr_gap_tab (gen_ctx);
  VARR_DESTROY (spill_cache_el_t, spill_cache);
  bitmap_destroy (conflict_locs1);
  free (gen_ctx->ra_ctx);
  gen_ctx->ra_ctx = NULL;
}

/* New Page */

/* Code selection */

struct var_ref { /* We keep track of the last reg ref in this struct. */
  MIR_insn_t insn;
  size_t insn_num;
  size_t nop;
  char def_p, del_p; /* def/use and deleted */
};

typedef struct var_ref var_ref_t;

DEF_VARR (var_ref_t);

struct selection_ctx {
  VARR (size_t) * var_ref_ages;
  VARR (var_ref_t) * var_refs;
  var_ref_t *var_refs_addr;
  size_t *var_ref_ages_addr;
  size_t curr_bb_var_ref_age;
  size_t last_mem_ref_insn_num;
  VARR (MIR_reg_t) * insn_vars; /* registers considered for substitution */
  VARR (size_t) * changed_op_numbers;
  VARR (MIR_op_t) * last_right_ops;
  bitmap_t vars_bitmap;
};

#define var_ref_ages gen_ctx->selection_ctx->var_ref_ages
#define var_refs gen_ctx->selection_ctx->var_refs
#define var_refs_addr gen_ctx->selection_ctx->var_refs_addr
#define var_ref_ages_addr gen_ctx->selection_ctx->var_ref_ages_addr
#define curr_bb_var_ref_age gen_ctx->selection_ctx->curr_bb_var_ref_age
#define last_mem_ref_insn_num gen_ctx->selection_ctx->last_mem_ref_insn_num
#define insn_vars gen_ctx->selection_ctx->insn_vars
#define changed_op_numbers gen_ctx->selection_ctx->changed_op_numbers
#define last_right_ops gen_ctx->selection_ctx->last_right_ops
#define vars_bitmap gen_ctx->selection_ctx->vars_bitmap

static MIR_insn_code_t commutative_insn_code (MIR_insn_code_t insn_code) {
  switch (insn_code) {
    /* we can not change fp comparison and branches because NaNs */
  case MIR_ADD:
  case MIR_ADDS:
  case MIR_FADD:
  case MIR_DADD:
  case MIR_LDADD:
  case MIR_MUL:
  case MIR_MULS:
  case MIR_MULO:
  case MIR_MULOS:
  case MIR_UMULO:
  case MIR_UMULOS:
  case MIR_FMUL:
  case MIR_DMUL:
  case MIR_LDMUL:
  case MIR_AND:
  case MIR_OR:
  case MIR_XOR:
  case MIR_ANDS:
  case MIR_ORS:
  case MIR_XORS:
  case MIR_EQ:
  case MIR_EQS:
  case MIR_FEQ:
  case MIR_DEQ:
  case MIR_LDEQ:
  case MIR_NE:
  case MIR_NES:
  case MIR_FNE:
  case MIR_DNE:
  case MIR_LDNE:
  case MIR_BEQ:
  case MIR_BEQS:
  case MIR_FBEQ:
  case MIR_DBEQ:
  case MIR_LDBEQ:
  case MIR_BNE:
  case MIR_BNES:
  case MIR_FBNE:
  case MIR_DBNE:
  case MIR_LDBNE: return insn_code; break;
  case MIR_LT: return MIR_GT;
  case MIR_LTS: return MIR_GTS;
  case MIR_ULT: return MIR_UGT;
  case MIR_ULTS: return MIR_UGTS;
  case MIR_LE: return MIR_GE;
  case MIR_LES: return MIR_GES;
  case MIR_ULE: return MIR_UGE;
  case MIR_ULES: return MIR_UGES;
  case MIR_GT: return MIR_LT;
  case MIR_GTS: return MIR_LTS;
  case MIR_UGT: return MIR_ULT;
  case MIR_UGTS: return MIR_ULTS;
  case MIR_GE: return MIR_LE;
  case MIR_GES: return MIR_LES;
  case MIR_UGE: return MIR_ULE;
  case MIR_UGES: return MIR_ULES;
  case MIR_BLT: return MIR_BGT;
  case MIR_BLTS: return MIR_BGTS;
  case MIR_UBLT: return MIR_UBGT;
  case MIR_UBLTS: return MIR_UBGTS;
  case MIR_BLE: return MIR_BGE;
  case MIR_BLES: return MIR_BGES;
  case MIR_UBLE: return MIR_UBGE;
  case MIR_UBLES: return MIR_UBGES;
  case MIR_BGT: return MIR_BLT;
  case MIR_BGTS: return MIR_BLTS;
  case MIR_UBGT: return MIR_UBLT;
  case MIR_UBGTS: return MIR_UBLTS;
  case MIR_BGE: return MIR_BLE;
  case MIR_BGES: return MIR_BLES;
  case MIR_UBGE: return MIR_UBLE;
  case MIR_UBGES: return MIR_UBLES;
  default: return MIR_INSN_BOUND;
  }
}

static int obsolete_var_p (gen_ctx_t gen_ctx, MIR_reg_t var, size_t def_insn_num) {
  return (var < VARR_LENGTH (size_t, var_ref_ages) && var_ref_ages_addr[var] == curr_bb_var_ref_age
          && var_refs_addr[var].insn_num > def_insn_num);
}

static int obsolete_var_op_p (gen_ctx_t gen_ctx, MIR_op_t op, size_t def_insn_num) {
  return op.mode == MIR_OP_VAR && obsolete_var_p (gen_ctx, op.u.var, def_insn_num);
}

static int obsolete_op_p (gen_ctx_t gen_ctx, MIR_op_t op, size_t def_insn_num) {
  if (obsolete_var_op_p (gen_ctx, op, def_insn_num)) return TRUE;
  if (op.mode != MIR_OP_VAR_MEM) return FALSE;
  if (op.u.var_mem.base != MIR_NON_VAR && obsolete_var_p (gen_ctx, op.u.var_mem.base, def_insn_num))
    return TRUE;
  if (op.u.var_mem.index != MIR_NON_VAR
      && obsolete_var_p (gen_ctx, op.u.var_mem.index, def_insn_num))
    return TRUE;
  return last_mem_ref_insn_num > def_insn_num;
}

static int safe_var_substitution_p (gen_ctx_t gen_ctx, MIR_reg_t var, bb_insn_t bb_insn) {
  return (var != MIR_NON_VAR && var < VARR_LENGTH (size_t, var_ref_ages)
          && var_ref_ages_addr[var] == curr_bb_var_ref_age
          && var_refs_addr[var].def_p
          /* It is not safe to substitute if there is another use after def insn before
             the current insn as we delete def insn after the substitution. */
          && find_bb_insn_dead_var (bb_insn, var) != NULL);
}

static void combine_process_var (gen_ctx_t gen_ctx, MIR_reg_t var, bb_insn_t bb_insn) {
  if (!safe_var_substitution_p (gen_ctx, var, bb_insn) || !bitmap_set_bit_p (vars_bitmap, var))
    return;
  VARR_PUSH (MIR_reg_t, insn_vars, var);
}

static void combine_process_op (gen_ctx_t gen_ctx, const MIR_op_t *op_ref, bb_insn_t bb_insn) {
  if (op_ref->mode == MIR_OP_VAR) {
    combine_process_var (gen_ctx, op_ref->u.var, bb_insn);
  } else if (op_ref->mode == MIR_OP_VAR_MEM) {
    if (op_ref->u.var_mem.base != MIR_NON_VAR)
      combine_process_var (gen_ctx, op_ref->u.var_mem.base, bb_insn);
    if (op_ref->u.var_mem.index != MIR_NON_VAR)
      combine_process_var (gen_ctx, op_ref->u.var_mem.index, bb_insn);
  }
}

static int combine_delete_insn (gen_ctx_t gen_ctx, MIR_insn_t def_insn, bb_insn_t bb_insn) {
  MIR_reg_t var;

  gen_assert (def_insn->ops[0].mode == MIR_OP_VAR);
  var = def_insn->ops[0].u.var;
  if (var_ref_ages_addr[var] != curr_bb_var_ref_age || var_refs_addr[var].del_p) return FALSE;
  DEBUG (2, {
    fprintf (debug_file, "      deleting now dead insn ");
    print_bb_insn (gen_ctx, def_insn->data, TRUE);
  });
  remove_bb_insn_dead_var (gen_ctx, bb_insn, var);
  move_bb_insn_dead_vars (bb_insn, def_insn->data);
  /* We should delete the def insn here because of possible substitution of the def
     insn 'r0 = ... r0 ...'.  We still need valid entry for def here to find obsolete
     definiton, e.g. "r1 = r0; r0 = ...; r0 = ... (deleted); ...= ...r1..." */
  gen_delete_insn (gen_ctx, def_insn);
  var_refs_addr[var].del_p = TRUE; /* to exclude repetitive deletion */
  return TRUE;
}

static int64_t power2 (int64_t p) {
  int64_t n = 1;

  if (p < 0) return 0;
  while (p-- > 0) n *= 2;
  return n;
}

static MIR_insn_t get_uptodate_def_insn (gen_ctx_t gen_ctx, int var) {
  MIR_insn_t def_insn;

  if (!var_refs_addr[var].def_p) return NULL;
  gen_assert (!var_refs_addr[var].del_p);
  def_insn = var_refs_addr[var].insn;
  /* Checking r0 = ... r1 ...; ...; r1 = ...; ...; insn */
  if ((def_insn->nops > 1 && obsolete_op_p (gen_ctx, def_insn->ops[1], var_refs_addr[var].insn_num))
      || (def_insn->nops > 2
          && obsolete_op_p (gen_ctx, def_insn->ops[2], var_refs_addr[var].insn_num)))
    return NULL;
  return def_insn;
}

static int combine_substitute (gen_ctx_t gen_ctx, bb_insn_t *bb_insn_ref, long *deleted_insns_num) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_insn_t bb_insn = *bb_insn_ref;
  MIR_insn_t insn = bb_insn->insn, def_insn;
  size_t i, nops = insn->nops;
  int out_p, insn_change_p, insn_var_change_p, op_change_p, mem_reg_change_p, success_p;
  MIR_op_t *op_ref, *src_op_ref, *src_op2_ref, saved_op;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int64_t scale;

  if (nops == 0) return FALSE;
  VARR_TRUNC (MIR_op_t, last_right_ops, 0);
  for (i = 0; i < nops; i++) VARR_PUSH (MIR_op_t, last_right_ops, insn->ops[i]);
  VARR_TRUNC (MIR_reg_t, insn_vars, 0);
  bitmap_clear (vars_bitmap);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (ctx, insn, i, &out_p);
    if (out_p && insn->ops[i].mode != MIR_OP_VAR_MEM) continue;
    combine_process_op (gen_ctx, &insn->ops[i], bb_insn);
  }

  if (move_code_p (insn->code) && insn->ops[1].mode == MIR_OP_VAR
      && VARR_LENGTH (MIR_reg_t, insn_vars) != 0
      && VARR_LAST (MIR_reg_t, insn_vars) == insn->ops[1].u.var) {
    /* We can change move src.  Try to change insn the following way:
       r0 = r2 op r3; ...; ... = r0  =>  ...; ... = r2 op r3 */
    var = insn->ops[1].u.var;
    if ((def_insn = get_uptodate_def_insn (gen_ctx, var)) == NULL
        || MIR_call_code_p (def_insn->code))
      return FALSE;
    target_get_early_clobbered_hard_regs (def_insn, &early_clobbered_hard_reg1,
                                          &early_clobbered_hard_reg2);
    if (!move_code_p (def_insn->code) && early_clobbered_hard_reg1 == MIR_NON_VAR
        && early_clobbered_hard_reg2 == MIR_NON_VAR && insn->ops[1].mode == MIR_OP_VAR
        && insn->ops[1].u.var == var
        /* Check that insn->ops[0] is not mem[...hr0...]: */
        && (insn->ops[0].mode != MIR_OP_VAR_MEM
            || (insn->ops[0].u.var_mem.base != var && insn->ops[0].u.var_mem.index != var))) {
      saved_op = def_insn->ops[0];
      def_insn->ops[0] = insn->ops[0];
      success_p = target_insn_ok_p (gen_ctx, def_insn, TRUE);
      def_insn->ops[0] = saved_op;
      if (!success_p) return FALSE;
      gen_move_insn_before (gen_ctx, insn, def_insn);
      DEBUG (2, {
        fprintf (debug_file, "      moving insn ");
        print_bb_insn (gen_ctx, def_insn->data, FALSE);
        fprintf (debug_file, "      before insn ");
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      });
      def_insn->ops[0] = insn->ops[0];
      DEBUG (2, {
        fprintf (debug_file, "      changing it to ");
        print_bb_insn (gen_ctx, def_insn->data, TRUE);
        fprintf (debug_file, "      deleting insn ");
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      });
      gen_delete_insn (gen_ctx, insn);
      (*deleted_insns_num)++;
      *bb_insn_ref = def_insn->data;
      return TRUE;
    }
  }
  insn_change_p = FALSE;
  while (VARR_LENGTH (MIR_reg_t, insn_vars) != 0) {
    var = VARR_POP (MIR_reg_t, insn_vars);
    if ((def_insn = get_uptodate_def_insn (gen_ctx, var)) == NULL) continue;
    insn_var_change_p = FALSE;
    for (i = 0; i < nops; i++) { /* Change all var occurences: */
      op_ref = &insn->ops[i];
      op_change_p = FALSE;
      MIR_insn_op_mode (ctx, insn, i, &out_p);
      if (!out_p && op_ref->mode == MIR_OP_VAR && op_ref->u.var == var) {
        if (!move_code_p (def_insn->code)) break;
        /* It is not safe to substitute if there is another use after def insn before
           the current as we delete def insn after substitution. */
        insn->ops[i] = def_insn->ops[1];
        insn_var_change_p = op_change_p = TRUE;
      } else if (op_ref->mode == MIR_OP_VAR_MEM) {
        src_op_ref = &def_insn->ops[1];
        if (op_ref->u.var_mem.index == var) {
          mem_reg_change_p = FALSE;
          if (src_op_ref->mode != MIR_OP_VAR) {
          } else if (def_insn->code == MIR_MOV) { /* index = r */
            insn->ops[i].u.var_mem.index = src_op_ref->u.var;
            mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
          } else if (def_insn->code == MIR_ADD
                     || def_insn->code == MIR_SUB) { /* index = r +- const */
            gen_assert (src_op_ref->u.var != MIR_NON_VAR);
            if ((src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT) {
              insn->ops[i].u.var_mem.index = src_op_ref->u.var;
              insn->ops[i].u.var_mem.disp
                += ((def_insn->code == MIR_ADD ? src_op2_ref->u.i : -src_op2_ref->u.i)
                    * insn->ops[i].u.var_mem.scale);
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            }
          } else if ((def_insn->code == MIR_MUL || def_insn->code == MIR_LSH)
                     && op_ref->u.var_mem.scale >= 1 && op_ref->u.var_mem.scale <= MIR_MAX_SCALE
                     && (src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT) {
            scale = def_insn->code == MIR_MUL ? src_op2_ref->u.i : power2 (src_op2_ref->u.i);
            if (scale >= 1 && scale <= MIR_MAX_SCALE
                && insn->ops[i].u.var_mem.scale * scale <= MIR_MAX_SCALE) {
              /* index = r * const */
              gen_assert (src_op_ref->u.var != MIR_NON_VAR);
              insn->ops[i].u.var_mem.index = src_op_ref->u.var;
              insn->ops[i].u.var_mem.scale *= scale;
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            }
          }
          if (!mem_reg_change_p) break;
        }
        if (op_ref->u.var_mem.base == var) {
          mem_reg_change_p = FALSE;
          op_ref = &insn->ops[i];
          if (def_insn->code == MIR_MOV) {
            if (src_op_ref->mode == MIR_OP_VAR) { /* base = r */
              insn->ops[i].u.var_mem.base = src_op_ref->u.var;
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            } else if (src_op_ref->mode == MIR_OP_INT) { /* base = const */
              if (insn->ops[i].u.var_mem.scale != 1) {
                insn->ops[i].u.var_mem.base = MIR_NON_VAR;
              } else {
                insn->ops[i].u.var_mem.base = insn->ops[i].u.var_mem.index;
                insn->ops[i].u.var_mem.index = MIR_NON_VAR;
              }
              insn->ops[i].u.var_mem.disp += src_op_ref->u.i;
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            }
          } else if (src_op_ref->mode != MIR_OP_VAR) { /* Can do nothing */
            ;
          } else if (def_insn->code == MIR_ADD || def_insn->code == MIR_SUB) {
            gen_assert (src_op_ref->u.var != MIR_NON_VAR);
            src_op2_ref = &def_insn->ops[2];
            if (def_insn->code == MIR_ADD && src_op2_ref->mode == MIR_OP_VAR
                && op_ref->u.var_mem.index == MIR_NON_VAR) { /* base = r1 + r2 */
              insn->ops[i].u.var_mem.base = src_op_ref->u.var;
              insn->ops[i].u.var_mem.index = src_op2_ref->u.var;
              insn->ops[i].u.var_mem.scale = 1;
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            } else if (src_op2_ref->mode == MIR_OP_INT) { /* base = r +- const */
              insn->ops[i].u.var_mem.base = src_op_ref->u.var;
              insn->ops[i].u.var_mem.disp
                += (def_insn->code == MIR_ADD ? src_op2_ref->u.i : -src_op2_ref->u.i);
              mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
            }
          } else if (def_insn->code == MIR_MUL && op_ref->u.var_mem.index == MIR_NON_VAR
                     && (src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT
                     && src_op2_ref->u.i >= 1
                     && src_op2_ref->u.i <= MIR_MAX_SCALE) { /* base = r * const */
            gen_assert (src_op_ref->u.var != MIR_NON_VAR && src_op2_ref->u.i != 1);
            insn->ops[i].u.var_mem.base = MIR_NON_VAR;
            insn->ops[i].u.var_mem.index = src_op_ref->u.var;
            insn->ops[i].u.var_mem.scale = src_op2_ref->u.i;
            mem_reg_change_p = op_change_p = insn_var_change_p = TRUE;
          }
          if (!mem_reg_change_p) {
            if (op_change_p) VARR_PUSH (size_t, changed_op_numbers, i); /* index was changed */
            break;
          }
        }
      }
      if (op_change_p) VARR_PUSH (size_t, changed_op_numbers, i);
    }
    if (insn_var_change_p) {
      if ((success_p = i >= nops && target_insn_ok_p (gen_ctx, insn, TRUE))) insn_change_p = TRUE;
      while (VARR_LENGTH (size_t, changed_op_numbers)) {
        i = VARR_POP (size_t, changed_op_numbers);
        if (success_p)
          VARR_SET (MIR_op_t, last_right_ops, i, insn->ops[i]);
        else
          insn->ops[i] = VARR_GET (MIR_op_t, last_right_ops, i); /* restore changed operands */
      }
      if (success_p) {
        gen_assert (def_insn != NULL);
        if (combine_delete_insn (gen_ctx, def_insn, bb_insn)) (*deleted_insns_num)++;
        DEBUG (2, {
          fprintf (debug_file, "      changing to ");
          print_bb_insn (gen_ctx, bb_insn, TRUE);
        });
      }
    }
  }
  return insn_change_p;
}

static MIR_insn_code_t get_combined_br_code (int true_p, MIR_insn_code_t cmp_code) {
  switch (cmp_code) {
  case MIR_EQ: return true_p ? MIR_BEQ : MIR_BNE;
  case MIR_EQS: return true_p ? MIR_BEQS : MIR_BNES;
  case MIR_NE: return true_p ? MIR_BNE : MIR_BEQ;
  case MIR_NES: return true_p ? MIR_BNES : MIR_BEQS;
  case MIR_LT: return true_p ? MIR_BLT : MIR_BGE;
  case MIR_LTS: return true_p ? MIR_BLTS : MIR_BGES;
  case MIR_ULT: return true_p ? MIR_UBLT : MIR_UBGE;
  case MIR_ULTS: return true_p ? MIR_UBLTS : MIR_UBGES;
  case MIR_LE: return true_p ? MIR_BLE : MIR_BGT;
  case MIR_LES: return true_p ? MIR_BLES : MIR_BGTS;
  case MIR_ULE: return true_p ? MIR_UBLE : MIR_UBGT;
  case MIR_ULES: return true_p ? MIR_UBLES : MIR_UBGTS;
  case MIR_GT: return true_p ? MIR_BGT : MIR_BLE;
  case MIR_GTS: return true_p ? MIR_BGTS : MIR_BLES;
  case MIR_UGT: return true_p ? MIR_UBGT : MIR_UBLE;
  case MIR_UGTS: return true_p ? MIR_UBGTS : MIR_UBLES;
  case MIR_GE: return true_p ? MIR_BGE : MIR_BLT;
  case MIR_GES: return true_p ? MIR_BGES : MIR_BLTS;
  case MIR_UGE: return true_p ? MIR_UBGE : MIR_UBLT;
  case MIR_UGES:
    return true_p ? MIR_UBGES : MIR_UBLTS;
    /* Cannot revert in the false case for IEEE754: */
  case MIR_FEQ: return true_p ? MIR_FBEQ : MIR_INSN_BOUND;
  case MIR_DEQ: return true_p ? MIR_DBEQ : MIR_INSN_BOUND;
  case MIR_LDEQ: return true_p ? MIR_LDBEQ : MIR_INSN_BOUND;
  case MIR_FNE: return true_p ? MIR_FBNE : MIR_INSN_BOUND;
  case MIR_DNE: return true_p ? MIR_DBNE : MIR_INSN_BOUND;
  case MIR_LDNE: return true_p ? MIR_LDBNE : MIR_INSN_BOUND;
  case MIR_FLT: return true_p ? MIR_FBLT : MIR_INSN_BOUND;
  case MIR_DLT: return true_p ? MIR_DBLT : MIR_INSN_BOUND;
  case MIR_LDLT: return true_p ? MIR_LDBLT : MIR_INSN_BOUND;
  case MIR_FLE: return true_p ? MIR_FBLE : MIR_INSN_BOUND;
  case MIR_DLE: return true_p ? MIR_DBLE : MIR_INSN_BOUND;
  case MIR_LDLE: return true_p ? MIR_LDBLE : MIR_INSN_BOUND;
  case MIR_FGT: return true_p ? MIR_FBGT : MIR_INSN_BOUND;
  case MIR_DGT: return true_p ? MIR_DBGT : MIR_INSN_BOUND;
  case MIR_LDGT: return true_p ? MIR_LDBGT : MIR_INSN_BOUND;
  case MIR_FGE: return true_p ? MIR_FBGE : MIR_INSN_BOUND;
  case MIR_DGE: return true_p ? MIR_DBGE : MIR_INSN_BOUND;
  case MIR_LDGE: return true_p ? MIR_LDBGE : MIR_INSN_BOUND;
  default: return MIR_INSN_BOUND;
  }
}

static MIR_insn_t combine_branch_and_cmp (gen_ctx_t gen_ctx, bb_insn_t bb_insn,
                                          long *deleted_insns_num) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t def_insn, new_insn, insn = bb_insn->insn;
  MIR_insn_code_t code = insn->code;
  MIR_op_t op;

  if (code != MIR_BT && code != MIR_BF && code != MIR_BTS && code != MIR_BFS) return NULL;
  op = insn->ops[1];
  if (op.mode != MIR_OP_VAR || !safe_var_substitution_p (gen_ctx, op.u.var, bb_insn)) return NULL;
  def_insn = var_refs_addr[op.u.var].insn;
  if ((code = get_combined_br_code (code == MIR_BT || code == MIR_BTS, def_insn->code))
      == MIR_INSN_BOUND)
    return NULL;
  if (obsolete_op_p (gen_ctx, def_insn->ops[1], var_refs_addr[op.u.var].insn_num)
      || obsolete_op_p (gen_ctx, def_insn->ops[2], var_refs_addr[op.u.var].insn_num))
    return NULL;
  new_insn = MIR_new_insn (ctx, code, insn->ops[0], def_insn->ops[1], def_insn->ops[2]);
  MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
  if (!target_insn_ok_p (gen_ctx, new_insn, TRUE)) {
    MIR_remove_insn (ctx, curr_func_item, new_insn);
    return NULL;
  } else {
    MIR_remove_insn (ctx, curr_func_item, insn);
    new_insn->data = bb_insn;
    bb_insn->insn = new_insn;
    DEBUG (2, {
      fprintf (debug_file, "      changing to ");
      print_bb_insn (gen_ctx, bb_insn, TRUE);
    });
    if (combine_delete_insn (gen_ctx, def_insn, bb_insn)) (*deleted_insns_num)++;
    return new_insn;
  }
}

static MIR_insn_t combine_exts (gen_ctx_t gen_ctx, bb_insn_t bb_insn, long *deleted_insns_num) {
  MIR_insn_t def_insn, insn = bb_insn->insn;
  MIR_insn_code_t code = insn->code;
  MIR_op_t op, saved_op;
  int size, size2, sign_p = FALSE, sign2_p = FALSE, ok_p;

  switch (code) {
  case MIR_EXT8: sign2_p = TRUE;
  case MIR_UEXT8: size2 = 1; break;
  case MIR_EXT16: sign2_p = TRUE;
  case MIR_UEXT16: size2 = 2; break;
  case MIR_EXT32: sign2_p = TRUE;
  case MIR_UEXT32: size2 = 3; break;
  default: return NULL;
  }
  op = insn->ops[1];
  if (op.mode != MIR_OP_VAR || !safe_var_substitution_p (gen_ctx, op.u.var, bb_insn)) return NULL;
  def_insn = var_refs_addr[op.u.var].insn;
  switch (def_insn->code) {
  case MIR_EXT8: sign_p = TRUE;
  case MIR_UEXT8: size = 1; break;
  case MIR_EXT16: sign_p = TRUE;
  case MIR_UEXT16: size = 2; break;
  case MIR_EXT32: sign_p = TRUE;
  case MIR_UEXT32: size = 3; break;
  default: return NULL;
  }
  if (obsolete_op_p (gen_ctx, def_insn->ops[1], var_refs_addr[op.u.var].insn_num)) return NULL;
  if (size2 <= size) {
    /* [u]ext<n> b,a; ... [u]ext<m> c,b -> [u]ext<m> c,a when <m> <= <n>: */
    saved_op = insn->ops[1];
    insn->ops[1] = def_insn->ops[1];
    if (!target_insn_ok_p (gen_ctx, insn, TRUE)) {
      insn->ops[1] = saved_op;
      return NULL;
    }
    DEBUG (2, {
      fprintf (debug_file, "      changing to ");
      print_bb_insn (gen_ctx, bb_insn, TRUE);
    });
    if (combine_delete_insn (gen_ctx, def_insn, bb_insn)) (*deleted_insns_num)++;
    return insn;
  } else if (sign_p == sign2_p && size < size2) {
    /* [u]ext b,a; .. [u]ext2 c,b -> [[u]ext b,a;] .. [u]ext c,a */
    saved_op = insn->ops[1];
    insn->ops[1] = def_insn->ops[1];
    insn->code = def_insn->code;
    ok_p = target_insn_ok_p (gen_ctx, insn, TRUE);
    insn->ops[1] = saved_op;
    insn->code = code;
    if (!ok_p) return NULL;
    DEBUG (2, {
      fprintf (debug_file, "      changing ");
      print_bb_insn (gen_ctx, bb_insn, FALSE);
    });
    insn->ops[1] = def_insn->ops[1];
    insn->code = def_insn->code;
    DEBUG (2, {
      fprintf (debug_file, " to ");
      print_bb_insn (gen_ctx, bb_insn, TRUE);
    });
    if (combine_delete_insn (gen_ctx, def_insn, bb_insn)) (*deleted_insns_num)++;
    return insn;
  }
  return NULL;
}

static void setup_var_ref (gen_ctx_t gen_ctx, MIR_reg_t var, MIR_insn_t insn, size_t nop,
                           size_t insn_num, int def_p) {
  static const var_ref_t var_ref = {NULL, 0, 0};

  if (var == MIR_NON_VAR) return;
  gen_assert (VARR_LENGTH (var_ref_t, var_refs) == VARR_LENGTH (size_t, var_ref_ages));
  if (VARR_LENGTH (var_ref_t, var_refs) <= var) {
    do {
      VARR_PUSH (size_t, var_ref_ages, 0);
      VARR_PUSH (var_ref_t, var_refs, var_ref);
    } while (VARR_LENGTH (var_ref_t, var_refs) <= var);
    var_refs_addr = VARR_ADDR (var_ref_t, var_refs);
    var_ref_ages_addr = VARR_ADDR (size_t, var_ref_ages);
  }
  var_ref_ages_addr[var] = curr_bb_var_ref_age;
  var_refs_addr[var].insn = insn;
  var_refs_addr[var].nop = nop;
  var_refs_addr[var].insn_num = insn_num;
  var_refs_addr[var].def_p = def_p;
  var_refs_addr[var].del_p = FALSE;
}

static void combine (gen_ctx_t gen_ctx, int no_property_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_code_t code, new_code;
  MIR_insn_t insn, new_insn;
  bb_insn_t bb_insn, next_bb_insn;
  size_t iter, nops, i, curr_insn_num;
  MIR_op_t temp_op, *op_ref;
  MIR_reg_t early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int out_p, change_p, block_change_p, label_only_p;
  long insns_num = 0, deleted_insns_num = 0;

  gen_assert (optimize_level > 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    do {
      DEBUG (2, { fprintf (debug_file, "Processing bb%lu\n", (unsigned long) bb->index); });
      block_change_p = FALSE;
      curr_bb_var_ref_age++;
      last_mem_ref_insn_num = 0; /* means undef */
      label_only_p = TRUE;
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns), curr_insn_num = 1; bb_insn != NULL;
           bb_insn = next_bb_insn, curr_insn_num++) {
        next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
        insn = bb_insn->insn;
        nops = MIR_insn_nops (ctx, insn);
        if (insn->code == MIR_LABEL) {
          if (!label_only_p) {
            /* We can move insns with temp hard regs inside BB. It
               is important to remove labels inside BB as we use labels to find BBs for lazy BB
               generation and temp regs can be used between BBs in this generation mode. */
            DEBUG (2, {
              fprintf (debug_file, "  Remove label inside BB ");
              print_bb_insn (gen_ctx, bb_insn, TRUE);
            });
            gen_delete_insn (gen_ctx, insn);
          }
          continue;
        }
        label_only_p = FALSE;
        insns_num++;
        DEBUG (2, {
          fprintf (debug_file, "  Processing ");
          print_bb_insn (gen_ctx, bb_insn, TRUE);
        });
        if (insn->code == MIR_PRSET || insn->code == MIR_PRBEQ || insn->code == MIR_PRBNE) {
          if (no_property_p) {
            if (insn->code == MIR_PRSET
                || (insn->code == MIR_PRBEQ
                    && (insn->ops[2].mode != MIR_OP_INT || insn->ops[2].u.i != 0))
                || (insn->code == MIR_PRBNE
                    && (insn->ops[2].mode != MIR_OP_INT || insn->ops[2].u.i == 0))) {
              DEBUG (2, { fprintf (debug_file, "      removing: it is a property insn\n"); });
              gen_delete_insn (gen_ctx, insn);
            } else { /* make unconditional jump */
              new_insn = MIR_new_insn (ctx, MIR_JMP, insn->ops[0]);
              MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
              MIR_remove_insn (ctx, curr_func_item, insn);
              new_insn->data = bb_insn;
              bb_insn->insn = new_insn;
              DEBUG (2, {
                fprintf (debug_file, "      changing to ");
                print_bb_insn (gen_ctx, bb_insn, TRUE);
              });
            }
          }
          continue;
        }
        target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                              &early_clobbered_hard_reg2);
        if (early_clobbered_hard_reg1 != MIR_NON_VAR)
          setup_var_ref (gen_ctx, early_clobbered_hard_reg1, insn, 0 /* whatever */, curr_insn_num,
                         TRUE);
        if (early_clobbered_hard_reg2 != MIR_NON_VAR)
          setup_var_ref (gen_ctx, early_clobbered_hard_reg2, insn, 0 /* whatever */, curr_insn_num,
                         TRUE);
        if (MIR_call_code_p (code = insn->code)) {
          for (size_t hr = 0; hr <= MAX_HARD_REG; hr++)
            if (bitmap_bit_p (call_used_hard_regs[MIR_T_UNDEF], hr)) {
              setup_var_ref (gen_ctx, hr, insn, 0 /* whatever */, curr_insn_num, TRUE);
            }
          last_mem_ref_insn_num = curr_insn_num; /* Potentially call can change memory */
        } else if (code == MIR_VA_BLOCK_ARG) {
          last_mem_ref_insn_num = curr_insn_num; /* Change memory */
        } else if (code == MIR_RET) {
          /* ret is transformed in machinize and should be not modified after that */
        } else if ((new_insn = combine_branch_and_cmp (gen_ctx, bb_insn, &deleted_insns_num))
                     != NULL
                   || (new_insn = combine_exts (gen_ctx, bb_insn, &deleted_insns_num)) != NULL) {
          bb_insn = new_insn->data;
          insn = new_insn;
          nops = MIR_insn_nops (ctx, insn);
          block_change_p = TRUE;
        } else {
          if ((change_p = combine_substitute (gen_ctx, &bb_insn, &deleted_insns_num))) {
            insn = bb_insn->insn;
            nops = MIR_insn_nops (ctx, insn);
          } else if (!change_p
                     && (new_code = commutative_insn_code (insn->code)) != MIR_INSN_BOUND) {
            insn->code = new_code;
            temp_op = insn->ops[1];
            insn->ops[1] = insn->ops[2];
            insn->ops[2] = temp_op;
            if (combine_substitute (gen_ctx, &bb_insn, &deleted_insns_num)) {
              insn = bb_insn->insn;
              nops = MIR_insn_nops (ctx, insn);
              change_p = TRUE;
            } else {
              insn->code = code;
              temp_op = insn->ops[1];
              insn->ops[1] = insn->ops[2];
              insn->ops[2] = temp_op;
            }
          }
          if (change_p) block_change_p = TRUE;
          if (code == MIR_BSTART || code == MIR_BEND) last_mem_ref_insn_num = curr_insn_num;
        }

        for (iter = 0; iter < 2; iter++) { /* update var ref info: */
          for (i = 0; i < nops; i++) {
            op_ref = &insn->ops[i];
            MIR_insn_op_mode (ctx, insn, i, &out_p);
            if (op_ref->mode == MIR_OP_VAR && !iter == !out_p) {
              /* process in ops on 0th iteration and out ops on 1th iteration */
              setup_var_ref (gen_ctx, op_ref->u.var, insn, i, curr_insn_num, iter == 1);
            } else if (op_ref->mode == MIR_OP_VAR_MEM) {
              if (out_p && iter == 1)
                last_mem_ref_insn_num = curr_insn_num;
              else if (iter == 0) {
                setup_var_ref (gen_ctx, op_ref->u.var_mem.base, insn, i, curr_insn_num, FALSE);
                setup_var_ref (gen_ctx, op_ref->u.var_mem.index, insn, i, curr_insn_num, FALSE);
              }
            }
          }
        }
      }
    } while (block_change_p);
  }
  DEBUG (1, {
    fprintf (debug_file, "%5ld deleted combine insns out of %ld (%.1f%%)\n", deleted_insns_num,
             insns_num, 100.0 * deleted_insns_num / insns_num);
  });
}

static void init_selection (gen_ctx_t gen_ctx) {
  gen_ctx->selection_ctx = gen_malloc (gen_ctx, sizeof (struct selection_ctx));
  curr_bb_var_ref_age = 0;
  VARR_CREATE (size_t, var_ref_ages, 0);
  VARR_CREATE (var_ref_t, var_refs, 0);
  VARR_CREATE (MIR_reg_t, insn_vars, 0);
  VARR_CREATE (size_t, changed_op_numbers, 16);
  VARR_CREATE (MIR_op_t, last_right_ops, 16);
  vars_bitmap = bitmap_create ();
}

static void finish_selection (gen_ctx_t gen_ctx) {
  VARR_DESTROY (size_t, var_ref_ages);
  VARR_DESTROY (var_ref_t, var_refs);
  VARR_DESTROY (MIR_reg_t, insn_vars);
  VARR_DESTROY (size_t, changed_op_numbers);
  VARR_DESTROY (MIR_op_t, last_right_ops);
  bitmap_destroy (vars_bitmap);
  free (gen_ctx->selection_ctx);
  gen_ctx->selection_ctx = NULL;
}

/* New Page */

/* Dead code elimnination */

#define live_out out

static int reachable_bo_exists_p (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  for (; bb_insn != NULL; bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
    if (bb_insn->insn->code == MIR_BO || bb_insn->insn->code == MIR_UBO
        || bb_insn->insn->code == MIR_BNO || bb_insn->insn->code == MIR_UBNO)
      return TRUE;
    else if (bb_insn->insn->code != MIR_MOV && bb_insn->insn->code != MIR_EXT32
             && bb_insn->insn->code != MIR_UEXT32)
      break;
  return FALSE;
}

static void dead_code_elimination (gen_ctx_t gen_ctx) {
  MIR_insn_t insn, nop_insn;
  bb_insn_t bb_insn, prev_bb_insn;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, reg_def_p, dead_p, mem_p;
  bitmap_t live;
  insn_var_iterator_t insn_var_iter;
  long dead_insns_num = 0;
  bitmap_t global_hard_regs
    = _MIR_get_module_global_var_hard_regs (gen_ctx->ctx, curr_func_item->module);

  gen_assert (optimize_level > 0);
  DEBUG (2, { fprintf (debug_file, "+++++++++++++Dead code elimination:\n"); });
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      reg_def_p = FALSE;
      dead_p = TRUE;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
        if (!out_p) continue;
        reg_def_p = TRUE;
        if (bitmap_clear_bit_p (live, var) || bitmap_bit_p (addr_regs, var)) dead_p = FALSE;
      }
      if (!reg_def_p) dead_p = FALSE;
      if (dead_p && !MIR_call_code_p (insn->code) && insn->code != MIR_RET && insn->code != MIR_JRET
          && insn->code != MIR_ALLOCA && insn->code != MIR_BSTART && insn->code != MIR_BEND
          && insn->code != MIR_VA_START && insn->code != MIR_VA_ARG && insn->code != MIR_VA_END
          && !(MIR_overflow_insn_code_p (insn->code)
               && reachable_bo_exists_p (gen_ctx, DLIST_NEXT (bb_insn_t, bb_insn)))
          && !(insn->ops[0].mode == MIR_OP_VAR
               && (insn->ops[0].u.var == FP_HARD_REG || insn->ops[0].u.var == SP_HARD_REG))) {
        DEBUG (2, {
          fprintf (debug_file, "  Removing dead insn %-5lu", (unsigned long) bb_insn->index);
          MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        });
        if (DLIST_HEAD (bb_insn_t, bb->bb_insns) == DLIST_TAIL (bb_insn_t, bb->bb_insns)) {
          gen_assert (bb_insn == DLIST_HEAD (bb_insn_t, bb->bb_insns));
          nop_insn = MIR_new_insn_arr (gen_ctx->ctx, MIR_USE, 0, NULL);
          DEBUG (2, {
            fprintf (debug_file,
                     "  Adding nop to keep bb%lu non-empty: ", (unsigned long) bb->index);
            MIR_output_insn (gen_ctx->ctx, debug_file, nop_insn, curr_func_item->u.func, TRUE);
          });
          gen_add_insn_after (gen_ctx, insn, nop_insn);
        }
        gen_delete_insn (gen_ctx, insn);
        dead_insns_num++;
        continue;
      }
      if (MIR_call_code_p (insn->code)) {
        bitmap_and_compl (live, live, call_used_hard_regs[MIR_T_UNDEF]);
        if (global_hard_regs != NULL) bitmap_ior (live, live, global_hard_regs);
      }
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p) {
        if (!out_p) bitmap_set_bit_p (live, var);
      }
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_VAR)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_VAR)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg2);
      if (MIR_call_code_p (insn->code)) bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
  DEBUG (1, { fprintf (debug_file, "%5ld removed dead insns\n", dead_insns_num); });
}

#undef live_out

/* New Page */

/* SSA dead code elimination */

static int dead_insn_p (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  MIR_insn_t insn = bb_insn->insn;
  int op_num, out_p, mem_p, output_exists_p = FALSE;
  MIR_reg_t var;
  insn_var_iterator_t iter;
  ssa_edge_t ssa_edge;

  /* check control insns with possible output: */
  if (MIR_call_code_p (insn->code) || insn->code == MIR_ALLOCA || insn->code == MIR_BSTART
      || insn->code == MIR_VA_START || insn->code == MIR_VA_ARG
      || (insn->nops > 0 && insn->ops[0].mode == MIR_OP_VAR
          && (insn->ops[0].u.var == FP_HARD_REG || insn->ops[0].u.var == SP_HARD_REG)))
    return FALSE;
  if (fake_insn_p (gen_ctx, bb_insn)) return FALSE;
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
    if (!out_p) continue;
    output_exists_p = TRUE;
    if (mem_p || (ssa_edge = insn->ops[op_num].data) != NULL) return FALSE;
  }
  if (!MIR_overflow_insn_code_p (insn->code)
      || !reachable_bo_exists_p (gen_ctx, DLIST_NEXT (bb_insn_t, bb_insn)))
    return output_exists_p;
  return FALSE;
}

static void ssa_dead_code_elimination (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, def;
  int op_num, out_p, mem_p;
  MIR_reg_t var;
  insn_var_iterator_t iter;
  ssa_edge_t ssa_edge;
  long dead_insns_num = 0;

  DEBUG (2, { fprintf (debug_file, "+++++++++++++Dead code elimination:\n"); });
  gen_assert (def_use_repr_p);
  VARR_TRUNC (bb_insn_t, temp_bb_insns, 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      if (dead_insn_p (gen_ctx, bb_insn)) VARR_PUSH (bb_insn_t, temp_bb_insns, bb_insn);
  while (VARR_LENGTH (bb_insn_t, temp_bb_insns) != 0) {
    bb_insn = VARR_POP (bb_insn_t, temp_bb_insns);
    insn = bb_insn->insn;
    DEBUG (2, {
      fprintf (debug_file, "  Removing dead insn %-5lu", (unsigned long) bb_insn->index);
      print_bb_insn (gen_ctx, bb_insn, FALSE);
    });
    FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p) {
      if (out_p) continue;
      if ((ssa_edge = insn->ops[op_num].data) == NULL) continue;
      def = ssa_edge->def;
      remove_ssa_edge (gen_ctx, ssa_edge);
      if (dead_insn_p (gen_ctx, def)) VARR_PUSH (bb_insn_t, temp_bb_insns, def);
    }
    gen_delete_insn (gen_ctx, insn);
    dead_insns_num++;
  }
  DEBUG (1, { fprintf (debug_file, "%5ld removed SSA dead insns\n", dead_insns_num); });
}

/* New Page */

#if !MIR_NO_GEN_DEBUG
#include "real-time.h"
#endif

#if MIR_GEN_CALL_TRACE
static void *print_and_execute_wrapper (gen_ctx_t gen_ctx, MIR_item_t called_func) {
  gen_assert (called_func->item_type == MIR_func_item);
  fprintf (stderr, "Calling %s\n", called_func->u.func->name);
  return called_func->u.func->machine_code;
}
#endif

#if MIR_PARALLEL_GEN
static void parallel_error (MIR_context_t ctx, const char *err_message) {
  MIR_get_error_func (ctx) (MIR_parallel_error, err_message);
}
#endif

static const int collect_bb_stat_p = FALSE;

static void *generate_func_code (MIR_context_t ctx, int gen_num, MIR_item_t func_item,
                                 int machine_code_p) {
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  gen_ctx_t gen_ctx;
  uint8_t *code;
  void *machine_code = NULL;
  size_t code_len = 0;
  double start_time = real_usec_time ();
  uint32_t bbs_num;

#if !MIR_PARALLEL_GEN
  gen_num = 0;
#endif
  gen_assert (gen_num >= 0 && gen_num < all_gen_ctx->gens_num);
  gen_ctx = &all_gen_ctx->gen_ctx[gen_num];
  gen_assert (func_item->item_type == MIR_func_item && func_item->data == NULL);
  if (func_item->u.func->machine_code != NULL) {
    gen_assert (func_item->u.func->call_addr != NULL);
    _MIR_redirect_thunk (ctx, func_item->addr, func_item->u.func->call_addr);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++The code for %s has been already generated\n",
               MIR_item_name (ctx, func_item));
    });
    return func_item->addr;
  }
  DEBUG (0, {
    fprintf (debug_file, "Code generation of function %s:\n", MIR_item_name (ctx, func_item));
  });
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR before generator:\n");
    MIR_output_item (ctx, debug_file, func_item);
  });
  curr_func_item = func_item;
  _MIR_duplicate_func_insns (ctx, func_item);
  curr_cfg = func_item->data = gen_malloc (gen_ctx, sizeof (struct func_cfg));
  build_func_cfg (gen_ctx);
  bbs_num = curr_bb_index;
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after building CFG:\n");
    print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, NULL);
  });
  if (optimize_level >= 2 && !addr_insn_p && clone_bbs (gen_ctx)) {
    /* do not clone bbs before addr transformation: it can prevent addr transformations */
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after cloning BBs:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, NULL);
    });
  }
  if (optimize_level >= 2) {
    build_ssa (gen_ctx, !addr_insn_p);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after building SSA%s:\n",
               addr_insn_p ? " for address transformation" : "");
      print_varr_insns (gen_ctx, "undef init", undef_insns);
      print_varr_insns (gen_ctx, "arg init", arg_bb_insns);
      fprintf (debug_file, "\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2 && addr_insn_p) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++Transform Addr Insns and cloning BBs:\n"); });
    transform_addrs (gen_ctx);
    undo_build_ssa (gen_ctx);
    clone_bbs (gen_ctx);
    build_ssa (gen_ctx, TRUE);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after Addr Insns Transformation and cloning BBs:\n");
      print_varr_insns (gen_ctx, "undef init", undef_insns);
      print_varr_insns (gen_ctx, "arg init", arg_bb_insns);
      fprintf (debug_file, "\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 1) {
    build_loop_tree (gen_ctx);
    DEBUG (2, { print_loop_tree (gen_ctx, TRUE); });
  }
  if (optimize_level >= 2 && licm (gen_ctx)) {
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after loop invariant motion:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++GVN:\n"); });
    gvn (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after GVN:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
    gvn_clear (gen_ctx);
  }
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++Copy Propagation:\n"); });
    copy_prop (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after Copy Propagation:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++DSE:\n"); });
    dse (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after DSE:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2) {
    ssa_dead_code_elimination (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after dead code elimination:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2 && pressure_relief (gen_ctx)) {
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after pressure relief:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
    });
  }
  if (optimize_level >= 2) {
    make_conventional_ssa (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after transformation to conventional SSA:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
    });
    undo_build_ssa (gen_ctx);
  }
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++Jump optimization:\n"); });
    jump_opt (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after Jump optimization:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
  target_machinize (gen_ctx);
  make_io_dup_op_insns (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after machinize:\n");
    print_CFG (gen_ctx, FALSE, FALSE, TRUE, TRUE, NULL);
  });
  if (optimize_level >= 1) {
    calculate_func_cfg_live_info (gen_ctx, FALSE);
    DEBUG (2, {
      add_bb_insn_dead_vars (gen_ctx);
      fprintf (debug_file, "+++++++++++++MIR after building live_info:\n");
      print_loop_tree (gen_ctx, TRUE);
      print_CFG (gen_ctx, TRUE, TRUE, FALSE, FALSE, output_bb_live_info);
    });
  }
  if (optimize_level >= 2) {
    coalesce (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after coalescing:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, output_bb_border_live_info);
    });
  }
  calculate_func_cfg_live_info (gen_ctx, TRUE);
  DEBUG (2, {
    if (optimize_level > 0) add_bb_insn_dead_vars (gen_ctx);
    fprintf (debug_file, "+++++++++++++MIR after building live_info:\n");
    print_loop_tree (gen_ctx, TRUE);
    print_CFG (gen_ctx, TRUE, TRUE, TRUE, FALSE, output_bb_live_info);
  });
  reg_alloc (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after RA:\n");
    print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, NULL);
  });
  if (optimize_level >= 2) {
    calculate_func_cfg_live_info (gen_ctx, FALSE);
    add_bb_insn_dead_vars (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR before combine:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, output_bb_live_info);
    });
    combine (gen_ctx, machine_code_p); /* After combine the BB live info is still valid */
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after combine:\n");
      print_CFG (gen_ctx, FALSE, FALSE, TRUE, FALSE, NULL);
    });
    dead_code_elimination (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after dead code elimination after 2nd combine:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, FALSE, output_bb_live_info);
    });
  }
  target_make_prolog_epilog (gen_ctx, func_used_hard_regs, func_stack_slots_num);
  target_split_insns (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after forming prolog/epilog and insn splitting:\n");
    print_CFG (gen_ctx, FALSE, FALSE, TRUE, TRUE, NULL);
  });
  if (machine_code_p) {
    code = target_translate (gen_ctx, &code_len);
    machine_code = func_item->u.func->call_addr = _MIR_publish_code (ctx, code, code_len);
    target_rebase (gen_ctx, func_item->u.func->call_addr);
#if MIR_GEN_CALL_TRACE
    func_item->u.func->call_addr = _MIR_get_wrapper (ctx, func_item, print_and_execute_wrapper);
#endif
    DEBUG (2, {
      _MIR_dump_code (NULL, gen_ctx->gen_num, machine_code, code_len);
      fprintf (debug_file, "code size = %lu:\n", (unsigned long) code_len);
    });
    _MIR_redirect_thunk (ctx, func_item->addr, func_item->u.func->call_addr);
  }
  if (optimize_level != 0) destroy_loop_tree (gen_ctx, curr_cfg->root_loop_node);
  destroy_func_cfg (gen_ctx);
  if (collect_bb_stat_p) {
#if MIR_PARALLEL_GEN
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
    all_gen_ctx->overall_bbs_num += bbs_num;
#if MIR_PARALLEL_GEN
    if (mir_cond_broadcast (&done_signal)) parallel_error (ctx, "error in cond broadcast");
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
  }
  if (!machine_code_p) return NULL;
  DEBUG (0, {
    fprintf (debug_file,
             "  Code generation for %s: %lu MIR insns (addr=%llx, len=%lu) -- time %.2f ms\n",
             MIR_item_name (ctx, func_item),
             (long unsigned) DLIST_LENGTH (MIR_insn_t, func_item->u.func->insns),
             (unsigned long long) machine_code, (unsigned long) code_len,
             (real_usec_time () - start_time) / 1000.0);
  });
  _MIR_restore_func_insns (ctx, func_item);
  /* ??? We should use atomic here but c2mir does not implement them yet.  */
#if MIR_PARALLEL_GEN
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
  func_item->u.func->machine_code = machine_code;
#if MIR_PARALLEL_GEN
  if (mir_cond_broadcast (&done_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
  return func_item->addr;
}

void *MIR_gen (MIR_context_t ctx, int gen_num, MIR_item_t func_item) {
  return generate_func_code (ctx, gen_num, func_item, TRUE);
}

void MIR_gen_set_debug_file (MIR_context_t ctx, int gen_num, FILE *f) {
#if !MIR_NO_GEN_DEBUG
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  gen_ctx_t gen_ctx;

  if (all_gen_ctx == NULL) {
    fprintf (stderr, "Calling MIR_gen_set_debug_file before MIR_gen_init -- good bye\n");
    exit (1);
  }
#if !MIR_PARALLEL_GEN
  gen_num = 0;
#endif
  gen_assert (gen_num >= 0 && gen_num < all_gen_ctx->gens_num);
  gen_ctx = &all_gen_ctx->gen_ctx[gen_num];
  debug_file = f;
#endif
}

void MIR_gen_set_debug_level (MIR_context_t ctx, int gen_num, int level) {
#if !MIR_NO_GEN_DEBUG
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  gen_ctx_t gen_ctx;

  if (all_gen_ctx == NULL) {
    fprintf (stderr, "Calling MIR_gen_set_debug_level before MIR_gen_init -- good bye\n");
    exit (1);
  }
#if !MIR_PARALLEL_GEN
  gen_num = 0;
#endif
  gen_assert (gen_num >= 0 && gen_num < all_gen_ctx->gens_num);
  gen_ctx = &all_gen_ctx->gen_ctx[gen_num];
  debug_level = level;
#endif
}

void MIR_gen_set_optimize_level (MIR_context_t ctx, int gen_num, unsigned int level) {
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  gen_ctx_t gen_ctx;

#if !MIR_PARALLEL_GEN
  gen_num = 0;
#endif
  gen_assert (gen_num >= 0 && gen_num < all_gen_ctx->gens_num);
  gen_ctx = &all_gen_ctx->gen_ctx[gen_num];
  optimize_level = level;
}

static void generate_bb_version_machine_code (gen_ctx_t gen_ctx, bb_version_t bb_version);
static void *bb_version_generator (gen_ctx_t gen_ctx, bb_version_t bb_version);

/* create bb stubs and set up label data to the corresponding bb stub */
/* todo finish bb on calls ??? */
static void create_bb_stubs (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn, last_lab_insn;
  size_t n_bbs;
  int new_bb_p = TRUE;
  bb_stub_t bb_stubs;

  n_bbs = 0;
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    if (insn->code == MIR_LABEL || new_bb_p) {
      last_lab_insn = insn;
      if (insn->code == MIR_LABEL)
        for (insn = DLIST_NEXT (MIR_insn_t, insn); insn != NULL && insn->code == MIR_LABEL;
             last_lab_insn = insn, insn = DLIST_NEXT (MIR_insn_t, insn))
          ;
      insn = last_lab_insn;
      n_bbs++;
    }
    new_bb_p = MIR_any_branch_code_p (insn->code) || insn->code == MIR_RET || insn->code == MIR_JRET
               || insn->code == MIR_PRBEQ || insn->code == MIR_PRBNE;
  }
  curr_func_item->data = bb_stubs = gen_malloc (gen_ctx, sizeof (struct bb_stub) * n_bbs);
  n_bbs = 0;
  new_bb_p = TRUE;
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    if (insn->code == MIR_LABEL || new_bb_p) {
      if (n_bbs != 0) bb_stubs[n_bbs - 1].last_insn = DLIST_PREV (MIR_insn_t, insn);
      bb_stubs[n_bbs].func_item = curr_func_item;
      bb_stubs[n_bbs].first_insn = insn;
      DLIST_INIT (bb_version_t, bb_stubs[n_bbs].bb_versions);
      last_lab_insn = insn;
      if (insn->code == MIR_LABEL) {
        insn->data = &bb_stubs[n_bbs];
        for (insn = DLIST_NEXT (MIR_insn_t, insn); insn != NULL && insn->code == MIR_LABEL;
             last_lab_insn = insn, insn = DLIST_NEXT (MIR_insn_t, insn))
          insn->data = &bb_stubs[n_bbs];
      }
      insn = last_lab_insn;
      n_bbs++;
    }
    new_bb_p = MIR_any_branch_code_p (insn->code) || insn->code == MIR_RET || insn->code == MIR_JRET
               || insn->code == MIR_PRBEQ || insn->code == MIR_PRBNE;
  }
  bb_stubs[n_bbs - 1].last_insn = DLIST_TAIL (MIR_insn_t, curr_func_item->u.func->insns);
  if (debug_file != NULL) {
    fprintf (debug_file, "BBs for lazy code generation:\n");
    for (size_t i = 0; i < n_bbs; i++) {
      fprintf (debug_file, "  BBStub%lx:\n", (long unsigned) &bb_stubs[i]);
      for (insn = bb_stubs[i].first_insn;; insn = DLIST_NEXT (MIR_insn_t, insn)) {
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        if (insn == bb_stubs[i].last_insn) break;
      }
    }
  }
}

static bb_version_t get_bb_version (gen_ctx_t gen_ctx, bb_stub_t bb_stub, uint32_t n_attrs,
                                    spot_attr_t *attrs, int call_p, void **addr) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_version_t bb_version;

  if ((bb_version = DLIST_HEAD (bb_version_t, bb_stub->bb_versions)) != NULL) {
    VARR_PUSH (target_bb_version_t, target_succ_bb_versions, NULL);
    *addr = bb_version->addr;
    return bb_version;
  }
  bb_version = gen_malloc (gen_ctx, sizeof (struct bb_version)
                                      + (n_attrs <= 1 ? 0 : n_attrs) * sizeof (spot_attr_t));
  target_init_bb_version_data (&bb_version->target_data);
  VARR_PUSH (target_bb_version_t, target_succ_bb_versions,
             call_p ? NULL : &bb_version->target_data);
  bb_version->bb_stub = bb_stub;
  bb_version->n_attrs = n_attrs;
  if (n_attrs != 0) memcpy (bb_version->attrs, attrs, n_attrs * sizeof (spot_attr_t));
  bb_version->call_p = call_p;
  DLIST_APPEND (bb_version_t, bb_stub->bb_versions, bb_version);
  bb_version->machine_code = NULL;
  *addr = bb_version->addr = _MIR_get_bb_thunk (ctx, bb_version, bb_wrapper);
  return bb_version;
}

#if MIR_PARALLEL_GEN
static void *func_generator (void *arg) {
  func_or_bb_t func_or_bb;
  gen_ctx_t gen_ctx = arg;
  struct all_gen_ctx *all_gen_ctx = gen_ctx->all_gen_ctx;
  MIR_context_t ctx = all_gen_ctx->ctx;
  size_t len;

  for (;;) {
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    while (VARR_LENGTH (func_or_bb_t, code_to_generate) <= funcs_start)
      if (mir_cond_wait (&generate_signal, &queue_mutex))
        parallel_error (ctx, "error in cond wait");
    func_or_bb = VARR_GET (func_or_bb_t, code_to_generate, funcs_start);
    if (func_or_bb.u.func_item == NULL) {
      if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
      break;
    }
    funcs_start++;
    if (funcs_start > 64 && VARR_LENGTH (func_or_bb_t, code_to_generate) < 2 * funcs_start) {
      len = VARR_LENGTH (func_or_bb_t, code_to_generate) - funcs_start;
      memmove (VARR_ADDR (func_or_bb_t, code_to_generate), /* compact */
               VARR_ADDR (func_or_bb_t, code_to_generate) + funcs_start,
               len * sizeof (func_or_bb_t));
      VARR_TRUNC (func_or_bb_t, code_to_generate, len);
      funcs_start = 0;
    }
    gen_ctx->busy_p = TRUE;
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
    if (func_or_bb.func_p) {
      generate_func_code (gen_ctx->ctx, gen_ctx->gen_num, func_or_bb.u.func_item,
                          func_or_bb.full_p);
      if (!func_or_bb.full_p) {
        create_bb_stubs (gen_ctx);
        void *addr;
        get_bb_version (gen_ctx, &((struct bb_stub *) func_or_bb.u.func_item->data)[0], 0, NULL,
                        TRUE, &addr);
        _MIR_redirect_thunk (ctx, func_or_bb.u.func_item->addr, addr);
#if MIR_PARALLEL_GEN
        if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
        func_or_bb.u.func_item->u.func->machine_code = addr; /* ??? done flag */
#if MIR_PARALLEL_GEN
        if (mir_cond_broadcast (&done_signal)) parallel_error (ctx, "error in cond broadcast");
        if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
      }
    } else {
      generate_bb_version_machine_code (gen_ctx, func_or_bb.u.bb_version);
    }
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    gen_ctx->busy_p = FALSE;
    if (mir_cond_signal (&done_signal)) parallel_error (ctx, "error in cond signal");
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  }
  return NULL;
}

static void signal_threads_to_finish (struct all_gen_ctx *all_gen_ctx) {
  MIR_context_t ctx = all_gen_ctx->ctx;

  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  funcs_start = 0;
  VARR_TRUNC (func_or_bb_t, code_to_generate, 0);
  VARR_PUSH (func_or_bb_t, code_to_generate, null_func_or_bb); /* flag to finish threads */
  if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
}
#endif

void MIR_gen_init (MIR_context_t ctx, int gens_num) {
  struct all_gen_ctx **all_gen_ctx_ptr = all_gen_ctx_loc (ctx), *all_gen_ctx;
  gen_ctx_t gen_ctx;

#if !MIR_PARALLEL_GEN
  gens_num = 1;
#else
  if (gens_num < 1) gens_num = 1;
#endif
  *all_gen_ctx_ptr = all_gen_ctx
    = gen_malloc (NULL, sizeof (struct all_gen_ctx) + sizeof (struct gen_ctx) * (gens_num - 1));
  all_gen_ctx->ctx = ctx;
  all_gen_ctx->gens_num = gens_num;
#if MIR_PARALLEL_GEN
  /* Create threads, mutex, and conditional for generators [1, gens_num): */
  funcs_start = 0;
  VARR_CREATE (func_or_bb_t, code_to_generate, 0);
  if (mir_mutex_init (&queue_mutex, NULL) != 0) {
    (*MIR_get_error_func (ctx)) (MIR_parallel_error, "can not create a generator thread lock");
  } else if (mir_cond_init (&generate_signal, NULL) != 0) {
    mir_mutex_destroy (&queue_mutex);
    (*MIR_get_error_func (ctx)) (MIR_parallel_error, "can not create a generator thread signal");
  } else if (mir_cond_init (&done_signal, NULL) != 0) {
    mir_cond_destroy (&generate_signal);
    mir_mutex_destroy (&queue_mutex);
    (*MIR_get_error_func (ctx)) (MIR_parallel_error, "can not create a generator thread signal");
  } else {
    for (int i = 0; i < gens_num; i++) {
      gen_ctx = &all_gen_ctx->gen_ctx[i];
      gen_ctx->busy_p = FALSE;
      gen_ctx->gen_num = i;
      gen_ctx->all_gen_ctx = all_gen_ctx;
      if (mir_thread_create (&gen_ctx->gen_thread, NULL, func_generator, gen_ctx) != 0) {
        signal_threads_to_finish (all_gen_ctx);
        for (int j = 0; j < i; j++) mir_thread_join (all_gen_ctx->gen_ctx[j].gen_thread, NULL);
        mir_cond_destroy (&done_signal);
        mir_cond_destroy (&generate_signal);
        mir_mutex_destroy (&queue_mutex);
        (*MIR_get_error_func (ctx)) (MIR_parallel_error, "can not create a generator thread");
      }
    }
  }
#endif
  for (int n = 0; n < gens_num; n++) {
    gen_ctx = &all_gen_ctx->gen_ctx[n];
#if !MIR_PARALLEL_GEN
    gen_ctx->all_gen_ctx = all_gen_ctx;
    gen_ctx->gen_num = n;
#endif
    gen_ctx->ctx = ctx;
    optimize_level = 2;
    gen_ctx->target_ctx = NULL;
    gen_ctx->data_flow_ctx = NULL;
    gen_ctx->gvn_ctx = NULL;
    gen_ctx->lr_ctx = NULL;
    gen_ctx->ra_ctx = NULL;
    gen_ctx->selection_ctx = NULL;
#if !MIR_NO_GEN_DEBUG
    debug_file = NULL;
    debug_level = 100;
#endif
    addr_insn_p = FALSE;
    VARR_CREATE (MIR_op_t, temp_ops, 16);
    VARR_CREATE (bb_insn_t, temp_bb_insns, 16);
    VARR_CREATE (bb_insn_t, temp_bb_insns2, 16);
    VARR_CREATE (loop_node_t, loop_nodes, 32);
    VARR_CREATE (loop_node_t, queue_nodes, 32);
    VARR_CREATE (loop_node_t, loop_entries, 16);
    VARR_CREATE (mem_attr_t, mem_attrs, 32);
    VARR_CREATE (target_bb_version_t, target_succ_bb_versions, 16);
    VARR_CREATE (void_ptr_t, succ_bb_addrs, 16);
    VARR_CREATE (spot_attr_t, spot_attrs, 32);
    VARR_CREATE (spot_attr_t, spot2attr, 32);
    temp_bitmap = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    temp_bitmap2 = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    temp_bitmap3 = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    init_dead_vars (gen_ctx);
    init_data_flow (gen_ctx);
    init_ssa (gen_ctx);
    init_gvn (gen_ctx);
    init_live_ranges (gen_ctx);
    init_coalesce (gen_ctx);
    init_ra (gen_ctx);
    init_selection (gen_ctx);
    target_init (gen_ctx);
    max_int_hard_regs = max_fp_hard_regs = 0;
    for (int i = 0; i <= MAX_HARD_REG; i++) {
      if (target_fixed_hard_reg_p (i)) continue;
      target_hard_reg_type_ok_p (i, MIR_T_I32) ? max_int_hard_regs++ : max_fp_hard_regs++;
    }
    for (MIR_type_t type = MIR_T_I8; type < MIR_T_BOUND; type++) {
      call_used_hard_regs[type] = bitmap_create2 (MAX_HARD_REG + 1);
      for (int i = 0; i <= MAX_HARD_REG; i++) {
        /* We need call_used_hard_regs even for fixed regs in combine. */
        if (target_call_used_hard_reg_p (i, type)) bitmap_set_bit_p (call_used_hard_regs[type], i);
      }
    }
    tied_regs = bitmap_create2 (256);
    addr_regs = bitmap_create2 (256);
    insn_to_consider = bitmap_create2 (1024);
    func_used_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
    bb_wrapper = _MIR_get_bb_wrapper (ctx, gen_ctx, bb_version_generator);
  }
  all_gen_ctx->overall_bbs_num = all_gen_ctx->overall_gen_bbs_num = 0;
}

void MIR_gen_finish (MIR_context_t ctx) {
  struct all_gen_ctx **all_gen_ctx_ptr = all_gen_ctx_loc (ctx), *all_gen_ctx = *all_gen_ctx_ptr;
  gen_ctx_t gen_ctx;

#if MIR_PARALLEL_GEN
  signal_threads_to_finish (all_gen_ctx);
  for (int i = 0; i < all_gen_ctx->gens_num; i++)
    mir_thread_join (all_gen_ctx->gen_ctx[i].gen_thread, NULL);
  if (mir_mutex_destroy (&queue_mutex) != 0 || mir_cond_destroy (&generate_signal) != 0
      || mir_cond_destroy (&done_signal) != 0) {  // ???
    (*MIR_get_error_func (all_gen_ctx->ctx)) (MIR_parallel_error,
                                              "can not destroy generator mutex or signals");
  }
  VARR_DESTROY (func_or_bb_t, code_to_generate);
#endif
  for (int i = 0; i < all_gen_ctx->gens_num; i++) {
    gen_ctx = &all_gen_ctx->gen_ctx[i];
    finish_data_flow (gen_ctx);
    finish_ssa (gen_ctx);
    finish_gvn (gen_ctx);
    finish_live_ranges (gen_ctx);
    finish_coalesce (gen_ctx);
    finish_ra (gen_ctx);
    finish_selection (gen_ctx);
    for (MIR_type_t type = MIR_T_I8; type < MIR_T_BOUND; type++)
      bitmap_destroy (call_used_hard_regs[type]);
    bitmap_destroy (tied_regs);
    bitmap_destroy (addr_regs);
    bitmap_destroy (insn_to_consider);
    bitmap_destroy (func_used_hard_regs);
    target_finish (gen_ctx);
    finish_dead_vars (gen_ctx);
    free (gen_ctx->data_flow_ctx);
    bitmap_destroy (temp_bitmap);
    bitmap_destroy (temp_bitmap2);
    bitmap_destroy (temp_bitmap3);
    VARR_DESTROY (MIR_op_t, temp_ops);
    VARR_DESTROY (bb_insn_t, temp_bb_insns);
    VARR_DESTROY (bb_insn_t, temp_bb_insns2);
    VARR_DESTROY (loop_node_t, loop_nodes);
    VARR_DESTROY (loop_node_t, queue_nodes);
    VARR_DESTROY (loop_node_t, loop_entries);
    VARR_DESTROY (mem_attr_t, mem_attrs);
    VARR_DESTROY (target_bb_version_t, target_succ_bb_versions);
    VARR_DESTROY (void_ptr_t, succ_bb_addrs);
    VARR_DESTROY (spot_attr_t, spot_attrs);
    VARR_DESTROY (spot_attr_t, spot2attr);
  }
  if (collect_bb_stat_p)
    fprintf (stderr, "Overall bbs num = %llu, generated bbs num = %llu\n",
             all_gen_ctx->overall_bbs_num, all_gen_ctx->overall_gen_bbs_num);
  free (all_gen_ctx);
  *all_gen_ctx_ptr = NULL;
}

void MIR_set_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  if (func_item == NULL) return; /* finish setting interfaces */
  MIR_gen (ctx, 0, func_item);
}
void MIR_set_parallel_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
#if !MIR_PARALLEL_GEN
  if (func_item == NULL) return; /* finish setting interfaces */
  MIR_gen (ctx, 0, func_item);
#else
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  func_or_bb_t func_or_bb;

  if (func_item == NULL) { /* finish setting interfaces */
    size_t i;
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    func_or_bb.func_p = func_or_bb.full_p = TRUE;
    func_or_bb.u.func_item = NULL;
    VARR_PUSH (func_or_bb_t, code_to_generate, func_or_bb);
    for (;;) {
      for (i = 0; i < all_gen_ctx->gens_num; i++)
        if (all_gen_ctx->gen_ctx[i].busy_p) break;
      if (VARR_LENGTH (func_or_bb_t, code_to_generate) <= funcs_start + 1
          && i >= all_gen_ctx->gens_num)
        break; /* nothing to generate and nothing is being generated */
      if (mir_cond_wait (&done_signal, &queue_mutex)) parallel_error (ctx, "error in cond wait");
    }
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  } else {
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    func_or_bb.func_p = func_or_bb.full_p = TRUE;
    func_or_bb.u.func_item = func_item;
    VARR_PUSH (func_or_bb_t, code_to_generate, func_or_bb);
    if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  }
#endif
}

/* Lazy func generation is done right away. */
static void generate_func_and_redirect (MIR_context_t ctx, MIR_item_t func_item, int full_p) {
#if !MIR_PARALLEL_GEN
  generate_func_code (ctx, 0, func_item, full_p);
  if (!full_p) {
    struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
    gen_ctx_t gen_ctx = &all_gen_ctx->gen_ctx[0];
    void *addr;

    create_bb_stubs (gen_ctx);
    (void) get_bb_version (gen_ctx, &((struct bb_stub *) func_item->data)[0], 0, NULL, TRUE, &addr);
    _MIR_redirect_thunk (ctx, func_item->addr, addr);
  }
#else
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  MIR_func_t func = func_item->u.func;
  func_or_bb_t func_or_bb;

  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  func_or_bb.func_p = TRUE;
  func_or_bb.full_p = full_p;
  func_or_bb.u.func_item = func_item;
  VARR_PUSH (func_or_bb_t, code_to_generate, func_or_bb);
  if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  for (;;) {
    if (func->machine_code != NULL) break;
    if (mir_cond_wait (&done_signal, &queue_mutex)) parallel_error (ctx, "error in cond wait");
  }
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
#endif
}

static void *generate_func_and_redirect_to_func_code (MIR_context_t ctx, MIR_item_t func_item) {
  generate_func_and_redirect (ctx, func_item, TRUE);
  return func_item->u.func->machine_code;
}

void MIR_set_lazy_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  void *addr;

  if (func_item == NULL) return;
  addr = _MIR_get_wrapper (ctx, func_item, generate_func_and_redirect_to_func_code);
  _MIR_redirect_thunk (ctx, func_item->addr, addr);
}

static void set_spot2attr (gen_ctx_t gen_ctx, const spot_attr_t *attr) {
  gen_assert (attr->spot != 0 && attr->prop != 0);
  while (VARR_LENGTH (spot_attr_t, spot2attr) <= attr->spot)
    VARR_PUSH (spot_attr_t, spot2attr, *attr);
  VARR_SET (spot_attr_t, spot2attr, attr->spot, *attr);
}

#define FIRST_MEM_SPOT (MAX_HARD_REG + 2)
static int mem_spot_p (gen_ctx_t gen_ctx, uint32_t spot) { return spot >= FIRST_MEM_SPOT; }

static uint32_t mem_nloc2spot (gen_ctx_t gen_ctx, uint32_t nloc) {
  return nloc == 0 ? 0 : nloc + 1 + MAX_HARD_REG + 1;
}

static uint32_t op2spot (gen_ctx_t gen_ctx, MIR_op_t *op_ref) {
  if (op_ref->mode == MIR_OP_VAR) return op_ref->u.var + 1;
  if (op_ref->mode == MIR_OP_VAR_MEM) return mem_nloc2spot (gen_ctx, op_ref->u.var_mem.nloc);
  return 0;
}

static void generate_bb_version_machine_code (gen_ctx_t gen_ctx, bb_version_t bb_version) {
  MIR_context_t ctx = gen_ctx->ctx;
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  int skip_p;
  bb_stub_t branch_bb_stub, bb_stub = bb_version->bb_stub;
  MIR_insn_t curr_insn, new_insn, next_insn;
  void *addr;
  uint8_t *code;
  size_t code_len, nel;
  uint32_t dest_spot, src_spot, max_spot = 0;
  bitmap_t nonzero_property_spots = temp_bitmap;
  bitmap_iterator_t bi;
  spot_attr_t spot_attr;

  bitmap_clear (nonzero_property_spots);
  for (size_t i = 0; i < bb_version->n_attrs; i++) {
    bitmap_set_bit_p (nonzero_property_spots, bb_version->attrs[i].spot);
    set_spot2attr (gen_ctx, &bb_version->attrs[i]);
  }
  if (bb_version->n_attrs != 0) max_spot = bb_version->attrs[bb_version->n_attrs - 1].spot;
  VARR_TRUNC (target_bb_version_t, target_succ_bb_versions, 0);
  target_bb_translate_start (gen_ctx);
  for (curr_insn = bb_stub->first_insn;; curr_insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, curr_insn);
    if (MIR_any_branch_code_p (curr_insn->code)) break;
    skip_p = FALSE;
    switch (curr_insn->code) {
    case MIR_USE: skip_p = TRUE; break;
    case MIR_PRSET:
      gen_assert (curr_insn->ops[1].mode == MIR_OP_INT || curr_insn->ops[1].mode == MIR_OP_UINT);
      dest_spot = op2spot (gen_ctx, &curr_insn->ops[0]);
      if (dest_spot == 0) {
      } else if (curr_insn->ops[1].u.i == 0) { /* ??? aliased */
        bitmap_clear_bit_p (nonzero_property_spots, dest_spot);
      } else {
        bitmap_set_bit_p (nonzero_property_spots, dest_spot);
        spot_attr.spot = dest_spot;
        spot_attr.prop = (uint32_t) curr_insn->ops[1].u.i;
        spot_attr.mem_ref = mem_spot_p (gen_ctx, dest_spot) ? &curr_insn->ops[0] : NULL;
        VARR_SET (spot_attr_t, spot2attr, dest_spot, spot_attr);
      }
      skip_p = TRUE;
      break;
    case MIR_PRBEQ:
    case MIR_PRBNE: /* ??? */
      if ((curr_insn->code == MIR_PRBEQ
           && ((curr_insn->ops[2].mode != MIR_OP_INT && curr_insn->ops[2].mode != MIR_OP_UINT)
               || curr_insn->ops[2].u.i != 0))
          || (curr_insn->code == MIR_PRBNE
              && ((curr_insn->ops[2].mode != MIR_OP_INT && curr_insn->ops[2].mode != MIR_OP_UINT)
                  || curr_insn->ops[2].u.i == 0))) {
        DEBUG (2, {
          fprintf (debug_file, "  Remove property insn ");
          MIR_output_insn (ctx, debug_file, curr_insn, curr_func_item->u.func, TRUE);
        });
        MIR_remove_insn (ctx, curr_func_item, curr_insn);
        skip_p = TRUE;
        break;
      } else { /* make unconditional jump */
        new_insn = MIR_new_insn (ctx, MIR_JMP, curr_insn->ops[0]);
        MIR_insert_insn_before (ctx, curr_func_item, curr_insn, new_insn);
        DEBUG (2, {
          fprintf (debug_file, "  Change ");
          MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, FALSE);
          fprintf (debug_file, " to ");
          MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, TRUE);
        });
        MIR_remove_insn (ctx, curr_func_item, curr_insn);
        curr_insn = new_insn;
        break;
      }
    case MIR_MOV:
    case MIR_FMOV:
    case MIR_DMOV:
    case MIR_LDMOV:
      dest_spot = op2spot (gen_ctx, &curr_insn->ops[0]);
      src_spot = op2spot (gen_ctx, &curr_insn->ops[1]);
      if (src_spot == 0) {
        bitmap_clear_bit_p (nonzero_property_spots, dest_spot);
      } else if (dest_spot == 0) { /* clear attrs of all memory locations */
        if (max_spot >= FIRST_MEM_SPOT)
          bitmap_clear_bit_range_p (nonzero_property_spots, FIRST_MEM_SPOT,
                                    max_spot - FIRST_MEM_SPOT + 1);
      } else if (bitmap_bit_p (nonzero_property_spots, src_spot)) {
        spot_attr = VARR_GET (spot_attr_t, spot2attr, src_spot);
        spot_attr.mem_ref = NULL;
        if (mem_spot_p (gen_ctx, dest_spot)) {
          spot_attr_t *spot_attr_addr = VARR_ADDR (spot_attr_t, spot_attrs);
          for (uint32_t spot = FIRST_MEM_SPOT; spot <= max_spot; spot++)
            if (may_mem_alias_p (spot_attr_addr[dest_spot].mem_ref, spot_attr_addr[spot].mem_ref))
              bitmap_clear_bit_p (nonzero_property_spots, spot);
          spot_attr.mem_ref = &curr_insn->ops[0];
        }
        bitmap_set_bit_p (nonzero_property_spots, dest_spot);
        VARR_SET (spot_attr_t, spot2attr, dest_spot, spot_attr);
      }
      break;
    default: break;
    }
    if (!skip_p) target_bb_insn_translate (gen_ctx, curr_insn, NULL);
    if (curr_insn == bb_stub->last_insn) break;
  }
  VARR_TRUNC (spot_attr_t, spot_attrs, 0);
  FOREACH_BITMAP_BIT (bi, nonzero_property_spots, nel) {
    if (MIR_call_code_p (curr_insn->code) && mem_spot_p (gen_ctx, (uint32_t) nel)) break;
    VARR_PUSH (spot_attr_t, spot_attrs, VARR_GET (spot_attr_t, spot2attr, nel));
  }
  VARR_TRUNC (void_ptr_t, succ_bb_addrs, 0);
  if (curr_insn->code == MIR_SWITCH) {
    for (size_t i = 1; i < curr_insn->nops; i++) {
      branch_bb_stub = curr_insn->ops[i].u.label->data;
      (void) get_bb_version (gen_ctx, branch_bb_stub, VARR_LENGTH (spot_attr_t, spot_attrs),
                             VARR_ADDR (spot_attr_t, spot_attrs), FALSE, &addr);
      VARR_PUSH (void_ptr_t, succ_bb_addrs, addr);
    }
    target_bb_insn_translate (gen_ctx, curr_insn, VARR_ADDR (void_ptr_t, succ_bb_addrs));
  } else if (MIR_branch_code_p (curr_insn->code)) {  // ??? generate branch
    branch_bb_stub = curr_insn->ops[0].u.label->data;
    (void) get_bb_version (gen_ctx, branch_bb_stub, VARR_LENGTH (spot_attr_t, spot_attrs),
                           VARR_ADDR (spot_attr_t, spot_attrs), FALSE, &addr);
    VARR_PUSH (void_ptr_t, succ_bb_addrs, addr);
    target_bb_insn_translate (gen_ctx, curr_insn, VARR_ADDR (void_ptr_t, succ_bb_addrs));
  }
  if (curr_insn->code != MIR_JMP && curr_insn->code != MIR_SWITCH && curr_insn->code != MIR_RET
      && curr_insn->code != MIR_JRET) {
    VARR_TRUNC (void_ptr_t, succ_bb_addrs, 0);
    (void) get_bb_version (gen_ctx, bb_stub + 1, VARR_LENGTH (spot_attr_t, spot_attrs),
                           VARR_ADDR (spot_attr_t, spot_attrs), FALSE, &addr);
    VARR_PUSH (void_ptr_t, succ_bb_addrs, addr);
    target_output_jump (gen_ctx, VARR_ADDR (void_ptr_t, succ_bb_addrs));
  }
  code = target_bb_translate_finish (gen_ctx, &code_len);
  addr = _MIR_publish_code (ctx, code, code_len);
  target_bb_rebase (gen_ctx, addr);
  target_setup_succ_bb_version_data (gen_ctx, addr);
  DEBUG (1, {
    _MIR_dump_code (NULL, 0, addr, code_len);
    fprintf (debug_file, "BBStub%lx code size = %lu:\n", (unsigned long) bb_stub,
             (unsigned long) code_len);
  });
  target_redirect_bb_origin_branch (gen_ctx, &bb_version->target_data, addr);
  _MIR_replace_bb_thunk (ctx, bb_version->addr, addr);
  bb_version->addr = addr;
#if MIR_PARALLEL_GEN
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
  all_gen_ctx->overall_gen_bbs_num++;
  bb_version->machine_code = addr;
#if MIR_PARALLEL_GEN
  if (mir_cond_broadcast (&done_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
#endif
}

static void *bb_version_generator (gen_ctx_t gen_ctx, bb_version_t bb_version) {
#if !MIR_PARALLEL_GEN
  generate_bb_version_machine_code (gen_ctx, bb_version);
#else
  MIR_context_t ctx = gen_ctx->ctx;
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  func_or_bb_t func_or_bb;

  func_or_bb.func_p = FALSE;
  func_or_bb.u.bb_version = bb_version;
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  VARR_PUSH (func_or_bb_t, code_to_generate, func_or_bb);
  if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  for (;;) {
    if (bb_version->machine_code != NULL) break;
    if (mir_cond_wait (&done_signal, &queue_mutex)) parallel_error (ctx, "error in cond wait");
  }
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
#endif
  return bb_version->machine_code;
}

/* attrs ignored ??? implement versions */
static void *generate_func_and_redirect_to_bb_gen (MIR_context_t ctx, MIR_item_t func_item) {
  generate_func_and_redirect (ctx, func_item, FALSE);
  return func_item->addr;
}

void MIR_set_lazy_bb_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  void *addr;

  if (func_item == NULL) return; /* finish setting interfaces */
  addr = _MIR_get_wrapper (ctx, func_item, generate_func_and_redirect_to_bb_gen);
  _MIR_redirect_thunk (ctx, func_item->addr, addr);
}

/* Local Variables:                */
/* mode: c                         */
/* page-delimiter: "/\\* New Page" */
/* End:                            */
