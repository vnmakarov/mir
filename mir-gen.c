/* This file is a part of MIR project.
   Copyright (C) 2018-2021 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Optimization pipeline:
                                                          -------------     -------------
           ----------     -----------     -----------    |  Copy       |   |   Global    |
   MIR -->| Simplify |-->| Build CFG |-->| Build SSA |-->| Propagation |-->|   Value     |
           ----------     -----------     -----------    |             |   |  Numbering  |
                                                          -------------     -------------
                                                                                   |
                                                           -------------           V
    -------     ---------                     --------    |   Sparse    |    -------------
   | Build |   | Finding |    -----------    | Out of |   | Conditional |   |  Dead Code  |
   | Live  |<--|  Loops  |<--| Machinize |<--| SSA    |<--|  Constant   |<--| Elimination |
   | Info  |    ---------     -----------     --------    | Propagation |    -------------
    -------                                                -------------
       |
       V
   --------                                                                ----------
  | Build  |    --------     ---------     ---------     -------------    | Generate |
  | Live   |-->| Assign |-->| Rewrite |-->| Combine |-->|  Dead Code  |-->| Machine  |--> Machine
  | Ranges |    --------     ---------     ---------    | Elimination |   |  Insns   |     Insns
   --------                                              -------------     ----------

   Simplify: Lowering MIR (in mir.c).  Always.
   Build CGF: Building Control Flow Graph (basic blocks and CFG edges).  Only for -O1 and above.
   Build SSA: Building Single Static Assignment Form by adding phi nodes and SSA edges
   Copy Propagation: SSA copy propagation keeping conventional SSA form and removing redundant
                     extension insns
   Global Value Numbering: Removing redundant insns through GVN. Only for -O2 and above.
   Dead code elimination: Removing insns with unused outputs.  Only for -O2 and above.
   Sparse Conditional Constant Propagation: Constant propagation and removing death paths of CFG.
                                            Only for -O2 and above.
   Out of SSA: Removing phi nodes and SSA edges (we keep conventional SSA all the time)
   Machinize: Machine-dependent code (e.g. in mir-gen-x86_64.c)
              transforming MIR for calls ABI, 2-op insns, etc.  Always.
   Finding Loops: Building loop tree which is used in subsequent register allocation.
                  Only for -O1 and above.
   Building Live Info: Calculating live in and live out for the basic blocks.
   Build Live Ranges: Calculating program point ranges for registers.  Only for -O1 and above.
   Assign: Fast RA for -O0 or Priority-based linear scan RA for -O1 and above.
   Rewrite: Transform MIR according to the assign using reserved hard regs.
   Combine (code selection): Merging data-depended insns into one.  Only for -O1 and above.
   Dead code elimination: Removing insns with unused outputs.  Only for -O1 and above.
   Generate machine insns: Machine-dependent code (e.g. in
                           mir-gen-x86_64.c) creating machine insns. Always.

   -O0 is 2 times faster than -O1 but generates much slower code.

   Terminology:
   reg - MIR (pseudo-)register (their numbers are in MIR_OP_REG and MIR_OP_MEM)
   hard reg - MIR hard register (their numbers are in MIR_OP_HARD_REG and MIR_OP_HARD_REG_MEM)
   breg (based reg) - function pseudo registers whose numbers start with zero
   var - pseudo and hard register (var numbers for pseudo-registers
         are based reg numbers + MAX_HARD_REG + 1)
   loc - hard register and stack locations (stack slot numbers start with MAX_HARD_REG + 1).

   We use conventional SSA to make out-of-ssa fast and simple.
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
struct ccp_ctx;
struct lr_ctx;
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
  bitmap_t insn_to_consider, temp_bitmap, temp_bitmap2;
  bitmap_t call_used_hard_regs[MIR_T_BOUND], func_used_hard_regs;
  func_cfg_t curr_cfg;
  uint32_t curr_bb_index, curr_loop_node_index;
  DLIST (dead_var_t) free_dead_vars;
  struct target_ctx *target_ctx;
  struct data_flow_ctx *data_flow_ctx;
  struct ssa_ctx *ssa_ctx;
  struct gvn_ctx *gvn_ctx;
  struct ccp_ctx *ccp_ctx;
  struct lr_ctx *lr_ctx;
  struct ra_ctx *ra_ctx;
  struct selection_ctx *selection_ctx;
  struct fg_ctx *fg_ctx;
  VARR (bb_insn_t) * dead_bb_insns;
  VARR (loop_node_t) * loop_nodes, *queue_nodes, *loop_entries; /* used in building loop tree */
  int max_int_hard_regs, max_fp_hard_regs;
  /* Slots num for variables.  Some variable can take several slots and can be aligned. */
  size_t func_stack_slots_num;
};

#define optimize_level gen_ctx->optimize_level
#define curr_func_item gen_ctx->curr_func_item
#define debug_file gen_ctx->debug_file
#define debug_level gen_ctx->debug_level
#define insn_to_consider gen_ctx->insn_to_consider
#define temp_bitmap gen_ctx->temp_bitmap
#define temp_bitmap2 gen_ctx->temp_bitmap2
#define call_used_hard_regs gen_ctx->call_used_hard_regs
#define func_used_hard_regs gen_ctx->func_used_hard_regs
#define curr_cfg gen_ctx->curr_cfg
#define curr_bb_index gen_ctx->curr_bb_index
#define curr_loop_node_index gen_ctx->curr_loop_node_index
#define free_dead_vars gen_ctx->free_dead_vars
#define dead_bb_insns gen_ctx->dead_bb_insns
#define loop_nodes gen_ctx->loop_nodes
#define queue_nodes gen_ctx->queue_nodes
#define loop_entries gen_ctx->loop_entries
#define max_int_hard_regs gen_ctx->max_int_hard_regs
#define max_fp_hard_regs gen_ctx->max_fp_hard_regs
#define func_stack_slots_num gen_ctx->func_stack_slots_num

DEF_VARR (MIR_item_t);
struct all_gen_ctx {
#if MIR_PARALLEL_GEN
  mir_mutex_t queue_mutex;
  mir_cond_t generate_signal, done_signal;
  size_t funcs_start;
  VARR (MIR_item_t) * funcs_to_generate;
#endif
  MIR_context_t ctx;
  size_t gens_num; /* size of the following array: */
  struct gen_ctx gen_ctx[1];
};

#if MIR_PARALLEL_GEN
#define queue_mutex all_gen_ctx->queue_mutex
#define generate_signal all_gen_ctx->generate_signal
#define done_signal all_gen_ctx->done_signal
#define funcs_start all_gen_ctx->funcs_start
#define funcs_to_generate all_gen_ctx->funcs_to_generate
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

static void MIR_NO_RETURN util_error (gen_ctx_t gen_ctx, const char *message) {
  (*MIR_get_error_func (gen_ctx->ctx)) (MIR_alloc_error, message);
}

static void *gen_malloc (gen_ctx_t gen_ctx, size_t size) {
  void *res = malloc (size);
  if (res == NULL) util_error (gen_ctx, "no memory");
  return res;
}

#define DEFAULT_INIT_BITMAP_BITS_NUM 256

static void make_io_dup_op_insns (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func;
  MIR_insn_t insn, next_insn;
  MIR_insn_code_t code;
  MIR_op_t input, output, temp_op;
  MIR_op_mode_t mode;
  MIR_type_t type;
  size_t i;
  int out_p;

  gen_assert (curr_func_item->item_type == MIR_func_item);
  func = curr_func_item->u.func;
  for (i = 0; target_io_dup_op_insn_codes[i] != MIR_INSN_BOUND; i++)
    bitmap_set_bit_p (insn_to_consider, target_io_dup_op_insn_codes[i]);
  if (bitmap_empty_p (insn_to_consider)) return;
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    code = insn->code;
    if (!bitmap_bit_p (insn_to_consider, code)) continue;
    gen_assert (MIR_insn_nops (ctx, insn) >= 2 && !MIR_call_code_p (code) && code != MIR_RET);
    mode = MIR_insn_op_mode (ctx, insn, 0, &out_p);
    gen_assert (out_p && mode == MIR_insn_op_mode (ctx, insn, 1, &out_p) && !out_p);
    output = insn->ops[0];
    input = insn->ops[1];
    gen_assert (input.mode == MIR_OP_REG || input.mode == MIR_OP_HARD_REG
                || output.mode == MIR_OP_REG || output.mode == MIR_OP_HARD_REG);
    if (input.mode == output.mode
        && ((input.mode == MIR_OP_HARD_REG && input.u.hard_reg == output.u.hard_reg)
            || (input.mode == MIR_OP_REG && input.u.reg == output.u.reg)))
      continue;
    if (mode == MIR_OP_FLOAT) {
      code = MIR_FMOV;
      type = MIR_T_F;
    } else if (mode == MIR_OP_DOUBLE) {
      code = MIR_DMOV;
      type = MIR_T_D;
    } else if (mode == MIR_OP_LDOUBLE) {
      code = MIR_LDMOV;
      type = MIR_T_LD;
    } else {
      code = MIR_MOV;
      type = MIR_T_I64;
    }
    temp_op = MIR_new_reg_op (ctx, gen_new_temp_reg (gen_ctx, type, func));
    gen_add_insn_before (gen_ctx, insn, MIR_new_insn (ctx, code, temp_op, insn->ops[1]));
    gen_add_insn_after (gen_ctx, insn, MIR_new_insn (ctx, code, insn->ops[0], temp_op));
    insn->ops[0] = insn->ops[1] = temp_op;
  }
}

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
  unsigned char back_edge_p;
  unsigned char skipped_p; /* used for CCP */
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

struct bb_insn {
  MIR_insn_t insn;
  unsigned char flag; /* used for CCP */
  uint32_t gvn_val;   /* used for GVN, it is negative index for non GVN expr insns */
  uint32_t index;
  DLIST_LINK (bb_insn_t) bb_insn_link;
  bb_t bb;
  DLIST (dead_var_t) dead_vars;
  bitmap_t call_hard_reg_args; /* non-null for calls */
  size_t label_disp;           /* for label */
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost, bfs; /* preorder, reverse post order, breadth first order */
  unsigned int flag;             /* used for CCP */
  DLIST_LINK (bb_t) bb_link;
  DLIST (in_edge_t) in_edges;
  /* The out edges order: optional fall through bb, optional label bb,
     optional exit bb.  There is always at least one edge.  */
  DLIST (out_edge_t) out_edges;
  DLIST (bb_insn_t) bb_insns;
  size_t freq;
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
  DLIST (loop_node_t) children;
  DLIST_LINK (loop_node_t) children_link;
  int max_int_pressure, max_fp_pressure;
};

DEF_DLIST_CODE (loop_node_t, children_link);

DEF_DLIST_LINK (func_cfg_t);

typedef struct mv *mv_t;
typedef mv_t dst_mv_t;
typedef mv_t src_mv_t;

DEF_DLIST_LINK (mv_t);
DEF_DLIST_LINK (dst_mv_t);
DEF_DLIST_LINK (src_mv_t);

struct mv {
  bb_insn_t bb_insn;
  size_t freq;
  DLIST_LINK (mv_t) mv_link;
  DLIST_LINK (dst_mv_t) dst_link;
  DLIST_LINK (src_mv_t) src_link;
};

DEF_DLIST (mv_t, mv_link);
DEF_DLIST (dst_mv_t, dst_link);
DEF_DLIST (src_mv_t, src_link);

struct reg_info {
  long freq;
  /* The following members are defined and used only in RA */
  long thread_freq; /* thread accumulated freq, defined for first thread breg */
  /* first/next breg of the same thread, MIR_MAX_REG_NUM is end mark  */
  MIR_reg_t thread_first, thread_next;
  size_t live_length; /* # of program points where breg lives */
  DLIST (dst_mv_t) dst_moves;
  DLIST (src_mv_t) src_moves;
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

#if !MIR_NO_GEN_DEBUG
static void print_const (FILE *f, const_t c) {
  if (c.uns_p)
    fprintf (f, "%" PRIu64, c.u.u);
  else
    fprintf (f, "%" PRId64, c.u.i);
}
#endif

struct func_cfg {
  MIR_reg_t min_reg, max_reg;
  uint32_t non_conflicting_moves; /* # of moves with non-conflicting regs */
  uint32_t curr_bb_insn_index;
  VARR (reg_info_t) * breg_info; /* bregs */
  bitmap_t call_crossed_bregs;
  DLIST (bb_t) bbs;
  DLIST (mv_t) used_moves, free_moves;
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

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL;
       dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var) return;
  dv = get_dead_var (gen_ctx);
  dv->var = var;
  DLIST_APPEND (dead_var_t, bb_insn->dead_vars, dv);
}

static dead_var_t find_bb_insn_dead_var (bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv;

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL;
       dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var) return dv;
  return NULL;
}

static void clear_bb_insn_dead_vars (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, bb_insn->dead_vars, dv);
    free_dead_var (gen_ctx, dv);
  }
}

static void remove_bb_insn_dead_var (gen_ctx_t gen_ctx, bb_insn_t bb_insn, MIR_reg_t hr) {
  dead_var_t dv, next_dv;

  gen_assert (hr <= MAX_HARD_REG);
  for (dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL; dv = next_dv) {
    next_dv = DLIST_NEXT (dead_var_t, dv);
    if (dv->var != hr) continue;
    DLIST_REMOVE (dead_var_t, bb_insn->dead_vars, dv);
    free_dead_var (gen_ctx, dv);
  }
}

static void move_bb_insn_dead_vars (bb_insn_t bb_insn, bb_insn_t from_bb_insn) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, from_bb_insn->dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, from_bb_insn->dead_vars, dv);
    DLIST_APPEND (dead_var_t, bb_insn->dead_vars, dv);
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
  bb_insn->flag = FALSE;
  bb_insn->call_hard_reg_args = NULL;
  gen_assert (curr_cfg->curr_bb_insn_index != (uint32_t) ~0ull);
  bb_insn->index = curr_cfg->curr_bb_insn_index++;
  bb_insn->gvn_val = bb_insn->index;
  DLIST_INIT (dead_var_t, bb_insn->dead_vars);
  if (MIR_call_code_p (insn->code)) bb_insn->call_hard_reg_args = bitmap_create2 (MAX_HARD_REG + 1);
  return bb_insn;
}

static bb_insn_t add_new_bb_insn (gen_ctx_t gen_ctx, MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = create_bb_insn (gen_ctx, insn, bb);

  DLIST_APPEND (bb_insn_t, bb->bb_insns, bb_insn);
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

  gen_assert (!MIR_branch_code_p (insn->code) && insn->code != MIR_LABEL);
  if (before->code == MIR_LABEL) {
    insn_for_bb = DLIST_PREV (MIR_insn_t, before);
    gen_assert (insn_for_bb == NULL || !MIR_branch_code_p (insn_for_bb->code));
  }
  MIR_insert_insn_before (ctx, curr_func_item, before, insn);
  create_new_bb_insns (gen_ctx, DLIST_PREV (MIR_insn_t, insn), before, insn_for_bb);
}

static void gen_add_insn_after (gen_ctx_t gen_ctx, MIR_insn_t after, MIR_insn_t insn) {
  gen_assert (insn->code != MIR_LABEL);
  gen_assert (!MIR_branch_code_p (after->code));
  MIR_insert_insn_after (gen_ctx->ctx, curr_func_item, after, insn);
  create_new_bb_insns (gen_ctx, after, DLIST_NEXT (MIR_insn_t, insn), after);
}

static void gen_move_insn_before (gen_ctx_t gen_ctx, MIR_insn_t before, MIR_insn_t insn) {
  DLIST_REMOVE (MIR_insn_t, curr_func_item->u.func->insns, insn);
  MIR_insert_insn_before (gen_ctx->ctx, curr_func_item, before, insn);
  if (optimize_level != 0) {
    bb_insn_t bb_insn = insn->data, before_bb_insn = before->data;
    DLIST_REMOVE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn);
    DLIST_INSERT_BEFORE (bb_insn_t, before_bb_insn->bb->bb_insns, before_bb_insn, bb_insn);
  }
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
  bb->flag = FALSE;
  bb->loop_node = NULL;
  DLIST_INIT (bb_insn_t, bb->bb_insns);
  DLIST_INIT (in_edge_t, bb->in_edges);
  DLIST_INIT (out_edge_t, bb->out_edges);
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
      add_new_bb_insn (gen_ctx, insn, bb);
  }
  return bb;
}

static void add_bb (gen_ctx_t gen_ctx, bb_t bb) {
  DLIST_APPEND (bb_t, curr_cfg->bbs, bb);
  bb->index = curr_bb_index++;
}

static edge_t create_edge (gen_ctx_t gen_ctx, bb_t src, bb_t dst, int append_p) {
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
  e->back_edge_p = e->skipped_p = FALSE;
  return e;
}

static void delete_edge (edge_t e) {
  DLIST_REMOVE (out_edge_t, e->src->out_edges, e);
  DLIST_REMOVE (in_edge_t, e->dst->in_edges, e);
  free (e);
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
  DLIST_REMOVE (bb_t, curr_cfg->bbs, bb);
  bitmap_destroy (bb->in);
  bitmap_destroy (bb->out);
  bitmap_destroy (bb->gen);
  bitmap_destroy (bb->kill);
  bitmap_destroy (bb->dom_in);
  bitmap_destroy (bb->dom_out);
  free (bb);
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

static void update_min_max_reg (gen_ctx_t gen_ctx, MIR_reg_t reg) {
  if (reg == 0) return;
  if (curr_cfg->max_reg == 0 || curr_cfg->min_reg > reg) curr_cfg->min_reg = reg;
  if (curr_cfg->max_reg < reg) curr_cfg->max_reg = reg;
}

static MIR_reg_t gen_new_temp_reg (gen_ctx_t gen_ctx, MIR_type_t type, MIR_func_t func) {
  MIR_reg_t reg = _MIR_new_temp_reg (gen_ctx->ctx, type, func);

  update_min_max_reg (gen_ctx, reg);
  return reg;
}

static MIR_reg_t reg2breg (gen_ctx_t gen_ctx, MIR_reg_t reg) { return reg - curr_cfg->min_reg; }
static MIR_reg_t breg2reg (gen_ctx_t gen_ctx, MIR_reg_t breg) { return breg + curr_cfg->min_reg; }
static MIR_reg_t reg2var (gen_ctx_t gen_ctx, MIR_reg_t reg) {
  return reg2breg (gen_ctx, reg) + MAX_HARD_REG + 1;
}
static MIR_reg_t var_is_reg_p (MIR_reg_t var) { return var > MAX_HARD_REG; }
static MIR_reg_t var2reg (gen_ctx_t gen_ctx, MIR_reg_t var) {
  gen_assert (var > MAX_HARD_REG);
  return breg2reg (gen_ctx, var - MAX_HARD_REG - 1);
}
static MIR_reg_t var2breg (gen_ctx_t gen_ctx, MIR_reg_t var) {
  gen_assert (var > MAX_HARD_REG);
  return var - MAX_HARD_REG - 1;
}

static MIR_reg_t get_nregs (gen_ctx_t gen_ctx) {
  return curr_cfg->max_reg == 0 ? 0 : curr_cfg->max_reg - curr_cfg->min_reg + 1;
}

static MIR_reg_t get_nvars (gen_ctx_t gen_ctx) { return get_nregs (gen_ctx) + MAX_HARD_REG + 1; }

static int move_code_p (MIR_insn_code_t code) {
  return code == MIR_MOV || code == MIR_FMOV || code == MIR_DMOV || code == MIR_LDMOV;
}

static int move_p (MIR_insn_t insn) {
  return (move_code_p (insn->code)
          && (insn->ops[0].mode == MIR_OP_REG || insn->ops[0].mode == MIR_OP_HARD_REG)
          && (insn->ops[1].mode == MIR_OP_REG || insn->ops[1].mode == MIR_OP_HARD_REG));
}

static int imm_move_p (MIR_insn_t insn) {
  return (move_code_p (insn->code)
          && (insn->ops[0].mode == MIR_OP_REG || insn->ops[0].mode == MIR_OP_HARD_REG)
          && (insn->ops[1].mode == MIR_OP_INT || insn->ops[1].mode == MIR_OP_UINT
              || insn->ops[1].mode == MIR_OP_FLOAT || insn->ops[1].mode == MIR_OP_DOUBLE
              || insn->ops[1].mode == MIR_OP_LDOUBLE || insn->ops[1].mode == MIR_OP_REF));
}

typedef struct {
  MIR_insn_t insn;
  size_t nops, op_num, op_part_num, passed_mem_num;
} insn_var_iterator_t;

static inline void insn_var_iterator_init (gen_ctx_t gen_ctx, insn_var_iterator_t *iter,
                                           MIR_insn_t insn) {
  iter->insn = insn;
  iter->nops = MIR_insn_nops (gen_ctx->ctx, insn);
  iter->op_num = 0;
  iter->op_part_num = 0;
  iter->passed_mem_num = 0;
}

static inline int insn_var_iterator_next (gen_ctx_t gen_ctx, insn_var_iterator_t *iter,
                                          MIR_reg_t *var, int *op_num, int *out_p, int *mem_p,
                                          size_t *passed_mem_num) {
  MIR_op_t op;

  while (iter->op_num < iter->nops) {
    *op_num = iter->op_num;
    MIR_insn_op_mode (gen_ctx->ctx, iter->insn, iter->op_num, out_p);
    op = iter->insn->ops[iter->op_num];
    *mem_p = FALSE;
    *passed_mem_num = iter->passed_mem_num;
    while (iter->op_part_num < 2) {
      if (op.mode == MIR_OP_MEM || op.mode == MIR_OP_HARD_REG_MEM) {
        *mem_p = TRUE;
        *passed_mem_num = ++iter->passed_mem_num;
        *out_p = FALSE;
        if (op.mode == MIR_OP_MEM) {
          *var = iter->op_part_num == 0 ? op.u.mem.base : op.u.mem.index;
          if (*var == 0) {
            iter->op_part_num++;
            continue;
          }
          *var = reg2var (gen_ctx, *var);
        } else {
          *var = iter->op_part_num == 0 ? op.u.hard_reg_mem.base : op.u.hard_reg_mem.index;
          if (*var == MIR_NON_HARD_REG) {
            iter->op_part_num++;
            continue;
          }
        }
      } else if (iter->op_part_num > 0) {
        break;
      } else if (op.mode == MIR_OP_REG) {
        *var = reg2var (gen_ctx, op.u.reg);
      } else if (op.mode == MIR_OP_HARD_REG) {
        *var = op.u.hard_reg;
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

#define FOREACH_INSN_VAR(gen_ctx, iterator, insn, var, op_num, out_p, mem_p, passed_mem_num) \
  for (insn_var_iterator_init (gen_ctx, &iterator, insn);                                    \
       insn_var_iterator_next (gen_ctx, &iterator, &var, &op_num, &out_p, &mem_p,            \
                               &passed_mem_num);)

#if !MIR_NO_GEN_DEBUG
static void output_in_edges (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  in edges:");
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    fprintf (debug_file, " %3lu", (unsigned long) e->src->index);
    if (e->skipped_p) fprintf (debug_file, "(CCP skip)");
  }
  fprintf (debug_file, "\n");
}

static void output_out_edges (gen_ctx_t gen_ctx, bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  out edges:");
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e)) {
    fprintf (debug_file, " %3lu", (unsigned long) e->dst->index);
    if (e->skipped_p) fprintf (debug_file, "(CCP skip)");
  }
  fprintf (debug_file, "\n");
}

static void output_bitmap (gen_ctx_t gen_ctx, const char *head, bitmap_t bm, int var_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  size_t nel;
  bitmap_iterator_t bi;

  if (bm == NULL || bitmap_empty_p (bm)) return;
  fprintf (debug_file, "%s", head);
  FOREACH_BITMAP_BIT (bi, bm, nel) {
    fprintf (debug_file, " %3lu", (unsigned long) nel);
    if (var_p && var_is_reg_p (nel))
      fprintf (debug_file, "(%s:%s)",
               MIR_type_str (ctx,
                             MIR_reg_type (ctx, var2reg (gen_ctx, nel), curr_func_item->u.func)),
               MIR_reg_name (ctx, var2reg (gen_ctx, nel), curr_func_item->u.func));
  }
  fprintf (debug_file, "\n");
}

static int get_op_reg_index (gen_ctx_t gen_ctx, MIR_op_t op);
static void print_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn, int with_notes_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_op_t op;
  int first_p;
  size_t nel;
  bitmap_iterator_t bi;

  MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
  fprintf (debug_file, " # indexes: ");
  for (size_t i = 0; i < bb_insn->insn->nops; i++) {
    op = bb_insn->insn->ops[i];
    if (i != 0) fprintf (debug_file, ",");
    if (op.data == NULL)
      fprintf (debug_file, "_");
    else
      fprintf (debug_file, "%d", get_op_reg_index (gen_ctx, op));
  }
  if (with_notes_p) {
    for (dead_var_t dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL;
         dv = DLIST_NEXT (dead_var_t, dv)) {
      if (var_is_reg_p (dv->var)) {
        op.mode = MIR_OP_REG;
        op.u.reg = var2reg (gen_ctx, dv->var);
      } else {
        op.mode = MIR_OP_HARD_REG;
        op.u.hard_reg = dv->var;
      }
      fprintf (debug_file, dv == DLIST_HEAD (dead_var_t, bb_insn->dead_vars) ? " # dead: " : " ");
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
  if (curr_cfg->root_loop_node == root)
    fprintf (debug_file, ":\n");
  else
    fprintf (debug_file, " (entry - bb%lu):\n", (unsigned long) root->entry->bb->index);
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
                           MIR_insn_t insn) {
  MIR_context_t ctx = gen_ctx->ctx;
  int change_p = FALSE;

  if (op_ref->mode == MIR_OP_REG && op_ref->u.reg == reg) {
    op_ref->u.reg = new_reg;
    change_p = TRUE;
  } else if (op_ref->mode == MIR_OP_MEM) {
    if (op_ref->u.mem.base == reg) {
      op_ref->u.mem.base = new_reg;
      change_p = TRUE;
    }
    if (op_ref->u.mem.index == reg) {
      op_ref->u.mem.index = new_reg;
      change_p = TRUE;
    }
  }
  if (!change_p) return; /* definition was already changed from another use */
  DEBUG (2, {
    MIR_func_t func = curr_func_item->u.func;

    fprintf (debug_file, "    Change %s to %s in insn %-5lu", MIR_reg_name (ctx, reg, func),
             MIR_reg_name (ctx, new_reg, func), (long unsigned) ((bb_insn_t) insn->data)->index);
    print_bb_insn (gen_ctx, insn->data, FALSE);
  });
}

static mv_t get_free_move (gen_ctx_t gen_ctx) {
  mv_t mv;

  if ((mv = DLIST_HEAD (mv_t, curr_cfg->free_moves)) != NULL)
    DLIST_REMOVE (mv_t, curr_cfg->free_moves, mv);
  else
    mv = gen_malloc (gen_ctx, sizeof (struct mv));
  DLIST_APPEND (mv_t, curr_cfg->used_moves, mv);
  return mv;
}

static void free_move (gen_ctx_t gen_ctx, mv_t mv) {
  DLIST_REMOVE (mv_t, curr_cfg->used_moves, mv);
  DLIST_APPEND (mv_t, curr_cfg->free_moves, mv);
}

static void build_func_cfg (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn, next_insn;
  size_t i, nops;
  MIR_op_t *op;
  MIR_var_t var;
  bb_t bb, prev_bb, entry_bb, exit_bb, label_bb;

  DLIST_INIT (bb_t, curr_cfg->bbs);
  DLIST_INIT (mv_t, curr_cfg->used_moves);
  DLIST_INIT (mv_t, curr_cfg->free_moves);
  curr_cfg->curr_bb_insn_index = 0;
  curr_cfg->max_reg = 0;
  curr_cfg->min_reg = 0;
  curr_cfg->non_conflicting_moves = 0;
  curr_cfg->root_loop_node = NULL;
  curr_bb_index = 0;
  for (i = 0; i < VARR_LENGTH (MIR_var_t, curr_func_item->u.func->vars); i++) {
    var = VARR_GET (MIR_var_t, curr_func_item->u.func->vars, i);
    update_min_max_reg (gen_ctx, MIR_reg (ctx, var.name, curr_func_item->u.func));
  }
  entry_bb = create_bb (gen_ctx, NULL);
  add_bb (gen_ctx, entry_bb);
  exit_bb = create_bb (gen_ctx, NULL);
  add_bb (gen_ctx, exit_bb);
  insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns);
  if (insn == NULL || insn->code == MIR_LABEL || MIR_call_code_p (insn->code)) {
    /* To deal with special cases like adding insns before call in
       machinize or moving invariant out of loop: */
    MIR_prepend_insn (ctx, curr_func_item, MIR_new_label (ctx));
    insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns);
  }
  bb = create_bb (gen_ctx, NULL);
  add_bb (gen_ctx, bb);
  for (; insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    if (insn->data == NULL) {
      if (optimize_level != 0)
        add_new_bb_insn (gen_ctx, insn, bb);
      else
        setup_insn_data (gen_ctx, insn, bb);
    }
    nops = MIR_insn_nops (ctx, insn);
    if (next_insn != NULL
        && (MIR_branch_code_p (insn->code) || insn->code == MIR_RET || insn->code == MIR_SWITCH
            || next_insn->code == MIR_LABEL)) {
      prev_bb = bb;
      if (next_insn->code == MIR_LABEL && next_insn->data != NULL)
        bb = get_insn_bb (gen_ctx, next_insn);
      else
        bb = create_bb (gen_ctx, next_insn);
      add_bb (gen_ctx, bb);
      if (insn->code != MIR_JMP && insn->code != MIR_RET && insn->code != MIR_SWITCH)
        create_edge (gen_ctx, prev_bb, bb, TRUE);
    }
    for (i = 0; i < nops; i++)
      if ((op = &insn->ops[i])->mode == MIR_OP_LABEL) {
        if (op->u.label->data == NULL) create_bb (gen_ctx, op->u.label);
        label_bb = get_insn_bb (gen_ctx, op->u.label);
        create_edge (gen_ctx, get_insn_bb (gen_ctx, insn), label_bb, TRUE);
      } else if (op->mode == MIR_OP_REG) {
        update_min_max_reg (gen_ctx, op->u.reg);
      } else if (op->mode == MIR_OP_MEM) {
        update_min_max_reg (gen_ctx, op->u.mem.base);
        update_min_max_reg (gen_ctx, op->u.mem.index);
      }
  }
  /* Add additional edges with entry and exit */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb != entry_bb && DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
      create_edge (gen_ctx, entry_bb, bb, TRUE);
    if (bb != exit_bb && DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
      create_edge (gen_ctx, bb, exit_bb, TRUE);
  }
  enumerate_bbs (gen_ctx);
  VARR_CREATE (reg_info_t, curr_cfg->breg_info, 128);
  curr_cfg->call_crossed_bregs = bitmap_create2 (curr_cfg->max_reg);
}

static void destroy_func_cfg (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t bb, next_bb;
  mv_t mv, next_mv;

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
  for (mv = DLIST_HEAD (mv_t, curr_cfg->used_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free (mv);
  }
  for (mv = DLIST_HEAD (mv_t, curr_cfg->free_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free (mv);
  }
  VARR_DESTROY (reg_info_t, curr_cfg->breg_info);
  bitmap_destroy (curr_cfg->call_crossed_bregs);
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

   We use conventional SSA to make out-of-ssa fast and simple.  We don't rename all regs for SSA.
   All phi insns always use the same reg to guarantee conventional SSA.  It also means that
   some regs have more one definition but ssa edges represent the correct SSA.  The only
   optimization in the pipeline which would benefit from full renaming is copy propagation (full
   SSA copy propagation would not keep conventional SSA).
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

DEF_VARR (MIR_op_t);
DEF_VARR (ssa_edge_t);
DEF_VARR (char);
DEF_VARR (size_t);

struct ssa_ctx {
  int def_use_repr_p; /* flag of def_use_chains */
  /* Insns defining undef and initial arg values. They are not in insn lists. */
  VARR (bb_insn_t) * arg_bb_insns, *undef_insns;
  VARR (bb_insn_t) * phis, *deleted_phis;
  VARR (MIR_op_t) * temp_ops;
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
#define temp_ops gen_ctx->ssa_ctx->temp_ops
#define def_tab gen_ctx->ssa_ctx->def_tab
#define ssa_edges_to_process gen_ctx->ssa_ctx->ssa_edges_to_process
#define curr_reg_indexes gen_ctx->ssa_ctx->curr_reg_indexes
#define reg_name gen_ctx->ssa_ctx->reg_name

static int get_op_reg_index (gen_ctx_t gen_ctx, MIR_op_t op) {
  return def_use_repr_p ? ((ssa_edge_t) op.data)->def->index : ((bb_insn_t) op.data)->index;
}

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

static bb_insn_t get_start_insn (gen_ctx_t gen_ctx, VARR (bb_insn_t) * start_insns, MIR_reg_t reg) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_type_t type;
  MIR_op_t op;
  MIR_insn_t insn;
  bb_insn_t bb_insn;

  gen_assert (DLIST_HEAD (bb_t, curr_cfg->bbs)->index == 0);
  op = MIR_new_reg_op (ctx, reg);
  while (VARR_LENGTH (bb_insn_t, start_insns) <= reg) VARR_PUSH (bb_insn_t, start_insns, NULL);
  if ((bb_insn = VARR_GET (bb_insn_t, start_insns, reg)) == NULL) {
    type = MIR_reg_type (ctx, reg, curr_func_item->u.func);
    insn = MIR_new_insn (ctx, get_move_code (type), op, op);
    bb_insn = create_bb_insn (gen_ctx, insn, DLIST_HEAD (bb_t, curr_cfg->bbs));
    VARR_SET (bb_insn_t, start_insns, reg, bb_insn);
  }
  return bb_insn;
}

static int start_insn_p (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  return bb_insn->bb == DLIST_HEAD (bb_t, curr_cfg->bbs);
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
  gen_assert (phi->insn->ops[0].mode == MIR_OP_REG);
  if (same == NULL) same = get_start_insn (gen_ctx, undef_insns, phi->insn->ops[0].u.reg);
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
  if (bb_insn->insn->code == MIR_LABEL)
    gen_add_insn_after (gen_ctx, bb_insn->insn, phi_insn);
  else
    gen_add_insn_before (gen_ctx, bb_insn->insn, phi_insn);
  phi_insn->ops[0].data = phi = phi_insn->data;
  VARR_PUSH (bb_insn_t, phis, phi);
  return phi;
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
      return get_start_insn (gen_ctx, arg_bb_insns, reg);
    }
    return get_def (gen_ctx, reg, DLIST_HEAD (in_edge_t, bb->in_edges)->src);
  }
  op = MIR_new_reg_op (ctx, reg);
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
  size_t passed_mem_num;
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
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p) continue;
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

static void change_ssa_edge_list_def (ssa_edge_t list, bb_insn_t new_bb_insn,
                                      unsigned new_def_op_num, MIR_reg_t reg, MIR_reg_t new_reg) {
  for (ssa_edge_t se = list; se != NULL; se = se->next_use) {
    se->def = new_bb_insn;
    se->def_op_num = new_def_op_num;
    if (new_reg != 0) {
      MIR_op_t *op_ref = &se->use->insn->ops[se->use_op_num];
      if (op_ref->mode == MIR_OP_REG) {
        op_ref->u.reg = new_reg;
      } else {
        gen_assert (op_ref->mode == MIR_OP_MEM && op_ref->u.mem.base == reg);
        op_ref->u.mem.base = new_reg;
      }
    }
  }
}

static int get_var_def_op_num (gen_ctx_t gen_ctx, MIR_reg_t var, MIR_insn_t insn) {
  int op_num, out_p, mem_p;
  size_t passed_mem_num;
  MIR_reg_t insn_var;
  insn_var_iterator_t iter;

  FOREACH_INSN_VAR (gen_ctx, iter, insn, insn_var, op_num, out_p, mem_p, passed_mem_num) {
    if (out_p && var == insn_var) return op_num;
  }
  gen_assert (FALSE);
  return -1;
}

static void make_ssa_def_use_repr (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_t bb;
  bb_insn_t bb_insn, def;
  int op_num, out_p, mem_p;
  size_t passed_mem_num;
  MIR_reg_t var;
  insn_var_iterator_t iter;

  if (def_use_repr_p) return;
  def_use_repr_p = TRUE;
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p) continue;
        def = insn->ops[op_num].data;
        gen_assert (var > MAX_HARD_REG && def != NULL);
        insn->ops[op_num].data = NULL;
        add_ssa_edge (gen_ctx, def, get_var_def_op_num (gen_ctx, var, def->insn), bb_insn, op_num);
      }
    }
}

static MIR_reg_t get_new_reg (gen_ctx_t gen_ctx, MIR_reg_t reg, size_t index) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_func_t func = curr_func_item->u.func;
  MIR_type_t type = MIR_reg_type (ctx, reg, func);
  const char *name = MIR_reg_name (ctx, reg, func);
  char ind_str[30];
  MIR_reg_t new_reg;

  VARR_TRUNC (char, reg_name, 0);
  VARR_PUSH_ARR (char, reg_name, name, strlen (name));
  VARR_PUSH (char, reg_name, '@');
  sprintf (ind_str, "%lu", (unsigned long) index); /* ??? should be enough to unique */
  VARR_PUSH_ARR (char, reg_name, ind_str, strlen (ind_str) + 1);
  new_reg = MIR_new_func_reg (ctx, func, type, VARR_ADDR (char, reg_name));
  update_min_max_reg (gen_ctx, new_reg);
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
    if (push_to_rename (gen_ctx, curr_edge) && curr_edge->use->insn->code == MIR_PHI)
      process_insn_to_rename (gen_ctx, curr_edge->use->insn, 0);
  if (insn->code != MIR_PHI) return;
  for (size_t i = 1; i < insn->nops; i++) { /* process a def -> the phi use */
    ssa_edge_t ssa_edge = insn->ops[i].data;
    bb_insn_t def = ssa_edge->def;

    /* process the def -> other uses: */
    if (push_to_rename (gen_ctx, ssa_edge))
      process_insn_to_rename (gen_ctx, def->insn, ssa_edge->def_op_num);
  }
}

static void rename_bb_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  int op_num, out_p, mem_p;
  size_t passed_mem_num, reg_index;
  MIR_reg_t var, reg, new_reg;
  MIR_insn_t insn, def_insn, use_insn;
  ssa_edge_t ssa_edge;
  insn_var_iterator_t iter;

  insn = bb_insn->insn;
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
    if (!out_p || !var_is_reg_p (var)) continue;
    ssa_edge = insn->ops[op_num].data;
    if (ssa_edge != NULL && ssa_edge->flag) continue; /* already processed */
    DEBUG (2, {
      fprintf (debug_file, "  Start def insn %-5lu", (long unsigned) bb_insn->index);
      print_bb_insn (gen_ctx, bb_insn, FALSE);
    });
    reg = var2reg (gen_ctx, var);
    while (VARR_LENGTH (size_t, curr_reg_indexes) <= reg) VARR_PUSH (size_t, curr_reg_indexes, 0);
    reg_index = VARR_GET (size_t, curr_reg_indexes, reg);
    VARR_SET (size_t, curr_reg_indexes, reg, reg_index + 1);
    new_reg = reg_index == 0 ? 0 : get_new_reg (gen_ctx, reg, reg_index);
    if (ssa_edge == NULL) { /* special case: unused output */
      if (new_reg != 0) rename_op_reg (gen_ctx, &insn->ops[op_num], reg, new_reg, insn);
      continue;
    }
    VARR_TRUNC (ssa_edge_t, ssa_edges_to_process, 0);
    process_insn_to_rename (gen_ctx, insn, op_num);
    if (new_reg != 0) {
      while (pop_to_rename (gen_ctx, &ssa_edge)) {
        def_insn = ssa_edge->def->insn;
        use_insn = ssa_edge->use->insn;
        rename_op_reg (gen_ctx, &def_insn->ops[ssa_edge->def_op_num], reg, new_reg, def_insn);
        rename_op_reg (gen_ctx, &use_insn->ops[ssa_edge->use_op_num], reg, new_reg, use_insn);
      }
    }
  }
}

static void rename_regs (gen_ctx_t gen_ctx) {
  bb_insn_t bb_insn;
  int op_num, out_p, mem_p;
  size_t passed_mem_num;
  MIR_reg_t var;
  MIR_insn_t insn;
  ssa_edge_t ssa_edge;
  insn_var_iterator_t iter;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) { /* clear all ssa edge flags */
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p || !var_is_reg_p (var)) continue;
        ssa_edge = insn->ops[op_num].data;
        ssa_edge->flag = FALSE;
      }
    }
  VARR_TRUNC (size_t, curr_reg_indexes, 0);
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

static void build_ssa (gen_ctx_t gen_ctx) {
  bb_t bb;
  bb_insn_t def, bb_insn, phi;
  int op_num, out_p, mem_p;
  size_t passed_mem_num, insns_num, i;
  MIR_reg_t var;
  def_tab_el_t el;
  insn_var_iterator_t iter;

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
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      if (bb_insn->insn->code != MIR_PHI) {
        FOREACH_INSN_VAR (gen_ctx, iter, bb_insn->insn, var, op_num, out_p, mem_p, passed_mem_num) {
          gen_assert (var > MAX_HARD_REG);
          if (out_p) continue;
          def = get_def (gen_ctx, var - MAX_HARD_REG, bb);
          bb_insn->insn->ops[op_num].data = def;
        }
        insns_num++;
        FOREACH_INSN_VAR (gen_ctx, iter, bb_insn->insn, var, op_num, out_p, mem_p, passed_mem_num) {
          if (!out_p) continue;
          el.bb = bb;
          el.reg = var - MAX_HARD_REG;
          el.def = bb_insn;
          HTAB_DO (def_tab_el_t, def_tab, el, HTAB_REPLACE, el);
        }
      }
    }
  }
  for (i = 0; i < VARR_LENGTH (bb_insn_t, phis); i++) {
    phi = VARR_GET (bb_insn_t, phis, i);
    add_phi_operands (gen_ctx, phi->insn->ops[0].u.reg, phi);
  }
  /* minimization can not be switched off for def_use representation
     building as it clears ops[0].data: */
  minimize_ssa (gen_ctx, insns_num);
  make_ssa_def_use_repr (gen_ctx);
  rename_regs (gen_ctx);
}

static void undo_build_ssa (gen_ctx_t gen_ctx) {
  bb_t bb;
  bb_insn_t bb_insn, next_bb_insn;
  int op_num, out_p, mem_p;
  size_t passed_mem_num;
  MIR_reg_t var;
  MIR_insn_t insn;
  insn_var_iterator_t iter;

  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
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
  while (VARR_LENGTH (bb_insn_t, arg_bb_insns) != 0)
    if ((bb_insn = VARR_POP (bb_insn_t, arg_bb_insns)) != NULL) {  // ??? specialized free funcs
      free (bb_insn->insn);
      free (bb_insn);
    }
  while (VARR_LENGTH (bb_insn_t, undef_insns) != 0)
    if ((bb_insn = VARR_POP (bb_insn_t, undef_insns)) != NULL) {  // ??? specialized free funcs
      free (bb_insn->insn);
      free (bb_insn);
    }
}

static void init_ssa (gen_ctx_t gen_ctx) {
  gen_ctx->ssa_ctx = gen_malloc (gen_ctx, sizeof (struct ssa_ctx));
  VARR_CREATE (bb_insn_t, arg_bb_insns, 0);
  VARR_CREATE (bb_insn_t, undef_insns, 0);
  VARR_CREATE (bb_insn_t, phis, 0);
  VARR_CREATE (bb_insn_t, deleted_phis, 0);
  VARR_CREATE (MIR_op_t, temp_ops, 16);
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
  VARR_DESTROY (MIR_op_t, temp_ops);
  HTAB_DESTROY (def_tab_el_t, def_tab);
  VARR_DESTROY (ssa_edge_t, ssa_edges_to_process);
  VARR_DESTROY (size_t, curr_reg_indexes);
  VARR_DESTROY (char, reg_name);
  free (gen_ctx->ssa_ctx);
  gen_ctx->ssa_ctx = NULL;
}

/* New Page */

/* Copy propagation */

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

static void copy_prop (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn, def_insn;
  bb_insn_t bb_insn, next_bb_insn, def;
  ssa_edge_t se;
  int op_num, out_p, mem_p, w, w2, sign_p, sign2_p;
  size_t passed_mem_num;
  MIR_reg_t var, reg, new_reg;
  insn_var_iterator_t iter;
  long deleted_insns_num = 0;

  bitmap_clear (temp_bitmap);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      if ((insn = bb_insn->insn)->code == MIR_LABEL) continue;
      if (insn->code != MIR_PHI) break;
      bitmap_set_bit_p (temp_bitmap, insn->ops[0].u.reg);
    }
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      if (insn->code == MIR_PHI) continue; /* keep conventional SSA */
      FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p || !var_is_reg_p (var)) continue;
        for (;;) {
          se = insn->ops[op_num].data;
          def = se->def;
          if (def->bb->index == 0) break; /* arg init or undef insn */
          def_insn = def->insn;
          if (se->prev_use != NULL || se->next_use != NULL || !move_p (def_insn)
              || bitmap_bit_p (temp_bitmap, def_insn->ops[1].u.reg))
            break;
          DEBUG (2, {
            fprintf (debug_file, "  Removing copy insn %-5lu", (unsigned long) def->index);
            MIR_output_insn (gen_ctx->ctx, debug_file, def_insn, curr_func_item->u.func, TRUE);
          });
          reg = var2reg (gen_ctx, var);
          new_reg = def_insn->ops[1].u.reg;
          remove_ssa_edge (gen_ctx, se);
          insn->ops[op_num].data = def_insn->ops[1].data;
          gen_delete_insn (gen_ctx, def_insn);
          deleted_insns_num++;
          se = insn->ops[op_num].data;
          se->use = bb_insn;
          se->use_op_num = op_num;
          rename_op_reg (gen_ctx, &insn->ops[op_num], reg, new_reg, insn);
        }
      }
      w = get_ext_params (insn->code, &sign_p);
      if (w != 0 && insn->ops[1].mode == MIR_OP_REG && var_is_reg_p (insn->ops[1].u.reg)) {
        se = insn->ops[1].data;
        def_insn = se->def->insn;
        w2 = get_ext_params (def_insn->code, &sign2_p);
        if (w2 != 0 && sign_p == sign2_p && w2 <= w
            && !bitmap_bit_p (temp_bitmap, def_insn->ops[1].u.reg)) {
          DEBUG (2, {
            fprintf (debug_file, "    Change code of insn %lu: before",
                     (unsigned long) bb_insn->index);
            MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
          });
          insn->code = MIR_MOV;
          DEBUG (2, {
            fprintf (debug_file, "    after");
            MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
          });
        }
      }
    }
  DEBUG (1, { fprintf (debug_file, "%5ld deleted copy insns\n", deleted_insns_num); });
}

/* New Page */

/* Removing redundant insns through GVN.  */

typedef struct expr {
  MIR_insn_t insn;    /* opcode and input operands are the expr keys */
  uint32_t num;       /* the expression number (0, 1 ...) */
  MIR_reg_t temp_reg; /* 0 initially and reg used to remove redundant expr */
} * expr_t;

DEF_VARR (expr_t);
DEF_HTAB (expr_t);

struct gvn_ctx {
  VARR (expr_t) * exprs;    /* the expr number -> expression */
  HTAB (expr_t) * expr_tab; /* keys: insn code and input operands */
};

#define exprs gen_ctx->gvn_ctx->exprs
#define expr_tab gen_ctx->gvn_ctx->expr_tab

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

static int op_eq (gen_ctx_t gen_ctx, MIR_op_t op1, MIR_op_t op2) {
  return MIR_op_eq_p (gen_ctx->ctx, op1, op2);
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
    if (out_p) continue;
    if ((insn1->ops[i].mode != MIR_OP_REG || insn2->ops[i].mode != MIR_OP_REG)
        && !op_eq (gen_ctx, insn1->ops[i], insn2->ops[i]))
      return FALSE;
    ssa_edge1 = insn1->ops[i].data;
    ssa_edge2 = insn2->ops[i].data;
    if (ssa_edge1 != NULL && ssa_edge2 != NULL
        && ssa_edge1->def->gvn_val != ssa_edge2->def->gvn_val)
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
    if (out_p) continue;
    if (e->insn->ops[i].mode != MIR_OP_REG) h = MIR_op_hash_step (ctx, h, e->insn->ops[i]);
    if ((ssa_edge = e->insn->ops[i].data) != NULL)
      h = mir_hash_step (h, (uint64_t) ssa_edge->def->gvn_val);
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

static expr_t add_expr (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  expr_t e = gen_malloc (gen_ctx, sizeof (struct expr));

  gen_assert (!MIR_call_code_p (insn->code) && insn->code != MIR_RET);
  e->insn = insn;
  e->num = ((bb_insn_t) insn->data)->index;
  e->temp_reg = 0;
  VARR_PUSH (expr_t, exprs, e);
  insert_expr (gen_ctx, e);
  return e;
}

static MIR_reg_t get_expr_temp_reg (gen_ctx_t gen_ctx, expr_t e) {
  int out_p;
  MIR_op_mode_t mode;

  if (e->temp_reg == 0) {
    mode = MIR_insn_op_mode (gen_ctx->ctx, e->insn, 0, &out_p);
    e->temp_reg = gen_new_temp_reg (gen_ctx,
                                    mode == MIR_OP_FLOAT     ? MIR_T_F
                                    : mode == MIR_OP_DOUBLE  ? MIR_T_D
                                    : mode == MIR_OP_LDOUBLE ? MIR_T_LD
                                                             : MIR_T_I64,
                                    curr_func_item->u.func);
  }
  return e->temp_reg;
}

static int gvn_insn_p (MIR_insn_t insn) {
  return (!MIR_branch_code_p (insn->code) && insn->code != MIR_RET && insn->code != MIR_SWITCH
          && insn->code != MIR_LABEL && !MIR_call_code_p (insn->code) && insn->code != MIR_ALLOCA
          && insn->code != MIR_BSTART && insn->code != MIR_BEND && insn->code != MIR_VA_START
          && insn->code != MIR_VA_ARG && insn->code != MIR_VA_END
          && insn->code != MIR_PHI
          /* After simplification we have only mem insn in form: mem = reg or reg = mem. */
          && (!move_code_p (insn->code)
              || (insn->ops[0].mode != MIR_OP_MEM && insn->ops[0].mode != MIR_OP_HARD_REG_MEM
                  && insn->ops[1].mode != MIR_OP_MEM && insn->ops[1].mode != MIR_OP_HARD_REG_MEM)));
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

static int phi_use_p (MIR_insn_t insn) {
  for (ssa_edge_t se = insn->ops[0].data; se != NULL; se = se->next_use)
    if (se->use->insn->code == MIR_PHI) return TRUE;
  return FALSE;
}

static void gvn_modify (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t bb;
  bb_insn_t bb_insn, new_bb_insn, next_bb_insn, expr_bb_insn;
  MIR_reg_t temp_reg;
  long gvn_insns_num = 0;

  for (size_t i = 0; i < VARR_LENGTH (bb_t, worklist); i++) {
    bb = VARR_GET (bb_t, worklist, i);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      expr_t e, new_e;
      MIR_op_t op;
      int add_def_p;
      MIR_type_t type;
      MIR_insn_code_t move_code;
      MIR_insn_t new_insn, def_insn, insn = bb_insn->insn;
      ssa_edge_t list;

      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (!gvn_insn_p (insn)) continue;
      if (!find_expr (gen_ctx, insn, &e)) {
        e = add_expr (gen_ctx, insn);
        DEBUG (2, { print_expr (gen_ctx, e, "Adding"); });
      }
      if (move_p (insn))
        bb_insn->gvn_val = ((ssa_edge_t) insn->ops[1].data)->def->gvn_val;
      else
        bb_insn->gvn_val = e->num;
      DEBUG (2, {
        fprintf (debug_file, "Val=%lu for insn %lu:", (unsigned long) bb_insn->gvn_val,
                 (unsigned long) bb_insn->index);
        MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, TRUE);
      });
      if (e->insn == insn || move_p (insn)
          || (imm_move_p (insn) && insn->ops[1].mode != MIR_OP_REF))
        continue;
      if (phi_use_p (e->insn)) continue; /* keep conventional SSA */
      expr_bb_insn = e->insn->data;
      if (bb->index != expr_bb_insn->bb->index
          && !bitmap_bit_p (bb->dom_in, expr_bb_insn->bb->index))
        continue;
      add_def_p = e->temp_reg == 0;
      temp_reg = get_expr_temp_reg (gen_ctx, e);
      op = MIR_new_reg_op (ctx, temp_reg);
      type = MIR_reg_type (ctx, temp_reg, curr_func_item->u.func);
#ifndef NDEBUG
      int out_p;
      MIR_insn_op_mode (ctx, insn, 0, &out_p); /* result here is always 0-th op */
      gen_assert (out_p);
#endif
      move_code = get_move_code (type);
      if (add_def_p) {
        list = e->insn->ops[0].data;
        e->insn->ops[0].data = NULL;
        new_insn = MIR_new_insn (ctx, move_code, op, e->insn->ops[0]);
        gen_add_insn_after (gen_ctx, e->insn, new_insn);
        add_ssa_edge (gen_ctx, e->insn->data, 0, new_insn->data, 1);
        new_insn->ops[0].data = list;
        new_bb_insn = new_insn->data;
        change_ssa_edge_list_def (list, new_bb_insn, 0, e->insn->ops[0].u.reg, temp_reg);
        if (!find_expr (gen_ctx, new_insn, &new_e)) new_e = add_expr (gen_ctx, new_insn);
        new_bb_insn->gvn_val = e->num;
        DEBUG (2, {
          fprintf (debug_file, "  adding insn ");
          MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, FALSE);
          fprintf (debug_file, "  after def insn ");
          MIR_output_insn (ctx, debug_file, e->insn, curr_func_item->u.func, TRUE);
        });
      }
      list = insn->ops[0].data;
      insn->ops[0].data = NULL; /* make redundant insn having no uses */
      new_insn = MIR_new_insn (ctx, move_code, insn->ops[0], op);
      gen_add_insn_after (gen_ctx, insn, new_insn);
      def_insn = DLIST_NEXT (MIR_insn_t, e->insn);
      add_ssa_edge (gen_ctx, def_insn->data, 0, new_insn->data, 1);
      new_insn->ops[0].data = list;
      new_bb_insn = new_insn->data;
      change_ssa_edge_list_def (list, new_bb_insn, 0, 0, 0);
      if (!find_expr (gen_ctx, new_insn, &new_e)) new_e = add_expr (gen_ctx, new_insn);
      new_bb_insn->gvn_val = e->num;
      gvn_insns_num++;
      DEBUG (2, {
        fprintf (debug_file, "  adding insn ");
        MIR_output_insn (ctx, debug_file, new_insn, curr_func_item->u.func, FALSE);
        fprintf (debug_file, "  after use insn ");
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
      });
    }
  }
  DEBUG (1, { fprintf (debug_file, "%5ld found GVN redundant insns\n", gvn_insns_num); });
}

static void gvn (gen_ctx_t gen_ctx) {
  calculate_dominators (gen_ctx);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    VARR_PUSH (bb_t, worklist, bb);
  qsort (VARR_ADDR (bb_t, worklist), VARR_LENGTH (bb_t, worklist), sizeof (bb_t), rpost_cmp);
  gvn_modify (gen_ctx);
}

static void gvn_clear (gen_ctx_t gen_ctx) {
  HTAB_CLEAR (expr_t, expr_tab);
  while (VARR_LENGTH (expr_t, exprs) != 0) free (VARR_POP (expr_t, exprs));
}

static void init_gvn (gen_ctx_t gen_ctx) {
  gen_ctx->gvn_ctx = gen_malloc (gen_ctx, sizeof (struct gvn_ctx));
  VARR_CREATE (expr_t, exprs, 512);
  HTAB_CREATE (expr_t, expr_tab, 1024, expr_hash, expr_eq, gen_ctx);
}

static void finish_gvn (gen_ctx_t gen_ctx) {
  VARR_DESTROY (expr_t, exprs);
  HTAB_DESTROY (expr_t, expr_tab);
  free (gen_ctx->gvn_ctx);
  gen_ctx->gvn_ctx = NULL;
}

/* New Page */

/* Sparse Conditional Constant Propagation.  Live info should exist.  */

#define live_in in
#define live_out out

enum ccp_val_kind { CCP_CONST = 0, CCP_VARYING, CCP_UNKNOWN };

struct ccp_val {
  enum ccp_val_kind val_kind : 8;
  unsigned int flag : 8;
  size_t ccp_run;
  const_t val;
};

typedef struct ccp_val *ccp_val_t;
DEF_VARR (ccp_val_t);

struct ccp_ctx {
  size_t curr_ccp_run;
  bitmap_t bb_visited;
  VARR (bb_t) * ccp_bbs;
  VARR (bb_insn_t) * ccp_insns;
  VARR (ccp_val_t) * ccp_vals;
};

#define curr_ccp_run gen_ctx->ccp_ctx->curr_ccp_run
#define bb_visited gen_ctx->ccp_ctx->bb_visited
#define ccp_bbs gen_ctx->ccp_ctx->ccp_bbs
#define ccp_insns gen_ctx->ccp_ctx->ccp_insns
#define ccp_vals gen_ctx->ccp_ctx->ccp_vals

static ccp_val_t get_ccp_val (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  ccp_val_t ccp_val;

  while (VARR_LENGTH (ccp_val_t, ccp_vals) <= bb_insn->index) VARR_PUSH (ccp_val_t, ccp_vals, NULL);
  if ((ccp_val = VARR_GET (ccp_val_t, ccp_vals, bb_insn->index)) == NULL) {
    ccp_val = gen_malloc (gen_ctx, sizeof (struct ccp_val));
    VARR_SET (ccp_val_t, ccp_vals, bb_insn->index, ccp_val);
    ccp_val->ccp_run = 0;
  }
  if (ccp_val->ccp_run != curr_ccp_run) {
    ccp_val->val_kind = bb_insn->bb == DLIST_HEAD (bb_t, curr_cfg->bbs) ? CCP_VARYING : CCP_UNKNOWN;
    ccp_val->flag = FALSE;
    ccp_val->ccp_run = curr_ccp_run;
  }
  return ccp_val;
}

#undef live_in
#undef live_out

static void initiate_ccp_info (gen_ctx_t gen_ctx) {
  bb_insn_t bb_insn;
  ccp_val_t ccp_val;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) != NULL
        && MIR_branch_code_p (bb_insn->insn->code) && bb_insn->insn->code != MIR_JMP
        && bb_insn->insn->code != MIR_SWITCH) {
      for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL;
           e = DLIST_NEXT (out_edge_t, e))
        if (e->dst != DLIST_EL (bb_t, curr_cfg->bbs, 1)) /* ignore exit bb */
          e->skipped_p = TRUE;
    }
  }
  bitmap_clear (bb_visited);
  VARR_TRUNC (bb_insn_t, ccp_insns, 0);
  VARR_TRUNC (bb_t, ccp_bbs, 0);
  while (VARR_LENGTH (ccp_val_t, ccp_vals) != 0)
    if ((ccp_val = VARR_POP (ccp_val_t, ccp_vals)) != NULL) free (ccp_val);
  VARR_PUSH (bb_t, ccp_bbs, DLIST_HEAD (bb_t, curr_cfg->bbs)); /* entry bb */
}

static int var_op_p (MIR_op_t op) { return op.mode == MIR_OP_HARD_REG || op.mode == MIR_OP_REG; }
static int var_insn_op_p (MIR_insn_t insn, size_t nop) { return var_op_p (insn->ops[nop]); }

static enum ccp_val_kind get_op (gen_ctx_t gen_ctx, MIR_insn_t insn, size_t nop, const_t *val) {
  MIR_op_t op;
  ssa_edge_t ssa_edge;
  ccp_val_t ccp_val;

  if (!var_insn_op_p (insn, nop)) {
    if ((op = insn->ops[nop]).mode == MIR_OP_INT) {
      val->uns_p = FALSE;
      val->u.i = op.u.i;
      return CCP_CONST;
    } else if (op.mode == MIR_OP_UINT) {
      val->uns_p = TRUE;
      val->u.u = op.u.u;
      return CCP_CONST;
    }
    return CCP_VARYING;
  }
  ssa_edge = insn->ops[nop].data;
  ccp_val = get_ccp_val (gen_ctx, ssa_edge->def);
  if (ccp_val->val_kind == CCP_CONST) *val = ccp_val->val;
  return ccp_val->val_kind;
}

static enum ccp_val_kind get_2ops (gen_ctx_t gen_ctx, MIR_insn_t insn, const_t *val1, int out_p) {
  if (out_p && !var_insn_op_p (insn, 0)) return CCP_UNKNOWN;
  return get_op (gen_ctx, insn, 1, val1);
}

static enum ccp_val_kind get_3ops (gen_ctx_t gen_ctx, MIR_insn_t insn, const_t *val1, const_t *val2,
                                   int out_p) {
  enum ccp_val_kind res1, res2;

  if (out_p && !var_insn_op_p (insn, 0)) return CCP_UNKNOWN;
  if ((res1 = get_op (gen_ctx, insn, 1, val1)) == CCP_VARYING) return CCP_VARYING;
  if ((res2 = get_op (gen_ctx, insn, 2, val2)) == CCP_VARYING) return CCP_VARYING;
  return res1 == CCP_UNKNOWN || res2 == CCP_UNKNOWN ? CCP_UNKNOWN : CCP_CONST;
}

static enum ccp_val_kind get_2iops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *p, int out_p) {
  const_t val;
  enum ccp_val_kind res;

  if ((res = get_2ops (gen_ctx, insn, &val, out_p))) return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_2isops (gen_ctx_t gen_ctx, MIR_insn_t insn, int32_t *p, int out_p) {
  const_t val;
  enum ccp_val_kind res;

  if ((res = get_2ops (gen_ctx, insn, &val, out_p))) return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind MIR_UNUSED get_2usops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint32_t *p,
                                                int out_p) {
  const_t val;
  enum ccp_val_kind res;

  if ((res = get_2ops (gen_ctx, insn, &val, out_p))) return res;
  *p = val.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3iops (gen_ctx_t gen_ctx, MIR_insn_t insn, int64_t *p1, int64_t *p2,
                                    int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;

  if ((res = get_3ops (gen_ctx, insn, &val1, &val2, out_p))) return res;
  *p1 = val1.u.i;
  *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3isops (gen_ctx_t gen_ctx, MIR_insn_t insn, int32_t *p1, int32_t *p2,
                                     int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;

  if ((res = get_3ops (gen_ctx, insn, &val1, &val2, out_p))) return res;
  *p1 = val1.u.i;
  *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3uops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint64_t *p1, uint64_t *p2,
                                    int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;

  if ((res = get_3ops (gen_ctx, insn, &val1, &val2, out_p))) return res;
  *p1 = val1.u.u;
  *p2 = val2.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3usops (gen_ctx_t gen_ctx, MIR_insn_t insn, uint32_t *p1, uint32_t *p2,
                                     int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;

  if ((res = get_3ops (gen_ctx, insn, &val1, &val2, out_p))) return res;
  *p1 = val1.u.u;
  *p2 = val2.u.u;
  return CCP_CONST;
}

#define EXT(tp)                                                                       \
  do {                                                                                \
    int64_t p;                                                                        \
    if ((ccp_res = get_2iops (gen_ctx, insn, &p, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                \
    val.u.i = (tp) p;                                                                 \
  } while (0)

#define IOP2(op)                                                                      \
  do {                                                                                \
    int64_t p;                                                                        \
    if ((ccp_res = get_2iops (gen_ctx, insn, &p, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                \
    val.u.i = op p;                                                                   \
  } while (0)

#define IOP2S(op)                                                                      \
  do {                                                                                 \
    int32_t p;                                                                         \
    if ((ccp_res = get_2isops (gen_ctx, insn, &p, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                 \
    val.u.i = op p;                                                                    \
  } while (0)

#define UOP2S(op)                                                                      \
  do {                                                                                 \
    uint32_t p;                                                                        \
    if ((ccp_res = get_2usops (gen_ctx, insn, &p, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                 \
    val.u.u = op p;                                                                    \
  } while (0)

#define IOP3(op)                                                                            \
  do {                                                                                      \
    int64_t p1, p2;                                                                         \
    if ((ccp_res = get_3iops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                      \
    val.u.i = p1 op p2;                                                                     \
  } while (0)

#define IOP3S(op)                                                                            \
  do {                                                                                       \
    int32_t p1, p2;                                                                          \
    if ((ccp_res = get_3isops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                       \
    val.u.i = p1 op p2;                                                                      \
  } while (0)

#define UOP3(op)                                                                            \
  do {                                                                                      \
    uint64_t p1, p2;                                                                        \
    if ((ccp_res = get_3uops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = TRUE;                                                                       \
    val.u.u = p1 op p2;                                                                     \
  } while (0)

#define UOP3S(op)                                                                            \
  do {                                                                                       \
    uint32_t p1, p2;                                                                         \
    if ((ccp_res = get_3usops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = TRUE;                                                                        \
    val.u.u = p1 op p2;                                                                      \
  } while (0)

#define IOP30(op)                                                                                  \
  do {                                                                                             \
    if ((ccp_res = get_op (gen_ctx, insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const0; \
    IOP3 (op);                                                                                     \
  } while (0)

#define IOP3S0(op)                                                                                 \
  do {                                                                                             \
    if ((ccp_res = get_op (gen_ctx, insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const0; \
    IOP3S (op);                                                                                    \
  } while (0)

#define UOP30(op)                                                                                  \
  do {                                                                                             \
    if ((ccp_res = get_op (gen_ctx, insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const0; \
    UOP3 (op);                                                                                     \
  } while (0)

#define UOP3S0(op)                                                                                 \
  do {                                                                                             \
    if ((ccp_res = get_op (gen_ctx, insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const0; \
    UOP3S (op);                                                                                    \
  } while (0)

#define ICMP(op)                                                                            \
  do {                                                                                      \
    int64_t p1, p2;                                                                         \
    if ((ccp_res = get_3iops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                      \
    val.u.i = p1 op p2;                                                                     \
  } while (0)

#define ICMPS(op)                                                                            \
  do {                                                                                       \
    int32_t p1, p2;                                                                          \
    if ((ccp_res = get_3isops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                       \
    val.u.i = p1 op p2;                                                                      \
  } while (0)

#define UCMP(op)                                                                            \
  do {                                                                                      \
    uint64_t p1, p2;                                                                        \
    if ((ccp_res = get_3uops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                      \
    val.u.i = p1 op p2;                                                                     \
  } while (0)

#define UCMPS(op)                                                                            \
  do {                                                                                       \
    uint32_t p1, p2;                                                                         \
    if ((ccp_res = get_3usops (gen_ctx, insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                       \
    val.u.i = p1 op p2;                                                                      \
  } while (0)

#define BICMP(op)                                                                            \
  do {                                                                                       \
    int64_t p1, p2;                                                                          \
    if ((ccp_res = get_3iops (gen_ctx, insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                       \
    val.u.i = p1 op p2;                                                                      \
  } while (0)

#define BICMPS(op)                                                                            \
  do {                                                                                        \
    int32_t p1, p2;                                                                           \
    if ((ccp_res = get_3isops (gen_ctx, insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                        \
    val.u.i = p1 op p2;                                                                       \
  } while (0)

#define BUCMP(op)                                                                            \
  do {                                                                                       \
    uint64_t p1, p2;                                                                         \
    if ((ccp_res = get_3uops (gen_ctx, insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                       \
    val.u.i = p1 op p2;                                                                      \
  } while (0)

#define BUCMPS(op)                                                                            \
  do {                                                                                        \
    uint32_t p1, p2;                                                                          \
    if ((ccp_res = get_3usops (gen_ctx, insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; \
    val.uns_p = FALSE;                                                                        \
    val.u.i = p1 op p2;                                                                       \
  } while (0)

static int get_ccp_res_op (gen_ctx_t gen_ctx, MIR_insn_t insn, int out_num, MIR_op_t *op) {
  MIR_context_t ctx = gen_ctx->ctx;
  int out_p;

  gen_assert (!MIR_call_code_p (insn->code));
  if (out_num > 0 || MIR_insn_nops (ctx, insn) < 1) return FALSE;
  MIR_insn_op_mode (ctx, insn, 0, &out_p);
  if (!out_p) return FALSE;
  *op = insn->ops[0];
  return TRUE;
}

static int ccp_phi_insn_update (gen_ctx_t gen_ctx, bb_insn_t phi) {
  MIR_insn_t phi_insn = phi->insn;
  bb_t bb = phi->bb;
  edge_t e;
  ssa_edge_t ssa_edge;
  ccp_val_t res_ccp_val, op_ccp_val;
  size_t nop;
  int change_p = FALSE;

  res_ccp_val = get_ccp_val (gen_ctx, phi);
  if (res_ccp_val->val_kind == CCP_VARYING) return FALSE;
  nop = 1;
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e), nop++) {
    /* Update phi value: */
    if (e->skipped_p) continue;
    gen_assert (nop < phi_insn->nops);
    ssa_edge = phi_insn->ops[nop].data;
    op_ccp_val = get_ccp_val (gen_ctx, ssa_edge->def);
    if (op_ccp_val->val_kind == CCP_UNKNOWN) continue;
    if (res_ccp_val->val_kind == CCP_UNKNOWN || op_ccp_val->val_kind == CCP_VARYING) {
      change_p = res_ccp_val->val_kind != op_ccp_val->val_kind;
      res_ccp_val->val_kind = op_ccp_val->val_kind;
      if (op_ccp_val->val_kind == CCP_VARYING) break;
      if (op_ccp_val->val_kind == CCP_CONST) res_ccp_val->val = op_ccp_val->val;
    } else {
      gen_assert (res_ccp_val->val_kind == CCP_CONST && op_ccp_val->val_kind == CCP_CONST);
      if (res_ccp_val->val.uns_p != op_ccp_val->val.uns_p
          || (res_ccp_val->val.uns_p && res_ccp_val->val.u.u != op_ccp_val->val.u.u)
          || (!res_ccp_val->val.uns_p && res_ccp_val->val.u.i != op_ccp_val->val.u.i)) {
        res_ccp_val->val_kind = CCP_VARYING;
        change_p = TRUE;
        break;
      }
    }
  }
  return change_p;
}

static int ccp_insn_update (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  // ??? should we do CCP for FP (fast-math) too
  MIR_op_t op;
  int change_p;
  enum ccp_val_kind ccp_res;
  const_t val;
  ccp_val_t ccp_val;
  enum ccp_val_kind val_kind;

  switch (insn->code) {
  case MIR_PHI: return ccp_phi_insn_update (gen_ctx, insn->data);
  case MIR_MOV: IOP2 (+); break;
  case MIR_EXT8: EXT (int8_t); break;
  case MIR_EXT16: EXT (int16_t); break;
  case MIR_EXT32: EXT (int32_t); break;
  case MIR_UEXT8: EXT (uint8_t); break;
  case MIR_UEXT16: EXT (uint16_t); break;
  case MIR_UEXT32: EXT (uint32_t); break;

  case MIR_NEG: IOP2 (-); break;
  case MIR_NEGS: IOP2S (-); break;

  case MIR_ADD: IOP3 (+); break;
  case MIR_ADDS: IOP3S (+); break;

  case MIR_SUB: IOP3 (-); break;
  case MIR_SUBS: IOP3S (-); break;

  case MIR_MUL: IOP3 (*); break;
  case MIR_MULS: IOP3S (*); break;

  case MIR_DIV: IOP30 (/); break;
  case MIR_DIVS: IOP3S0 (/); break;
  case MIR_UDIV: UOP30 (/); break;
  case MIR_UDIVS: UOP3S0 (/); break;

  case MIR_MOD: IOP30 (%); break;
  case MIR_MODS: IOP3S0 (%); break;
  case MIR_UMOD: UOP30 (%); break;
  case MIR_UMODS: UOP3S0 (%); break;

  case MIR_AND: IOP3 (&); break;
  case MIR_ANDS: IOP3S (&); break;
  case MIR_OR: IOP3 (|); break;
  case MIR_ORS: IOP3S (|); break;
  case MIR_XOR: IOP3 (^); break;
  case MIR_XORS: IOP3S (^); break;

  case MIR_LSH: IOP3 (<<); break;
  case MIR_LSHS: IOP3S (<<); break;
  case MIR_RSH: IOP3 (>>); break;
  case MIR_RSHS: IOP3S (>>); break;
  case MIR_URSH: UOP3 (>>); break;
  case MIR_URSHS: UOP3S (>>); break;

  case MIR_EQ: ICMP (==); break;
  case MIR_EQS: ICMPS (==); break;
  case MIR_NE: ICMP (!=); break;
  case MIR_NES: ICMPS (!=); break;

  case MIR_LT: ICMP (<); break;
  case MIR_LTS: ICMPS (<); break;
  case MIR_ULT: UCMP (<); break;
  case MIR_ULTS: UCMPS (<); break;
  case MIR_LE: ICMP (<=); break;
  case MIR_LES: ICMPS (<=); break;
  case MIR_ULE: UCMP (<=); break;
  case MIR_ULES: UCMPS (<=); break;
  case MIR_GT: ICMP (>); break;
  case MIR_GTS: ICMPS (>); break;
  case MIR_UGT: UCMP (>); break;
  case MIR_UGTS: UCMPS (>); break;
  case MIR_GE: ICMP (>=); break;
  case MIR_GES: ICMPS (>=); break;
  case MIR_UGE: UCMP (>=); break;
  case MIR_UGES: UCMPS (>=); break;

  default: ccp_res = CCP_VARYING; goto non_const;
  }
#ifndef NDEBUG
  {
    int out_p;

    MIR_insn_op_mode (gen_ctx->ctx, insn, 0, &out_p); /* result here is always 0-th op */
    gen_assert (out_p);
  }
#endif
  ccp_val = get_ccp_val (gen_ctx, insn->data);
  val_kind = ccp_val->val_kind;
  gen_assert (val_kind == CCP_UNKNOWN || val_kind == CCP_CONST);
  ccp_val->val_kind = CCP_CONST;
  ccp_val->val = val;
  return val_kind != CCP_CONST;
non_const0:
  if (ccp_res == CCP_CONST && val.u.i == 0) ccp_res = CCP_VARYING;
non_const:
  if (ccp_res == CCP_UNKNOWN) return FALSE;
  gen_assert (ccp_res == CCP_VARYING);
  change_p = FALSE;
  if (MIR_call_code_p (insn->code)) {
    ccp_val = get_ccp_val (gen_ctx, insn->data);
    if (ccp_val->val_kind != CCP_VARYING) change_p = TRUE;
    ccp_val->val_kind = CCP_VARYING;
  } else if (get_ccp_res_op (gen_ctx, insn, 0, &op)
             && (op.mode == MIR_OP_HARD_REG || op.mode == MIR_OP_REG)) {
    ccp_val = get_ccp_val (gen_ctx, insn->data);
    if (ccp_val->val_kind != CCP_VARYING) change_p = TRUE;
    ccp_val->val_kind = CCP_VARYING;
    gen_assert (!get_ccp_res_op (gen_ctx, insn, 1, &op));
  }
  return change_p;
}

static enum ccp_val_kind ccp_branch_update (gen_ctx_t gen_ctx, MIR_insn_t insn, int *res) {
  enum ccp_val_kind ccp_res;
  const_t val;

  switch (insn->code) {
  case MIR_BT:
  case MIR_BTS:
  case MIR_BF:
  case MIR_BFS:
    if ((ccp_res = get_op (gen_ctx, insn, 1, &val)) != CCP_CONST) return ccp_res;
    if (insn->code == MIR_BTS || insn->code == MIR_BFS)
      *res = val.uns_p ? (uint32_t) val.u.u != 0 : (int32_t) val.u.i != 0;
    else
      *res = val.uns_p ? val.u.u != 0 : val.u.i != 0;
    if (insn->code == MIR_BF || insn->code == MIR_BFS) *res = !*res;
    return CCP_CONST;
  case MIR_BEQ: BICMP (==); break;
  case MIR_BEQS: BICMPS (==); break;
  case MIR_BNE: BICMP (!=); break;
  case MIR_BNES: BICMPS (!=); break;

  case MIR_BLT: BICMP (<); break;
  case MIR_BLTS: BICMPS (<); break;
  case MIR_UBLT: BUCMP (<); break;
  case MIR_UBLTS: BUCMPS (<); break;
  case MIR_BLE: BICMP (<=); break;
  case MIR_BLES: BICMPS (<=); break;
  case MIR_UBLE: BUCMP (<=); break;
  case MIR_UBLES: BUCMPS (<=); break;
  case MIR_BGT: BICMP (>); break;
  case MIR_BGTS: BICMPS (>); break;
  case MIR_UBGT: BUCMP (>); break;
  case MIR_UBGTS: BUCMPS (>); break;
  case MIR_BGE: BICMP (>=); break;
  case MIR_BGES: BICMPS (>=); break;
  case MIR_UBGE: BUCMP (>=); break;
  case MIR_UBGES: BUCMPS (>=); break;

  default: return CCP_VARYING;  // ??? should we do CCP for FP BCMP too
  }
  *res = val.u.i;
  return CCP_CONST;
non_const:
  return ccp_res;
}

static void ccp_push_used_insns (gen_ctx_t gen_ctx, ssa_edge_t first_ssa_edge) {
  MIR_context_t ctx = gen_ctx->ctx;

  for (ssa_edge_t ssa_edge = first_ssa_edge; ssa_edge != NULL; ssa_edge = ssa_edge->next_use) {
    bb_insn_t bb_insn = ssa_edge->use;

    if (bb_insn->flag || !bitmap_bit_p (bb_visited, bb_insn->bb->index))
      continue; /* already in ccp_insns or bb is not processed yet */
    VARR_PUSH (bb_insn_t, ccp_insns, bb_insn);
    DEBUG (2, {
      fprintf (debug_file, "           pushing bb%lu insn: ", (unsigned long) bb_insn->bb->index);
      MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
    });
    bb_insn->flag = TRUE;
  }
}

static void ccp_process_active_edge (gen_ctx_t gen_ctx, edge_t e) {
  if (e->skipped_p && !e->dst->flag) {
    DEBUG (2, {
      fprintf (debug_file, "         Make edge bb%lu->bb%lu active\n",
               (unsigned long) e->src->index, (unsigned long) e->dst->index);
    });
    e->dst->flag = TRUE; /* just activated edge whose dest is not in ccp_bbs */
    VARR_PUSH (bb_t, ccp_bbs, e->dst);
  }
  e->skipped_p = FALSE;
}

static void ccp_make_insn_update (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  MIR_op_t op;
  ccp_val_t ccp_val;

  if (!ccp_insn_update (gen_ctx, insn)) {
    DEBUG (2, {
      if (MIR_call_code_p (insn->code)) {
        fprintf (debug_file, " -- keep all results varying");
      } else if (get_ccp_res_op (gen_ctx, insn, 0, &op) && var_insn_op_p (insn, 0)) {
        ccp_val = get_ccp_val (gen_ctx, insn->data);
        if (ccp_val->val_kind == CCP_UNKNOWN) {
          fprintf (debug_file, " -- make the result unknown");
        } else if (ccp_val->val_kind == CCP_VARYING) {
          fprintf (debug_file, " -- keep the result varying");
        } else {
          gen_assert (ccp_val->val_kind == CCP_CONST);
          fprintf (debug_file, " -- keep the result a constant ");
          print_const (debug_file, ccp_val->val);
        }
      }
      fprintf (debug_file, "\n");
    });
  } else {
    ccp_val = NULL; /* to remove an initilized warning */
    if (MIR_call_code_p (insn->code)) {
      ccp_val = get_ccp_val (gen_ctx, insn->data);
      gen_assert (insn->ops[0].u.ref->item_type == MIR_proto_item);
      MIR_proto_t proto = insn->ops[0].u.ref->u.proto;
      for (uint32_t i = 0; i < proto->nres; i++)
        ccp_push_used_insns (gen_ctx, insn->ops[i + 2].data);
    } else if (get_ccp_res_op (gen_ctx, insn, 0, &op) && var_op_p (op)) {
      ccp_val = get_ccp_val (gen_ctx, insn->data);
      ccp_push_used_insns (gen_ctx, op.data);
    }
    gen_assert (ccp_val != NULL);
    DEBUG (2, {
      if (MIR_call_code_p (insn->code)) {
        fprintf (debug_file, " -- make all results varying\n");
      } else if (ccp_val->val_kind == CCP_VARYING) {
        fprintf (debug_file, " -- make the result varying\n");
      } else {
        gen_assert (ccp_val->val_kind == CCP_CONST);
        fprintf (debug_file, " -- make the result a constant ");
        print_const (debug_file, ccp_val->val);
        fprintf (debug_file, "\n");
      }
    });
  }
}

static void ccp_process_insn (gen_ctx_t gen_ctx, bb_insn_t bb_insn) {
  int res;
  enum ccp_val_kind ccp_res;
  edge_t e;
  bb_t bb = bb_insn->bb;
  MIR_insn_t insn = bb_insn->insn;

  DEBUG (2, {
    fprintf (debug_file, "       processing bb%lu insn: ", (unsigned long) bb_insn->bb->index);
    MIR_output_insn (gen_ctx->ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
  });
  if (!MIR_branch_code_p (insn->code) || insn->code == MIR_JMP || insn->code == MIR_SWITCH) {
    ccp_make_insn_update (gen_ctx, insn);  // ??? should we process SWITCH as cond branch
    return;
  }
  DEBUG (2, { fprintf (debug_file, "\n"); });
  if ((ccp_res = ccp_branch_update (gen_ctx, insn, &res)) == CCP_CONST) {
    /* Remember about an edge to exit bb.  First edge is always for
       fall through and the 2nd edge is for jump bb. */
    gen_assert (DLIST_LENGTH (out_edge_t, bb->out_edges) >= 2);
    e = res ? DLIST_EL (out_edge_t, bb->out_edges, 1) : DLIST_EL (out_edge_t, bb->out_edges, 0);
    ccp_process_active_edge (gen_ctx, e);
  } else if (ccp_res == CCP_VARYING) { /* activate all edges */
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
      ccp_process_active_edge (gen_ctx, e);
  }
}

static void ccp_process_bb (gen_ctx_t gen_ctx, bb_t bb) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  edge_t e;

  DEBUG (2, { fprintf (debug_file, "       processing bb%lu\n", (unsigned long) bb->index); });
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
       bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
    if ((insn = bb_insn->insn)->code == MIR_LABEL) continue;
    if (insn->code != MIR_PHI) break;
    DEBUG (2, {
      gen_assert (insn->ops[0].mode == MIR_OP_REG);
      fprintf (debug_file,
               "       processing phi of reg%lu(%s) in bb%lu:", (long unsigned) insn->ops[0].u.reg,
               MIR_reg_name (gen_ctx->ctx, insn->ops[0].u.reg, curr_func_item->u.func),
               (unsigned long) bb->index);
    });
    ccp_make_insn_update (gen_ctx, bb_insn->insn);
  }
  if (!bitmap_set_bit_p (bb_visited, bb->index)) return;
  for (; bb_insn != NULL; bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
    ccp_process_insn (gen_ctx, bb_insn);
  }
  if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL
      || !MIR_branch_code_p (bb_insn->insn->code) || bb_insn->insn->code == MIR_JMP
      || bb_insn->insn->code == MIR_SWITCH) {
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e)) {
      gen_assert (!e->skipped_p);
      if (!bitmap_bit_p (bb_visited, e->dst->index) && !e->dst->flag) {
        e->dst->flag = TRUE; /* first process of dest which is not in ccp_bbs */
        VARR_PUSH (bb_t, ccp_bbs, e->dst);
      }
      ccp_process_active_edge (gen_ctx, e);
    }
  }
}

static void ccp_traverse (bb_t bb) {
  bb->flag = TRUE;
  for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    if (!e->skipped_p && !e->dst->flag)
      ccp_traverse (e->dst); /* visit unvisited active edge destination */
}

static int get_ccp_res_val (gen_ctx_t gen_ctx, MIR_insn_t insn, const_t *val) {
  ccp_val_t ccp_val;
  MIR_op_t op;

  if (MIR_call_code_p (insn->code) || !get_ccp_res_op (gen_ctx, insn, 0, &op))
    return FALSE; /* call results always produce varying values */
  if (!var_insn_op_p (insn, 0)) return FALSE;
  ccp_val = get_ccp_val (gen_ctx, insn->data);
  if (ccp_val->val_kind != CCP_CONST) return FALSE;
  *val = ccp_val->val;
  return TRUE;
}

static void ccp_remove_insn_ssa_edges (gen_ctx_t gen_ctx, MIR_insn_t insn) {
  ssa_edge_t ssa_edge;
  for (size_t i = 0; i < insn->nops; i++) {
    /* output operand refers to chain of ssa edges -- remove them all: */
    while ((ssa_edge = insn->ops[i].data) != NULL) remove_ssa_edge (gen_ctx, ssa_edge);
  }
}

static int ccp_modify (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_t bb, next_bb;
  bb_insn_t bb_insn, next_bb_insn;
  const_t val;
  MIR_op_t op;
  MIR_insn_t insn, prev_insn, first_insn;
  ssa_edge_t se, next_se;
  int res, change_p = FALSE;
  long deleted_insns_num = 0, deleted_branches_num = 0;

#ifndef NDEBUG
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    gen_assert (!bb->flag);
#endif
  ccp_traverse (DLIST_HEAD (bb_t, curr_cfg->bbs)); /* entry */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    if (!bb->flag) {
      change_p = TRUE;
      DEBUG (2, {
        fprintf (debug_file, "  deleting unreachable bb%lu and its edges\n",
                 (unsigned long) bb->index);
      });
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
           bb_insn = next_bb_insn) {
        next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
        insn = bb_insn->insn;
        ccp_remove_insn_ssa_edges (gen_ctx, insn);
        gen_delete_insn (gen_ctx, insn);
        deleted_insns_num++;
      }
      delete_bb (gen_ctx, bb);
      continue;
    }
    bb->flag = FALSE; /* reset for the future use */
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (get_ccp_res_val (gen_ctx, bb_insn->insn, &val)
          && (bb_insn->insn->code != MIR_MOV
              || (bb_insn->insn->ops[1].mode != MIR_OP_INT
                  && bb_insn->insn->ops[1].mode != MIR_OP_UINT))) {
        gen_assert (!MIR_call_code_p (bb_insn->insn->code));
        change_p = TRUE;
        DEBUG (2, {
          fprintf (debug_file, "  changing insn ");
          MIR_output_insn (gen_ctx->ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
        });
        op = val.uns_p ? MIR_new_uint_op (ctx, val.u.u) : MIR_new_int_op (ctx, val.u.i);
#ifndef NDEBUG
        {
          int out_p;

          MIR_insn_op_mode (ctx, bb_insn->insn, 0, &out_p); /* result here is always 0-th op */
          gen_assert (out_p);
        }
#endif
        /* remove edges whose def and use is the insn, e.g. for case "5: phi a,a #index 5,5" */
        for (se = bb_insn->insn->ops[0].data; se != NULL; se = next_se) {
          next_se = se->next_use;
          if (se->use == bb_insn) remove_ssa_edge (gen_ctx, se);
        }
        insn = MIR_new_insn (ctx, MIR_MOV, bb_insn->insn->ops[0], op); /* copy ops[0].data too! */
        MIR_insert_insn_before (ctx, curr_func_item, bb_insn->insn, insn);
        bb_insn->insn->ops[0].data = NULL;
        ccp_remove_insn_ssa_edges (gen_ctx, bb_insn->insn);
        MIR_remove_insn (ctx, curr_func_item, bb_insn->insn);
        insn->data = bb_insn;
        bb_insn->insn = insn;
        DEBUG (2, {
          fprintf (debug_file, "    on insn ");
          MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        });
      }
    }
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL) continue;
    insn = bb_insn->insn;
    first_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns)->insn;
    if (first_insn->code == MIR_LABEL && (prev_insn = DLIST_PREV (MIR_insn_t, first_insn)) != NULL
        && prev_insn->code == MIR_JMP && prev_insn->ops[0].u.label == first_insn) {
      DEBUG (2, {
        fprintf (debug_file, "  removing useless jump insn ");
        MIR_output_insn (ctx, debug_file, prev_insn, curr_func_item->u.func, TRUE);
        fprintf (debug_file, "\n");
      });
      ccp_remove_insn_ssa_edges (gen_ctx, prev_insn);
      gen_delete_insn (gen_ctx, prev_insn);
      deleted_branches_num++;
    }
    if (!MIR_branch_code_p (insn->code) || insn->code == MIR_JMP || insn->code == MIR_SWITCH
        || ccp_branch_update (gen_ctx, insn, &res) != CCP_CONST)
      continue;
    change_p = TRUE;
    if (!res) {
      edge_t e;

      DEBUG (2, {
        fprintf (debug_file, "  removing branch insn ");
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        fprintf (debug_file, "\n");
      });
      ccp_remove_insn_ssa_edges (gen_ctx, insn);
      gen_delete_insn (gen_ctx, insn);
      if ((e = DLIST_EL (out_edge_t, bb->out_edges, 1)) != NULL)
        delete_edge (e); /* e can be arleady deleted by previous removing an unreachable BB */
      deleted_branches_num++;
    } else {
      insn = MIR_new_insn (ctx, MIR_JMP, insn->ops[0]); /* label is always 0-th op */
      DEBUG (2, {
        fprintf (debug_file, "  changing branch insn ");
        MIR_output_insn (ctx, debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
        fprintf (debug_file, " onto jump insn ");
        MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        fprintf (debug_file, "\n");
      });
      MIR_insert_insn_before (ctx, curr_func_item, bb_insn->insn, insn);
      ccp_remove_insn_ssa_edges (gen_ctx, bb_insn->insn);
      MIR_remove_insn (ctx, curr_func_item, bb_insn->insn);
      insn->data = bb_insn;
      bb_insn->insn = insn;
      delete_edge (DLIST_EL (out_edge_t, bb->out_edges, 0));
    }
  }
  DEBUG (1, {
    fprintf (debug_file, "%5ld deleted CCP insns + %ld deleted branches\n", deleted_insns_num,
             deleted_branches_num);
  });
  return change_p;
}

static int ccp (gen_ctx_t gen_ctx) { /* conditional constant propagation */
  DEBUG (2, { fprintf (debug_file, "  CCP analysis:\n"); });
  curr_ccp_run++;
  bb_visited = temp_bitmap;
  initiate_ccp_info (gen_ctx);
  while (VARR_LENGTH (bb_t, ccp_bbs) != 0 || VARR_LENGTH (bb_insn_t, ccp_insns) != 0) {
    while (VARR_LENGTH (bb_t, ccp_bbs) != 0) {
      bb_t bb = VARR_POP (bb_t, ccp_bbs);

      bb->flag = FALSE;
      ccp_process_bb (gen_ctx, bb);
    }
    while (VARR_LENGTH (bb_insn_t, ccp_insns) != 0) {
      bb_insn_t bb_insn = VARR_POP (bb_insn_t, ccp_insns);

      gen_assert (bb_insn->flag);
      bb_insn->flag = FALSE;
      ccp_process_insn (gen_ctx, bb_insn);
    }
  }
  DEBUG (2, { fprintf (debug_file, "  CCP modification:\n"); });
  return ccp_modify (gen_ctx);
}

static void init_ccp (gen_ctx_t gen_ctx) {
  gen_ctx->ccp_ctx = gen_malloc (gen_ctx, sizeof (struct ccp_ctx));
  curr_ccp_run = 0;
  VARR_CREATE (bb_t, ccp_bbs, 256);
  VARR_CREATE (bb_insn_t, ccp_insns, 256);
  VARR_CREATE (ccp_val_t, ccp_vals, 256);
}

static void finish_ccp (gen_ctx_t gen_ctx) {
  ccp_val_t ccp_val;

  VARR_DESTROY (bb_t, ccp_bbs);
  VARR_DESTROY (bb_insn_t, ccp_insns);
  while (VARR_LENGTH (ccp_val_t, ccp_vals) != 0)
    if ((ccp_val = VARR_POP (ccp_val_t, ccp_vals)) != NULL) free (ccp_val);
  VARR_DESTROY (ccp_val_t, ccp_vals);
  free (gen_ctx->ccp_ctx);
  gen_ctx->ccp_ctx = NULL;
}

#undef live_in
#undef live_out

/* New Page */

#define live_in in
#define live_out out
#define live_kill kill
#define live_gen gen

/* Life analysis */
static void live_con_func_0 (bb_t bb) { bitmap_clear (bb->live_in); }

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
  if (!var_is_reg_p (var)) return target_hard_reg_type_ok_p (var, MIR_T_I32);
  return MIR_int_type_p (
    MIR_reg_type (gen_ctx->ctx, var2reg (gen_ctx, var), curr_func_item->u.func));
}

static MIR_insn_t initiate_bb_live_info (gen_ctx_t gen_ctx, MIR_insn_t bb_tail_insn, int moves_p,
                                         uint32_t *mvs_num) {
  bb_t bb = get_insn_bb (gen_ctx, bb_tail_insn);
  MIR_insn_t insn;
  size_t niter, passed_mem_num, bb_freq;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, mem_p, int_p = FALSE;
  int bb_int_pressure, bb_fp_pressure;
  mv_t mv;
  reg_info_t *breg_infos;
  insn_var_iterator_t insn_var_iter;

  gen_assert (!moves_p || optimize_level != 0);
  breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  bb_freq = 1;
  if (moves_p)
    for (int i = bb_loop_level (bb); i > 0; i--)
      if (bb_freq < SIZE_MAX / 8) bb_freq *= 5;
  bb->max_int_pressure = bb_int_pressure = bb->max_fp_pressure = bb_fp_pressure = 0;
  for (insn = bb_tail_insn; insn != NULL && get_insn_bb (gen_ctx, insn) == bb;
       insn = DLIST_PREV (MIR_insn_t, insn)) {
    if (MIR_call_code_p (insn->code)) {
      bitmap_ior (bb->live_kill, bb->live_kill, call_used_hard_regs[MIR_T_UNDEF]);
      bitmap_and_compl (bb->live_gen, bb->live_gen, call_used_hard_regs[MIR_T_UNDEF]);
    }
    /* Process output ops on 0-th iteration, then input ops. */
    for (niter = 0; niter <= 1; niter++) {
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (!out_p && niter != 0) {
          if (bitmap_set_bit_p (bb->live_gen, var) && optimize_level != 0)
            increase_pressure (int_var_type_p (gen_ctx, var), bb, &bb_int_pressure,
                               &bb_fp_pressure);
        } else if (niter == 0) {
          if (bitmap_clear_bit_p (bb->live_gen, var) && optimize_level != 0)
            (int_var_type_p (gen_ctx, var) ? bb_int_pressure-- : bb_fp_pressure--);
          bitmap_set_bit_p (bb->live_kill, var);
        }
        if (var_is_reg_p (var)) {
          if (breg_infos[var2breg (gen_ctx, var)].freq < LONG_MAX - bb_freq)
            breg_infos[var2breg (gen_ctx, var)].freq += bb_freq;
          else
            breg_infos[var2breg (gen_ctx, var)].freq = LONG_MAX;
        }
      }
    }
    target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                          &early_clobbered_hard_reg2);
    if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG) {
      if (optimize_level != 0) {
        int_p = int_var_type_p (gen_ctx, early_clobbered_hard_reg1);
        increase_pressure (int_p, bb, &bb_int_pressure, &bb_fp_pressure);
      }
      bitmap_clear_bit_p (bb->live_gen, early_clobbered_hard_reg1);
      bitmap_set_bit_p (bb->live_kill, early_clobbered_hard_reg1);
      if (optimize_level != 0) (int_p ? bb_int_pressure-- : bb_fp_pressure--);
    }
    if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG) {
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
    if (moves_p && move_p (insn)) {
      mv = get_free_move (gen_ctx);
      mv->bb_insn = insn->data;
      mv->freq = bb_freq;
      if (insn->ops[0].mode == MIR_OP_REG)
        DLIST_APPEND (dst_mv_t, breg_infos[reg2breg (gen_ctx, insn->ops[0].u.reg)].dst_moves, mv);
      if (insn->ops[1].mode == MIR_OP_REG)
        DLIST_APPEND (src_mv_t, breg_infos[reg2breg (gen_ctx, insn->ops[1].u.reg)].src_moves, mv);
      (*mvs_num)++;
      DEBUG (2, {
        fprintf (debug_file, "  move with freq %10lu:", (unsigned long) mv->freq);
        MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
      });
    }
  }
  return insn;
}

static void initiate_live_info (gen_ctx_t gen_ctx, int moves_p) {
  MIR_reg_t nregs, n;
  mv_t mv, next_mv;
  reg_info_t ri;
  uint32_t mvs_num = 0;

  for (mv = DLIST_HEAD (mv_t, curr_cfg->used_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free_move (gen_ctx, mv);
  }
  VARR_TRUNC (reg_info_t, curr_cfg->breg_info, 0);
  nregs = get_nregs (gen_ctx);
  for (n = 0; n < nregs; n++) {
    ri.freq = ri.thread_freq = 0;
    ri.live_length = 0;
    ri.thread_first = n;
    ri.thread_next = MIR_MAX_REG_NUM;
    DLIST_INIT (dst_mv_t, ri.dst_moves);
    DLIST_INIT (src_mv_t, ri.src_moves);
    VARR_PUSH (reg_info_t, curr_cfg->breg_info, ri);
  }
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    gen_assert (bb != NULL && bb->live_in != NULL && bb->live_out != NULL && bb->live_gen != NULL
                && bb->live_kill != NULL);
    bitmap_clear (bb->live_in);
    bitmap_clear (bb->live_out);
    bitmap_clear (bb->live_gen);
    bitmap_clear (bb->live_kill);
  }
  for (MIR_insn_t tail = DLIST_TAIL (MIR_insn_t, curr_func_item->u.func->insns); tail != NULL;)
    tail = initiate_bb_live_info (gen_ctx, tail, moves_p, &mvs_num);
  if (moves_p) curr_cfg->non_conflicting_moves = mvs_num;
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

static void calculate_func_cfg_live_info (gen_ctx_t gen_ctx, int moves_p) {
  initiate_live_info (gen_ctx, moves_p);
  solve_dataflow (gen_ctx, FALSE, live_con_func_0, live_con_func_n, live_trans_func);
  if (optimize_level != 0) update_bb_pressure (gen_ctx);
}

static void add_bb_insn_dead_vars (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t passed_mem_num;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, mem_p;
  bitmap_t live;
  insn_var_iterator_t insn_var_iter;

  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      clear_bb_insn_dead_vars (gen_ctx, bb_insn);
      insn = bb_insn->insn;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p) bitmap_clear_bit_p (live, var);
      }
      if (MIR_call_code_p (insn->code))
        bitmap_and_compl (live, live, call_used_hard_regs[MIR_T_UNDEF]);
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p) continue;
        if (bitmap_set_bit_p (live, var)) add_bb_insn_dead_var (gen_ctx, bb_insn, var);
      }
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg2);
      if (MIR_call_code_p (insn->code)) bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
}

typedef struct live_range *live_range_t; /* vars */

struct live_range {
  int start, finish;
  live_range_t next;
};

DEF_VARR (live_range_t);

struct lr_ctx {
  int curr_point;
  bitmap_t live_vars, born_vars, dead_vars, born_or_dead_vars;
  VARR (live_range_t) * var_live_ranges;
  VARR (int) * point_map;
};

#define curr_point gen_ctx->lr_ctx->curr_point
#define live_vars gen_ctx->lr_ctx->live_vars
#define born_vars gen_ctx->lr_ctx->born_vars
#define dead_vars gen_ctx->lr_ctx->dead_vars
#define born_or_dead_vars gen_ctx->lr_ctx->born_or_dead_vars
#define var_live_ranges gen_ctx->lr_ctx->var_live_ranges
#define point_map gen_ctx->lr_ctx->point_map

static live_range_t create_live_range (gen_ctx_t gen_ctx, int start, int finish,
                                       live_range_t next) {
  live_range_t lr = gen_malloc (gen_ctx, sizeof (struct live_range));

  gen_assert (finish < 0 || start <= finish);
  lr->start = start;
  lr->finish = finish;
  lr->next = next;
  return lr;
}

static void destroy_live_range (live_range_t lr) {
  live_range_t next_lr;

  for (; lr != NULL; lr = next_lr) {
    next_lr = lr->next;
    free (lr);
  }
}

static inline int make_var_dead (gen_ctx_t gen_ctx, MIR_reg_t var, int point) {
  live_range_t lr;

  if (bitmap_clear_bit_p (live_vars, var)) {
    lr = VARR_GET (live_range_t, var_live_ranges, var);
    lr->finish = point;
  } else { /* insn with unused result: result still needs a register */
    VARR_SET (live_range_t, var_live_ranges, var,
              create_live_range (gen_ctx, point, point,
                                 VARR_GET (live_range_t, var_live_ranges, var)));
  }
  return TRUE;
}

static inline int make_var_live (gen_ctx_t gen_ctx, MIR_reg_t var, int point) {
  live_range_t lr;

  if (!bitmap_set_bit_p (live_vars, var)) return FALSE;
  if ((lr = VARR_GET (live_range_t, var_live_ranges, var)) == NULL
      || (lr->finish != point && lr->finish + 1 != point))
    VARR_SET (live_range_t, var_live_ranges, var, create_live_range (gen_ctx, point, -1, lr));
  return TRUE;
}

#if !MIR_NO_GEN_DEBUG
static void print_live_ranges (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  live_range_t lr;

  fprintf (debug_file, "+++++++++++++Live ranges:\n");
  gen_assert (get_nvars (gen_ctx) == VARR_LENGTH (live_range_t, var_live_ranges));
  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    if ((lr = VARR_GET (live_range_t, var_live_ranges, i)) == NULL) continue;
    fprintf (debug_file, "%lu", (unsigned long) i);
    if (var_is_reg_p (i))
      fprintf (debug_file, " (%s:%s)",
               MIR_type_str (ctx, MIR_reg_type (ctx, var2reg (gen_ctx, i), curr_func_item->u.func)),
               MIR_reg_name (ctx, var2reg (gen_ctx, i), curr_func_item->u.func));
    fprintf (debug_file, ":");
    for (; lr != NULL; lr = lr->next) fprintf (debug_file, " [%d..%d]", lr->start, lr->finish);
    fprintf (debug_file, "\n");
  }
}
#endif

static void shrink_live_ranges (gen_ctx_t gen_ctx) {
  size_t p;
  long int n;
  live_range_t lr, prev_lr, next_lr;
  int born_p, dead_p, prev_dead_p;
  bitmap_iterator_t bi;

  bitmap_clear (born_vars);
  bitmap_clear (dead_vars);
  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next) {
      gen_assert (lr->start <= lr->finish);
      bitmap_set_bit_p (born_vars, lr->start);
      bitmap_set_bit_p (dead_vars, lr->finish);
    }
  }

  VARR_TRUNC (int, point_map, 0);
  for (size_t i = 0; i <= curr_point; i++) VARR_PUSH (int, point_map, 0);
  bitmap_ior (born_or_dead_vars, born_vars, dead_vars);
  n = -1;
  prev_dead_p = TRUE;
  FOREACH_BITMAP_BIT (bi, born_or_dead_vars, p) {
    born_p = bitmap_bit_p (born_vars, p);
    dead_p = bitmap_bit_p (dead_vars, p);
    assert (born_p || dead_p);
    if (!prev_dead_p || !born_p) /* 1st point is always a born */
      VARR_SET (int, point_map, p, n);
    else
      VARR_SET (int, point_map, p, ++n);
    prev_dead_p = dead_p;
  }

  n++;
  DEBUG (2, {
    fprintf (debug_file, "Compressing live ranges: from %d to %ld - %ld%%\n", curr_point, n,
             curr_point == 0 ? 100 : 100 * n / curr_point);
  });
  curr_point = n;

  for (size_t i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i), prev_lr = NULL; lr != NULL;
         lr = next_lr) {
      next_lr = lr->next;
      lr->start = VARR_GET (int, point_map, lr->start);
      lr->finish = VARR_GET (int, point_map, lr->finish);
      if (prev_lr == NULL || prev_lr->start > lr->finish + 1) {
        prev_lr = lr;
        continue;
      }
      prev_lr->start = lr->start;
      prev_lr->next = next_lr;
      free (lr);
    }
  }
  DEBUG (2, {
    fprintf (debug_file, "Ranges after the compression:\n");
    print_live_ranges (gen_ctx);
  });
}

static void build_live_ranges (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  MIR_reg_t var, nvars, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  size_t i, nel, passed_mem_num;
  int op_num, incr_p, out_p, mem_p;
  bitmap_iterator_t bi;
  insn_var_iterator_t insn_var_iter;

  curr_point = 0;
  nvars = get_nvars (gen_ctx);
  gen_assert (VARR_LENGTH (live_range_t, var_live_ranges) == 0);
  for (i = 0; i < nvars; i++) VARR_PUSH (live_range_t, var_live_ranges, NULL);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    DEBUG (2, {
      fprintf (debug_file, "  ------BB%u end: point=%d\n", (unsigned) bb->index, curr_point);
    });
    bitmap_clear (live_vars);
    if (bb->live_out != NULL) FOREACH_BITMAP_BIT (bi, bb->live_out, nel) {
        make_var_live (gen_ctx, nel, curr_point);
      }
    for (bb_insn_t bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_PREV (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      DEBUG (2, {
        fprintf (debug_file, "  p%-5d", curr_point);
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      });
      incr_p = FALSE;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (out_p) incr_p |= make_var_dead (gen_ctx, var, curr_point);
      }
      if (MIR_call_code_p (insn->code)) {
        FOREACH_BITMAP_BIT (bi, call_used_hard_regs[MIR_T_UNDEF], nel) {
          make_var_dead (gen_ctx, nel, curr_point);
        }
        FOREACH_BITMAP_BIT (bi, bb_insn->call_hard_reg_args, nel) {
          make_var_live (gen_ctx, nel, curr_point);
        }
        FOREACH_BITMAP_BIT (bi, live_vars, nel) {
          MIR_reg_t breg;

          if (!var_is_reg_p (nel)) continue;
          breg = reg2breg (gen_ctx, var2reg (gen_ctx, nel));
          bitmap_set_bit_p (curr_cfg->call_crossed_bregs, breg);
        }
      }
      if (incr_p) curr_point++;
      incr_p = FALSE;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (!out_p) incr_p |= make_var_live (gen_ctx, var, curr_point);
      }
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG) {
        incr_p |= make_var_live (gen_ctx, early_clobbered_hard_reg1, curr_point);
        incr_p |= make_var_dead (gen_ctx, early_clobbered_hard_reg1, curr_point);
      }
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG) {
        incr_p |= make_var_live (gen_ctx, early_clobbered_hard_reg2, curr_point);
        incr_p |= make_var_dead (gen_ctx, early_clobbered_hard_reg2, curr_point);
      }
      if (incr_p) curr_point++;
    }
    gen_assert (bitmap_equal_p (live_vars, bb->live_in));
    FOREACH_BITMAP_BIT (bi, bb->live_in, nel) { make_var_dead (gen_ctx, nel, curr_point); }
    if (!bitmap_empty_p (bb->live_in)) curr_point++;
  }
  DEBUG (2, { print_live_ranges (gen_ctx); });
  shrink_live_ranges (gen_ctx);
}

static void destroy_func_live_ranges (gen_ctx_t gen_ctx) {
  size_t i;

  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++)
    destroy_live_range (VARR_GET (live_range_t, var_live_ranges, i));
  VARR_TRUNC (live_range_t, var_live_ranges, 0);
}

#if !MIR_NO_GEN_DEBUG
static void output_bb_live_info (gen_ctx_t gen_ctx, bb_t bb) {
  output_bitmap (gen_ctx, "  live_in:", bb->live_in, TRUE);
  output_bitmap (gen_ctx, "  live_out:", bb->live_out, TRUE);
  output_bitmap (gen_ctx, "  live_gen:", bb->live_gen, TRUE);
  output_bitmap (gen_ctx, "  live_kill:", bb->live_kill, TRUE);
}
#endif

static void init_live_ranges (gen_ctx_t gen_ctx) {
  gen_ctx->lr_ctx = gen_malloc (gen_ctx, sizeof (struct lr_ctx));
  VARR_CREATE (live_range_t, var_live_ranges, 0);
  VARR_CREATE (int, point_map, 1024);
  live_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  born_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  dead_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  born_or_dead_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
}

static void finish_live_ranges (gen_ctx_t gen_ctx) {
  VARR_DESTROY (live_range_t, var_live_ranges);
  VARR_DESTROY (int, point_map);
  bitmap_destroy (live_vars);
  bitmap_destroy (born_vars);
  bitmap_destroy (dead_vars);
  bitmap_destroy (born_or_dead_vars);
  free (gen_ctx->lr_ctx);
  gen_ctx->lr_ctx = NULL;
}

/* New Page */

/* Register allocation */

DEF_VARR (MIR_reg_t);

typedef struct breg_info {
  MIR_reg_t breg;
  reg_info_t *breg_infos;
} breg_info_t;

DEF_VARR (breg_info_t);
DEF_VARR (bitmap_t);

struct ra_ctx {
  VARR (MIR_reg_t) * breg_renumber;
  VARR (breg_info_t) * sorted_bregs;
  VARR (bitmap_t) * used_locs; /* indexed by bb or point */
  VARR (bitmap_t) * var_bbs;
  bitmap_t conflict_locs;
  reg_info_t *curr_breg_infos;
  VARR (size_t) * loc_profits;
  VARR (size_t) * loc_profit_ages;
  size_t curr_age;
};

#define breg_renumber gen_ctx->ra_ctx->breg_renumber
#define sorted_bregs gen_ctx->ra_ctx->sorted_bregs
#define used_locs gen_ctx->ra_ctx->used_locs
#define var_bbs gen_ctx->ra_ctx->var_bbs
#define conflict_locs gen_ctx->ra_ctx->conflict_locs
#define curr_breg_infos gen_ctx->ra_ctx->curr_breg_infos
#define loc_profits gen_ctx->ra_ctx->loc_profits
#define loc_profit_ages gen_ctx->ra_ctx->loc_profit_ages
#define curr_age gen_ctx->ra_ctx->curr_age

static void fast_assign (gen_ctx_t gen_ctx) {
  MIR_reg_t loc, curr_loc, best_loc, i, reg, breg, var, nregs = get_nregs (gen_ctx);
  MIR_type_t type;
  int slots_num;
  int k;
  bitmap_t bm;
  bitmap_t *used_locs_addr;
  size_t nel;
  bitmap_iterator_t bi;

  func_stack_slots_num = 0;
  if (nregs == 0) return;
  for (size_t n = 0; n < nregs + MAX_HARD_REG + 1 && n < VARR_LENGTH (bitmap_t, var_bbs); n++)
    bitmap_clear (VARR_GET (bitmap_t, var_bbs, n));
  while (VARR_LENGTH (bitmap_t, var_bbs) < nregs + MAX_HARD_REG + 1) {
    bm = bitmap_create2 (curr_bb_index);
    VARR_PUSH (bitmap_t, var_bbs, bm);
  }
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_ior (temp_bitmap, bb->live_in, bb->live_out);
    bitmap_ior (temp_bitmap, temp_bitmap, bb->gen);
    bitmap_ior (temp_bitmap, temp_bitmap, bb->kill);
    FOREACH_BITMAP_BIT (bi, temp_bitmap, nel) {
      bitmap_set_bit_p (VARR_GET (bitmap_t, var_bbs, nel), bb->index);
    }
  }
  VARR_TRUNC (MIR_reg_t, breg_renumber, 0);
  for (i = 0; i < nregs; i++) VARR_PUSH (MIR_reg_t, breg_renumber, MIR_NON_HARD_REG);
  for (size_t n = 0; n < curr_bb_index && n < VARR_LENGTH (bitmap_t, used_locs); n++)
    bitmap_clear (VARR_GET (bitmap_t, used_locs, n));
  while (VARR_LENGTH (bitmap_t, used_locs) < curr_bb_index) {
    bm = bitmap_create2 (2 * MAX_HARD_REG + 1);
    VARR_PUSH (bitmap_t, used_locs, bm);
  }
  used_locs_addr = VARR_ADDR (bitmap_t, used_locs);
  for (i = 0; i <= MAX_HARD_REG; i++)
    FOREACH_BITMAP_BIT (bi, VARR_GET (bitmap_t, var_bbs, i), nel) {
      bitmap_set_bit_p (used_locs_addr[nel], i);
    }
  bitmap_clear (func_used_hard_regs);
  for (i = 0; i < nregs; i++) { /* hard reg and stack slot assignment */
    breg = i;
    reg = breg2reg (gen_ctx, breg);
    var = reg2var (gen_ctx, reg);
    bitmap_clear (conflict_locs);
    FOREACH_BITMAP_BIT (bi, VARR_GET (bitmap_t, var_bbs, var), nel) {
      bitmap_ior (conflict_locs, conflict_locs, used_locs_addr[nel]);
    }
    type = MIR_reg_type (gen_ctx->ctx, reg, curr_func_item->u.func);
    /* Call used hard regs are already taken into account above for call crossed regs. */
    best_loc = MIR_NON_HARD_REG;
    for (loc = 0; loc <= MAX_HARD_REG; loc++) {
      if (bitmap_bit_p (conflict_locs, loc)) continue;
      if (!target_hard_reg_type_ok_p (loc, type) || target_fixed_hard_reg_p (loc)) continue;
      if ((slots_num = target_locs_num (loc, type)) > 1) {
        if (target_nth_loc (loc, type, slots_num - 1) > MAX_HARD_REG) break;
        for (k = slots_num - 1; k > 0; k--) {
          curr_loc = target_nth_loc (loc, type, k);
          if (target_fixed_hard_reg_p (curr_loc) || bitmap_bit_p (conflict_locs, curr_loc)) break;
        }
        if (k > 0) continue;
      }
      best_loc = loc;
      break;
    }
    if (best_loc != MIR_NON_HARD_REG) {
      setup_used_hard_regs (gen_ctx, type, best_loc);
    } else {
      for (loc = MAX_HARD_REG + 1; loc <= func_stack_slots_num + MAX_HARD_REG; loc++) {
        slots_num = target_locs_num (loc, type);
        if (target_nth_loc (loc, type, slots_num - 1) > func_stack_slots_num + MAX_HARD_REG) break;
        for (k = 0; k < slots_num; k++) {
          curr_loc = target_nth_loc (loc, type, k);
          if (bitmap_bit_p (conflict_locs, curr_loc)) break;
        }
        if (k < slots_num) continue;
        if ((loc - MAX_HARD_REG - 1) % slots_num != 0)
          continue; /* we align stack slots according to the type size */
        best_loc = loc;
        break;
      }
      if (best_loc == MIR_NON_HARD_REG) { /* Add stack slot ??? */
        slots_num = 1;
        for (k = 0; k < slots_num; k++) {
          if (k == 0) {
            best_loc = func_stack_slots_num + MAX_HARD_REG + 1;
            slots_num = target_locs_num (best_loc, type);
          }
          func_stack_slots_num++;
          if (k == 0 && (best_loc - MAX_HARD_REG - 1) % slots_num != 0) k--; /* align */
        }
      }
    }
    DEBUG (2, {
      fprintf (debug_file, " Assigning to %s:var=%3u, breg=%3u -- %lu\n",
               MIR_reg_name (gen_ctx->ctx, reg, curr_func_item->u.func), reg2var (gen_ctx, reg),
               breg, (unsigned long) best_loc);
    });
    VARR_SET (MIR_reg_t, breg_renumber, breg, best_loc);
    slots_num = target_locs_num (best_loc, type);
    FOREACH_BITMAP_BIT (bi, VARR_GET (bitmap_t, var_bbs, var), nel) {
      for (k = 0; k < slots_num; k++)
        bitmap_set_bit_p (used_locs_addr[nel], target_nth_loc (best_loc, type, k));
    }
  }
}

#undef live_in
#undef live_out
#undef live_kill
#undef live_gen

static void process_move_to_form_thread (gen_ctx_t gen_ctx, mv_t mv) {
  MIR_op_t op1 = mv->bb_insn->insn->ops[0], op2 = mv->bb_insn->insn->ops[1];
  MIR_reg_t breg1, breg2, breg1_first, breg2_first, last;

  if (op1.mode != MIR_OP_REG || op2.mode != MIR_OP_REG) return;
  breg1 = reg2breg (gen_ctx, op1.u.reg);
  breg2 = reg2breg (gen_ctx, op2.u.reg);
  breg1_first = curr_breg_infos[breg1].thread_first;
  breg2_first = curr_breg_infos[breg2].thread_first;
  if (breg1_first != breg2_first) {
    for (last = breg2_first; curr_breg_infos[last].thread_next != MIR_MAX_REG_NUM;
         last = curr_breg_infos[last].thread_next)
      curr_breg_infos[last].thread_first = breg1_first;
    curr_breg_infos[last].thread_first = breg1_first;
    curr_breg_infos[last].thread_next = curr_breg_infos[breg1_first].thread_next;
    curr_breg_infos[breg1_first].thread_next = breg2_first;
    if (curr_breg_infos[breg1_first].thread_freq
        < LONG_MAX - curr_breg_infos[breg2_first].thread_freq)
      curr_breg_infos[breg1_first].thread_freq += curr_breg_infos[breg2_first].thread_freq;
    else
      curr_breg_infos[breg1_first].thread_freq = LONG_MAX;
  }
  if (curr_breg_infos[breg1_first].thread_freq < 2 * mv->freq)
    curr_breg_infos[breg1_first].thread_freq = 0;
  else
    curr_breg_infos[breg1_first].thread_freq -= 2 * mv->freq;
  gen_assert (curr_breg_infos[breg1_first].thread_freq >= 0);
}

static int breg_info_compare_func (const void *a1, const void *a2) {
  const breg_info_t *breg_info1 = (const breg_info_t *) a1, *breg_info2 = (const breg_info_t *) a2;
  MIR_reg_t breg1 = breg_info1->breg, breg2 = breg_info2->breg;
  reg_info_t *breg_infos = breg_info1->breg_infos;
  MIR_reg_t t1 = breg_infos[breg1].thread_first, t2 = breg_infos[breg2].thread_first;
  long diff;

  gen_assert (breg_infos == breg_info2->breg_infos);
  if ((diff = breg_infos[t2].thread_freq - breg_infos[t1].thread_freq) != 0) return diff;
  if (t1 < t2) return -1;
  if (t2 < t1) return 1;
  if (breg_infos[breg2].live_length < breg_infos[breg1].live_length) return -1;
  if (breg_infos[breg1].live_length < breg_infos[breg2].live_length) return 1;
  return breg1 < breg2 ? -1 : 1; /* make sort stable */
}

static void setup_loc_profit_from_op (gen_ctx_t gen_ctx, MIR_op_t op, size_t freq) {
  MIR_reg_t loc;
  size_t *curr_loc_profits = VARR_ADDR (size_t, loc_profits);
  size_t *curr_loc_profit_ages = VARR_ADDR (size_t, loc_profit_ages);

  if (op.mode == MIR_OP_HARD_REG)
    loc = op.u.hard_reg;
  else if ((loc = VARR_GET (MIR_reg_t, breg_renumber, reg2breg (gen_ctx, op.u.reg)))
           == MIR_NON_HARD_REG)
    return;
  if (curr_loc_profit_ages[loc] == curr_age) {
    if (curr_loc_profits[loc] < SIZE_MAX - freq)
      curr_loc_profits[loc] += freq;
    else
      curr_loc_profits[loc] = SIZE_MAX;
  } else {
    curr_loc_profit_ages[loc] = curr_age;
    curr_loc_profits[loc] = freq;
  }
}

static void setup_loc_profits (gen_ctx_t gen_ctx, MIR_reg_t breg) {
  mv_t mv;
  reg_info_t *info = &curr_breg_infos[breg];

  for (mv = DLIST_HEAD (dst_mv_t, info->dst_moves); mv != NULL; mv = DLIST_NEXT (dst_mv_t, mv))
    setup_loc_profit_from_op (gen_ctx, mv->bb_insn->insn->ops[0], mv->freq);
  for (mv = DLIST_HEAD (src_mv_t, info->src_moves); mv != NULL; mv = DLIST_NEXT (src_mv_t, mv))
    setup_loc_profit_from_op (gen_ctx, mv->bb_insn->insn->ops[1], mv->freq);
}

static void quality_assign (gen_ctx_t gen_ctx) {
  MIR_reg_t loc, curr_loc, best_loc, i, reg, breg, var, nregs = get_nregs (gen_ctx);
  MIR_type_t type;
  int n, slots_num;
  int j, k;
  live_range_t lr;
  bitmap_t bm;
  size_t length, profit, best_profit;
  bitmap_t *used_locs_addr;
  breg_info_t breg_info;

  func_stack_slots_num = 0;
  if (nregs == 0) return;
  curr_breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  VARR_TRUNC (MIR_reg_t, breg_renumber, 0);
  for (i = 0; i < nregs; i++) {
    VARR_PUSH (MIR_reg_t, breg_renumber, MIR_NON_HARD_REG);
    curr_breg_infos[i].thread_freq = curr_breg_infos[i].freq;
  }
  for (mv_t mv = DLIST_HEAD (mv_t, curr_cfg->used_moves); mv != NULL; mv = DLIST_NEXT (mv_t, mv))
    process_move_to_form_thread (gen_ctx, mv);
  /* min_reg, max_reg for func */
  VARR_TRUNC (breg_info_t, sorted_bregs, 0);
  breg_info.breg_infos = curr_breg_infos;
  for (i = 0; i < nregs; i++) {
    breg_info.breg = i;
    VARR_PUSH (breg_info_t, sorted_bregs, breg_info);
    var = reg2var (gen_ctx, breg2reg (gen_ctx, i));
    for (length = 0, lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
      length += lr->finish - lr->start + 1;
    curr_breg_infos[i].live_length = length;
  }
  VARR_TRUNC (size_t, loc_profits, 0);
  VARR_TRUNC (size_t, loc_profit_ages, 0);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (size_t, loc_profits, 0);
    VARR_PUSH (size_t, loc_profit_ages, 0);
  }
  for (size_t n = 0; n <= curr_point && n < VARR_LENGTH (bitmap_t, used_locs); n++)
    bitmap_clear (VARR_GET (bitmap_t, used_locs, n));
  while (VARR_LENGTH (bitmap_t, used_locs) <= curr_point) {
    bm = bitmap_create2 (MAX_HARD_REG + 1);
    VARR_PUSH (bitmap_t, used_locs, bm);
  }
  qsort (VARR_ADDR (breg_info_t, sorted_bregs), nregs, sizeof (breg_info_t),
         breg_info_compare_func);
  curr_age = 0;
  used_locs_addr = VARR_ADDR (bitmap_t, used_locs);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++) bitmap_set_bit_p (used_locs_addr[j], i);
  }
  bitmap_clear (func_used_hard_regs);
  for (i = 0; i < nregs; i++) { /* hard reg and stack slot assignment */
    breg = VARR_GET (breg_info_t, sorted_bregs, i).breg;
    if (VARR_GET (MIR_reg_t, breg_renumber, breg) != MIR_NON_HARD_REG) continue;
    reg = breg2reg (gen_ctx, breg);
    var = reg2var (gen_ctx, reg);
    bitmap_clear (conflict_locs);
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
        bitmap_ior (conflict_locs, conflict_locs, used_locs_addr[j]);
    curr_age++;
    setup_loc_profits (gen_ctx, breg);
    best_loc = MIR_NON_HARD_REG;
    best_profit = 0;
    type = MIR_reg_type (gen_ctx->ctx, reg, curr_func_item->u.func);
    if (bitmap_bit_p (curr_cfg->call_crossed_bregs, breg))
      bitmap_ior (conflict_locs, conflict_locs, call_used_hard_regs[type]);
    for (n = 0; n <= MAX_HARD_REG; n++) {
#ifdef TARGET_HARD_REG_ALLOC_ORDER
      loc = TARGET_HARD_REG_ALLOC_ORDER (n);
#else
      loc = n;
#endif
      if (bitmap_bit_p (conflict_locs, loc)) continue;
      if (!target_hard_reg_type_ok_p (loc, type) || target_fixed_hard_reg_p (loc)) continue;
      if ((slots_num = target_locs_num (loc, type)) > 1) {
        if (target_nth_loc (loc, type, slots_num - 1) > MAX_HARD_REG) break;
        for (k = slots_num - 1; k > 0; k--) {
          curr_loc = target_nth_loc (loc, type, k);
          if (target_fixed_hard_reg_p (curr_loc) || bitmap_bit_p (conflict_locs, curr_loc)) break;
        }
        if (k > 0) continue;
      }
      profit = (VARR_GET (size_t, loc_profit_ages, loc) != curr_age
                  ? 0
                  : VARR_GET (size_t, loc_profits, loc));
      if (best_loc == MIR_NON_HARD_REG || best_profit < profit) {
        best_loc = loc;
        best_profit = profit;
      }
    }
    if (best_loc != MIR_NON_HARD_REG) {
      setup_used_hard_regs (gen_ctx, type, best_loc);
    } else {
      for (loc = MAX_HARD_REG + 1; loc <= func_stack_slots_num + MAX_HARD_REG; loc++) {
        slots_num = target_locs_num (loc, type);
        if (target_nth_loc (loc, type, slots_num - 1) > func_stack_slots_num + MAX_HARD_REG) break;
        for (k = 0; k < slots_num; k++) {
          curr_loc = target_nth_loc (loc, type, k);
          if (bitmap_bit_p (conflict_locs, curr_loc)) break;
        }
        if (k < slots_num) continue;
        if ((loc - MAX_HARD_REG - 1) % slots_num != 0)
          continue; /* we align stack slots according to the type size */
        profit = (VARR_GET (size_t, loc_profit_ages, loc) != curr_age
                    ? 0
                    : VARR_GET (size_t, loc_profits, loc));
        if (best_loc == MIR_NON_HARD_REG || best_profit < profit) {
          best_loc = loc;
          best_profit = profit;
        }
      }
      if (best_loc == MIR_NON_HARD_REG) { /* Add stack slot ??? */
        slots_num = 1;
        for (k = 0; k < slots_num; k++) {
          if (k == 0) {
            best_loc = VARR_LENGTH (size_t, loc_profits);
            slots_num = target_locs_num (best_loc, type);
          }
          VARR_PUSH (size_t, loc_profits, 0);
          VARR_PUSH (size_t, loc_profit_ages, 0);
          if (k == 0 && (best_loc - MAX_HARD_REG - 1) % slots_num != 0) k--; /* align */
        }
        func_stack_slots_num = VARR_LENGTH (size_t, loc_profits) - MAX_HARD_REG - 1;
      }
    }
    DEBUG (2, {
      MIR_reg_t thread_breg = curr_breg_infos[breg].thread_first;

      fprintf (debug_file,
               " Assigning to %s:var=%3u, breg=%3u (freq %-3ld), thread breg=%3u (freq %-3ld) "
               "-- "
               "%lu\n",
               MIR_reg_name (gen_ctx->ctx, reg, curr_func_item->u.func), reg2var (gen_ctx, reg),
               breg, curr_breg_infos[breg].freq, thread_breg,
               curr_breg_infos[thread_breg].thread_freq, (unsigned long) best_loc);
    });
    VARR_SET (MIR_reg_t, breg_renumber, breg, best_loc);
    slots_num = target_locs_num (best_loc, type);
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
        for (k = 0; k < slots_num; k++)
          bitmap_set_bit_p (used_locs_addr[j], target_nth_loc (best_loc, type, k));
  }
}

static void assign (gen_ctx_t gen_ctx) {
  MIR_reg_t i, reg, nregs = get_nregs (gen_ctx);

  if (optimize_level == 0)
    fast_assign (gen_ctx);
  else
    quality_assign (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++Disposition after assignment:");
    for (i = 0; i < nregs; i++) {
      if (i % 8 == 0) fprintf (debug_file, "\n");
      reg = breg2reg (gen_ctx, i);
      fprintf (debug_file, " %3u=>%-2u", reg2var (gen_ctx, reg),
               VARR_GET (MIR_reg_t, breg_renumber, i));
    }
    fprintf (debug_file, "\n");
  });
}

static MIR_reg_t change_reg (gen_ctx_t gen_ctx, MIR_op_t *mem_op, MIR_reg_t reg,
                             MIR_op_mode_t data_mode, int first_p, MIR_insn_t insn, int out_p) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_reg_t loc = VARR_GET (MIR_reg_t, breg_renumber, reg2breg (gen_ctx, reg));
  MIR_reg_t hard_reg;
  MIR_disp_t offset;
  MIR_insn_code_t code;
  MIR_insn_t new_insn, new_insns[3];
  MIR_type_t type;
  bb_insn_t bb_insn, new_bb_insn;
  MIR_op_t hard_reg_op;
  size_t n;

  gen_assert (loc != MIR_NON_HARD_REG);
  if (loc <= MAX_HARD_REG) return loc;
  gen_assert (data_mode == MIR_OP_INT || data_mode == MIR_OP_FLOAT || data_mode == MIR_OP_DOUBLE
              || data_mode == MIR_OP_LDOUBLE);
  if (data_mode == MIR_OP_INT) {
    type = MIR_T_I64;
    code = MIR_MOV;
  } else if (data_mode == MIR_OP_FLOAT) {
    type = MIR_T_F;
    code = MIR_FMOV;
  } else if (data_mode == MIR_OP_DOUBLE) {
    type = MIR_T_D;
    code = MIR_DMOV;
  } else {
    type = MIR_T_LD;
    code = MIR_LDMOV;
  }
  hard_reg = get_temp_hard_reg (type, first_p);
  setup_used_hard_regs (gen_ctx, type, hard_reg);
  offset = target_get_stack_slot_offset (gen_ctx, type, loc - MAX_HARD_REG - 1);
  n = 0;
  if (target_valid_mem_offset_p (gen_ctx, type, offset)) {
    *mem_op = _MIR_new_hard_reg_mem_op (ctx, type, offset, FP_HARD_REG, MIR_NON_HARD_REG, 0);
  } else {
    MIR_reg_t temp_hard_reg
      = (first_p && !out_p) || (out_p && !first_p) ? TEMP_INT_HARD_REG1 : TEMP_INT_HARD_REG2;
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, _MIR_new_hard_reg_op (ctx, temp_hard_reg),
                                 MIR_new_int_op (ctx, offset));
    new_insns[1] = MIR_new_insn (ctx, MIR_ADD, _MIR_new_hard_reg_op (ctx, temp_hard_reg),
                                 _MIR_new_hard_reg_op (ctx, temp_hard_reg),
                                 _MIR_new_hard_reg_op (ctx, FP_HARD_REG));
    n = 2;
    *mem_op = _MIR_new_hard_reg_mem_op (ctx, type, 0, temp_hard_reg, MIR_NON_HARD_REG, 0);
  }
  if (hard_reg == MIR_NON_HARD_REG) return hard_reg;
  hard_reg_op = _MIR_new_hard_reg_op (ctx, hard_reg);
  if (!out_p) {
    new_insns[n++] = MIR_new_insn (ctx, code, hard_reg_op, *mem_op);
  } else {
    new_insns[n++] = MIR_new_insn (ctx, code, *mem_op, hard_reg_op);
    for (size_t i = 0, j = n - 1; i < j; i++, j--) { /* reverse for subsequent correct insertion: */
      new_insn = new_insns[i];
      new_insns[i] = new_insns[j];
      new_insns[j] = new_insn;
    }
  }
  for (size_t i = 0; i < n; i++) {
    new_insn = new_insns[i];
    if (out_p)
      MIR_insert_insn_after (ctx, curr_func_item, insn, new_insn);
    else
      MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
    if (optimize_level == 0) {
      new_insn->data = get_insn_data_bb (insn);
    } else {
      bb_insn = insn->data;
      new_bb_insn = create_bb_insn (gen_ctx, new_insn, bb_insn->bb);
      if (out_p)
        DLIST_INSERT_AFTER (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
      else
        DLIST_INSERT_BEFORE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
    }
  }
  return hard_reg;
}

static void rewrite (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t insn, next_insn;
  size_t nops, i;
  MIR_op_t *op, mem_op;
#if !MIR_NO_GEN_DEBUG
  MIR_op_t in_op = MIR_new_int_op (ctx, 0),
           out_op = MIR_new_int_op (ctx, 0); /* To remove unitilized warning */
#endif
  MIR_mem_t mem;
  MIR_op_mode_t data_mode;
  MIR_reg_t hard_reg;
  int out_p, first_in_p;
  size_t insns_num = 0, movs_num = 0, deleted_movs_num = 0;

  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns); insn != NULL;
       insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    nops = MIR_insn_nops (ctx, insn);
    first_in_p = TRUE;
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
      case MIR_OP_HARD_REG: bitmap_set_bit_p (func_used_hard_regs, op->u.hard_reg); break;
      case MIR_OP_HARD_REG_MEM:
        if (op->u.hard_reg_mem.base != MIR_NON_HARD_REG)
          bitmap_set_bit_p (func_used_hard_regs, op->u.hard_reg_mem.base);
        if (op->u.hard_reg_mem.index != MIR_NON_HARD_REG)
          bitmap_set_bit_p (func_used_hard_regs, op->u.hard_reg_mem.index);
        break;
      case MIR_OP_REG:
        hard_reg
          = change_reg (gen_ctx, &mem_op, op->u.reg, data_mode, out_p || first_in_p, insn, out_p);
        if (!out_p) first_in_p = FALSE;
        if (hard_reg == MIR_NON_HARD_REG) {
          *op = mem_op;
        } else {
          op->mode = MIR_OP_HARD_REG;
          op->u.hard_reg = hard_reg;
        }
        break;
      case MIR_OP_MEM:
        mem = op->u.mem;
        /* Always second for mov MEM[R2], R1 or mov R1, MEM[R2]. */
        if (op->u.mem.base == 0) {
          mem.base = MIR_NON_HARD_REG;
        } else {
          mem.base = change_reg (gen_ctx, &mem_op, op->u.mem.base, MIR_OP_INT, FALSE, insn, FALSE);
          gen_assert (mem.base != MIR_NON_HARD_REG); /* we can always use GP regs */
        }
        gen_assert (op->u.mem.index == 0);
        mem.index = MIR_NON_HARD_REG;
        op->mode = MIR_OP_HARD_REG_MEM;
        op->u.hard_reg_mem = mem;
        break;
      default: /* do nothing */ break;
      }
    }
    insns_num++;
    if (move_code_p (insn->code)) {
      movs_num++;
      if (MIR_op_eq_p (ctx, insn->ops[0], insn->ops[1])) {
        DEBUG (2, {
          fprintf (debug_file, "Deleting noop move ");
          MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, FALSE);
          fprintf (debug_file, " which was ");
          insn->ops[0] = out_op;
          insn->ops[1] = in_op;
          MIR_output_insn (ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        });
        gen_delete_insn (gen_ctx, insn);
        deleted_movs_num++;
      }
    }
  }
  DEBUG (1, {
    fprintf (debug_file,
             "%5lu deleted RA noop moves out of %lu non-conflicting moves "
             "(%.1f%%), "
             "out of %lu all moves (%.1f%%), out of %lu all insns (%.1f%%)\n",
             (unsigned long) deleted_movs_num, (unsigned long) curr_cfg->non_conflicting_moves,
             curr_cfg->non_conflicting_moves == 0
               ? 100.0
               : deleted_movs_num * 100.0 / curr_cfg->non_conflicting_moves,
             (unsigned long) movs_num, deleted_movs_num * 100.0 / movs_num,
             (unsigned long) insns_num, deleted_movs_num * 100.0 / insns_num);
  });
}

static void init_ra (gen_ctx_t gen_ctx) {
  gen_ctx->ra_ctx = gen_malloc (gen_ctx, sizeof (struct ra_ctx));
  VARR_CREATE (MIR_reg_t, breg_renumber, 0);
  VARR_CREATE (breg_info_t, sorted_bregs, 0);
  VARR_CREATE (bitmap_t, used_locs, 0);
  VARR_CREATE (bitmap_t, var_bbs, 0);
  VARR_CREATE (size_t, loc_profits, 0);
  VARR_CREATE (size_t, loc_profit_ages, 0);
  conflict_locs = bitmap_create2 (3 * MAX_HARD_REG / 2);
}

static void finish_ra (gen_ctx_t gen_ctx) {
  VARR_DESTROY (MIR_reg_t, breg_renumber);
  VARR_DESTROY (breg_info_t, sorted_bregs);
  while (VARR_LENGTH (bitmap_t, used_locs) != 0) bitmap_destroy (VARR_POP (bitmap_t, used_locs));
  VARR_DESTROY (bitmap_t, used_locs);
  while (VARR_LENGTH (bitmap_t, var_bbs) != 0) bitmap_destroy (VARR_POP (bitmap_t, var_bbs));
  VARR_DESTROY (bitmap_t, var_bbs);
  VARR_DESTROY (size_t, loc_profits);
  VARR_DESTROY (size_t, loc_profit_ages);
  bitmap_destroy (conflict_locs);
  free (gen_ctx->ra_ctx);
  gen_ctx->ra_ctx = NULL;
}

/* New Page */

/* Code selection */

struct hreg_ref { /* We keep track of the last hard reg ref in this struct. */
  MIR_insn_t insn;
  size_t insn_num;
  size_t nop;
  char def_p, del_p; /* def/use and deleted */
};

typedef struct hreg_ref hreg_ref_t;

DEF_VARR (hreg_ref_t);

struct selection_ctx {
  VARR (size_t) * hreg_ref_ages;
  VARR (hreg_ref_t) * hreg_refs;
  hreg_ref_t *hreg_refs_addr;
  size_t *hreg_ref_ages_addr;
  size_t curr_bb_hreg_ref_age;
  size_t last_mem_ref_insn_num;
  VARR (MIR_reg_t) * insn_hard_regs; /* registers considered for substitution */
  VARR (size_t) * changed_op_numbers;
  VARR (MIR_op_t) * last_right_ops;
  bitmap_t hard_regs_bitmap;
};

#define hreg_ref_ages gen_ctx->selection_ctx->hreg_ref_ages
#define hreg_refs gen_ctx->selection_ctx->hreg_refs
#define hreg_refs_addr gen_ctx->selection_ctx->hreg_refs_addr
#define hreg_ref_ages_addr gen_ctx->selection_ctx->hreg_ref_ages_addr
#define curr_bb_hreg_ref_age gen_ctx->selection_ctx->curr_bb_hreg_ref_age
#define last_mem_ref_insn_num gen_ctx->selection_ctx->last_mem_ref_insn_num
#define insn_hard_regs gen_ctx->selection_ctx->insn_hard_regs
#define changed_op_numbers gen_ctx->selection_ctx->changed_op_numbers
#define last_right_ops gen_ctx->selection_ctx->last_right_ops
#define hard_regs_bitmap gen_ctx->selection_ctx->hard_regs_bitmap

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

static int obsolete_hard_reg_p (gen_ctx_t gen_ctx, MIR_reg_t hard_reg, size_t def_insn_num) {
  return (hreg_ref_ages_addr[hard_reg] == curr_bb_hreg_ref_age
          && hreg_refs_addr[hard_reg].insn_num > def_insn_num);
}

static int obsolete_hard_reg_op_p (gen_ctx_t gen_ctx, MIR_op_t op, size_t def_insn_num) {
  return op.mode == MIR_OP_HARD_REG && obsolete_hard_reg_p (gen_ctx, op.u.hard_reg, def_insn_num);
}

static int obsolete_op_p (gen_ctx_t gen_ctx, MIR_op_t op, size_t def_insn_num) {
  if (obsolete_hard_reg_op_p (gen_ctx, op, def_insn_num)) return TRUE;
  if (op.mode != MIR_OP_HARD_REG_MEM) return FALSE;
  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG
      && obsolete_hard_reg_p (gen_ctx, op.u.hard_reg_mem.base, def_insn_num))
    return TRUE;
  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG
      && obsolete_hard_reg_p (gen_ctx, op.u.hard_reg_mem.index, def_insn_num))
    return TRUE;
  return last_mem_ref_insn_num > def_insn_num;
}

static int safe_hreg_substitution_p (gen_ctx_t gen_ctx, MIR_reg_t hr, bb_insn_t bb_insn) {
  return (hr != MIR_NON_HARD_REG
          && hreg_ref_ages_addr[hr] == curr_bb_hreg_ref_age
          /* It is not safe to substitute if there is another use after def insn before
             the current insn as we delete def insn after the substitution. */
          && hreg_refs_addr[hr].def_p && find_bb_insn_dead_var (bb_insn, hr) != NULL);
}

static void combine_process_hard_reg (gen_ctx_t gen_ctx, MIR_reg_t hr, bb_insn_t bb_insn) {
  if (!safe_hreg_substitution_p (gen_ctx, hr, bb_insn) || !bitmap_set_bit_p (hard_regs_bitmap, hr))
    return;
  VARR_PUSH (MIR_reg_t, insn_hard_regs, hr);
}

static void combine_process_op (gen_ctx_t gen_ctx, const MIR_op_t *op_ref, bb_insn_t bb_insn) {
  if (op_ref->mode == MIR_OP_HARD_REG) {
    combine_process_hard_reg (gen_ctx, op_ref->u.hard_reg, bb_insn);
  } else if (op_ref->mode == MIR_OP_HARD_REG_MEM) {
    if (op_ref->u.hard_reg_mem.base != MIR_NON_HARD_REG)
      combine_process_hard_reg (gen_ctx, op_ref->u.hard_reg_mem.base, bb_insn);
    if (op_ref->u.hard_reg_mem.index != MIR_NON_HARD_REG)
      combine_process_hard_reg (gen_ctx, op_ref->u.hard_reg_mem.index, bb_insn);
  }
}

static int combine_delete_insn (gen_ctx_t gen_ctx, MIR_insn_t def_insn, bb_insn_t bb_insn) {
  MIR_reg_t hr;

  gen_assert (def_insn->ops[0].mode == MIR_OP_HARD_REG);
  hr = def_insn->ops[0].u.hard_reg;
  if (hreg_ref_ages_addr[hr] != curr_bb_hreg_ref_age || hreg_refs_addr[hr].del_p) return FALSE;
  DEBUG (2, {
    fprintf (debug_file, "      deleting now dead insn ");
    print_bb_insn (gen_ctx, def_insn->data, TRUE);
  });
  remove_bb_insn_dead_var (gen_ctx, bb_insn, hr);
  move_bb_insn_dead_vars (bb_insn, def_insn->data);
  /* We should delete the def insn here because of possible
     substitution of the def insn 'r0 = ... r0 ...'.  We still
     need valid entry for def here to find obsolete definiton,
     e.g. "hr1 = hr0; hr0 = ...; hr0 = ... (deleted); ...= ...hr1..." */
  gen_delete_insn (gen_ctx, def_insn);
  hreg_refs_addr[hr].del_p = TRUE; /* to exclude repetitive deletion */
  return TRUE;
}

static int64_t power2 (int64_t p) {
  int64_t n = 1;

  if (p < 0) return 0;
  while (p-- > 0) n *= 2;
  return n;
}

static int64_t int_log2 (int64_t i) {
  int64_t n;

  if (i <= 0) return -1;
  for (n = 0; (i & 1) == 0; n++, i >>= 1)
    ;
  return i == 1 ? n : -1;
}

static MIR_insn_t get_uptodate_def_insn (gen_ctx_t gen_ctx, int hr) {
  MIR_insn_t def_insn;

  if (!hreg_refs_addr[hr].def_p) return NULL;
  gen_assert (!hreg_refs_addr[hr].del_p);
  def_insn = hreg_refs_addr[hr].insn;
  /* Checking hr0 = ... hr1 ...; ...; hr1 = ...; ...; insn */
  if ((def_insn->nops > 1 && obsolete_op_p (gen_ctx, def_insn->ops[1], hreg_refs_addr[hr].insn_num))
      || (def_insn->nops > 2
          && obsolete_op_p (gen_ctx, def_insn->ops[2], hreg_refs_addr[hr].insn_num)))
    return NULL;
  return def_insn;
}

static int combine_substitute (gen_ctx_t gen_ctx, bb_insn_t *bb_insn_ref, long *deleted_insns_num) {
  MIR_context_t ctx = gen_ctx->ctx;
  bb_insn_t bb_insn = *bb_insn_ref;
  MIR_insn_t insn = bb_insn->insn, def_insn;
  size_t i, nops = insn->nops;
  int out_p, insn_change_p, insn_hr_change_p, op_change_p, mem_reg_change_p, success_p;
  MIR_op_t *op_ref, *src_op_ref, *src_op2_ref, saved_op;
  MIR_reg_t hr, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int64_t scale;

  if (nops == 0) return FALSE;
  VARR_TRUNC (MIR_op_t, last_right_ops, 0);
  for (i = 0; i < nops; i++) VARR_PUSH (MIR_op_t, last_right_ops, insn->ops[i]);
  VARR_TRUNC (MIR_reg_t, insn_hard_regs, 0);
  bitmap_clear (hard_regs_bitmap);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (ctx, insn, i, &out_p);
    if (out_p && insn->ops[i].mode != MIR_OP_HARD_REG_MEM) continue;
    combine_process_op (gen_ctx, &insn->ops[i], bb_insn);
  }
  if (move_code_p (insn->code) && VARR_LENGTH (MIR_reg_t, insn_hard_regs) == 1) {
    /* We processed all other regs already.  Try to change insn the following way:
       hr0 = hr2 op hr3; ...; ... = hr0  =>  ...; ... = hr2 op hr3 */
    hr = VARR_GET (MIR_reg_t, insn_hard_regs, 0);
    if ((def_insn = get_uptodate_def_insn (gen_ctx, hr)) == NULL
        || MIR_call_code_p (def_insn->code))
      return FALSE;
    target_get_early_clobbered_hard_regs (def_insn, &early_clobbered_hard_reg1,
                                          &early_clobbered_hard_reg2);
    if (!move_code_p (def_insn->code) && early_clobbered_hard_reg1 == MIR_NON_HARD_REG
        && early_clobbered_hard_reg2 == MIR_NON_HARD_REG && insn->ops[1].mode == MIR_OP_HARD_REG
        && insn->ops[1].u.hard_reg == hr
        /* Check that insn->ops[0] is not mem[...hr0...]: */
        && (insn->ops[0].mode != MIR_OP_HARD_REG_MEM
            || (insn->ops[0].u.hard_reg_mem.base != hr
                && insn->ops[0].u.hard_reg_mem.index != hr))) {
      saved_op = def_insn->ops[0];
      def_insn->ops[0] = insn->ops[0];
      success_p = target_insn_ok_p (gen_ctx, def_insn);
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
  while (VARR_LENGTH (MIR_reg_t, insn_hard_regs) != 0) {
    hr = VARR_POP (MIR_reg_t, insn_hard_regs);
    if ((def_insn = get_uptodate_def_insn (gen_ctx, hr)) == NULL) continue;
    insn_hr_change_p = FALSE;
    for (i = 0; i < nops; i++) { /* Change all hr occurences: */
      op_ref = &insn->ops[i];
      op_change_p = FALSE;
      MIR_insn_op_mode (ctx, insn, i, &out_p);
      if (!out_p && op_ref->mode == MIR_OP_HARD_REG && op_ref->u.hard_reg == hr) {
        if (!move_code_p (def_insn->code)) break;
        /* It is not safe to substitute if there is another use after def insn before
           the current as we delete def insn after substitution. */
        insn->ops[i] = def_insn->ops[1];
        insn_hr_change_p = op_change_p = TRUE;
      } else if (op_ref->mode == MIR_OP_HARD_REG_MEM) {
        src_op_ref = &def_insn->ops[1];
        if (op_ref->u.hard_reg_mem.index == hr) {
          mem_reg_change_p = FALSE;
          if (src_op_ref->mode != MIR_OP_HARD_REG) {
          } else if (def_insn->code == MIR_MOV) { /* index = r */
            insn->ops[i].u.hard_reg_mem.index = src_op_ref->u.hard_reg;
            mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
          } else if (def_insn->code == MIR_ADD) { /* index = r + const */
            gen_assert (src_op_ref->u.hard_reg != MIR_NON_HARD_REG);
            if ((src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT) {
              insn->ops[i].u.hard_reg_mem.index = src_op_ref->u.hard_reg;
              insn->ops[i].u.hard_reg_mem.disp
                += src_op2_ref->u.i * insn->ops[i].u.hard_reg_mem.scale;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            }
          } else if ((def_insn->code == MIR_MUL || def_insn->code == MIR_LSH)
                     && op_ref->u.mem.scale >= 1 && op_ref->u.mem.scale <= MIR_MAX_SCALE
                     && (src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT) {
            scale = def_insn->code == MIR_MUL ? src_op2_ref->u.i : power2 (src_op2_ref->u.i);
            if (scale >= 1 && scale <= MIR_MAX_SCALE
                && insn->ops[i].u.hard_reg_mem.scale * scale <= MIR_MAX_SCALE) {
              /* index = r * const */
              gen_assert (src_op_ref->u.hard_reg != MIR_NON_HARD_REG);
              insn->ops[i].u.hard_reg_mem.index = src_op_ref->u.hard_reg;
              insn->ops[i].u.hard_reg_mem.scale *= scale;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            }
          }
          if (!mem_reg_change_p) break;
        }
        if (op_ref->u.hard_reg_mem.base == hr) {
          mem_reg_change_p = FALSE;
          op_ref = &insn->ops[i];
          if (def_insn->code == MIR_MOV) {
            if (src_op_ref->mode == MIR_OP_HARD_REG) { /* base = r */
              insn->ops[i].u.hard_reg_mem.base = src_op_ref->u.hard_reg;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            } else if (src_op_ref->mode == MIR_OP_INT) { /* base = const */
              if (insn->ops[i].u.hard_reg_mem.scale != 1) {
                insn->ops[i].u.hard_reg_mem.base = MIR_NON_HARD_REG;
              } else {
                insn->ops[i].u.hard_reg_mem.base = insn->ops[i].u.hard_reg_mem.index;
                insn->ops[i].u.hard_reg_mem.index = MIR_NON_HARD_REG;
              }
              insn->ops[i].u.hard_reg_mem.disp += src_op_ref->u.i;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            }
          } else if (src_op_ref->mode != MIR_OP_HARD_REG) { /* Can do nothing */
            ;
          } else if (def_insn->code == MIR_ADD) {
            gen_assert (src_op_ref->u.hard_reg != MIR_NON_HARD_REG);
            src_op2_ref = &def_insn->ops[2];
            if (src_op2_ref->mode == MIR_OP_HARD_REG
                && op_ref->u.hard_reg_mem.index == MIR_NON_HARD_REG) { /* base = r1 + r2 */
              insn->ops[i].u.hard_reg_mem.base = src_op_ref->u.hard_reg;
              insn->ops[i].u.hard_reg_mem.index = src_op2_ref->u.hard_reg;
              insn->ops[i].u.hard_reg_mem.scale = 1;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            } else if (src_op2_ref->mode == MIR_OP_INT) { /* base = r + const */
              insn->ops[i].u.hard_reg_mem.base = src_op_ref->u.hard_reg;
              insn->ops[i].u.hard_reg_mem.disp += src_op2_ref->u.i;
              mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
            }
          } else if (def_insn->code == MIR_MUL && op_ref->u.hard_reg_mem.index == MIR_NON_HARD_REG
                     && (src_op2_ref = &def_insn->ops[2])->mode == MIR_OP_INT
                     && src_op2_ref->u.i >= 1
                     && src_op2_ref->u.i <= MIR_MAX_SCALE) { /* base = r * const */
            gen_assert (src_op_ref->u.hard_reg != MIR_NON_HARD_REG && src_op2_ref->u.i != 1);
            insn->ops[i].u.hard_reg_mem.base = MIR_NON_HARD_REG;
            insn->ops[i].u.hard_reg_mem.index = src_op_ref->u.hard_reg;
            insn->ops[i].u.hard_reg_mem.scale = src_op2_ref->u.i;
            mem_reg_change_p = op_change_p = insn_hr_change_p = TRUE;
          }
          if (!mem_reg_change_p) {
            if (op_change_p) VARR_PUSH (size_t, changed_op_numbers, i); /* index was changed */
            break;
          }
        }
      }
      if (op_change_p) VARR_PUSH (size_t, changed_op_numbers, i);
    }
    if (insn_hr_change_p) {
      if ((success_p = i >= nops && target_insn_ok_p (gen_ctx, insn))) insn_change_p = TRUE;
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
  if (op.mode != MIR_OP_HARD_REG || !safe_hreg_substitution_p (gen_ctx, op.u.hard_reg, bb_insn))
    return NULL;
  def_insn = hreg_refs_addr[op.u.hard_reg].insn;
  if ((code = get_combined_br_code (code == MIR_BT || code == MIR_BTS, def_insn->code))
      == MIR_INSN_BOUND)
    return NULL;
  if (obsolete_op_p (gen_ctx, def_insn->ops[1], hreg_refs_addr[op.u.hard_reg].insn_num)
      || obsolete_op_p (gen_ctx, def_insn->ops[2], hreg_refs_addr[op.u.hard_reg].insn_num))
    return NULL;
  new_insn = MIR_new_insn (ctx, code, insn->ops[0], def_insn->ops[1], def_insn->ops[2]);
  MIR_insert_insn_before (ctx, curr_func_item, insn, new_insn);
  if (!target_insn_ok_p (gen_ctx, new_insn)) {
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
  if (op.mode != MIR_OP_HARD_REG || !safe_hreg_substitution_p (gen_ctx, op.u.hard_reg, bb_insn))
    return NULL;
  def_insn = hreg_refs_addr[op.u.hard_reg].insn;
  switch (def_insn->code) {
  case MIR_EXT8: sign_p = TRUE;
  case MIR_UEXT8: size = 1; break;
  case MIR_EXT16: sign_p = TRUE;
  case MIR_UEXT16: size = 2; break;
  case MIR_EXT32: sign_p = TRUE;
  case MIR_UEXT32: size = 3; break;
  default: return NULL;
  }
  if (obsolete_op_p (gen_ctx, def_insn->ops[1], hreg_refs_addr[op.u.hard_reg].insn_num))
    return NULL;
  if (size2 <= size) {
    /* [u]ext<n> b,a; ... [u]ext<m> c,b -> [u]ext<m> c,a when <m> <= <n>: */
    saved_op = insn->ops[1];
    insn->ops[1] = def_insn->ops[1];
    if (!target_insn_ok_p (gen_ctx, insn)) {
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
    saved_op = def_insn->ops[0];
    def_insn->ops[0] = insn->ops[0];
    ok_p = target_insn_ok_p (gen_ctx, def_insn);
    def_insn->ops[0] = saved_op;
    if (!ok_p) return NULL;
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
    return def_insn;
  }
  return NULL;
}

static MIR_insn_t combine_mul_div_substitute (gen_ctx_t gen_ctx, bb_insn_t bb_insn,
                                              long *deleted_insns_num) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_t def_insn = NULL, new_insns[6], insn = bb_insn->insn;
  MIR_insn_code_t new_code, code = insn->code;
  int n, sh, ok_p;
  MIR_op_t op, temp;

  switch (code) {
  case MIR_MUL: new_code = MIR_LSH; break;
  case MIR_MULS: new_code = MIR_LSHS; break;
  case MIR_UDIV: new_code = MIR_URSH; break;
  case MIR_UDIVS: new_code = MIR_URSHS; break;
  case MIR_DIV: new_code = MIR_RSH; break;
  case MIR_DIVS: new_code = MIR_RSHS; break;
  default: return NULL;
  }
  op = insn->ops[2];
  if (op.mode == MIR_OP_HARD_REG && safe_hreg_substitution_p (gen_ctx, op.u.hard_reg, bb_insn)) {
    def_insn = hreg_refs_addr[op.u.hard_reg].insn;
    if (def_insn->code != MIR_MOV) return NULL;
    op = def_insn->ops[1];
  }
  if (op.mode != MIR_OP_INT && op.mode != MIR_OP_UINT) return NULL;
  if ((sh = int_log2 (op.u.i)) < 0) return NULL;
  if (sh == 0) {
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], insn->ops[1]);
    gen_add_insn_before (gen_ctx, insn, new_insns[0]);
    move_bb_insn_dead_vars (new_insns[0]->data, bb_insn);
    DEBUG (2, {
      fprintf (debug_file, "      changing to ");
      print_bb_insn (gen_ctx, new_insns[0]->data, TRUE);
    });
    gen_delete_insn (gen_ctx, insn);
    if (def_insn != NULL) {
      DEBUG (2, {
        fprintf (debug_file, "      deleting now dead insn ");
        print_bb_insn (gen_ctx, def_insn->data, TRUE);
      });
      gen_delete_insn (gen_ctx, def_insn);
      (*deleted_insns_num)++;
    }
    return new_insns[0];
  } else if (code == MIR_MUL || code == MIR_MULS || code == MIR_UDIV || code == MIR_UDIVS) {
    new_insns[0]
      = MIR_new_insn (ctx, new_code, insn->ops[0], insn->ops[1], MIR_new_int_op (ctx, sh));
    MIR_insert_insn_after (ctx, curr_func_item, insn, new_insns[0]);
    if ((ok_p = target_insn_ok_p (gen_ctx, new_insns[0]))) {
      insn->code = new_insns[0]->code;
      insn->ops[2] = new_insns[0]->ops[2];
      DEBUG (2, {
        fprintf (debug_file, "      changing to ");
        print_bb_insn (gen_ctx, bb_insn, TRUE);
      });
    }
    MIR_remove_insn (ctx, curr_func_item, new_insns[0]);
    return ok_p ? insn : NULL;
  } else if (insn->ops[1].mode == MIR_OP_HARD_REG
             && insn->ops[1].u.hard_reg == TEMP_INT_HARD_REG2) {
  } else if (insn->ops[1].mode == MIR_OP_HARD_REG_MEM
             && (insn->ops[1].u.hard_reg_mem.base == TEMP_INT_HARD_REG2
                 || insn->ops[1].u.hard_reg_mem.index == TEMP_INT_HARD_REG2)) {
  } else {
    temp = _MIR_new_hard_reg_op (ctx, TEMP_INT_HARD_REG2);
    gen_assert (code == MIR_DIV || code == MIR_DIVS);
    new_insns[0] = MIR_new_insn (ctx, MIR_MOV, temp, insn->ops[1]);
    if (code == MIR_DIV) {
      new_insns[1] = MIR_new_insn (ctx, MIR_RSH, temp, temp, MIR_new_int_op (ctx, 63));
      new_insns[2] = MIR_new_insn (ctx, MIR_AND, temp, temp, MIR_new_int_op (ctx, op.u.i - 1));
      new_insns[3] = MIR_new_insn (ctx, MIR_ADD, temp, temp, insn->ops[1]);
    } else {
      new_insns[1] = MIR_new_insn (ctx, MIR_RSHS, temp, temp, MIR_new_int_op (ctx, 31));
      new_insns[2] = MIR_new_insn (ctx, MIR_ANDS, temp, temp, MIR_new_int_op (ctx, op.u.i - 1));
      new_insns[3] = MIR_new_insn (ctx, MIR_ADDS, temp, temp, insn->ops[1]);
    }
    new_insns[4] = MIR_new_insn (ctx, new_code, temp, temp, MIR_new_int_op (ctx, sh));
    new_insns[5] = MIR_new_insn (ctx, MIR_MOV, insn->ops[0], temp);
    for (n = 0; n < 6; n++) gen_add_insn_before (gen_ctx, insn, new_insns[n]);
    for (n = 0; n < 6; n++)
      if (!target_insn_ok_p (gen_ctx, new_insns[n])) break;
    if (n < 6) {
      for (n = 0; n < 6; n++) gen_delete_insn (gen_ctx, new_insns[n]);
    } else {
      move_bb_insn_dead_vars (new_insns[3]->data, bb_insn);
      add_bb_insn_dead_var (gen_ctx, new_insns[5]->data, TEMP_INT_HARD_REG2);
      DEBUG (2, {
        fprintf (debug_file, "      changing to ");
        for (n = 0; n < 6; n++) {
          if (n != 0) fprintf (debug_file, "                  ");
          print_bb_insn (gen_ctx, new_insns[n]->data, TRUE);
        }
      });
      gen_delete_insn (gen_ctx, insn);
      *deleted_insns_num -= 5;
      if (def_insn != NULL) {
        DEBUG (2, {
          fprintf (debug_file, "      deleting now dead insn ");
          print_bb_insn (gen_ctx, def_insn->data, TRUE);
        });
        gen_delete_insn (gen_ctx, def_insn);
        (*deleted_insns_num)++;
      }
      return new_insns[0];
    }
  }
  return NULL;
}

static void setup_hreg_ref (gen_ctx_t gen_ctx, MIR_reg_t hr, MIR_insn_t insn, size_t nop,
                            size_t insn_num, int def_p) {
  if (hr == MIR_NON_HARD_REG) return;
  hreg_ref_ages_addr[hr] = curr_bb_hreg_ref_age;
  hreg_refs_addr[hr].insn = insn;
  hreg_refs_addr[hr].nop = nop;
  hreg_refs_addr[hr].insn_num = insn_num;
  hreg_refs_addr[hr].def_p = def_p;
  hreg_refs_addr[hr].del_p = FALSE;
}

static void combine (gen_ctx_t gen_ctx) {
  MIR_context_t ctx = gen_ctx->ctx;
  MIR_insn_code_t code, new_code;
  MIR_insn_t insn, new_insn;
  bb_insn_t bb_insn;
  size_t iter, nops, i, curr_insn_num;
  MIR_op_t temp_op, *op_ref;
  MIR_reg_t early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int out_p, change_p, block_change_p;
  long insns_num = 0, deleted_insns_num = 0;

  hreg_refs_addr = VARR_ADDR (hreg_ref_t, hreg_refs);
  hreg_ref_ages_addr = VARR_ADDR (size_t, hreg_ref_ages);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    do {
      DEBUG (2, { fprintf (debug_file, "Processing bb%lu\n", (unsigned long) bb->index); });
      block_change_p = FALSE;
      curr_bb_hreg_ref_age++;
      last_mem_ref_insn_num = 0; /* means undef */
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns), curr_insn_num = 1; bb_insn != NULL;
           bb_insn = DLIST_NEXT (bb_insn_t, bb_insn), curr_insn_num++) {
        insn = bb_insn->insn;
        nops = MIR_insn_nops (ctx, insn);
        if (insn->code != MIR_LABEL) insns_num++;
        DEBUG (2, {
          fprintf (debug_file, "  Processing ");
          print_bb_insn (gen_ctx, bb_insn, TRUE);
        });
        target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                              &early_clobbered_hard_reg2);
        if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
          setup_hreg_ref (gen_ctx, early_clobbered_hard_reg1, insn, 0 /* whatever */, curr_insn_num,
                          TRUE);
        if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
          setup_hreg_ref (gen_ctx, early_clobbered_hard_reg2, insn, 0 /* whatever */, curr_insn_num,
                          TRUE);
        if (MIR_call_code_p (code = insn->code)) {
          for (size_t hr = 0; hr <= MAX_HARD_REG; hr++)
            if (bitmap_bit_p (call_used_hard_regs[MIR_T_UNDEF], hr)) {
              setup_hreg_ref (gen_ctx, hr, insn, 0 /* whatever */, curr_insn_num, TRUE);
            }
          last_mem_ref_insn_num = curr_insn_num; /* Potentially call can change memory */
        } else if (code == MIR_VA_BLOCK_ARG) {
          last_mem_ref_insn_num = curr_insn_num; /* Change memory */
        } else if (code == MIR_RET) {
          /* ret is transformed in machinize and should be not modified after that */
        } else if ((new_insn = combine_branch_and_cmp (gen_ctx, bb_insn, &deleted_insns_num))
                     != NULL
                   || (new_insn = combine_exts (gen_ctx, bb_insn, &deleted_insns_num)) != NULL
                   || (new_insn = combine_mul_div_substitute (gen_ctx, bb_insn, &deleted_insns_num))
                        != NULL) {
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

        for (iter = 0; iter < 2; iter++) { /* update hreg ref info: */
          for (i = 0; i < nops; i++) {
            op_ref = &insn->ops[i];
            MIR_insn_op_mode (ctx, insn, i, &out_p);
            if (op_ref->mode == MIR_OP_HARD_REG && !iter == !out_p) {
              /* process in ops on 0th iteration and out ops on 1th iteration */
              setup_hreg_ref (gen_ctx, op_ref->u.hard_reg, insn, i, curr_insn_num, iter == 1);
            } else if (op_ref->mode == MIR_OP_HARD_REG_MEM) {
              if (out_p && iter == 1)
                last_mem_ref_insn_num = curr_insn_num;
              else if (iter == 0) {
                setup_hreg_ref (gen_ctx, op_ref->u.hard_reg_mem.base, insn, i, curr_insn_num,
                                FALSE);
                setup_hreg_ref (gen_ctx, op_ref->u.hard_reg_mem.index, insn, i, curr_insn_num,
                                FALSE);
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
  hreg_ref_t hreg_ref = {NULL, 0, 0};

  gen_ctx->selection_ctx = gen_malloc (gen_ctx, sizeof (struct selection_ctx));
  curr_bb_hreg_ref_age = 0;
  VARR_CREATE (size_t, hreg_ref_ages, MAX_HARD_REG + 1);
  VARR_CREATE (hreg_ref_t, hreg_refs, MAX_HARD_REG + 1);
  VARR_CREATE (MIR_reg_t, insn_hard_regs, 0);
  VARR_CREATE (size_t, changed_op_numbers, 16);
  VARR_CREATE (MIR_op_t, last_right_ops, 16);
  hard_regs_bitmap = bitmap_create2 (MAX_HARD_REG + 1);
  for (MIR_reg_t i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (hreg_ref_t, hreg_refs, hreg_ref);
    VARR_PUSH (size_t, hreg_ref_ages, 0);
  }
}

static void finish_selection (gen_ctx_t gen_ctx) {
  VARR_DESTROY (size_t, hreg_ref_ages);
  VARR_DESTROY (hreg_ref_t, hreg_refs);
  VARR_DESTROY (MIR_reg_t, insn_hard_regs);
  VARR_DESTROY (size_t, changed_op_numbers);
  VARR_DESTROY (MIR_op_t, last_right_ops);
  bitmap_destroy (hard_regs_bitmap);
  free (gen_ctx->selection_ctx);
  gen_ctx->selection_ctx = NULL;
}

/* New Page */

/* Dead code elimnination */

#define live_out out

static void dead_code_elimination (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t passed_mem_num;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int op_num, out_p, reg_def_p, dead_p, mem_p;
  bitmap_t live;
  insn_var_iterator_t insn_var_iter;
  long dead_insns_num = 0;

  DEBUG (2, { fprintf (debug_file, "+++++++++++++Dead code elimination:\n"); });
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      reg_def_p = FALSE;
      dead_p = TRUE;
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (!out_p) continue;
        reg_def_p = TRUE;
        if (bitmap_clear_bit_p (live, var)) dead_p = FALSE;
      }
      if (!reg_def_p) dead_p = FALSE;
      if (dead_p && !MIR_call_code_p (insn->code) && insn->code != MIR_RET
          && insn->code != MIR_ALLOCA && insn->code != MIR_BSTART && insn->code != MIR_BEND
          && insn->code != MIR_VA_START && insn->code != MIR_VA_ARG && insn->code != MIR_VA_END
          && !(insn->ops[0].mode == MIR_OP_HARD_REG
               && (insn->ops[0].u.hard_reg == FP_HARD_REG
                   || insn->ops[0].u.hard_reg == SP_HARD_REG))) {
        DEBUG (2, {
          fprintf (debug_file, "  Removing dead insn %-5lu", (unsigned long) bb_insn->index);
          MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
        });
        gen_delete_insn (gen_ctx, insn);
        dead_insns_num++;
        continue;
      }
      if (MIR_call_code_p (insn->code))
        bitmap_and_compl (live, live, call_used_hard_regs[MIR_T_UNDEF]);
      FOREACH_INSN_VAR (gen_ctx, insn_var_iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
        if (!out_p) bitmap_set_bit_p (live, var);
      }
      target_get_early_clobbered_hard_regs (insn, &early_clobbered_hard_reg1,
                                            &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
        bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
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
  size_t passed_mem_num;
  MIR_reg_t var;
  insn_var_iterator_t iter;
  ssa_edge_t ssa_edge;

  /* check control insns with possible output: */
  if (MIR_call_code_p (insn->code) || insn->code == MIR_ALLOCA || insn->code == MIR_BSTART
      || insn->code == MIR_VA_START || insn->code == MIR_VA_ARG
      || (insn->nops > 0 && insn->ops[0].mode == MIR_OP_HARD_REG
          && (insn->ops[0].u.hard_reg == FP_HARD_REG || insn->ops[0].u.hard_reg == SP_HARD_REG)))
    return FALSE;
  if (start_insn_p (gen_ctx, bb_insn)) return FALSE;
  FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
    if (!out_p) continue;
    output_exists_p = TRUE;
    if (mem_p || (ssa_edge = insn->ops[op_num].data) != NULL) return FALSE;
  }
  return output_exists_p;
}

static void ssa_dead_code_elimination (gen_ctx_t gen_ctx) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, def;
  int op_num, out_p, mem_p;
  size_t passed_mem_num;
  MIR_reg_t var;
  insn_var_iterator_t iter;
  ssa_edge_t ssa_edge;
  long dead_insns_num = 0;

  DEBUG (2, { fprintf (debug_file, "+++++++++++++Dead code elimination:\n"); });
  gen_assert (def_use_repr_p);
  VARR_TRUNC (bb_insn_t, dead_bb_insns, 0);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL;
         bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
      if (dead_insn_p (gen_ctx, bb_insn)) VARR_PUSH (bb_insn_t, dead_bb_insns, bb_insn);
  while (VARR_LENGTH (bb_insn_t, dead_bb_insns) != 0) {
    bb_insn = VARR_POP (bb_insn_t, dead_bb_insns);
    insn = bb_insn->insn;
    DEBUG (2, {
      fprintf (debug_file, "  Removing dead insn %-5lu", (unsigned long) bb_insn->index);
      MIR_output_insn (gen_ctx->ctx, debug_file, insn, curr_func_item->u.func, TRUE);
    });
    FOREACH_INSN_VAR (gen_ctx, iter, insn, var, op_num, out_p, mem_p, passed_mem_num) {
      if (out_p && !mem_p) continue;
      if ((ssa_edge = insn->ops[op_num].data) == NULL) continue;
      def = ssa_edge->def;
      remove_ssa_edge (gen_ctx, ssa_edge);
      if (dead_insn_p (gen_ctx, def)) VARR_PUSH (bb_insn_t, dead_bb_insns, def);
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

static void parallel_error (MIR_context_t ctx, const char *err_message) {
  MIR_get_error_func (ctx) (MIR_parallel_error, err_message);
}

void *MIR_gen (MIR_context_t ctx, int gen_num, MIR_item_t func_item) {
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  gen_ctx_t gen_ctx;
  uint8_t *code;
  void *machine_code;
  size_t code_len;
  double start_time = real_usec_time ();

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
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after building CFG:\n");
    print_CFG (gen_ctx, TRUE, FALSE, TRUE, FALSE, NULL);
  });
  if (optimize_level >= 2) {
    build_ssa (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after building SSA:\n");
      print_varr_insns (gen_ctx, "undef init", undef_insns);
      print_varr_insns (gen_ctx, "arg init", arg_bb_insns);
      fprintf (debug_file, "\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
#ifndef NO_COPY_PROP
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++Copy Propagation:\n"); });
    copy_prop (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after Copy Propagation:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
  }
#endif /* #ifndef NO_COPY_PROP */
#ifndef NO_GVN
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++GVN:\n"); });
    gvn (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after GVN:\n");
      print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
    });
    gvn_clear (gen_ctx);
  }
#endif /* #ifndef NO_GVN */
#ifndef NO_GVN
  if (optimize_level >= 2) {
    ssa_dead_code_elimination (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after dead code elimination after GVN:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
    });
  }
#endif /* #ifndef NO_GVN */
#ifndef NO_CCP
  if (optimize_level >= 2) {
    DEBUG (2, { fprintf (debug_file, "+++++++++++++CCP:\n"); });
    if (ccp (gen_ctx)) {
      DEBUG (2, {
        fprintf (debug_file, "+++++++++++++MIR after CCP:\n");
        print_CFG (gen_ctx, TRUE, FALSE, TRUE, TRUE, NULL);
      });
      ssa_dead_code_elimination (gen_ctx);
      DEBUG (2, {
        fprintf (debug_file, "+++++++++++++MIR after dead code elimination after CCP:\n");
        print_CFG (gen_ctx, TRUE, TRUE, TRUE, TRUE, NULL);
      });
    }
  }
#endif /* #ifndef NO_CCP */
  if (optimize_level >= 2) undo_build_ssa (gen_ctx);
  make_io_dup_op_insns (gen_ctx);
  target_machinize (gen_ctx);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after machinize:\n");
    print_CFG (gen_ctx, FALSE, FALSE, TRUE, TRUE, NULL);
  });
  if (optimize_level != 0) build_loop_tree (gen_ctx);
  calculate_func_cfg_live_info (gen_ctx, optimize_level != 0);
  DEBUG (2, {
    add_bb_insn_dead_vars (gen_ctx);
    fprintf (debug_file, "+++++++++++++MIR after building live_info:\n");
    print_loop_tree (gen_ctx, TRUE);
    print_CFG (gen_ctx, TRUE, TRUE, FALSE, FALSE, output_bb_live_info);
  });
  if (optimize_level != 0) build_live_ranges (gen_ctx);
  assign (gen_ctx);
  rewrite (gen_ctx); /* After rewrite the BB live info is still valid */
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after rewrite:\n");
    print_CFG (gen_ctx, FALSE, FALSE, TRUE, FALSE, NULL);
  });
#ifndef NO_COMBINE
  if (optimize_level >= 1) {
    calculate_func_cfg_live_info (gen_ctx, FALSE);
    add_bb_insn_dead_vars (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR before combine:\n");
      print_CFG (gen_ctx, FALSE, FALSE, TRUE, FALSE, NULL);
    });
    combine (gen_ctx); /* After combine the BB live info is still valid */
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after combine:\n");
      print_CFG (gen_ctx, FALSE, FALSE, TRUE, FALSE, NULL);
    });
    dead_code_elimination (gen_ctx);
    DEBUG (2, {
      fprintf (debug_file, "+++++++++++++MIR after dead code elimination after combine:\n");
      print_CFG (gen_ctx, TRUE, TRUE, TRUE, FALSE, output_bb_live_info);
    });
  }
#endif /* #ifndef NO_COMBINE */
  target_make_prolog_epilog (gen_ctx, func_used_hard_regs, func_stack_slots_num);
  DEBUG (2, {
    fprintf (debug_file, "+++++++++++++MIR after forming prolog/epilog:\n");
    print_CFG (gen_ctx, FALSE, FALSE, TRUE, FALSE, NULL);
  });
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
  destroy_func_live_ranges (gen_ctx);
  if (optimize_level != 0) destroy_loop_tree (gen_ctx, curr_cfg->root_loop_node);
  destroy_func_cfg (gen_ctx);
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

#if MIR_PARALLEL_GEN
static void *gen (void *arg) {
  MIR_item_t func_item;
  gen_ctx_t gen_ctx = arg;
  struct all_gen_ctx *all_gen_ctx = gen_ctx->all_gen_ctx;
  MIR_context_t ctx = all_gen_ctx->ctx;
  size_t len;

  for (;;) {
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    while (VARR_LENGTH (MIR_item_t, funcs_to_generate) <= funcs_start)
      if (mir_cond_wait (&generate_signal, &queue_mutex))
        parallel_error (ctx, "error in cond wait");
    if ((func_item = VARR_GET (MIR_item_t, funcs_to_generate, funcs_start)) == NULL) {
      if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
      break;
    }
    funcs_start++;
    if (funcs_start > 64 && VARR_LENGTH (MIR_item_t, funcs_to_generate) < 2 * funcs_start) {
      len = VARR_LENGTH (MIR_item_t, funcs_to_generate) - funcs_start;
      memmove (VARR_ADDR (MIR_item_t, funcs_to_generate), /* compact */
               VARR_ADDR (MIR_item_t, funcs_to_generate) + funcs_start, len * sizeof (MIR_item_t));
      VARR_TRUNC (MIR_item_t, funcs_to_generate, len);
      funcs_start = 0;
    }
    gen_ctx->busy_p = TRUE;
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
    MIR_gen (gen_ctx->ctx, gen_ctx->gen_num, func_item);
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
  VARR_TRUNC (MIR_item_t, funcs_to_generate, 0);
  VARR_PUSH (MIR_item_t, funcs_to_generate, NULL); /* flag to finish threads */
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
  funcs_start = 0;
  VARR_CREATE (MIR_item_t, funcs_to_generate, 0);
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
      if (mir_thread_create (&gen_ctx->gen_thread, NULL, gen, gen_ctx) != 0) {
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
    gen_ctx->ccp_ctx = NULL;
    gen_ctx->lr_ctx = NULL;
    gen_ctx->ra_ctx = NULL;
    gen_ctx->selection_ctx = NULL;
#if !MIR_NO_GEN_DEBUG
    debug_file = NULL;
    debug_level = 100;
#endif
    VARR_CREATE (bb_insn_t, dead_bb_insns, 16);
    VARR_CREATE (loop_node_t, loop_nodes, 32);
    VARR_CREATE (loop_node_t, queue_nodes, 32);
    VARR_CREATE (loop_node_t, loop_entries, 16);
    init_dead_vars (gen_ctx);
    init_data_flow (gen_ctx);
    init_ssa (gen_ctx);
    init_gvn (gen_ctx);
    init_ccp (gen_ctx);
    temp_bitmap = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    temp_bitmap2 = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    init_live_ranges (gen_ctx);
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
    insn_to_consider = bitmap_create2 (1024);
    func_used_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  }
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
                                              "can not destroy generator mutex  or signals");
  }
  VARR_DESTROY (MIR_item_t, funcs_to_generate);
#endif
  for (int i = 0; i < all_gen_ctx->gens_num; i++) {
    gen_ctx = &all_gen_ctx->gen_ctx[i];
    finish_data_flow (gen_ctx);
    finish_ssa (gen_ctx);
    finish_gvn (gen_ctx);
    finish_ccp (gen_ctx);
    bitmap_destroy (temp_bitmap);
    bitmap_destroy (temp_bitmap2);
    finish_live_ranges (gen_ctx);
    finish_ra (gen_ctx);
    finish_selection (gen_ctx);
    for (MIR_type_t type = MIR_T_I8; type < MIR_T_BOUND; type++)
      bitmap_destroy (call_used_hard_regs[type]);
    bitmap_destroy (insn_to_consider);
    bitmap_destroy (func_used_hard_regs);
    target_finish (gen_ctx);
    finish_dead_vars (gen_ctx);
    free (gen_ctx->data_flow_ctx);
    VARR_DESTROY (bb_insn_t, dead_bb_insns);
    VARR_DESTROY (loop_node_t, loop_nodes);
    VARR_DESTROY (loop_node_t, queue_nodes);
    VARR_DESTROY (loop_node_t, loop_entries);
  }
  free (all_gen_ctx);
  *all_gen_ctx_ptr = NULL;
}

void MIR_set_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  if (func_item == NULL) return; /* finish setting interfaces */
  MIR_gen (ctx, 0, func_item);
}

void MIR_set_parallel_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);

#if !MIR_PARALLEL_GEN
  if (func_item == NULL) return; /* finish setting interfaces */
  MIR_gen (ctx, 0, func_item);
#else
  if (func_item == NULL) {
    size_t i;

    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    for (;;) {
      for (i = 0; i < all_gen_ctx->gens_num; i++)
        if (all_gen_ctx->gen_ctx[i].busy_p) break;
      if (VARR_LENGTH (MIR_item_t, funcs_to_generate) <= funcs_start && i >= all_gen_ctx->gens_num)
        break; /* nothing to generate and nothing is being generated */
      if (mir_cond_wait (&done_signal, &queue_mutex)) parallel_error (ctx, "error in cond wait");
    }
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  } else {
    if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
    VARR_PUSH (MIR_item_t, funcs_to_generate, func_item);
    if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
    if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  }
#endif
}

static void *gen_and_redirect (MIR_context_t ctx, MIR_item_t func_item) {
#if !MIR_PARALLEL_GEN
  MIR_gen (ctx, 0, func_item);
#else
  struct all_gen_ctx *all_gen_ctx = *all_gen_ctx_loc (ctx);
  MIR_func_t func = func_item->u.func;

  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  VARR_PUSH (MIR_item_t, funcs_to_generate, func_item);
  if (mir_cond_broadcast (&generate_signal)) parallel_error (ctx, "error in cond broadcast");
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
  if (mir_mutex_lock (&queue_mutex)) parallel_error (ctx, "error in mutex lock");
  for (;;) {
    if (func->machine_code != NULL) break;
    if (mir_cond_wait (&done_signal, &queue_mutex)) parallel_error (ctx, "error in cond wait");
  }
  if (mir_mutex_unlock (&queue_mutex)) parallel_error (ctx, "error in mutex unlock");
#endif
  return func_item->u.func->machine_code;
}

void MIR_set_lazy_gen_interface (MIR_context_t ctx, MIR_item_t func_item) {
  void *addr;

  if (func_item == NULL) return;
  addr = _MIR_get_wrapper (ctx, func_item, gen_and_redirect);
  _MIR_redirect_thunk (ctx, func_item->addr, addr);
}

/* Local Variables:                */
/* mode: c                         */
/* page-delimiter: "/\\* New Page" */
/* End:                            */
