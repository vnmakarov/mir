/* Optimization pipeline:

            ----------------      -----------      ------------------      ---------------------- 
   MIR --->|    Simplify    |--->| Build CFG |--->|  Common Sub-Expr |--->| Conditional Constant |
            ----------------     -----------      |    Elimination   |	  |     Propagation      |
                                                   -------------------	  ----------------------- 
                                                                                     |
                                                                                     v
           --------      -------------      ------------       -------------      -----------
          | Assign |<---| Build Live  |<---| Build Live |<----|  Dead Code  |<---| Machinize |
           --------     |   Ranges    |    |    Info    |     | Elimination |     -----------
              |          -------------      ------------       -------------     
              |
              v
           ---------     ---------     -------------      ---------------
          | Rewrite |-->| Combine |-->|  Dead Code  |--->|   Generate    |-> Machine Insns
           ---------     ---------    | Elimination |    | machine insns |
                                       -------------      ---------------
              
              

   Simplify: Lowering MIR (in mir.c).
   Machinize: Machine-dependent code (e.g. in x86_64-target.c)
              transforming MIR for calls ABI, 2-op insns, etc.
   Build CGF: Builing Control Flow Graph (basic blocks and CFG edges).
   Common Sub-Expression Elimination: Reusing calculated values
   Conditional Constant Propagation: constant propagation and removing death paths of CFG
   Dead code elimination: Removing insns with unused outputs. 
   Building Live Info: Calculating live in and live out for the basic blocks.
   Build Live Ranges: Calculating program point ranges for registers.
   Assign: Priority-based assigning hard regs and stack slots to registers.
   Rewrite: Transform MIR according to the assign using reserved hard regs.
   Combine (code selection): Merging data-depended insns into one.
   Dead code elimination: Removing insns with unused outputs. 
   Generate machine insns: Machine-dependent code (e.g. in
                           x86_64-target.c) creating machine insns.

   Terminology:
   reg - MIR (pseudo-)register (their numbers are in MIR_OP_REG and MIR_OP_MEM)
   hard reg - MIR hard register (their numbers are in MIR_OP_HARD_REG and MIR_OP_HARD_REG_MEM)
   breg (based reg) - function pseudo registers whose numbers start with zero
   var - pseudo and hard register (var numbers for psedo-registers are based reg numbers + MAX_HARD_REG + 1)
   loc - hard register and stack locations (stack slot numbers start with MAX_HARD_REG + 1).

   We don't use SSA becuase the optimization pipeline is short and going into / out of SSA is expensive
*/

#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

static void util_error (const char *message);
#define MIR_VARR_ERROR util_error

#include "mir.h"
#include "mir-dlist.h"
#include "mir-bitmap.h"
#include "mir-htab.h"
#include "mir-mum.h"

static void MIR_NO_RETURN util_error (const char *message) { (*MIR_get_error_func ()) (MIR_alloc_error, message); }

static void *gen_malloc (size_t size) {
  void *res = malloc (size);
  if (res == NULL)
    util_error ("no memory");
  return res;
}

static void set_label_disp (MIR_insn_t insn, size_t disp);
static size_t get_label_disp (MIR_insn_t insn);
static void gen_add_insn_before (MIR_item_t func_item, MIR_insn_t insn, MIR_insn_t before);

#ifdef __x86_64__
#include "x86_64-target.c"
#else
#error "undefined or unsupported generation target"
#endif

#ifndef MIR_GEN_DEBUG
#define MIR_GEN_DEBUG 0
#endif

#if MIR_GEN_DEBUG
static FILE *debug_file;
#endif

#define DEFAULT_INIT_BITMAP_BITS_NUM 256
static bitmap_t insn_to_consider, temp_bitmap, temp_bitmap2, all_vars;

static void make_2op_insns (MIR_item_t func_item) {
  MIR_func_t func;
  MIR_insn_t insn, next_insn;
  MIR_insn_code_t code;
  MIR_op_t input, output, temp_op;
  MIR_op_mode_t mode;
  MIR_type_t type;
  size_t i;
  int out_p;
  
  assert (func_item->func_p);
  func = func_item->u.func;
  for (i = 0; i < sizeof (two_op_insn_codes) / sizeof (MIR_insn_code_t); i++)
    bitmap_set_bit_p (insn_to_consider, two_op_insn_codes[i]);
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    code = insn->code;
    if (! bitmap_bit_p (insn_to_consider, code))
      continue;
    assert (MIR_insn_nops (code) > 2);
    mode = MIR_insn_op_mode (code, 0, &out_p);
    assert (out_p && mode == MIR_insn_op_mode (code, 1, &out_p) && ! out_p);
    output = insn->ops[0];
    input = insn->ops[1];
    assert (input.mode == MIR_OP_REG || input.mode == MIR_OP_HARD_REG
	    || output.mode == MIR_OP_REG || output.mode == MIR_OP_HARD_REG);
    if (input.mode == output.mode
	&& ((input.mode == MIR_OP_HARD_REG && input.u.hard_reg == output.u.hard_reg)
	    || (input.mode == MIR_OP_REG && input.u.reg == output.u.reg)))
      continue;
    if (mode == MIR_OP_FLOAT) {
      code = MIR_FMOV; type = MIR_F;
    } else if (mode == MIR_OP_DOUBLE) {
      code = MIR_DMOV; type = MIR_D;
    } else {
      code = MIR_MOV; type = MIR_I64;
    }
    temp_op = MIR_new_reg_op (_MIR_new_temp_reg (type, func));
    MIR_insert_insn_before (func_item, insn, MIR_new_insn (code, temp_op, insn->ops[1]));
    MIR_insert_insn_after (func_item, insn, MIR_new_insn (code, insn->ops[0], temp_op));
    insn->ops[0] = insn->ops[1] = temp_op;
  }
}

typedef struct bb *bb_t;

DEF_DLIST_LINK (bb_t);

typedef struct bb_insn *bb_insn_t;

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
  unsigned int skipped_p : 1; /* used for CCP */
};

DEF_DLIST (in_edge_t, in_link);
DEF_DLIST (out_edge_t, out_link);

struct bb_insn {
  MIR_insn_t insn;
  DLIST_LINK (bb_insn_t) bb_insn_link;
  bb_t bb;
  bitmap_t call_hard_reg_args; /* non-null for calls */
  size_t label_disp; /* for label */
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost;
  unsigned int reachable_p : 1; /* used for CPP */
  DLIST_LINK (bb_t) bb_link;
  DLIST (in_edge_t) in_edges;
  /* The out edges order: optional fall through bb, optional label bb,
     optional exit bb.  There is always at least one edge.  */
  DLIST (out_edge_t) out_edges;
  DLIST (bb_insn_t) bb_insns;
  size_t freq;
  bitmap_t in, out, gen, kill; /* var bitmaps for different data flow problems */
};

DEF_DLIST (bb_t, bb_link);

typedef struct func_cfg *func_cfg_t;

DEF_DLIST_LINK (func_cfg_t);

typedef struct mv *mv_t;
typedef mv_t dst_mv_t;
typedef mv_t src_mv_t;

DEF_DLIST_LINK (mv_t);
DEF_DLIST_LINK (dst_mv_t);
DEF_DLIST_LINK (src_mv_t);

struct mv {
  bb_insn_t bb_insn;
  DLIST_LINK (mv_t) mv_link;
  DLIST_LINK (dst_mv_t) dst_link;
  DLIST_LINK (src_mv_t) src_link;
};

DEF_DLIST (mv_t, mv_link);
DEF_DLIST (dst_mv_t, dst_link);
DEF_DLIST (src_mv_t, src_link);

struct reg_info {
  size_t freq;
  size_t calls_num;
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

typedef struct {
  bb_t bb;
  MIR_reg_t var;
  unsigned int in_p : 1;
  const_t val;
} var_const_t;

struct func_cfg {
  MIR_reg_t min_reg, max_reg;
  VARR (reg_info_t) *breg_info; /* bregs */
  DLIST (bb_t) bbs;
  DLIST (mv_t) used_moves;
  DLIST (mv_t) free_moves;
};

static bitmap_t call_used_hard_regs;
static MIR_item_t curr_func_item;
static func_cfg_t curr_cfg;

static bb_insn_t create_bb_insn (MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = gen_malloc (sizeof (struct bb_insn));

  insn->data = bb_insn;
  bb_insn->bb = bb;
  bb_insn->insn = insn;
  bb_insn->call_hard_reg_args = NULL;
  if (insn->code == MIR_CALL || insn->code == MIR_CALL_C)
    bb_insn->call_hard_reg_args = bitmap_create2 (MAX_HARD_REG + 1);
  return bb_insn;
}

static bb_insn_t add_new_bb_insn (MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = create_bb_insn (insn, bb);

  DLIST_APPEND (bb_insn_t, bb->bb_insns, bb_insn);
  return bb_insn;
}

static void delete_bb_insn (bb_insn_t bb_insn) {
  DLIST_REMOVE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn);
  bb_insn->insn->data = NULL;
  if (bb_insn->call_hard_reg_args != NULL)
    bitmap_destroy (bb_insn->call_hard_reg_args);
  free (bb_insn);
}

static void gen_add_insn_before (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t insn) {
  bb_insn_t bb_insn, bb_before_insn;
  bb_t bb;

  assert (before != NULL);
  bb_before_insn = before->data;
  bb = bb_before_insn->bb;
  bb_insn = create_bb_insn (insn, bb);
  MIR_insert_insn_before (func_item, before, insn);
  DLIST_INSERT_BEFORE (bb_insn_t, bb->bb_insns, bb_before_insn, bb_insn);
}

static void set_label_disp (MIR_insn_t insn, size_t disp) {
  assert (insn->code == MIR_LABEL);
  ((bb_insn_t) insn->data)->label_disp = disp;
}
static size_t get_label_disp (MIR_insn_t insn) {
  assert (insn->code == MIR_LABEL);
  return ((bb_insn_t) insn->data)->label_disp;
}

static size_t curr_bb_index;

static bb_t create_bb (MIR_insn_t insn) {
  bb_t bb = gen_malloc (sizeof (struct bb));

  bb->pre = bb->rpost = 0;
  DLIST_INIT (bb_insn_t, bb->bb_insns);
  DLIST_INIT (in_edge_t, bb->in_edges);
  DLIST_INIT (out_edge_t, bb->out_edges);
  bb->in = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->out = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->gen = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb->kill = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  if (insn != NULL)
    add_new_bb_insn (insn, bb);
  return bb;
}

static void add_bb (bb_t bb) {
  DLIST_APPEND (bb_t, curr_cfg->bbs, bb);
  bb->index = curr_bb_index++;
}

static edge_t create_edge (bb_t src, bb_t dst) {
  edge_t e = gen_malloc (sizeof (struct edge));

  e->src = src; e->dst = dst;
  DLIST_APPEND (in_edge_t, dst->in_edges, e);
  DLIST_APPEND (out_edge_t, src->out_edges, e);
  e->skipped_p = FALSE;
  return e;
}

static void delete_edge (edge_t e) {
  DLIST_REMOVE (out_edge_t, e->src->out_edges, e);
  DLIST_REMOVE (in_edge_t, e->dst->in_edges, e);
  free (e);
}

static void delete_bb (bb_t bb) {
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
  free (bb);
}

static void DFS (bb_t bb, size_t *pre, size_t *rpost) {
  edge_t e;
  
  bb->pre = *pre;
  (*pre)++;
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    if (e->dst->pre == 0)
      DFS (e->dst, pre, rpost);
  bb->rpost = *rpost;
  (*rpost)--;
}

static void enumerate_bbs (void) {
  size_t pre, rpost;

  pre = 1;
  rpost = DLIST_LENGTH (bb_t, curr_cfg->bbs);
  DFS (DLIST_HEAD (bb_t, curr_cfg->bbs), &pre, &rpost);
}

static void update_min_max_reg (MIR_reg_t reg) {
  if (reg == 0)
    return;
  if (curr_cfg->max_reg == 0 || curr_cfg->min_reg > reg)
    curr_cfg->min_reg = reg;
  if (curr_cfg->max_reg < reg)
    curr_cfg->max_reg = reg;
}

static MIR_reg_t reg2breg (MIR_reg_t reg) { return reg - curr_cfg->min_reg; }
static MIR_reg_t breg2reg (MIR_reg_t breg) { return breg + curr_cfg->min_reg; }
static MIR_reg_t reg2var (MIR_reg_t reg) { return reg2breg (reg) + MAX_HARD_REG + 1; }
static MIR_reg_t var_is_reg_p (MIR_reg_t var) { return var > MAX_HARD_REG; }
static MIR_reg_t var2reg (MIR_reg_t var) {
  assert (var > MAX_HARD_REG);
  return breg2reg (var - MAX_HARD_REG - 1);
}

static MIR_reg_t get_nregs (void) {
  return curr_cfg->max_reg == 0 ? 0 : curr_cfg->max_reg - curr_cfg->min_reg + 1;
}

static MIR_reg_t get_nvars (void) {
  return get_nregs () + MAX_HARD_REG + 1;
}

static int move_p (MIR_insn_t insn) {
  return ((insn->code == MIR_MOV || insn->code == MIR_FMOV || insn->code == MIR_DMOV)
	  && (insn->ops[0].mode == MIR_OP_REG || insn->ops[0].mode == MIR_OP_HARD_REG)
	  && (insn->ops[1].mode == MIR_OP_REG || insn->ops[1].mode == MIR_OP_HARD_REG));
}

static int imm_move_p (MIR_insn_t insn) {
  return ((insn->code == MIR_MOV || insn->code == MIR_FMOV || insn->code == MIR_DMOV)
	  && (insn->ops[0].mode == MIR_OP_REG || insn->ops[0].mode == MIR_OP_HARD_REG)
	  && (insn->ops[1].mode == MIR_OP_INT || insn->ops[1].mode == MIR_OP_UINT));
}

DEF_HTAB (var_const_t);
static HTAB (var_const_t) *var_const_tab; /* keys: bb, var, and in_p */

static int var_const_eq (var_const_t vc1, var_const_t vc2) {
  return vc1.bb == vc2.bb && vc1.var == vc2.var && vc1.in_p == vc2.in_p;
}

static htab_hash_t var_const_hash (var_const_t vc) {
  return mum_hash_finish (mum_hash_step (mum_hash_step
					 (mum_hash_step (mum_hash_init (0x42), (uint64_t) vc.bb),
					  (uint64_t) vc.var), (uint64_t) vc.in_p));
}

static int find_var_const (bb_t bb, int in_p, MIR_reg_t var, var_const_t *var_const) {
  var_const_t vc;
  
  vc.bb = bb; vc.in_p = in_p; vc.var = var;
  return HTAB_DO (var_const_t, var_const_tab, vc, HTAB_FIND, *var_const);
}

static void insert_var_const (bb_t bb, int in_p, MIR_reg_t var, const_t val) {
  var_const_t vc;
  
  assert (! find_var_const (bb, in_p, var, &vc));
  vc.bb = bb; vc.in_p = in_p; vc.var = var; vc.val = val;
  HTAB_DO (var_const_t, var_const_tab, vc, HTAB_INSERT, vc);
}

static void delete_var_const (bb_t bb, int in_p, MIR_reg_t var) {
  var_const_t vc;
  
  vc.bb = bb; vc.in_p = in_p; vc.var = var;
  HTAB_DO (var_const_t, var_const_tab, vc, HTAB_DELETE, vc);
}

#if MIR_GEN_DEBUG
static void output_in_edges (bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  in edges:");
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    fprintf (debug_file, " %3lu", (unsigned long) e->src->index);
    if (e->skipped_p)
      fprintf (debug_file, "(CCP skip)");
  }
  fprintf (debug_file, "\n");
}

static void output_out_edges (bb_t bb) {
  edge_t e;

  fprintf (debug_file, "  out edges:");
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e)) {
    fprintf (debug_file, " %3lu", (unsigned long) e->dst->index);
    if (e->skipped_p)
      fprintf (debug_file, "(CCP skip)");
  }
  fprintf (debug_file, "\n");

}

static void output_live_element (size_t nel) {
  fprintf (debug_file, "%3lu", (unsigned long) nel);
  if (var_is_reg_p (nel))
    fprintf (debug_file, "(%s)", MIR_reg_name (var2reg (nel), curr_func_item->u.func));
}

static void output_bitmap (const char *head, bitmap_t bm) {
  if (bm == NULL || bitmap_empty_p (bm))
    return;
  fprintf (debug_file, head);
  bitmap_for_each (bm, output_live_element);
  fprintf (debug_file, "\n");
}

static void print_CFG (int bb_p, int insns_p, void (*bb_info_print_func) (bb_t)) {
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb_p) {
      fprintf (debug_file, "BB %3lu:\n", (unsigned long) bb->index);
      output_in_edges (bb); output_out_edges (bb);
      if (bb_info_print_func != NULL) {
	bb_info_print_func (bb);
	fprintf (debug_file, "\n");
      }
    }
    if (insns_p) {
      for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	   bb_insn != NULL;
	   bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
	MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func);
      fprintf (debug_file, "\n");
    }
  }
}
#endif

static mv_t get_free_move (void) {
  mv_t mv;
  
  if ((mv = DLIST_HEAD (mv_t, curr_cfg->free_moves)) != NULL)
    DLIST_REMOVE (mv_t, curr_cfg->free_moves, mv);
  else
    mv = gen_malloc (sizeof (struct mv));
  DLIST_APPEND (mv_t, curr_cfg->used_moves, mv);
  return mv;
}

static void free_move (mv_t mv) {
  DLIST_REMOVE (mv_t, curr_cfg->used_moves, mv);
  DLIST_APPEND (mv_t, curr_cfg->free_moves, mv);
}

static void build_func_cfg (void) {
  MIR_insn_t insn, next_insn;
  bb_insn_t bb_insn, label_bb_insn;
  size_t i, nops;
  MIR_op_t *op;
  bb_t bb, prev_bb, entry_bb, exit_bb;
  
  DLIST_INIT (bb_t, curr_cfg->bbs);
  DLIST_INIT (mv_t, curr_cfg->used_moves);
  DLIST_INIT (mv_t, curr_cfg->free_moves);
  curr_cfg->max_reg = 0;
  curr_cfg->min_reg = 0;
  curr_bb_index = 0;
  entry_bb = create_bb (NULL); add_bb (entry_bb);
  exit_bb = create_bb (NULL); add_bb (exit_bb);
  insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns);
  if (insn != NULL) {
    bb = create_bb (NULL); add_bb (bb);
  }
  for (; insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    if (insn->data == NULL)
      add_new_bb_insn (insn, bb);
    nops = MIR_insn_nops (insn->code);
    if (next_insn != NULL
	&& (MIR_branch_code_p (insn->code)
	    || MIR_ret_code_p (insn->code) || next_insn->code == MIR_LABEL)) {
      prev_bb = bb;
      if (next_insn->code == MIR_LABEL && (label_bb_insn = next_insn->data) != NULL)
	bb = label_bb_insn->bb;
      else
	bb = create_bb (NULL);
      add_bb (bb);
      if (insn->code != MIR_JMP && ! MIR_ret_code_p (insn->code))
	create_edge (prev_bb, bb);
    }
    for (i = 0; i < nops; i++)
      if ((op = &insn->ops[i])->mode == MIR_OP_LABEL) {
	if ((label_bb_insn = op->u.label->data) == NULL) {
	  create_bb (op->u.label);
	  label_bb_insn = op->u.label->data;
	}
	bb_insn = insn->data;
	create_edge (bb_insn->bb, label_bb_insn->bb);
      } else if (op->mode == MIR_OP_REG) {
	update_min_max_reg (op->u.reg);
      } else if (op->mode == MIR_OP_MEM) {
	update_min_max_reg (op->u.mem.base);
	update_min_max_reg (op->u.mem.index);
      }
  }
  update_min_max_reg (MIR_func_reg (FP_NAME, curr_func_item->u.func));
  /* Add additional edges with entry and exit */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb != entry_bb && DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
      create_edge (entry_bb, bb);
    if (bb != exit_bb && DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
      create_edge (bb, exit_bb);
  }
  enumerate_bbs ();
  VARR_CREATE (reg_info_t, curr_cfg->breg_info, 128);
}

static void destroy_func_cfg (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t bb, last_bb;
  mv_t mv, next_mv;
  
  assert (curr_func_item->func_p && curr_func_item->data != NULL);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_destroy (bb->in); bitmap_destroy (bb->out);
    bitmap_destroy (bb->gen); bitmap_destroy (bb->kill);
  }
  last_bb = NULL;
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    bb_insn = insn->data;
    assert (bb_insn != NULL && bb_insn->bb != NULL);
    bb = bb_insn->bb;
    delete_bb_insn (bb_insn);
    if (last_bb != bb) {
      if (last_bb != NULL)
	delete_bb (last_bb);
      last_bb = bb;
    }
  }
  if (last_bb != NULL)
    delete_bb (last_bb);
  for (mv = DLIST_HEAD (mv_t, curr_cfg->used_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free (mv);
  }
  for (mv = DLIST_HEAD (mv_t, curr_cfg->free_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free (mv);
  }
  VARR_DESTROY (reg_info_t, curr_cfg->breg_info);
  free (curr_func_item->data);
  curr_func_item->data = NULL;
}

static void add_new_bb_insns (MIR_item_t func_item) {
  MIR_func_t func;
  size_t i, nops;
  MIR_op_t op;
  bb_t bb = DLIST_EL (bb_t, curr_cfg->bbs, 2);
  bb_insn_t bb_insn, last_bb_insn = NULL;
  
  assert (func_item->func_p);
  func = func_item->u.func;
  for (MIR_insn_t insn = DLIST_HEAD (MIR_insn_t, func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn))
    if (insn->data != NULL) {
      bb = (last_bb_insn = insn->data)->bb;
      if (MIR_branch_code_p (insn->code) || MIR_ret_code_p (insn->code)) {
	bb = DLIST_NEXT (bb_t, bb);
	last_bb_insn = NULL;
      }
    } else { /* New insn: */
      assert (bb != NULL);
      bb_insn = create_bb_insn (insn, bb);
      if (last_bb_insn == NULL)
	DLIST_PREPEND (bb_insn_t, bb->bb_insns, bb_insn);
      else
	DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, last_bb_insn, bb_insn);
      last_bb_insn = bb_insn;
      nops = MIR_insn_nops (insn->code);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	if (op.mode == MIR_OP_REG) {
	  update_min_max_reg (op.u.reg);
	} else if (op.mode == MIR_OP_MEM) {
	  update_min_max_reg (op.u.mem.base);
	  update_min_max_reg (op.u.mem.index);
	}
      }
    }
}

static int rpost_cmp (const void *a1, const void *a2) {
  return (*(const struct bb **) a1)->rpost - (*(const struct bb **) a2)->rpost;
}

static int post_cmp (const void *a1, const void *a2) { return -rpost_cmp (a1, a2); }

DEF_VARR (bb_t);

static VARR (bb_t) *worklist, *pending;
static bitmap_t bb_to_consider;

static void
solve_dataflow (int forward_p, void (*con_func_0) (bb_t), int (*con_func_n) (bb_t),
		int (*trans_func) (bb_t)) {
  size_t i, iter;
  bb_t bb, *addr;
  VARR (bb_t) *t;
  
  VARR_TRUNC (bb_t, worklist, 0);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    VARR_PUSH (bb_t, worklist, bb);
  VARR_TRUNC (bb_t, pending, 0);
  iter = 0;
  while (VARR_LENGTH (bb_t, worklist) != 0) {
    VARR_TRUNC (bb_t, pending, 0);
    addr = VARR_ADDR (bb_t, worklist);
    qsort (addr, VARR_LENGTH (bb_t, worklist), sizeof (bb),
	   forward_p ? rpost_cmp : post_cmp); 
    bitmap_clear (bb_to_consider);
    for (i = 0; i < VARR_LENGTH (bb_t, worklist); i++) {
      int changed_p = iter == 0;
      edge_t e;
      
      bb = addr[i];
      if (forward_p) {
	if (DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
	  con_func_0 (bb);
	else
	  changed_p |= con_func_n (bb);
      } else {
	if (DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
	  con_func_0 (bb);
	else
	  changed_p |= con_func_n (bb);
      }
      if (changed_p && trans_func (bb)) {
	if (forward_p) {
	  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
	    if (bitmap_set_bit_p (bb_to_consider, e->dst->index))
	      VARR_PUSH (bb_t, pending, e->dst);
	} else {
	  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e))
	    if (bitmap_set_bit_p (bb_to_consider, e->src->index))
	      VARR_PUSH (bb_t, pending, e->src);
	}
      }
    }
    iter++;
    t = worklist; worklist = pending; pending = t;
  }
}



/* Common Sub-expression Elimination.  */

#define av_in in
#define av_out out
#define av_kill kill
#define av_gen gen

typedef struct expr {
  MIR_insn_t insn;    /* operation and input operands are the expr keys */
  unsigned int num;   /* the expression number (0, 1 ...) */
  MIR_reg_t temp_reg; /* ??? */
} *expr_t;

DEF_VARR (expr_t);
static VARR (expr_t) *exprs; /* the expr number -> expression */

DEF_VARR (bitmap_t);
/* map: var number -> bitmap of numbers of exprs with given var as an operand. */
static VARR (bitmap_t) *var2dep_expr;

DEF_HTAB (expr_t);
static HTAB (expr_t) *expr_tab; /* keys: insn code and operands */

static int op_eq (MIR_op_t op1, MIR_op_t op2) {
  if (op1.mode != op2.mode)
    return FALSE;
  switch (op1.mode) {
  case MIR_OP_REG: return op1.u.reg == op2.u.reg;
  case MIR_OP_HARD_REG: return op1.u.hard_reg == op2.u.hard_reg;
  case MIR_OP_INT: return op1.u.i == op2.u.i;
  case MIR_OP_UINT: return op1.u.u == op2.u.u;
  case MIR_OP_NAME: return strcmp (op1.u.name, op2.u.name) == 0;
  case MIR_OP_MEM:
    return (op1.u.mem.type == op2.u.mem.type && op1.u.mem.disp == op2.u.mem.disp
	    && op1.u.mem.base == op2.u.mem.base && op1.u.mem.index == op2.u.mem.index
	    && (op1.u.mem.index == 0 || op1.u.mem.scale == op2.u.mem.scale));
  case MIR_OP_HARD_REG_MEM:
    return (op1.u.hard_reg_mem.type == op2.u.hard_reg_mem.type
	    && op1.u.hard_reg_mem.disp == op2.u.hard_reg_mem.disp
	    && op1.u.hard_reg_mem.base == op2.u.hard_reg_mem.base
	    && op1.u.hard_reg_mem.index == op2.u.hard_reg_mem.index
	    && (op1.u.hard_reg_mem.index == MIR_NON_HARD_REG
		|| op1.u.hard_reg_mem.scale == op2.u.hard_reg_mem.scale));
  default:
    assert (FALSE); /* we should not have all the rest operand here */
  }
}

static int expr_eq (expr_t e1, expr_t e2) {
  size_t i, nops;
  int out_p;
  
  if (e1->insn->code != e2->insn->code)
    return FALSE;
  nops = MIR_insn_nops (e1->insn->code);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (e1->insn->code, i, &out_p);
    if (out_p)
      continue;
    if (! op_eq (e1->insn->ops[i], e2->insn->ops[i]))
      return FALSE;
  }
  return TRUE;
}

static htab_hash_t add_op_hash (htab_hash_t h, MIR_op_t op) {
  h = mum_hash_step (h, (uint64_t) op.mode);
  switch (op.mode) {
  case MIR_OP_REG: return mum_hash_step (h, (uint64_t) op.u.reg);
  case MIR_OP_HARD_REG: return mum_hash_step (h, (uint64_t) op.u.hard_reg);
  case MIR_OP_INT: return mum_hash_step (h, (uint64_t) op.u.i);
  case MIR_OP_UINT: return mum_hash_step (h, (uint64_t) op.u.u);
  case MIR_OP_NAME: return mum_hash_step (h, (uint64_t) op.u.i);
  case MIR_OP_MEM:
    h = mum_hash_step (h, (uint64_t) op.u.mem.type);
    h = mum_hash_step (h, (uint64_t) op.u.mem.disp);
    h = mum_hash_step (h, (uint64_t) op.u.mem.base);
    h = mum_hash_step (h, (uint64_t) op.u.mem.index);
    if (op.u.mem.index != 0)
      h = mum_hash_step (h, (uint64_t) op.u.mem.scale);
  case MIR_OP_HARD_REG_MEM:
    h = mum_hash_step (h, (uint64_t) op.u.hard_reg_mem.type);
    h = mum_hash_step (h, (uint64_t) op.u.hard_reg_mem.disp);
    h = mum_hash_step (h, (uint64_t) op.u.hard_reg_mem.base);
    h = mum_hash_step (h, (uint64_t) op.u.hard_reg_mem.index);
    if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
      h = mum_hash_step (h, (uint64_t) op.u.hard_reg_mem.scale);
  default:
    assert (FALSE); /* we should not have all the rest operand here */
  }
  return h;
}

static htab_hash_t expr_hash (expr_t e) {
  size_t i, nops;
  int out_p;
  htab_hash_t h = mum_hash_init (0x42);
  
  h = mum_hash_step (h, (uint64_t) e->insn->code);
  nops = MIR_insn_nops (e->insn->code);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (e->insn->code, i, &out_p);
    if (out_p)
      continue;
    h = add_op_hash (h, e->insn->ops[i]);
  }
  return mum_hash_finish (h);
}

static int find_expr (MIR_insn_t insn, expr_t *e) {
  struct expr es;
  
  es.insn = insn;
  return HTAB_DO (expr_t, expr_tab, &es, HTAB_FIND, *e);
}

static void insert_expr (expr_t e) {
  expr_t e2;
  
  assert (! find_expr (e->insn, &e2));
  HTAB_DO (expr_t, expr_tab, e, HTAB_INSERT, e);
}

static void process_var (MIR_reg_t var, expr_t e) {
  bitmap_t b;
  
  while (var >= VARR_LENGTH (bitmap_t, var2dep_expr))
    VARR_PUSH (bitmap_t, var2dep_expr, NULL);
  if ((b = VARR_GET (bitmap_t, var2dep_expr, var)) == NULL) {
    b = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
    VARR_SET (bitmap_t, var2dep_expr, var, b);
  }
  bitmap_set_bit_p (b, e->num);
}

static void process_op_vars (MIR_op_t op, expr_t e) {
  switch (op.mode) { // ???
  case MIR_OP_REG:
    process_var (reg2var (op.u.reg), e);
    break;
  case MIR_OP_HARD_REG:
    process_var (op.u.hard_reg, e);
    break;
  case MIR_OP_INT: case MIR_OP_UINT: case MIR_OP_NAME:
    break;
  case MIR_OP_MEM:
    if (op.u.mem.base != 0)
      process_var (reg2var (op.u.mem.base), e);
    if (op.u.mem.index != 0)
      process_var (reg2var (op.u.mem.index), e);
    break;
  case MIR_OP_HARD_REG_MEM:
    if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
      process_var (op.u.hard_reg_mem.base, e);
    if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
      process_var (op.u.hard_reg_mem.index, e);
    break;
  default:
    assert (FALSE); /* we should not have all the rest operand here */
  }
}

static expr_t add_expr (MIR_insn_t insn) {
  size_t i, nops;
  int out_p;
  MIR_op_mode_t mode;
  expr_t e = gen_malloc (sizeof (struct expr));
  
  e->insn = insn; e->num = VARR_LENGTH (expr_t, exprs);
  mode = MIR_insn_op_mode (insn->code, 0, &out_p);
  e->temp_reg = _MIR_new_temp_reg (mode == MIR_OP_FLOAT ? MIR_F
				   : mode == MIR_OP_DOUBLE ? MIR_D : MIR_I64,
				   curr_func_item->u.func);
  update_min_max_reg (e->temp_reg);
  VARR_PUSH (expr_t, exprs, e);
  insert_expr (e);
  nops = MIR_insn_nops (insn->code);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (insn->code, i, &out_p);
    if (! out_p)
      process_op_vars (insn->ops[i], e);
  }
  return e;
}

static void cse_con_func_0 (bb_t bb) { bitmap_clear (bb->av_in); }

static int cse_con_func_n (bb_t bb) {
  edge_t e, head;
  bitmap_t prev_av_in = temp_bitmap;

  bitmap_copy (prev_av_in, bb->av_in);
  head = DLIST_HEAD (in_edge_t, bb->in_edges);
  bitmap_copy (bb->av_in, head->src->av_out);
  for (e = DLIST_NEXT (in_edge_t, head); e != NULL; e = DLIST_NEXT (in_edge_t, e))
    bitmap_and (bb->av_in, bb->av_in, e->src->av_out); /* av_in &= av_out */
  return ! bitmap_equal_p (bb->av_in, prev_av_in);
}

static int cse_trans_func (bb_t bb) {
  return bitmap_ior_and_compl (bb->av_out, bb->av_gen, bb->av_in, bb->av_kill);
}

static void create_exprs (void) {
  HTAB_CLEAR (expr_t, expr_tab);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      expr_t e;
      MIR_insn_t insn = bb_insn->insn;
      
      if (! MIR_branch_code_p (insn->code) && ! MIR_ret_code_p (insn->code)
	  && insn->code != MIR_LABEL && insn->code != MIR_CALL && insn->code != MIR_CALL_C
	  && ! move_p (insn) && ! imm_move_p (insn) && ! find_expr (insn, &e))
	add_expr (insn);
    }
}

static void create_av_bitmaps (void) {
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_clear (bb->av_in); bitmap_clear (bb->av_out);
    bitmap_clear (bb->av_kill); bitmap_clear (bb->av_gen);
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      size_t i, nops;
      int out_p;
      MIR_reg_t var;
      MIR_op_t op;
      expr_t e;
      bitmap_t b;
      MIR_insn_t insn = bb_insn->insn;
      
      if (MIR_branch_code_p (bb_insn->insn->code) || MIR_ret_code_p (insn->code)
	  || insn->code == MIR_LABEL || insn->code == MIR_CALL || insn->code == MIR_CALL_C
	  || move_p (insn) ||  imm_move_p (insn))
	continue;
      if (! find_expr (insn, &e))
	assert (FALSE);
      bitmap_set_bit_p (bb->av_gen, e->num);
      nops = MIR_insn_nops (insn->code);
      for (i = 0; i < nops; i++) { // ??? MEM
	MIR_insn_op_mode (insn->code, i, &out_p);
	op = insn->ops[i];
	if (! out_p || (op.mode != MIR_OP_REG && op.mode != MIR_OP_HARD_REG))
	  continue;
	var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
	if ((b = VARR_GET (bitmap_t, var2dep_expr, var)) != NULL) {
	  bitmap_and_compl (bb->av_gen, bb->av_gen, b);
	  bitmap_ior (bb->av_kill, bb->av_kill, b);
	}
      }
    }
  }
}

static void cse_modify (void) {
  bb_insn_t bb_insn, new_bb_insn, next_bb_insn;
  bitmap_t av = temp_bitmap;
  
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (av, bb->av_in);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      size_t i, nops;
      expr_t e;
      MIR_reg_t var;
      MIR_op_t op;
      int out_p;
      bitmap_t b;
      MIR_insn_t new_insn, insn = bb_insn->insn;
      
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (MIR_branch_code_p (insn->code) || MIR_ret_code_p (insn->code)
	  || insn->code == MIR_LABEL || insn->code == MIR_CALL || insn->code == MIR_CALL_C
	  || move_p (insn) || imm_move_p (insn))
	continue;
      if (! find_expr (insn, &e))
	assert (FALSE);
      if (! bitmap_bit_p (av, e->num)) {
	bitmap_set_bit_p (av, e->num);
	op = MIR_new_reg_op (e->temp_reg);
	new_insn = MIR_new_insn (MIR_MOV, op, insn->ops[0]); /* result is always 0-th op */
	new_bb_insn = create_bb_insn (new_insn, bb);
	MIR_insert_insn_after (curr_func_item, insn, new_insn);
	DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
	next_bb_insn = DLIST_NEXT (bb_insn_t, new_bb_insn);
#if MIR_GEN_DEBUG
	fprintf (debug_file, "  adding insn ");
	MIR_output_insn (debug_file, new_insn, curr_func_item->u.func);
#endif
      } else {
#if MIR_GEN_DEBUG
	fprintf (debug_file, "  changing insn ");
	MIR_output_insn (debug_file, insn, curr_func_item->u.func);
#endif
	op = MIR_new_reg_op (e->temp_reg);
	new_insn = MIR_new_insn (MIR_MOV, insn->ops[0], op); /* result is always 0-th op */
	MIR_insert_insn_before (curr_func_item, insn, new_insn);
	MIR_remove_insn (curr_func_item, insn);
	new_insn->data = bb_insn;
	bb_insn->insn = new_insn;
#if MIR_GEN_DEBUG
	fprintf (debug_file, "    on insn ");
	MIR_output_insn (debug_file, new_insn, curr_func_item->u.func);
#endif
      }
      nops = MIR_insn_nops (insn->code);
      for (i = 0; i < nops; i++) { // ??? MEM
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (! out_p || (op.mode != MIR_OP_REG && op.mode != MIR_OP_HARD_REG))
	  continue;
	var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
	if ((b = VARR_GET (bitmap_t, var2dep_expr, var)) != NULL)
	  bitmap_and_compl (av, av, b);
      }
    }
  }
}

static void cse (void) {
  create_exprs ();
  create_av_bitmaps ();
  solve_dataflow (TRUE, cse_con_func_0, cse_con_func_n, cse_trans_func);
  cse_modify ();
}

#if MIR_GEN_DEBUG
static void print_exprs (void) {
  for (size_t i = 0; i < VARR_LENGTH (expr_t, exprs); i++) {
    size_t nops;
    expr_t e = VARR_GET (expr_t, exprs, i);
    
    fprintf (debug_file, "%3d: ", i);
    fprintf (debug_file, "%s _", MIR_insn_name (e->insn->code));
    nops = MIR_insn_nops (e->insn->code);
    for (size_t j = 1; j < nops; j++) {
      fprintf (debug_file, ", ");
      MIR_output_op (debug_file, e->insn->ops[j], curr_func_item->u.func);
    }
    fprintf (debug_file, "\n");
  }
}

static void output_bb_cse_info (bb_t bb) {
  output_bitmap ("  av_in:", bb->av_in); output_bitmap ("  av_out:", bb->av_out);
  output_bitmap ("  av_gen:", bb->av_gen); output_bitmap ("  av_kill:", bb->av_kill);
}
#endif

#undef av_in
#undef av_out
#undef av_kill
#undef av_gen



/* Conditional Constant Propagation.  */

#define ccp_unknown_in in
#define ccp_unknown_out out
#define ccp_varying_in kill
#define ccp_varying_out gen

static void ccp_con_func_0 (bb_t bb) {}

static bb_t ccp_src, ccp_dst;
static int ccp_con_func_change_p, ccp_trans_func_change_p;

static void process_const_out (size_t var) {
  var_const_t vc1, vc2;
  
  if (bitmap_bit_p (ccp_dst->ccp_varying_in, var))
    return;
  if (! find_var_const (ccp_src, FALSE, var, &vc1))
    assert (FALSE);
  if (bitmap_bit_p (ccp_dst->ccp_unknown_in, var)) { /* unknown became a constat */
    bitmap_clear_bit_p (ccp_dst->ccp_unknown_in, var);
    assert (! find_var_const (ccp_dst, TRUE, var, &vc2));
    insert_var_const (ccp_dst, TRUE, var, vc1.val);
    ccp_con_func_change_p = TRUE;
    return;
  }
  if (! find_var_const (ccp_dst, TRUE, var, &vc2))
    assert (FALSE);
  if (vc1.val.uns_p != vc2.val.uns_p
      || (vc1.val.uns_p && vc1.val.u.u != vc2.val.u.u)
      || (! vc1.val.uns_p && vc1.val.u.i != vc2.val.u.i)) { /* constant became another constant */
    delete_var_const (ccp_dst, TRUE, var);
    bitmap_set_bit_p (ccp_dst->ccp_varying_in, var);
    ccp_con_func_change_p = TRUE;
  }
}

static void process_new_varying (size_t var) {
  var_const_t vc;
  
  ccp_con_func_change_p = TRUE;
  if (! bitmap_bit_p (ccp_dst->ccp_unknown_in, var)) { /* it was a constant */
    assert (find_var_const (ccp_dst, TRUE, var, &vc));
    delete_var_const (ccp_dst, TRUE, var);
  }
}

static int ccp_con_func_n (bb_t bb) {
  edge_t e;
  bitmap_t const_out = temp_bitmap, new_varying = temp_bitmap2;
  
  ccp_con_func_change_p = FALSE;
  for (e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    if (e->skipped_p)
      continue;
    ccp_src = e->src; ccp_dst = e->dst;
    /* const_out = all - varying_out - unknown_out */
    bitmap_and_compl (const_out, all_vars, ccp_src->ccp_varying_out);
    bitmap_and_compl (const_out, const_out, ccp_src->ccp_unknown_out);
    bitmap_for_each (const_out, process_const_out);
    /* new_varying = varying_out - varying_in */
    bitmap_and_compl (new_varying, ccp_src->ccp_varying_out, ccp_dst->ccp_varying_in);
    bitmap_for_each (new_varying, process_new_varying);
    /* varying_in += new_varying */
    bitmap_ior (ccp_dst->ccp_varying_in, ccp_dst->ccp_varying_in, new_varying);
    /* unknown_in -= new_varying */
    bitmap_and_compl (ccp_dst->ccp_unknown_in, ccp_dst->ccp_unknown_in, new_varying);
  }
  return ccp_con_func_change_p;
}

DEF_VARR (const_t);
static VARR (const_t) *curr_ccp_vals;

static bitmap_t curr_ccp_varying, curr_ccp_unknown;

static void setup_curr_ccp_vals (size_t var) {
  var_const_t vc;

  assert (! bitmap_bit_p (ccp_dst->ccp_varying_in, var)
	  && ! bitmap_bit_p (ccp_dst->ccp_unknown_in, var));
  if (! find_var_const (ccp_dst, TRUE, var, &vc))
    assert (FALSE);
  VARR_SET (const_t, curr_ccp_vals, var, vc.val);
}

static void update_curr_ccp_vals (size_t var) {
  var_const_t vc;
  const_t val;

  if (! bitmap_bit_p (curr_ccp_varying, var) && ! bitmap_bit_p (curr_ccp_unknown, var)
      && (bitmap_bit_p (ccp_dst->ccp_varying_out, var)
	  || bitmap_bit_p (ccp_dst->ccp_unknown_out, var))) {
    assert (! find_var_const (ccp_dst, FALSE, var, &vc));
    ccp_trans_func_change_p = TRUE;
    insert_var_const (ccp_dst, FALSE, var, VARR_GET (const_t, curr_ccp_vals, var));
    return;
  }
  if (! bitmap_bit_p (ccp_dst->ccp_varying_out, var)
      && ! bitmap_bit_p (ccp_dst->ccp_unknown_out, var)
      && (bitmap_bit_p (curr_ccp_varying, var) || bitmap_bit_p (curr_ccp_unknown, var))) {
    assert (find_var_const (ccp_dst, FALSE, var, &vc));
    ccp_trans_func_change_p = TRUE;
    delete_var_const (ccp_dst, FALSE, var);
    return;
  }
#ifndef NDEBUG
  if (! find_var_const (ccp_dst, FALSE, var, &vc))
    assert (FALSE);
  val = VARR_GET (const_t, curr_ccp_vals, var);
  assert (vc.val.uns_p == val.uns_p /* value change can happen only on a joint point */
	  && ((vc.val.uns_p && vc.val.u.u == val.u.u)
	      || (! vc.val.uns_p && vc.val.u.i == val.u.i)));
#endif
}

static int get_var (MIR_insn_t insn, size_t nop, MIR_reg_t *var) {
  MIR_op_t op = insn->ops[nop];
  
  if (op.mode != MIR_OP_HARD_REG && op.mode != MIR_OP_REG)
    return TRUE;
  *var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
  return FALSE;
}

enum ccp_val_kind {CCP_CONST = 0, CCP_VARYING, CCP_UNKNOWN};

static enum ccp_val_kind get_op (MIR_insn_t insn, size_t nop, const_t *val) {
  MIR_reg_t var;
  MIR_op_t op;
  
  if (get_var (insn, nop, &var)) {
    if ((op = insn->ops[nop]).mode == MIR_OP_INT) {
      val->uns_p = FALSE; val->u.i = op.u.i;
      return CCP_CONST;
    } else if (op.mode == MIR_OP_UINT) {
      val->uns_p = TRUE; val->u.u = op.u.u;
      return CCP_CONST;
    }
    return CCP_VARYING;
  }
  if (bitmap_bit_p (curr_ccp_varying, var))
    return CCP_VARYING;
  else if (bitmap_bit_p (curr_ccp_unknown, var))
    return CCP_UNKNOWN;
  *val = VARR_GET (const_t, curr_ccp_vals, var);
  return CCP_CONST;
}

static enum ccp_val_kind get_2ops (MIR_insn_t insn, MIR_reg_t *var, const_t *val1) {
  if (var != NULL && get_var (insn, 0, var))
    return CCP_UNKNOWN;
  return get_op (insn, 1, val1);
}

static enum ccp_val_kind get_3ops (MIR_insn_t insn, MIR_reg_t *var, const_t *val1, const_t *val2) {
  enum ccp_val_kind res1, res2;
  
  if (var != NULL && get_var (insn, 0, var))
    return CCP_UNKNOWN;
  if ((res1 = get_op (insn, 1, val1)) == CCP_VARYING)
    return CCP_VARYING;
  if ((res2 = get_op (insn, 2, val2)) == CCP_VARYING)
    return CCP_VARYING;
  return res1 == CCP_UNKNOWN || res2 == CCP_UNKNOWN ? CCP_UNKNOWN : CCP_CONST;
}

static enum ccp_val_kind get_2iops (MIR_insn_t insn, int64_t *p, MIR_reg_t *var) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, var, &val)))
    return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_2isops (MIR_insn_t insn, int32_t *p, MIR_reg_t *var) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, var, &val)))
    return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_2usops (MIR_insn_t insn, uint32_t *p, MIR_reg_t *var) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, var, &val)))
    return res;
  *p = val.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3iops (MIR_insn_t insn, int64_t *p1, int64_t *p2, MIR_reg_t *var) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, var, &val1, &val2)))
    return res;
  *p1 = val1.u.i; *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3isops (MIR_insn_t insn, int32_t *p1, int32_t *p2, MIR_reg_t *var) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, var, &val1, &val2)))
    return res;
  *p1 = val1.u.i; *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3uops (MIR_insn_t insn, uint64_t *p1, uint64_t *p2, MIR_reg_t *var) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, var, &val1, &val2)))
    return res;
  *p1 = val1.u.u; *p2 = val2.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3usops (MIR_insn_t insn, uint32_t *p1, uint32_t *p2, MIR_reg_t *var) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, var, &val1, &val2)))
    return res;
  *p1 = val1.u.u; *p2 = val2.u.u;
  return CCP_CONST;
}

#define IOP2(op) do { int64_t p;			 			\
    if ((ccp_res = get_2iops (insn, &p, &var)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = op p;	  	 	 			\
  } while (0)

#define IOP2S(op) do { int32_t p;		  	 			\
    if ((ccp_res = get_2isops (insn, &p, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = op p;	  	 	 			\
  } while (0)

#define UOP2S(op) do { uint32_t p;		  	 			\
    if ((ccp_res = get_2usops (insn, &p, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.u = op p;	  	 	 			\
  } while (0)

#define IOP3(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define IOP3S(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UOP3(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const;	\
    val.uns_p = TRUE; val.u.u = p1 op p2;	  	 				\
  } while (0)

#define UOP3S(op) do { uint32_t p1, p2;		  	 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = TRUE; val.u.u = p1 op p2;	  	 				\
  } while (0)

#define IOP30(op) do { const_t val;			 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const;	\
    IOP3(op);											\
  } while (0)

#define IOP3S0(op) do { const_t val;			 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const;	\
    IOP3S(op);											\
  } while (0)

#define UOP30(op) do { const_t val;			 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const;	\
    UOP3(op);											\
  } while (0)

#define UOP3S0(op) do { const_t val;			 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const;	\
    UOP3S(op);											\
  } while (0)

#define ICMP(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define ICMPS(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UCMP(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UCMPS(op) do { uint32_t p1, p2;		  	 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, &var)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BICMP(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, NULL)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BICMPS(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, NULL)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BUCMP(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, NULL)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BUCMPS(op) do { uint32_t p1, p2;		 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, NULL)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

static int ccp_insn_update (MIR_insn_t insn, const_t *res) {
  size_t i, nops;
  MIR_reg_t var;
  MIR_op_t op;
  int out_p;
  enum ccp_val_kind ccp_res;
  const_t val;
  
  switch (insn->code) {
  case MIR_MOV:  IOP2(+); break;
  case MIR_S2I:  IOP2S(+); break;
  case MIR_US2I: UOP2S(+); break;
      
  case MIR_NEG:  IOP2(-); break;
  case MIR_NEGS: IOP2S(-); break;
      
  case MIR_ADD:  IOP3(+); break;
  case MIR_ADDS: IOP3S(+); break;
      
  case MIR_SUB:  IOP3(-); break; 
  case MIR_SUBS: IOP3S(-); break; 
      
  case MIR_MUL:   IOP3(*); break;
  case MIR_MULS:  IOP3S(*); break;
  case MIR_UMUL:  UOP3(*); break;
  case MIR_UMULS: UOP3S(*); break;

  case MIR_DIV:   IOP30(/); break;
  case MIR_DIVS:  IOP3S0(/); break;
  case MIR_UDIV:  UOP30(/); break;
  case MIR_UDIVS: UOP3S0(/); break;

  case MIR_MOD:   IOP30(%); break;
  case MIR_MODS:  IOP3S0(%); break;
  case MIR_UMOD:  UOP30(%); break;
  case MIR_UMODS: UOP3S0(%); break;

  case MIR_AND:  IOP3(&); break;
  case MIR_ANDS: IOP3S(&); break;
  case MIR_OR:   IOP3(|); break;
  case MIR_ORS:  IOP3S(|); break;
  case MIR_XOR:  IOP3(^); break;
  case MIR_XORS: IOP3S(^); break;

  case MIR_LSH:   IOP3(<<); break;
  case MIR_LSHS:  IOP3S(<<); break;
  case MIR_RSH:   IOP3(>>); break;
  case MIR_RSHS:  IOP3S(>>); break;
  case MIR_URSH:  UOP3(>>); break;
  case MIR_URSHS: UOP3S(>>); break;
    
  case MIR_EQ:  ICMP(=); break;
  case MIR_EQS: ICMPS(=); break;
  case MIR_NE:  ICMP(!=); break;
  case MIR_NES: ICMPS(!=); break;

  case MIR_LT:   ICMP(<); break;
  case MIR_LTS:  ICMPS(<); break;
  case MIR_ULT:  UCMP(<); break;
  case MIR_ULTS: UCMPS(<); break;
  case MIR_LE:   ICMP(<=); break;
  case MIR_LES:  ICMPS(<=); break;
  case MIR_ULE:  UCMP(<=); break;
  case MIR_ULES: UCMPS(<=); break;
  case MIR_GT:   ICMP(>); break;
  case MIR_GTS:  ICMPS(>); break;
  case MIR_UGT:  UCMP(>); break;
  case MIR_UGTS: UCMPS(>); break;
  case MIR_GE:   ICMP(>=); break;
  case MIR_GES:  ICMPS(>=); break;
  case MIR_UGE:  UCMP(>=); break;
  case MIR_UGES: UCMPS(>=); break;
      
  default: ccp_res = CCP_VARYING; goto non_const;
  }
  bitmap_clear_bit_p (curr_ccp_varying, var);
  bitmap_clear_bit_p (curr_ccp_unknown, var);
  VARR_SET (const_t, curr_ccp_vals, var, val);
  if (res != NULL)
    *res = val;
  return TRUE;
 non_const:
  if (ccp_res == CCP_UNKNOWN)
    return FALSE;
  nops = MIR_insn_nops (insn->code);
  for (i = 0; i < nops; i++) {
    op = insn->ops[i];
    MIR_insn_op_mode (insn->code, i, &out_p);
    if (! out_p || (op.mode != MIR_OP_HARD_REG && op.mode != MIR_OP_REG))
      continue;
    var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
    bitmap_set_bit_p (curr_ccp_varying, var);
    bitmap_clear_bit_p (curr_ccp_unknown, var);
  }
  return FALSE;
}

static enum ccp_val_kind ccp_branch_update (MIR_insn_t insn, int *res) {
  enum ccp_val_kind ccp_res;
  const_t val;
  
  switch (insn->code) {
  case MIR_BT: case MIR_BF:
    if ((ccp_res = get_op (insn, 1, &val)) != CCP_CONST)
      return ccp_res;
    *res = val.uns_p ? val.u.u != 0 : val.u.i != 0;
    if (insn->code == MIR_BF)
      *res = ! *res;
    return CCP_CONST;
  case MIR_BEQ:  BICMP(=); break;
  case MIR_BEQS: BICMPS(=); break;
  case MIR_BNE:  BICMP(!=); break;
  case MIR_BNES: BICMPS(!=); break;

  case MIR_BLT:   BICMP(<); break;
  case MIR_BLTS:  BICMPS(<); break;
  case MIR_UBLT:  BUCMP(<); break;
  case MIR_UBLTS: BUCMPS(<); break;
  case MIR_BLE:   BICMP(<=); break;
  case MIR_BLES:  BICMPS(<=); break;
  case MIR_UBLE:  BUCMP(<=); break;
  case MIR_UBLES: BUCMPS(<=); break;
  case MIR_BGT:   BICMP(>); break;
  case MIR_BGTS:  BICMPS(>); break;
  case MIR_UBGT:  BUCMP(>); break;
  case MIR_UBGTS: BUCMPS(>); break;
  case MIR_BGE:   BICMP(>=); break;
  case MIR_BGES:  BICMPS(>=); break;
  case MIR_UBGE:  BUCMP(>=); break;
  case MIR_UBGES: BUCMPS(>=); break;
      
  default:
    assert (FALSE);
  }
  *res = val.u.i;
  return CCP_CONST;
 non_const:
  return ccp_res;
}

static void setup_curr_ccp_bb_data (bb_t bb) {
  const_t val;
  
  ccp_dst = bb;
  bitmap_copy (curr_ccp_varying, bb->ccp_varying_in);
  bitmap_copy (curr_ccp_unknown, bb->ccp_unknown_in);
  bitmap_and_compl (temp_bitmap, all_vars, bb->ccp_unknown_in);
  bitmap_and_compl (temp_bitmap, temp_bitmap, bb->ccp_varying_in);
  VARR_TRUNC (const_t, curr_ccp_vals, 0);
  val.uns_p = FALSE; val.u.i = 0;
  while (VARR_LENGTH (const_t, curr_ccp_vals) != get_nvars ())
    VARR_PUSH (const_t, curr_ccp_vals, val);
  bitmap_for_each (temp_bitmap, setup_curr_ccp_vals);
}

static int ccp_trans_func (bb_t bb) {
  bb_insn_t bb_insn;
  MIR_insn_t insn;
  edge_t e;
  enum ccp_val_kind ccp_res;
  int res;
  
  setup_curr_ccp_bb_data (bb);
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
       bb_insn != NULL;
       bb_insn = DLIST_NEXT (bb_insn_t, bb_insn))
    ccp_insn_update (bb_insn->insn, NULL);
  ccp_trans_func_change_p = FALSE;
  if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) != NULL) {
    insn = bb_insn->insn;
    if (MIR_branch_code_p (insn->code) && insn->code != MIR_JMP) {
      if ((ccp_res = ccp_branch_update (insn, &res)) == CCP_CONST) {
	/* Remember about an edge to exit bb.  First edge is always for
	   fall through and 2nd edge is for jump bb. */
	assert (DLIST_LENGTH (out_edge_t, bb->out_edges) >= 2);
	e = res ? DLIST_EL (out_edge_t, bb->out_edges, 1) : DLIST_EL (out_edge_t, bb->out_edges, 0);
	if (e->skipped_p)
	  ccp_trans_func_change_p = TRUE;
	e->skipped_p = FALSE;
      } else if (ccp_res == CCP_VARYING) {
	for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
	  e->skipped_p = FALSE;
	ccp_trans_func_change_p = TRUE;
      }
    }
  }
  ccp_trans_func_change_p |= ! bitmap_equal_p (bb->ccp_varying_out, curr_ccp_varying);
  ccp_trans_func_change_p |= ! bitmap_equal_p (bb->ccp_unknown_out, curr_ccp_unknown);
  bitmap_and_compl (temp_bitmap, all_vars, bb->ccp_unknown_out);
  bitmap_and_compl (temp_bitmap, temp_bitmap, bb->ccp_varying_out);
  bitmap_and_compl (temp_bitmap2, all_vars, curr_ccp_unknown);
  bitmap_ior_and_compl (temp_bitmap, temp_bitmap, temp_bitmap2, curr_ccp_varying);
  bitmap_for_each (temp_bitmap, update_curr_ccp_vals);
  bitmap_copy (bb->ccp_varying_out, curr_ccp_varying);
  bitmap_copy (bb->ccp_unknown_out, curr_ccp_unknown);
  return ccp_trans_func_change_p;
}

static void initiate_bb_ccp_info (bb_t bb) {
  MIR_reg_t nvars = get_nvars ();
  int param_p;
  
  assert (bb->ccp_unknown_in != NULL && bb->ccp_unknown_out != NULL
	  && bb->ccp_varying_in != NULL && bb->ccp_varying_out != NULL);
  bitmap_clear (bb->ccp_unknown_in); bitmap_clear (bb->ccp_unknown_out);
  bitmap_clear (bb->ccp_varying_in); bitmap_clear (bb->ccp_varying_out);
  for (MIR_reg_t var = 0; var < nvars; var++) {
    param_p = var_is_reg_p (var) && var2reg (var) <= curr_func_item->u.func->nargs;
    bitmap_set_bit_p (param_p ? bb->ccp_varying_in : bb->ccp_unknown_in, var);
    bitmap_set_bit_p (param_p ? bb->ccp_varying_out : bb->ccp_unknown_out, var);
  }
}

static void initiate_ccp_info (void) {
  MIR_reg_t nvars = get_nvars ();
  bb_insn_t bb_insn;
  
  bitmap_clear (all_vars);
  for (MIR_reg_t var = 0; var < nvars; var++)
    bitmap_set_bit_p (all_vars, var);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    initiate_bb_ccp_info (bb);
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) != NULL
	&& MIR_branch_code_p (bb_insn->insn->code) && bb_insn->insn->code != MIR_JMP) {
      for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges);
	   e != NULL;
	   e = DLIST_NEXT (out_edge_t, e))
	if (DLIST_HEAD (out_edge_t, e->dst->out_edges) != NULL) /* ignore exit bb */
	  e->skipped_p = TRUE;
    }
  }
  HTAB_CLEAR (var_const_t, var_const_tab);
}

static void ccp_traverse (bb_t bb) {
  bb->reachable_p = TRUE;
  for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    if (! e->skipped_p && ! e->dst->reachable_p)
      ccp_traverse (e->dst);
}

static void ccp_modify (void) {
  bb_t bb, next_bb;
  bb_insn_t bb_insn, next_bb_insn;
  const_t val;
  MIR_op_t op;
  MIR_insn_t insn;
  int res;
  
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    bb->reachable_p = FALSE;
  ccp_traverse (DLIST_HEAD (bb_t, curr_cfg->bbs)); /* entry */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    if (! bb->reachable_p) {
#if MIR_GEN_DEBUG
      fprintf (debug_file, "  deleting unreachable bb %d and its edges\n", bb->index);
#endif
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
	next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
	MIR_remove_insn (curr_func_item, bb_insn->insn);
	delete_bb_insn (bb_insn);
      }
      delete_bb (bb);
      continue;
    }
    setup_curr_ccp_bb_data (bb);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (ccp_insn_update (bb_insn->insn, &val)
	  && (bb_insn->insn->code != MIR_MOV || (bb_insn->insn->ops[1].mode != MIR_OP_INT
						 && bb_insn->insn->ops[1].mode != MIR_OP_UINT))) {
#if MIR_GEN_DEBUG
	fprintf (debug_file, "  changing insn ");
	MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func);
#endif
	op = val.uns_p ? MIR_new_uint_op (val.u.u) : MIR_new_int_op (val.u.i);
	insn = MIR_new_insn (MIR_MOV, bb_insn->insn->ops[0], op); /* result is always 0-th op */
	MIR_insert_insn_before (curr_func_item, bb_insn->insn, insn);
	MIR_remove_insn (curr_func_item, bb_insn->insn);
	insn->data = bb_insn;
	bb_insn->insn = insn;
#if MIR_GEN_DEBUG
	fprintf (debug_file, "    on insn ");
	MIR_output_insn (debug_file, insn, curr_func_item->u.func);
#endif
      }
    }
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL)
      continue;
    insn = bb_insn->insn;
    if (! MIR_branch_code_p (insn->code) || insn->code == MIR_JMP
	|| ccp_branch_update (insn, &res) != CCP_CONST)
      continue;
    if (! res) {
#if MIR_GEN_DEBUG
      fprintf (debug_file, "  removing branch insn ");
      MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func);
      fprintf (debug_file, "\n");
#endif
      MIR_remove_insn (curr_func_item, bb_insn->insn);
      delete_bb_insn (bb_insn);
      delete_edge (DLIST_EL (out_edge_t, bb->out_edges, 1));
    } else {
      insn = MIR_new_insn (MIR_JMP, bb_insn->insn->ops[0]); /* label is always 0-th op */
#if MIR_GEN_DEBUG
      fprintf (debug_file, "  changing branch insn ");
      MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func);
      fprintf (debug_file, " onto jump insn ");
      MIR_output_insn (debug_file, insn, curr_func_item->u.func);
      fprintf (debug_file, "\n");
#endif
      MIR_insert_insn_before (curr_func_item, bb_insn->insn, insn);
      MIR_remove_insn (curr_func_item, bb_insn->insn);
      insn->data = bb_insn;
      bb_insn->insn = insn;
      delete_edge (DLIST_EL (out_edge_t, bb->out_edges, 0));
    }
  }
}

static void ccp (void) { /* conditional constant propagation */
  initiate_ccp_info ();
  solve_dataflow (TRUE, ccp_con_func_0, ccp_con_func_n, ccp_trans_func);
  ccp_modify ();
}

#if MIR_GEN_DEBUG

static void output_constants (bb_t bb, int in_p) {
  MIR_reg_t nvars = get_nvars ();
  var_const_t vc;

  fprintf (debug_file, "  %s constants:", in_p ? "in" : "out");
  for (MIR_reg_t var = 0; var < nvars; var++)
    if (find_var_const (bb, in_p, var, &vc)) {
      output_live_element (var);
      fprintf (debug_file, "=");
      if (vc.val.uns_p)
	fprintf (debug_file, "%" PRIu64, vc.val.u.u);
      else
	fprintf (debug_file, "%" PRId64, vc.val.u.i);
    }
  fprintf (debug_file, "\n");
}

static void output_bb_ccp_info (bb_t bb) {
  output_bitmap ("  unknown_in:", bb->ccp_unknown_in);
  output_bitmap ("  unknown_out:", bb->ccp_unknown_out);
  output_bitmap ("  varying_in:", bb->ccp_varying_in);
  output_bitmap ("  varying_out:", bb->ccp_varying_out);
  output_constants (bb, TRUE); output_constants (bb, FALSE);
}

#endif

#undef ccp_unknown_in
#undef ccp_unknown_out
#undef ccp_varying_in
#undef ccp_varying_out



#define live_in in
#define live_out out
#define live_kill kill
#define live_gen gen

/* Life analysis */
static void live_con_func_0 (bb_t bb) { bitmap_clear (bb->live_in); }

static int live_con_func_n (bb_t bb) {
  edge_t e;
  int change_p = FALSE;
  
  for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    change_p |= bitmap_ior (bb->live_out, bb->live_out, e->dst->live_in);
  return change_p;
}

static int live_trans_func (bb_t bb) {
  return bitmap_ior_and_compl (bb->live_in, bb->live_gen, bb->live_out, bb->live_kill);
}

static void initiate_bb_live_info (bb_t bb) {
  MIR_insn_t insn;
  size_t nops, i, niter;
  MIR_reg_t nregs, n;
  MIR_op_t op;
  int out_p;
  mv_t mv, next_mv;
  reg_info_t *breg_infos;
  
  assert (bb->live_in != NULL && bb->live_out != NULL
	  && bb->live_gen != NULL && bb->live_kill != NULL);
  bitmap_clear (bb->live_in); bitmap_clear (bb->live_out);
  bitmap_clear (bb->live_gen); bitmap_clear (bb->live_kill);
  for (mv = DLIST_HEAD (mv_t, curr_cfg->used_moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free_move (mv);
  }
  VARR_TRUNC (reg_info_t, curr_cfg->breg_info, 0);
  nregs = get_nregs ();
  for (n = 0; n < nregs; n++) {
    reg_info_t ri;

    ri.freq = ri.calls_num = 0;
    DLIST_INIT (dst_mv_t, ri.dst_moves);
    DLIST_INIT (src_mv_t, ri.src_moves);
    VARR_PUSH (reg_info_t, curr_cfg->breg_info, ri);
  }
  breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  for (bb_insn_t bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
       bb_insn != NULL;
       bb_insn = DLIST_PREV (bb_insn_t, bb_insn)) {
    insn = bb_insn->insn;
    nops = MIR_insn_nops (insn->code);
    /* Process output ops on the first iteration, then input ops. */
    for (niter = 0; niter <= 1; niter++) {
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	switch (op.mode) {
	case MIR_OP_REG:
	  if (! out_p && niter != 0)
	    bitmap_set_bit_p (bb->live_gen, reg2var (op.u.reg));
	  else if (niter == 0) {
	    bitmap_clear_bit_p (bb->live_gen, reg2var (op.u.reg));
	    bitmap_set_bit_p (bb->live_kill, reg2var (op.u.reg));
	  }
	  breg_infos[reg2breg (op.u.reg)].freq++;
	  break;
	case MIR_OP_HARD_REG:
	  if (! out_p && niter != 0)
	    bitmap_set_bit_p (bb->live_gen, op.u.hard_reg);
	  else if (niter == 0) {
	    bitmap_clear_bit_p (bb->live_gen, op.u.hard_reg);
	    bitmap_set_bit_p (bb->live_kill, op.u.hard_reg);
	  }
	  break;
	case MIR_OP_MEM:
	  if (niter == 0)
	    break;
	  if (op.u.mem.base != 0) {
	    bitmap_set_bit_p (bb->live_gen, reg2var (op.u.mem.base));
	    breg_infos[reg2breg (op.u.mem.base)].freq++;
	  }
	  if (op.u.mem.index != 0) {
	    bitmap_set_bit_p (bb->live_gen, reg2var (op.u.mem.index));
	    breg_infos[reg2breg (op.u.mem.index)].freq++;
	  }
	  break;
	case MIR_OP_HARD_REG_MEM:
	  if (niter == 0)
	    break;
	  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
	    bitmap_set_bit_p (bb->live_gen, op.u.hard_reg_mem.base);
	  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
	    bitmap_set_bit_p (bb->live_gen, op.u.hard_reg_mem.index);
	  break;
	default: /* do nothing */
	  break;
	}
      }
    }
    if (insn->code == MIR_CALL || insn->code == MIR_CALL_C) {
      bitmap_ior (bb->live_kill, bb->live_kill, call_used_hard_regs);
      bitmap_and_compl (bb->live_gen, bb->live_gen, call_used_hard_regs);
      bitmap_ior (bb->live_gen, bb->live_gen, bb_insn->call_hard_reg_args);
    }
    if (move_p (insn)) {
      mv = get_free_move ();
      mv->bb_insn = bb_insn;
      if (insn->ops[0].mode == MIR_OP_REG)
	DLIST_APPEND (dst_mv_t, breg_infos[reg2breg (insn->ops[0].u.reg)].dst_moves, mv);
      if (insn->ops[1].mode == MIR_OP_REG)
	DLIST_APPEND (src_mv_t, breg_infos[reg2breg (insn->ops[1].u.reg)].src_moves, mv);
    }
  }
}

static void initiate_live_info (void) {
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    initiate_bb_live_info (bb);
}

void calculate_func_cfg_live_info (void) {
  initiate_live_info ();
  solve_dataflow (FALSE, live_con_func_0, live_con_func_n, live_trans_func);
}

typedef struct live_range *live_range_t; /* vars */

struct live_range {
  int start, finish;
  live_range_t next;
};

static int curr_point;
static bitmap_t live_vars;

DEF_VARR (live_range_t);

static VARR (live_range_t) *var_live_ranges;

static live_range_t create_live_range (int start, int finish, live_range_t next) {
  live_range_t lr = gen_malloc (sizeof (struct live_range));

  assert (finish < 0 || start <= finish);
  lr->start = start; lr->finish = finish; lr->next = next;
  return lr;
}

static void destroy_live_range (live_range_t lr) {
  live_range_t next_lr;
  
  for (; lr != NULL; lr = next_lr) {
    next_lr = lr->next;
    free (lr);
  }
}

static int make_var_dead (MIR_reg_t var, int point) {
  live_range_t lr;

  if (! bitmap_clear_bit_p (live_vars, var))
    return FALSE;
  lr = VARR_GET (live_range_t, var_live_ranges, var); lr->finish = point;
  return TRUE;
}

static int make_var_live (MIR_reg_t var, int point) {
  live_range_t lr;

  if (! bitmap_set_bit_p (live_vars, var))
    return FALSE;
  if ((lr = VARR_GET (live_range_t, var_live_ranges, var)) == NULL
      || (lr->finish != point && lr->finish + 1 != point))
    VARR_SET (live_range_t, var_live_ranges, var, create_live_range (point, -1, lr));
  return TRUE;
}

static int make_reg_dead (MIR_reg_t reg, int hard_reg_p, int point) {
  return make_var_dead (hard_reg_p ? reg : reg2var (reg), point);
}

static int make_reg_live (MIR_reg_t reg, int hard_reg_p, int point) {
  return make_var_live (hard_reg_p ? reg : reg2var (reg), point);
}

static void make_live (size_t nb) { make_var_live (nb, curr_point); }
static void make_dead (size_t nb) { make_var_dead (nb, curr_point); }

static void make_live_through_call (size_t nb) {
  reg_info_t *bri;
  MIR_reg_t breg;
  
  if (! var_is_reg_p (nb))
    return;
  breg = reg2breg (var2reg (nb));
  bri = &VARR_ADDR (reg_info_t, curr_cfg->breg_info)[breg];
  bri->calls_num++;
}

#if MIR_GEN_DEBUG
static void print_live_ranges (void) {
  size_t i;
  live_range_t lr;
  
  fprintf (debug_file, "+++++++++++++Live ranges:\n");
  assert (get_nvars () == VARR_LENGTH (live_range_t, var_live_ranges));
  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    if ((lr = VARR_GET (live_range_t, var_live_ranges, i)) == NULL)
      continue;
    fprintf (debug_file, "%lu", i);
    if (var_is_reg_p (i))
      fprintf (debug_file, " (%s)", MIR_reg_name (var2reg (i), curr_func_item->u.func));
    fprintf (debug_file, ":");
    for (; lr != NULL; lr = lr->next)
      fprintf (debug_file, " [%d..%d]", lr->start, lr->finish);
    fprintf (debug_file, "\n");
  }
}
#endif

static void build_live_ranges (void) {
  MIR_insn_t insn;
  MIR_reg_t nvars;
  size_t i, nops;
  int incr_p, out_p;
  MIR_op_t op;
  
  curr_point = 0;
  nvars = get_nvars ();
  assert (VARR_LENGTH (live_range_t, var_live_ranges) == 0);
  for (i = 0; i < nvars; i++)
    VARR_PUSH (live_range_t, var_live_ranges, NULL);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
#if MIR_GEN_DEBUG
    fprintf (debug_file, "  ------BB%u end: point=%d\n", (unsigned) bb->index, curr_point);
#endif
    bitmap_clear (live_vars);
    if (bb->live_out != NULL)
      bitmap_for_each (bb->live_out, make_live);
    for (bb_insn_t bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_PREV (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
#if MIR_GEN_DEBUG
      fprintf (debug_file, "  p%-5d", curr_point);
      MIR_output_insn (debug_file, insn, curr_func_item->u.func);
#endif
      nops = MIR_insn_nops (insn->code);
      incr_p = FALSE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (op.mode == MIR_OP_REG && out_p)
	  incr_p |= make_reg_dead (op.u.reg, FALSE, curr_point);
	else if (op.mode == MIR_OP_HARD_REG && out_p)
	  incr_p |= make_reg_dead (op.u.hard_reg, TRUE, curr_point);
      }
      if (insn->code == MIR_CALL || insn->code == MIR_CALL_C) {
	bitmap_for_each (call_used_hard_regs, make_dead);
	bitmap_for_each (bb_insn->call_hard_reg_args, make_live);
	bitmap_for_each (live_vars, make_live_through_call);
      }
      if (incr_p)
	curr_point++;
      incr_p = FALSE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	switch (op.mode) {
	case MIR_OP_REG:
	  MIR_insn_op_mode (insn->code, i, &out_p);
	  if (! out_p)
	    incr_p |= make_reg_live (op.u.reg, FALSE, curr_point);
	  break;
	case MIR_OP_HARD_REG:
	  MIR_insn_op_mode (insn->code, i, &out_p);
	  if (! out_p)
	    incr_p |= make_reg_live (op.u.hard_reg, TRUE, curr_point);
	  break;
	case MIR_OP_MEM:
	  if (op.u.mem.base != 0)
	    incr_p |= make_reg_live (op.u.mem.base, FALSE, curr_point);
	  if (op.u.mem.index != 0)
	    incr_p |= make_reg_live (op.u.mem.index, FALSE, curr_point);
	  break;
	case MIR_OP_HARD_REG_MEM:
	  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
	    incr_p |= make_reg_live (op.u.hard_reg_mem.base, TRUE, curr_point);
	  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
	    incr_p |= make_reg_live (op.u.hard_reg_mem.index, TRUE, curr_point);
	  break;
	default: /* do nothing */
	  break;
	}
	if (incr_p)
	  curr_point++;
      }
    }
    assert (bitmap_equal_p (live_vars, bb->live_in));
    bitmap_for_each (live_vars, make_dead);
    if (! bitmap_empty_p (bb->live_in))
      curr_point++;
  }
#if MIR_GEN_DEBUG
  print_live_ranges ();
#endif
}

static void destroy_func_live_ranges (void) {
  size_t i;
  
  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++)
    destroy_live_range (VARR_GET (live_range_t, var_live_ranges, i));
  VARR_TRUNC (live_range_t, var_live_ranges, 0);
}

#if MIR_GEN_DEBUG
static void output_bb_live_info (bb_t bb) {
  output_bitmap ("  live_in:", bb->live_in); output_bitmap ("  live_out:", bb->live_out);
  output_bitmap ("  live_gen:", bb->live_gen); output_bitmap ("  live_kill:", bb->live_kill);
}
#endif

#undef live_in
#undef live_out
#undef live_kill
#undef live_gen



/* Register allocation */

DEF_VARR (MIR_reg_t);

static VARR (MIR_reg_t) *breg_renumber;

static VARR (MIR_reg_t) *sorted_bregs;

static VARR (bitmap_t) *point_used_locs;
  
static bitmap_t conflict_locs;

static reg_info_t *curr_breg_infos;

static int breg_info_compare_func (const void *a1, const void *a2) {
  MIR_reg_t br1 = *(const MIR_reg_t *) a1, br2 = *(const MIR_reg_t *) a2;

  return ((int) curr_breg_infos[br2].freq - (int) curr_breg_infos[br1].freq);
}

DEF_VARR (size_t);

static VARR (size_t) *loc_profits;
static VARR (size_t) *loc_profit_ages;

static size_t curr_age;

static void setup_loc_profit_from_op (MIR_op_t op) {
  MIR_reg_t loc;
  size_t *curr_loc_profits = VARR_ADDR (size_t, loc_profits);
  size_t *curr_loc_profit_ages = VARR_ADDR (size_t, loc_profit_ages);

  if (op.mode == MIR_OP_HARD_REG)
    loc = op.u.hard_reg;
  else if ((loc = VARR_GET (MIR_reg_t, breg_renumber, reg2breg (op.u.reg))) == MIR_NON_HARD_REG)
    return;
  if (curr_loc_profit_ages[loc] == curr_age)
    curr_loc_profits[loc]++; /* should be freq */
  else {
    curr_loc_profit_ages[loc] = curr_age;
    curr_loc_profits[loc] = 1; /* should be freq */
  }
}

static void setup_loc_profits (MIR_reg_t breg) {
  mv_t mv;
  
  for (mv = DLIST_HEAD (dst_mv_t, curr_breg_infos[breg].dst_moves); mv != NULL; mv = DLIST_NEXT (dst_mv_t, mv))
    setup_loc_profit_from_op (mv->bb_insn->insn->ops[1]);
  for (mv = DLIST_HEAD (src_mv_t, curr_breg_infos[breg].src_moves); mv != NULL; mv = DLIST_NEXT (src_mv_t, mv))
    setup_loc_profit_from_op (mv->bb_insn->insn->ops[1]);
}

static size_t func_stack_slots_num;
static bitmap_t func_assigned_hard_regs;

static void assign (void) {
  MIR_reg_t loc, best_loc, i, reg, breg, var, nregs = get_nregs ();
  int j;
  live_range_t lr;
  bitmap_t bm;
  size_t profit, best_profit;
  bitmap_t *point_used_locs_addr;
  MIR_reg_t fp_reg = MIR_func_reg (FP_NAME, curr_func_item->u.func);
  
  if (nregs == 0)
    return;
  curr_breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  VARR_TRUNC (MIR_reg_t, breg_renumber, 0);
  for (i = 0; i < nregs; i++)
    VARR_PUSH (MIR_reg_t, breg_renumber, MIR_NON_HARD_REG);
  VARR_SET (MIR_reg_t, breg_renumber, reg2breg (fp_reg), HARD_REG_FRAME_POINTER);
  /* min_reg, max_reg for func */
  VARR_TRUNC (MIR_reg_t, sorted_bregs, 0);
  for (i = 0; i < nregs; i++)
    VARR_PUSH (MIR_reg_t, sorted_bregs, i);
  VARR_TRUNC (size_t, loc_profits, 0);
  VARR_TRUNC (size_t, loc_profit_ages, 0);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (size_t, loc_profits, 0);
    VARR_PUSH (size_t, loc_profit_ages, 0);
  }
  for (i = 0; i <= curr_point; i++) {
    bm = bitmap_create2 (MAX_HARD_REG + 1);
    VARR_PUSH (bitmap_t, point_used_locs, bm);
  }
  qsort (VARR_ADDR (MIR_reg_t, sorted_bregs), nregs, sizeof (MIR_reg_t), breg_info_compare_func);
  curr_age = 0;
  point_used_locs_addr = VARR_ADDR (bitmap_t, point_used_locs);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
	bitmap_set_bit_p (point_used_locs_addr[j], i);
  }
  func_stack_slots_num = 0;
  bitmap_clear (func_assigned_hard_regs);
  for (i = 0; i < nregs; i++) {
    breg = VARR_GET (MIR_reg_t, sorted_bregs, i);
    if (VARR_GET (MIR_reg_t, breg_renumber, breg) != MIR_NON_HARD_REG)
      continue;
    reg = breg2reg (breg);
    var = reg2var (reg);
    bitmap_clear (conflict_locs);
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
	for (j = lr->start; j <= lr->finish; j++)
	  bitmap_ior (conflict_locs, conflict_locs, point_used_locs_addr[j]);
    curr_age++;
    setup_loc_profits (breg);
    best_loc = MIR_NON_HARD_REG; best_profit = 0;
    for (loc = 0; loc <= func_stack_slots_num + MAX_HARD_REG; loc++) {
      if ((loc <= MAX_HARD_REG
	   && (fixed_hard_reg_p (loc)
	       || ! hard_reg_type_ok_p (loc, MIR_reg_type (reg, curr_func_item->u.func))
	       || (call_used_hard_reg_p (loc) && curr_breg_infos[breg].calls_num > 0)))
	  || bitmap_bit_p (conflict_locs, loc))
	continue;
      profit = VARR_GET (size_t, loc_profit_ages, loc) != curr_age ? 0 : VARR_GET (size_t, loc_profits, loc);
      if (best_loc == MIR_NON_HARD_REG || best_profit < profit) {
	best_loc = loc;
	best_profit = profit;
      }
      if (best_loc != MIR_NON_HARD_REG && loc == MAX_HARD_REG)
	break;
    }
    if (best_loc <= MAX_HARD_REG) {
      bitmap_set_bit_p (func_assigned_hard_regs, best_loc);
    } else if (best_loc == MIR_NON_HARD_REG) { /* Add stack slot */
      VARR_PUSH (size_t, loc_profits, 0);
      VARR_PUSH (size_t, loc_profit_ages, 0);
      best_loc = VARR_LENGTH (size_t, loc_profits);
      func_stack_slots_num = best_loc - MAX_HARD_REG;
    }
    VARR_SET (MIR_reg_t, breg_renumber, breg, best_loc);
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
	bitmap_set_bit_p (point_used_locs_addr[j], best_loc);
  }
  for (i = 0; i <= curr_point; i++)
    bitmap_destroy (VARR_POP (bitmap_t, point_used_locs));
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++Disposition after assignment:");
  for (i = 0; i < nregs; i++) {
    if (i % 8 == 0)
      fprintf (debug_file, "\n");
    reg = breg2reg (i);
    fprintf (debug_file, " %3u:%-2u", reg2var (reg), VARR_GET (MIR_reg_t, breg_renumber, i));
  }
  fprintf (debug_file, "\n");
#endif  
}

static MIR_reg_t change_reg (MIR_reg_t reg, MIR_op_mode_t data_mode, int first_p, bb_insn_t bb_insn, int out_p) {
  MIR_reg_t loc = VARR_GET (MIR_reg_t, breg_renumber, reg2breg (reg));
  MIR_reg_t hard_reg;
  MIR_disp_t offset;
  MIR_insn_code_t code;
  MIR_type_t type;
  MIR_insn_t insn;
  bb_insn_t new_bb_insn;
  MIR_op_t hard_reg_op, mem_op;
  
  assert (loc != MIR_NON_HARD_REG);
  if (loc <= MAX_HARD_REG)
    return loc;
  offset = get_stack_slot_offset (loc - MAX_HARD_REG - 1);
  assert (data_mode == MIR_OP_INT || data_mode == MIR_OP_FLOAT || data_mode == MIR_OP_DOUBLE);
  if (data_mode == MIR_OP_INT) {
    type = MIR_I64; code = MIR_MOV;
    hard_reg = first_p ? TEMP_INT_HARD_REG1 : TEMP_INT_HARD_REG2;
  } else if (data_mode == MIR_OP_FLOAT) {
    type = MIR_F; code = MIR_FMOV;
    hard_reg = first_p ? TEMP_FLOAT_HARD_REG1 : TEMP_FLOAT_HARD_REG2;
  } else {
    type = MIR_D; code = MIR_DMOV;
    hard_reg = first_p ? TEMP_DOUBLE_HARD_REG1 : TEMP_DOUBLE_HARD_REG2;
  }
  hard_reg_op = MIR_new_hard_reg_op (hard_reg);
  mem_op = MIR_new_hard_reg_mem_op (type, offset, BP_HARD_REG, MIR_NON_HARD_REG, 0);
  if (out_p) {
    insn = MIR_new_insn (code, mem_op, hard_reg_op);
    MIR_insert_insn_after (curr_func_item, bb_insn->insn, insn);
  } else {
    insn = MIR_new_insn (code, hard_reg_op, mem_op);
    MIR_insert_insn_before (curr_func_item, bb_insn->insn, insn);
  }
  new_bb_insn = create_bb_insn (insn, bb_insn->bb);
  if (out_p) 
    DLIST_INSERT_AFTER (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
  else
    DLIST_INSERT_BEFORE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
  return hard_reg;
}

static void rewrite (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, next_bb_insn;
  size_t nops, i;
  MIR_op_t *op;
  MIR_mem_t mem;
  MIR_op_mode_t data_mode;
  MIR_reg_t hard_reg;
  int out_p, first_in_p;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      first_in_p = TRUE;
      for (i = 0; i < nops; i++) {
	op = &insn->ops[i];
	data_mode = MIR_insn_op_mode (insn->code, i, &out_p);
	switch (op->mode) {
	case MIR_OP_REG:
	  hard_reg = change_reg (op->u.reg, data_mode, out_p || first_in_p, bb_insn, out_p);
	  if (! out_p)
	    first_in_p = FALSE;
	  op->mode = MIR_OP_HARD_REG;
	  op->u.hard_reg = hard_reg;
	  break;
	case MIR_OP_MEM:
	  mem = op->u.mem;
	  /* Always second for mov MEM[R2], R1 or mov R1, MEM[R2]. */
	  mem.base = (op->u.mem.base == 0 ? MIR_NON_HARD_REG
		      : change_reg (op->u.mem.base, data_mode, FALSE, bb_insn, out_p));
	  assert (op->u.mem.index == 0);
	  mem.index = MIR_NON_HARD_REG;
	  op->mode = MIR_OP_HARD_REG_MEM;
	  op->u.hard_reg_mem = mem;
	  break;
	default: /* do nothing */
	  break;
	}
      }
      if ((insn->code == MIR_MOV || insn->code == MIR_FMOV || insn->code == MIR_DMOV)
	  && insn->ops[0].mode == MIR_OP_HARD_REG && insn->ops[1].mode == MIR_OP_HARD_REG
	  && insn->ops[0].u.hard_reg == insn->ops[1].u.hard_reg) {
	DLIST_REMOVE (bb_insn_t, bb->bb_insns, bb_insn);
	free (bb_insn);
	DLIST_REMOVE (MIR_insn_t, curr_func_item->u.func->insns, insn);
	free (insn);
      }
    }
  }
}



/* Code selection */

struct hreg_def {
  MIR_insn_t insn;
  size_t insn_num;
  size_t nop;
};

typedef struct hreg_def hreg_def_t;

DEF_VARR (hreg_def_t);

static VARR (size_t) *hreg_def_ages;
static VARR (hreg_def_t) *hreg_defs;
static hreg_def_t *hreg_defs_addr;
static size_t *hreg_def_ages_addr;

static size_t curr_bb_hreg_def_age;

static MIR_insn_code_t commutative_insn_code (MIR_insn_t insn) {
  switch (insn->code) {
  case MIR_ADD: case MIR_FADD: case MIR_DADD:
  case MIR_MUL: case MIR_FMUL: case MIR_DMUL:
  case MIR_AND: case MIR_OR: case MIR_XOR:
  case MIR_EQ: case MIR_FEQ: case MIR_DEQ:
  case MIR_NE: case MIR_FNE: case MIR_DNE:
  case MIR_BEQ: case MIR_FBEQ: case MIR_DBEQ:
  case MIR_BNE: case MIR_FBNE: case MIR_DBNE:
    return insn->code;
    break;
  case MIR_LT: return MIR_GT;
  case MIR_ULT: return MIR_UGT;
  case MIR_FLT: return MIR_FGT;
  case MIR_DLT: return MIR_DGT;
  case MIR_LE: return MIR_GE;
  case MIR_ULE: return MIR_UGE;
  case MIR_FLE: return MIR_FGE;
  case MIR_DLE: return MIR_DGE;
  case MIR_GT: return MIR_LT;
  case MIR_UGT: return MIR_ULT;
  case MIR_FGT: return MIR_FLT;
  case MIR_DGT: return MIR_DLT;
  case MIR_GE: return MIR_LE;
  case MIR_UGE: return MIR_ULE;
  case MIR_FGE: return MIR_FLE;
  case MIR_DGE: return MIR_DLE;
  case MIR_BLT: return MIR_BGT;
  case MIR_UBLT: return MIR_UBGT;
  case MIR_FBLT: return MIR_FBGT;
  case MIR_DBLT: return MIR_DBGT;
  case MIR_BLE: return MIR_BGE;
  case MIR_UBLE: return MIR_UBGE;
  case MIR_FBLE: return MIR_FBGE;
  case MIR_DBLE: return MIR_DBGE;
  case MIR_BGT: return MIR_BLT;
  case MIR_UBGT: return MIR_UBLT;
  case MIR_FBGT: return MIR_FBLT;
  case MIR_DBGT: return MIR_DBLT;
  case MIR_BGE: return MIR_BLE;
  case MIR_UBGE: return MIR_UBLE;
  case MIR_FBGE: return MIR_FBLE;
  case MIR_DBGE: return MIR_DBLE;
  default: return MIR_INSN_BOUND;
  }
}

static int obsolete_hard_reg_op_p (MIR_op_t op, size_t def_insn_num) {
  if (op.mode == MIR_OP_HARD_REG
      && hreg_def_ages_addr[op.u.hard_reg] == curr_bb_hreg_def_age
      && hreg_defs_addr[op.u.hard_reg].insn_num > def_insn_num)
    return TRUE;
  return FALSE;
}

static int substitute_op_p (MIR_insn_t insn, size_t nop, int first_p) {
  MIR_insn_t def_insn;
  MIR_op_t src_op, op = insn->ops[nop];
  size_t def_insn_num;
  int successfull_change_p = FALSE;
  
  if (op.mode == MIR_OP_HARD_REG && hreg_def_ages_addr[op.u.hard_reg] == curr_bb_hreg_def_age) {
    def_insn = hreg_defs_addr[op.u.hard_reg].insn;
    assert (hreg_defs_addr[op.u.hard_reg].nop == 0);
    if (def_insn->code != MIR_MOV && def_insn->code != MIR_FMOV && def_insn->code != MIR_DMOV)
      return FALSE;
    insn->ops[nop] = def_insn->ops[1];
    successfull_change_p = insn_ok_p (insn);
  } else if (op.mode == MIR_OP_HARD_REG_MEM)  {
    MIR_op_t src_op2;
    int change_p = FALSE;
    
    if (!first_p && op.u.hard_reg_mem.index != MIR_NON_HARD_REG
	&& hreg_def_ages_addr[op.u.hard_reg_mem.index] == curr_bb_hreg_def_age) {
      def_insn = hreg_defs_addr[op.u.hard_reg_mem.index].insn;
      def_insn_num = hreg_defs_addr[op.u.hard_reg_mem.index].insn_num;
      assert (hreg_defs_addr[op.u.hard_reg_mem.index].nop == 0);
      src_op = def_insn->ops[1];
      if (obsolete_hard_reg_op_p (src_op, def_insn_num))
	;
      else if (def_insn->code == MIR_ADD) { /* index = r + const */
	assert (src_op.u.hard_reg != MIR_NON_HARD_REG);
	if ((src_op2 = def_insn->ops[2]).mode == MIR_OP_INT) {
	  insn->ops[nop].u.hard_reg_mem.index = src_op.u.hard_reg;
	  insn->ops[nop].u.hard_reg_mem.disp += src_op2.u.i * insn->ops[nop].u.hard_reg_mem.scale;
	  change_p = TRUE;
	}
      } else if (def_insn->code == MIR_MUL
		 && op.u.mem.scale >= 1 && op.u.mem.scale <= MIR_MAX_SCALE
		 && (src_op2 = def_insn->ops[2]).mode == MIR_OP_INT
		 && src_op2.u.i >= 1 && src_op2.u.i <= MIR_MAX_SCALE
		 && insn->ops[nop].u.hard_reg_mem.scale * src_op2.u.i <= MIR_MAX_SCALE) {
	/* index = r * const */
	assert (src_op.u.hard_reg != MIR_NON_HARD_REG && src_op2.u.i != 1);
	insn->ops[nop].u.hard_reg_mem.index = src_op.u.hard_reg;
	insn->ops[nop].u.hard_reg_mem.scale *= src_op2.u.i;
	change_p = TRUE;
      }
    } else if (first_p && op.u.hard_reg_mem.base != MIR_NON_HARD_REG
	       && hreg_def_ages_addr[op.u.hard_reg_mem.base] == curr_bb_hreg_def_age) {
      def_insn = hreg_defs_addr[op.u.hard_reg_mem.base].insn;
      def_insn_num = hreg_defs_addr[op.u.hard_reg_mem.base].insn_num;
      assert (hreg_defs_addr[op.u.hard_reg_mem.base].nop == 0);
      src_op = def_insn->ops[1];
      if (obsolete_hard_reg_op_p (src_op, def_insn_num))
	;
      else if (def_insn->code == MIR_MOV) {
	if (src_op.mode == MIR_OP_HARD_REG) { /* base = r */
	  insn->ops[nop].u.hard_reg_mem.base = src_op.u.hard_reg;
	  change_p = TRUE;
	} else if (src_op.mode == MIR_OP_INT) { /* base = const */
	  insn->ops[nop].u.hard_reg_mem.base = src_op.u.hard_reg;
	  insn->ops[nop].u.hard_reg_mem.disp += src_op.u.i;
	  change_p = TRUE;
	}
      } else if (src_op.mode != MIR_OP_HARD_REG) { /* Do nothing */
      } else if (def_insn->code == MIR_ADD) {
	assert (src_op.u.hard_reg != MIR_NON_HARD_REG);
	src_op2 = def_insn->ops[2];
	if (obsolete_hard_reg_op_p (src_op2, def_insn_num))
	  ;
	else if (src_op2.mode == MIR_OP_HARD_REG
	    && op.u.hard_reg_mem.index == MIR_NON_HARD_REG) { /* base = r1 + r2 */
	  insn->ops[nop].u.hard_reg_mem.base = src_op.u.hard_reg;
	  insn->ops[nop].u.hard_reg_mem.index = src_op2.u.hard_reg;
	  insn->ops[nop].u.hard_reg_mem.scale = 1;
	  change_p = TRUE;
	} else if (src_op2.mode == MIR_OP_INT) { /* base = r + const */
	  insn->ops[nop].u.hard_reg_mem.base = src_op.u.hard_reg;
	  insn->ops[nop].u.hard_reg_mem.disp += src_op2.u.i;
	  change_p = TRUE;
	}
      } else if (def_insn->code == MIR_MUL
		 && op.u.hard_reg_mem.index == MIR_NON_HARD_REG
		 && (src_op2 = def_insn->ops[2]).mode == MIR_OP_INT
		 && src_op2.u.i >= 1 && src_op2.u.i <= MIR_MAX_SCALE) { /* base = r * const */
	assert (src_op.u.hard_reg != MIR_NON_HARD_REG && src_op2.u.i != 1);
	insn->ops[nop].u.hard_reg_mem.base = MIR_NON_HARD_REG;
	insn->ops[nop].u.hard_reg_mem.index = src_op.u.hard_reg;
	insn->ops[nop].u.hard_reg_mem.scale = src_op2.u.i;
	change_p = TRUE;
      }
    }
    if (change_p) {
      if (insn->ops[nop].u.hard_reg_mem.base != MIR_NON_HARD_REG
	  && insn->ops[nop].u.hard_reg_mem.index != MIR_NON_HARD_REG
	  && insn->ops[nop].u.hard_reg_mem.scale == 1
	  && ! insn_ok_p (insn)) { /* swap base, index */
	MIR_reg_t temp = insn->ops[nop].u.hard_reg_mem.base;

	insn->ops[nop].u.hard_reg_mem.base = insn->ops[nop].u.hard_reg_mem.index;
	insn->ops[nop].u.hard_reg_mem.index = temp;
      }
      successfull_change_p = insn_ok_p (insn);
    }
  }
  if (! successfull_change_p)
      insn->ops[nop] = op;
  return successfull_change_p;
}

static int combine_op (MIR_insn_t insn, size_t nop) {
  int first_p, op_change_p, change_p = FALSE;
  MIR_op_t res_op = insn->ops[nop], temp_op;

  for (first_p = TRUE;; first_p = !first_p) {
    if (! (op_change_p = substitute_op_p (insn, nop, first_p)) && ! first_p)
      break;
    temp_op = insn->ops[nop];
    if (op_change_p) {
      res_op = temp_op;
      change_p = TRUE;
    }
  }
  insn->ops[nop] = res_op;
  return change_p;
}

static void combine (void) {
  MIR_insn_code_t code, new_code;
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  size_t nops, i, curr_insn_num;
  MIR_op_t temp_op, *op;
  int iter, out_p, change_p;

  hreg_defs_addr = VARR_ADDR (hreg_def_t, hreg_defs);
  hreg_def_ages_addr = VARR_ADDR (size_t, hreg_def_ages);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    curr_bb_hreg_def_age++;
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns), curr_insn_num = 0;
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn), curr_insn_num++) {
      ;
      insn = bb_insn->insn;
      code = insn->code;
      nops = MIR_insn_nops (insn->code);
      for (iter = 0; iter < 2; iter++) {
	change_p = FALSE;
	for (i = 0; i < nops; i++) {
	  MIR_insn_op_mode (insn->code, i, &out_p);
	  if ((! out_p || insn->ops[i].mode != MIR_OP_HARD_REG) && combine_op (insn, i))
	      change_p = TRUE;
	}
	if (iter == 0) {
	  if ((new_code = commutative_insn_code (insn)) == MIR_INSN_BOUND)
	    break;
	  insn->code = new_code;
	  temp_op = insn->ops[1]; insn->ops[1] = insn->ops[2]; insn->ops[2] = temp_op;
	} else if (! change_p) {
	  assert (commutative_insn_code (insn) == code);
	  insn->code = code;
	  temp_op = insn->ops[1]; insn->ops[1] = insn->ops[2]; insn->ops[2] = temp_op;
	}
      }
      
      for (i = 0; i < nops; i++) {
	op = &insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (out_p && op->mode == MIR_OP_HARD_REG) {
	  hreg_def_ages_addr[op->u.hard_reg] = curr_bb_hreg_def_age;
	  hreg_defs_addr[op->u.hard_reg].insn = insn;
	  hreg_defs_addr[op->u.hard_reg].nop = i;
	  hreg_defs_addr[op->u.hard_reg].insn_num = curr_insn_num;
	}
      }
    }
  }
}



/* Dead code elimnination */

#define live_out out

static void
dead_code_elimination (MIR_item_t func) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t nops, i;
  MIR_reg_t var;
  MIR_op_t op;
  int out_p, reg_def_p, dead_p;
  bitmap_t live;
  
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++Dead code elimination:\n");
#endif
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      reg_def_p = FALSE; dead_p = TRUE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (! out_p || (op.mode != MIR_OP_REG && op.mode != MIR_OP_HARD_REG))
	  continue;
	reg_def_p = TRUE;
	var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
	if (bitmap_clear_bit_p (live, var))
	  dead_p = FALSE;
      }
      if (! reg_def_p)
	dead_p = FALSE;
      if (dead_p) {
#if MIR_GEN_DEBUG
	fprintf (debug_file, "  Removing dead insn");
	MIR_output_insn (debug_file, insn, curr_func_item->u.func);
#endif
	MIR_remove_insn (func, insn);
	DLIST_REMOVE (bb_insn_t, bb->bb_insns, bb_insn);
	free (bb_insn);
	continue;
      }
      if (insn->code == MIR_CALL || insn->code == MIR_CALL_C)
	bitmap_and_compl (live, live, call_used_hard_regs);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	switch (op.mode) {
	case MIR_OP_REG:
	  if (! out_p)
	    bitmap_set_bit_p (live, reg2var (op.u.reg));
	  break;
	case MIR_OP_HARD_REG:
	  if (! out_p)
	    bitmap_set_bit_p (live, op.u.hard_reg);
	  break;
	case MIR_OP_MEM:
	  if (op.u.mem.base != 0)
	    bitmap_set_bit_p (live, reg2var (op.u.mem.base));
	  if (op.u.mem.index != 0)
	    bitmap_set_bit_p (live, reg2var (op.u.mem.index));
	  break;
	case MIR_OP_HARD_REG_MEM:
	  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
	    bitmap_set_bit_p (live, op.u.hard_reg_mem.base);
	  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
	    bitmap_set_bit_p (live, op.u.hard_reg_mem.index);
	  break;
	default:
	  break;
	}
      }
      if (insn->code == MIR_CALL || insn->code == MIR_CALL_C)
	bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
}

#undef live_out



#include <sys/mman.h>
#include <unistd.h>

static size_t page_size;

static uint8_t *get_code (uint8_t *code, size_t code_len) {
  uint8_t *mem;
  size_t npages = (code_len + page_size - 1) / page_size;

  mem = (uint8_t *) mmap (NULL, page_size * npages, PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS , -1, 0);
  if (mem == MAP_FAILED)
    return NULL;
  memcpy (mem, code, code_len);
  if (mprotect (mem, page_size * npages, PROT_EXEC) < 0) {
    munmap (mem, page_size * npages);
    return NULL;
  }
  return mem;
}

#if MIR_GEN_DEBUG

#include <sys/types.h>

static void print_code (uint8_t *code, size_t code_len) {
  size_t i;
  int ch;
  char cfname[30];
  char command[500];
  FILE *f;
  
  sprintf (cfname, "_mir_%lu.c", (unsigned long) getpid ());
  if ((f = fopen (cfname, "w")) == NULL)
    return;
  fprintf (f, "unsigned char code[] = {");
  for (i = 0; i < code_len; i++) {
    if (i != 0)
      fprintf (f, ", ");
    fprintf (f, "0x%x", code[i]);
  }
  fprintf (f, "};\n");
  fclose (f);
  sprintf (command, "gcc -c -o %s.o %s 2>&1 && objdump --section=.data --adjust-vma=0x%lx -D %s.o; rm -f %s.o %s",
	   cfname, cfname, (long) 0, cfname, cfname, cfname);
  if ((f = popen (command, "r")) == NULL)
      return;
  while ((ch = fgetc (f)) != EOF)
    fprintf (debug_file, "%c", ch);
  pclose (f);
}
#endif 

void *MIR_gen (MIR_item_t func_item) {
  uint8_t *code;
  size_t code_len;
  void *res;
  
  assert (func_item->func_p && func_item->data == NULL);
  curr_func_item = func_item;
  curr_cfg = func_item->data = gen_malloc (sizeof (struct func_cfg));
  build_func_cfg ();
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after building CFG:\n");
  print_CFG (TRUE, TRUE, NULL);
#endif
  cse ();
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after CSE:\n");
  print_exprs ();
  print_CFG (TRUE, TRUE, output_bb_cse_info);
#endif
  ccp ();
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after CCP:\n");
  print_CFG (TRUE, TRUE, output_bb_ccp_info);
#endif
  calculate_func_cfg_live_info ();
  dead_code_elimination (func_item);
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after 1st dead code elimination:\n");
  print_CFG (TRUE, TRUE, output_bb_live_info);
#endif
  MIR_simplify_func (func_item);
#if MIR_GEN_DEBUG
  fprintf (stderr, "+++++++++++++MIR after simplification:\n");
  MIR_output (stderr);
#endif
  make_2op_insns (func_item);
  machinize (func_item);
  add_new_bb_insns (func_item);
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after machinize:\n");
  print_CFG (TRUE, TRUE, output_bb_live_info);
#endif
  calculate_func_cfg_live_info ();
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after building live_info:\n");
  print_CFG (TRUE, FALSE, output_bb_live_info);
#endif
  build_live_ranges ();
  assign ();
  rewrite (); /* After rewrite the BB live info is still valid */
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after rewrite:\n");
  print_CFG (FALSE, TRUE, NULL);
#endif
  combine (); /* After combine the BB live info is still valid */
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after combine:\n");
  print_CFG (FALSE, TRUE, NULL);
#endif
  calculate_func_cfg_live_info ();
  dead_code_elimination (func_item);
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after 2nd dead code elimination:\n");
  print_CFG (TRUE, TRUE, output_bb_live_info);
#endif
  make_prolog_epilog (func_item, func_assigned_hard_regs, func_stack_slots_num);
#if MIR_GEN_DEBUG
  fprintf (debug_file, "+++++++++++++MIR after forming prolog/epilog:\n");
  print_CFG (FALSE, TRUE, NULL);
#endif
  code = target_translate (func_item, &code_len);
#if MIR_GEN_DEBUG
  print_code (code, code_len);
#endif 
  res = get_code (code, code_len);
  destroy_func_live_ranges ();
  destroy_func_cfg ();
  return res;
}

void MIR_init_gen (void) {
  MIR_reg_t i;
  static hreg_def_t hreg_def = {NULL, 0, 0};
    
  page_size = sysconf(_SC_PAGE_SIZE);
#ifdef TEST_MIR_GEN
  fprintf (stderr, "Page size = %lu\n", (unsigned long) page_size);
#endif
  VARR_CREATE (bb_t, worklist, 0);
  VARR_CREATE (bb_t, pending, 0);
  VARR_CREATE (expr_t, exprs, 512);
  VARR_CREATE (bitmap_t, var2dep_expr, 512);
  VARR_CREATE (const_t, curr_ccp_vals, 512);
  VARR_CREATE (live_range_t, var_live_ranges, 0);
  HTAB_CREATE (expr_t, expr_tab, 1024, expr_hash, expr_eq);
  HTAB_CREATE (var_const_t, var_const_tab, 1024, var_const_hash, var_const_eq);
  curr_ccp_varying = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  curr_ccp_unknown = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  temp_bitmap = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  temp_bitmap2 = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  bb_to_consider = bitmap_create2 (512);
  all_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  live_vars = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  VARR_CREATE (MIR_reg_t, breg_renumber, 0);
  VARR_CREATE (MIR_reg_t, sorted_bregs, 0);
  VARR_CREATE (bitmap_t, point_used_locs, 0);
  VARR_CREATE (size_t, loc_profits, 0);
  VARR_CREATE (size_t, loc_profit_ages, 0);
  curr_bb_hreg_def_age = 0;
  VARR_CREATE (size_t, hreg_def_ages, MAX_HARD_REG + 1);
  VARR_CREATE (hreg_def_t, hreg_defs, MAX_HARD_REG + 1);
  conflict_locs = bitmap_create2 (3 * MAX_HARD_REG / 2);
  call_used_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (hreg_def_t, hreg_defs, hreg_def);
    VARR_PUSH (size_t, hreg_def_ages, 0);
    if (call_used_hard_reg_p (i))
      bitmap_set_bit_p (call_used_hard_regs, i);
  }
  func_assigned_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  insn_to_consider = bitmap_create2 (1024);
  target_init ();
}

void MIR_finish_gen (void) {
  VARR_DESTROY (bb_t, worklist);
  VARR_DESTROY (const_t, curr_ccp_vals);
  VARR_DESTROY (expr_t, exprs);
  VARR_DESTROY (bitmap_t, var2dep_expr);
  VARR_DESTROY (bb_t, pending);
  VARR_DESTROY (live_range_t, var_live_ranges);
  HTAB_DESTROY (expr_t, expr_tab);
  HTAB_DESTROY (var_const_t, var_const_tab);
  bitmap_destroy (curr_ccp_varying);
  bitmap_destroy (curr_ccp_unknown);
  bitmap_destroy (temp_bitmap);
  bitmap_destroy (temp_bitmap2);
  bitmap_destroy (bb_to_consider);
  bitmap_destroy (all_vars);
  bitmap_destroy (live_vars);
  VARR_DESTROY (MIR_reg_t, breg_renumber);
  VARR_DESTROY (MIR_reg_t, sorted_bregs);
  VARR_DESTROY (bitmap_t, point_used_locs);
  VARR_DESTROY (size_t, loc_profits);
  VARR_DESTROY (size_t, loc_profit_ages);
  VARR_DESTROY (size_t, hreg_def_ages);
  VARR_DESTROY (hreg_def_t, hreg_defs);
  bitmap_destroy (conflict_locs);
  bitmap_destroy (call_used_hard_regs);
  bitmap_destroy (func_assigned_hard_regs);
  bitmap_destroy (insn_to_consider);
  target_finish ();
}


/* Test code */
#if defined(TEST_MIR_GEN) || defined(TEST_MIR_GEN2)
#include <sys/time.h>

static double
real_usec_time(void) {
    struct timeval  tv;

    gettimeofday(&tv, NULL);
    return tv.tv_usec + tv.tv_sec * 1000000.0;
}

#endif

#if defined(TEST_MIR_GEN)

extern MIR_item_t create_mir_func_with_loop (void);
int main (void) {
  double start_time = real_usec_time ();
  double start_execution_time;
  MIR_item_t func;
  uint64_t (*fun) (uint64_t n_iter);
  uint64_t res, arg = 1000000000;
  
  MIR_init ();
  fprintf (stderr, "MIR_init end -- %.0f usec\n", real_usec_time () - start_time);
  func = create_mir_func_with_loop ();
#if MIR_GEN_DEBUG
  fprintf (stderr, "+++++++++++++original MIR:\n");
  MIR_output (stderr);
#endif
  fprintf (stderr, "MIR creation end -- %.0f usec\n", real_usec_time () - start_time);
  MIR_init_gen ();
  fprintf (stderr, "MIR_init_gen end -- %.0f usec\n", real_usec_time () - start_time);
#if MIR_GEN_DEBUG
  debug_file = stderr;
#endif
  fun = MIR_gen (func);
  fprintf (stderr, "MIR_gen end -- %.0f usec\n", real_usec_time () - start_time);
  start_execution_time = real_usec_time ();
  res = fun (arg);
  fprintf (stderr, "fun (%ld) -> %ld -- call %.0f usec\n",
	   arg, res, real_usec_time () - start_execution_time);
  MIR_finish_gen ();
  fprintf (stderr, "MIR_finish_gen end -- %.0f usec\n", real_usec_time () - start_time);
  MIR_finish ();
  fprintf (stderr, "MIR_finish end -- %.0f usec\n", real_usec_time () - start_time);
  return 0;
}

#endif

#if defined(TEST_MIR_GEN2)

extern MIR_item_t create_mir_func_sieve (size_t *);
int main (void) {
  double start_time = real_usec_time ();
  double start_execution_time;
  MIR_item_t func;
  uint64_t (*fun) (void);
  uint64_t res;
  
  MIR_init ();
  fprintf (stderr, "MIR_init end -- %.0f usec\n", real_usec_time () - start_time);
  func = create_mir_func_sieve (NULL);
#if MIR_GEN_DEBUG
  fprintf (stderr, "+++++++++++++original MIR:\n");
  MIR_output (stderr);
#endif
  fprintf (stderr, "MIR creation end -- %.0f usec\n", real_usec_time () - start_time);
  MIR_init_gen ();
  fprintf (stderr, "MIR_init_gen end -- %.0f usec\n", real_usec_time () - start_time);
#if MIR_GEN_DEBUG
  debug_file = stderr;
#endif
  fun = MIR_gen (func);
  fprintf (stderr, "MIR_gen end -- %.0f usec\n", real_usec_time () - start_time);
  start_execution_time = real_usec_time ();
  res = fun ();
  fprintf (stderr, "sieve () -> %ld -- call %.0f usec\n",
	   res, real_usec_time () - start_execution_time);
  MIR_finish_gen ();
  fprintf (stderr, "MIR_finish_gen end -- %.0f usec\n", real_usec_time () - start_time);
  MIR_finish ();
  fprintf (stderr, "MIR_finish end -- %.0f usec\n", real_usec_time () - start_time);
  return 0;
}

#endif

#if defined(TEST_MIR_GEN3)

int main (void) {
  MIR_item_t func0, func1, func2;
  
  MIR_init ();
  MIR_scan_string ("\n\
cse:   func 0, i64:i\n\
\n\
       local i64:l, i64:j, i64:k\n\
       mov j, 0\n\
       mov k, 0\n\
       mul l, 2, i\n\
       bgt L1, i, 0\n\
       mul j, 2, i\n\
       jmp L2\n\
L1:\n\
       mul k, 2, i\n\
L2:\n\
       add i, l, j\n\
       add i, i, k\n\
       ret i\n\
       endfunc\n\
  ");
  func0 = DLIST_TAIL (MIR_item_t, MIR_items);
#if 0
  MIR_scan_string ("\n\
ccp:   func 0\n\
\n\
       local i64:a, i64:b, i64:c\n\
       mov a, 2\n\
       mov b, 3\n\
       blt L1, a, b\n\
       mov c, 5\n\
       jmp L2\n\
L1:\n\
       mov c, 5\n\
L2:    ret c\n\
       endfunc\n\
  ");
  func1 = DLIST_TAIL (MIR_item_t, MIR_items);
  MIR_scan_string ("\n\
ccp2:   func 0\n\
\n\
       local i64:a, i64:d, i64:f, i64:g\n\
       mov a, 3\n\
       mov d, 2\n\
L1:\n\
       add f, a, d\n\
       mov g, 5\n\
       sub a, g, d\n\
       ble L2, f, g\n\
       blt L3, g, a\n\
       ret f\n\
L2:\n\
       add f, g, 1\n\
L3:\n\
       mov d, 2\n\
       jmp L1\n\
       endfunc\n\
  ");
  func2 = DLIST_TAIL (MIR_item_t, MIR_items);
#endif
  MIR_init_gen ();
#if MIR_GEN_DEBUG
  debug_file = stderr;
#endif
  MIR_gen (func0);
#if 0
  MIR_gen (func1);
  MIR_gen (func2);
#endif
  MIR_finish_gen ();
  MIR_finish ();
  return 0;
}

#endif
