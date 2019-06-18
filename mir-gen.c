/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* Optimization pipeline:

            ----------------      -----------      ------------------      -------------     
   MIR --->|    Simplify    |--->| Build CFG |--->|  Common Sub-Expr |--->|  Dead Code  |	 
            ----------------      -----------     |    Elimination   |	  | Elimination |    
                                                   ------------------	   -------------     
                                                                                  |
                                                                                  v
    --------      -------------      ------------       -----------     ---------------------- 
   | Assign |<---| Build Live  |<---| Build Live |<---| Machinize |<---|  Sparse Conditional  |
    --------     |   Ranges    |    |    Info    |      -----------    | Constant Propagation |
       |          -------------      ------------                       ---------------------- 
       |
       v
    ---------     ---------     -------------      ---------------
   | Rewrite |-->| Combine |-->|  Dead Code  |--->|   Generate    |---> Machine Insns
    ---------     ---------    | Elimination |    | machine insns |
                                -------------      ---------------
              
              

   Simplify: Lowering MIR (in mir.c).
   Build CGF: Builing Control Flow Graph (basic blocks and CFG edges).
   Common Sub-Expression Elimination: Reusing calculated values
   Dead code elimination: Removing insns with unused outputs. 
   Sparse Conditional Constant Propagation: constant propagation and removing death paths of CFG
   Machinize: Machine-dependent code (e.g. in x86_64-target.c)
              transforming MIR for calls ABI, 2-op insns, etc.
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

   We don't use SSA because the optimization pipeline could use SSA is
   short (2 passes) and going into / out of SSA is expensive.
*/

#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include <assert.h>

#ifdef NDEBUG
static inline int gen_assert (int cond) {return 0 && cond;}
#else
#define gen_assert(cond) assert (cond)
#endif

static void util_error (const char *message);
#define MIR_VARR_ERROR util_error

#include "mir.h"
#include "mir-dlist.h"
#include "mir-bitmap.h"
#include "mir-htab.h"
#include "mir-hash.h"
#include "mir-gen.h"

static void MIR_NO_RETURN util_error (const char *message) { (*MIR_get_error_func ()) (MIR_alloc_error, message); }

static void *gen_malloc (size_t size) {
  void *res = malloc (size);
  if (res == NULL)
    util_error ("no memory");
  return res;
}

static MIR_reg_t gen_new_temp_reg (MIR_type_t type, MIR_func_t func);
static void set_label_disp (MIR_insn_t insn, size_t disp);
static size_t get_label_disp (MIR_insn_t insn);
static void create_new_bb_insns (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t after);
static void gen_delete_insn (MIR_item_t func_item, MIR_insn_t insn);
static void gen_add_insn_before (MIR_item_t func_item, MIR_insn_t insn, MIR_insn_t before);
static void gen_add_insn_after (MIR_item_t func_item, MIR_insn_t insn, MIR_insn_t after);
static void setup_call_hard_reg_args (MIR_insn_t call_insn, MIR_reg_t hard_reg);

#ifdef __x86_64__
#include "mir-gen-x86_64.c"
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
  
  gen_assert (func_item->item_type == MIR_func_item);
  func = func_item->u.func;
  for (i = 0; i < sizeof (two_op_insn_codes) / sizeof (MIR_insn_code_t); i++)
    bitmap_set_bit_p (insn_to_consider, two_op_insn_codes[i]);
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    code = insn->code;
    if (! bitmap_bit_p (insn_to_consider, code))
      continue;
    gen_assert (MIR_insn_nops (insn) > 2);
    mode = MIR_insn_op_mode (insn, 0, &out_p);
    gen_assert (out_p && mode == MIR_insn_op_mode (insn, 1, &out_p) && ! out_p);
    output = insn->ops[0];
    input = insn->ops[1];
    gen_assert (input.mode == MIR_OP_REG || input.mode == MIR_OP_HARD_REG
		|| output.mode == MIR_OP_REG || output.mode == MIR_OP_HARD_REG);
    if (input.mode == output.mode
	&& ((input.mode == MIR_OP_HARD_REG && input.u.hard_reg == output.u.hard_reg)
	    || (input.mode == MIR_OP_REG && input.u.reg == output.u.reg)))
      continue;
    if (mode == MIR_OP_FLOAT) {
      code = MIR_FMOV; type = MIR_T_F;
    } else if (mode == MIR_OP_DOUBLE) {
      code = MIR_DMOV; type = MIR_T_D;
    } else {
      code = MIR_MOV; type = MIR_T_I64;
    }
    temp_op = MIR_new_reg_op (gen_new_temp_reg (type, func));
    gen_add_insn_before (func_item, insn, MIR_new_insn (code, temp_op, insn->ops[1]));
    gen_add_insn_after (func_item, insn, MIR_new_insn (code, insn->ops[0], temp_op));
    insn->ops[0] = insn->ops[1] = temp_op;
  }
}

typedef struct dead_var *dead_var_t;

DEF_DLIST_LINK (dead_var_t);

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

struct dead_var {
  MIR_reg_t var;
  DLIST_LINK (dead_var_t) dead_var_link;
};

DEF_DLIST (dead_var_t, dead_var_link);

struct bb_insn {
  MIR_insn_t insn;
  unsigned int flag; /* used for CPP */
  DLIST_LINK (bb_insn_t) bb_insn_link;
  bb_t bb;
  DLIST (dead_var_t) dead_vars;
  bitmap_t call_hard_reg_args; /* non-null for calls */
  size_t label_disp; /* for label */
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost;
  unsigned int flag : 1; /* used for CPP */
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

#if MIR_GEN_DEBUG
static void print_const (FILE *f, const_t c) {
  if (c.uns_p)
    fprintf (f, "%" PRIu64, c.u.u);
  else
    fprintf (f, "%" PRId64, c.u.i);
}
#endif

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

static DLIST (dead_var_t) free_dead_vars;

static void init_dead_vars (void) {
  DLIST_INIT (dead_var_t, free_dead_vars);
}

static void free_dead_var (dead_var_t dv) { DLIST_APPEND (dead_var_t, free_dead_vars, dv); }

static dead_var_t get_dead_var (void) {
  dead_var_t dv;
  
  if ((dv = DLIST_HEAD (dead_var_t, free_dead_vars)) == NULL)
    return gen_malloc (sizeof (struct dead_var));
  DLIST_REMOVE (dead_var_t, free_dead_vars, dv);
  return dv;
}

static void finish_dead_vars (void) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, free_dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, free_dead_vars, dv);
    free (dv);
  }
}

static void add_bb_insn_dead_var (bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv;

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL; dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var)
      return;
  dv = get_dead_var ();
  dv->var = var;
  DLIST_APPEND (dead_var_t, bb_insn->dead_vars, dv);
}

static dead_var_t find_bb_insn_dead_var (bb_insn_t bb_insn, MIR_reg_t var) {
  dead_var_t dv;

  for (dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars); dv != NULL; dv = DLIST_NEXT (dead_var_t, dv))
    if (dv->var == var)
      return dv;
  return NULL;
}

static void clear_bb_insn_dead_vars (bb_insn_t bb_insn) {
  dead_var_t dv;

  while ((dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars)) != NULL) {
    DLIST_REMOVE (dead_var_t, bb_insn->dead_vars, dv);
    free_dead_var (dv);
  }
}

static bb_insn_t create_bb_insn (MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = gen_malloc (sizeof (struct bb_insn));

  insn->data = bb_insn;
  bb_insn->bb = bb;
  bb_insn->insn = insn;
  bb_insn->flag = FALSE;
  bb_insn->call_hard_reg_args = NULL;
  DLIST_INIT (dead_var_t, bb_insn->dead_vars);
  if (MIR_call_code_p (insn->code))
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
  clear_bb_insn_dead_vars (bb_insn);
  if (bb_insn->call_hard_reg_args != NULL)
    bitmap_destroy (bb_insn->call_hard_reg_args);
  free (bb_insn);
}

static void create_new_bb_insns (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t after) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, new_bb_insn;
  bb_t bb;
  
  if (before != NULL) {
    insn = DLIST_NEXT (MIR_insn_t, before);
    bb_insn = before->data;
  } else {
    gen_assert (after != NULL);
    insn = DLIST_HEAD (MIR_insn_t, func_item->u.func->insns);
    bb_insn = after->data;
  }
  bb = bb_insn->bb;
  for (; insn != after; insn = DLIST_NEXT (MIR_insn_t, insn), bb_insn = new_bb_insn) {
    new_bb_insn = create_bb_insn (insn, bb);
    if (before != NULL)
      DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
    else
      DLIST_INSERT_BEFORE (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
    before = insn;
  }
}

static void gen_delete_insn (MIR_item_t func_item, MIR_insn_t insn) {
  delete_bb_insn (insn->data);
  MIR_remove_insn (curr_func_item, insn);
}

static void gen_add_insn_before (MIR_item_t func_item, MIR_insn_t before, MIR_insn_t insn) {
  MIR_insert_insn_before (func_item, before, insn);
  create_new_bb_insns (func_item, DLIST_PREV (MIR_insn_t, insn), before);
}

static void gen_add_insn_after (MIR_item_t func_item, MIR_insn_t after, MIR_insn_t insn) {
  MIR_insert_insn_after (func_item, after, insn);
  create_new_bb_insns (func_item, after, DLIST_NEXT (MIR_insn_t, insn));
}

static void setup_call_hard_reg_args (MIR_insn_t call_insn, MIR_reg_t hard_reg) {
  bb_insn_t bb_insn = call_insn->data;
  
  gen_assert (MIR_call_code_p (call_insn->code) && hard_reg <= MAX_HARD_REG);
  bitmap_set_bit_p (bb_insn->call_hard_reg_args, hard_reg);
}

static void set_label_disp (MIR_insn_t insn, size_t disp) {
  gen_assert (insn->code == MIR_LABEL);
  ((bb_insn_t) insn->data)->label_disp = disp;
}
static size_t get_label_disp (MIR_insn_t insn) {
  gen_assert (insn->code == MIR_LABEL);
  return ((bb_insn_t) insn->data)->label_disp;
}

static size_t curr_bb_index;

static bb_t create_bb (MIR_insn_t insn) {
  bb_t bb = gen_malloc (sizeof (struct bb));

  bb->pre = bb->rpost = 0;
  bb->flag = FALSE;
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

static MIR_reg_t gen_new_temp_reg (MIR_type_t type, MIR_func_t func) {
  MIR_reg_t reg = _MIR_new_temp_reg (type, func);

  update_min_max_reg (reg);
  return reg;
}

static MIR_reg_t reg2breg (MIR_reg_t reg) { return reg - curr_cfg->min_reg; }
static MIR_reg_t breg2reg (MIR_reg_t breg) { return breg + curr_cfg->min_reg; }
static MIR_reg_t reg2var (MIR_reg_t reg) { return reg2breg (reg) + MAX_HARD_REG + 1; }
static MIR_reg_t var_is_reg_p (MIR_reg_t var) { return var > MAX_HARD_REG; }
static MIR_reg_t var2reg (MIR_reg_t var) {
  gen_assert (var > MAX_HARD_REG);
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
	  && (insn->ops[1].mode == MIR_OP_INT || insn->ops[1].mode == MIR_OP_UINT
	      || insn->ops[1].mode == MIR_OP_FLOAT || insn->ops[1].mode == MIR_OP_DOUBLE
	      || insn->ops[1].mode == MIR_OP_REF));
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
    fprintf (debug_file, "(%s:%s)", MIR_type_str (MIR_reg_type (var2reg (nel), curr_func_item->u.func)),
	     MIR_reg_name (var2reg (nel), curr_func_item->u.func));
}

static void output_bitmap (const char *head, bitmap_t bm) {
  if (bm == NULL || bitmap_empty_p (bm))
    return;
  fprintf (debug_file, head);
  bitmap_for_each (bm, output_live_element);
  fprintf (debug_file, "\n");
}

static void print_bb_insn (bb_insn_t bb_insn, int with_notes_p) {
  MIR_op_t op;
  
  MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
  if (with_notes_p) {
    for (dead_var_t dv = DLIST_HEAD (dead_var_t, bb_insn->dead_vars);
	 dv != NULL;
	 dv = DLIST_NEXT (dead_var_t, dv)) {
      if (var_is_reg_p (dv->var)) {
	op.mode = MIR_OP_REG;
	op.u.reg = var2reg (dv->var);
      } else {
	op.mode = MIR_OP_HARD_REG;
	op.u.hard_reg = dv->var;
      }
      fprintf (debug_file, dv == DLIST_HEAD (dead_var_t, bb_insn->dead_vars) ? " # dead: " : " ");
      MIR_output_op (debug_file, op, curr_func_item->u.func);
    }
  }
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
	print_bb_insn (bb_insn, TRUE);
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
  MIR_var_t var;
  bb_t bb, prev_bb, entry_bb, exit_bb;
  
  DLIST_INIT (bb_t, curr_cfg->bbs);
  DLIST_INIT (mv_t, curr_cfg->used_moves);
  DLIST_INIT (mv_t, curr_cfg->free_moves);
  curr_cfg->max_reg = 0;
  curr_cfg->min_reg = 0;
  curr_bb_index = 0;
  for (i = 0; i < VARR_LENGTH (MIR_var_t, curr_func_item->u.func->vars); i++) {
    var = VARR_GET (MIR_var_t, curr_func_item->u.func->vars, i);
    update_min_max_reg (MIR_reg (var.name, curr_func_item->u.func));
  }
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
    nops = MIR_insn_nops (insn);
    if (next_insn != NULL
	&& (MIR_branch_code_p (insn->code)
	    || MIR_ret_code_p (insn->code) || next_insn->code == MIR_LABEL)) {
      prev_bb = bb;
      if (next_insn->code == MIR_LABEL && (label_bb_insn = next_insn->data) != NULL)
	bb = label_bb_insn->bb;
      else
	bb = create_bb (next_insn);
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
  bb_t bb, next_bb;
  mv_t mv, next_mv;
  
  gen_assert (curr_func_item->item_type == MIR_func_item && curr_func_item->data != NULL);
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func_item->u.func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    bb_insn = insn->data;
    gen_assert (bb_insn != NULL);
    delete_bb_insn (bb_insn);
  }
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    bitmap_destroy (bb->in); bitmap_destroy (bb->out);
    bitmap_destroy (bb->gen); bitmap_destroy (bb->kill);
    delete_bb (bb);
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
  free (curr_func_item->data);
  curr_func_item->data = NULL;
}

static void add_new_bb_insns (MIR_item_t func_item) {
  MIR_func_t func;
  size_t i, nops;
  MIR_op_t op;
  bb_t bb = DLIST_EL (bb_t, curr_cfg->bbs, 2);
  bb_insn_t bb_insn, last_bb_insn = NULL;
  
  gen_assert (func_item->item_type == MIR_func_item);
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
      gen_assert (bb != NULL);
      bb_insn = create_bb_insn (insn, bb);
      if (last_bb_insn != NULL) {
	DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, last_bb_insn, bb_insn);
      } else {
	gen_assert (DLIST_HEAD (bb_insn_t, bb->bb_insns) != NULL
		    && DLIST_HEAD (bb_insn_t, bb->bb_insns)->insn->code != MIR_LABEL);
	DLIST_PREPEND (bb_insn_t, bb->bb_insns, bb_insn);
      }
      last_bb_insn = bb_insn;
      nops = MIR_insn_nops (insn);
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
/* map: var number -> bitmap of numbers of exprs with given var as an input operand. */
static VARR (bitmap_t) *var2dep_expr;
static bitmap_t memory_exprs; /* expressions containing memory */

DEF_HTAB (expr_t);
static HTAB (expr_t) *expr_tab; /* keys: insn code and input operands */

static int op_eq (MIR_op_t op1, MIR_op_t op2) { return MIR_op_eq_p (op1, op2); }

static int expr_eq (expr_t e1, expr_t e2) {
  size_t i, nops;
  int out_p;
  
  if (e1->insn->code != e2->insn->code)
    return FALSE;
  nops = MIR_insn_nops (e1->insn);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (e1->insn, i, &out_p);
    if (out_p)
      continue;
    if (! op_eq (e1->insn->ops[i], e2->insn->ops[i]))
      return FALSE;
  }
  return TRUE;
}

static htab_hash_t add_op_hash (htab_hash_t h, MIR_op_t op) { return MIR_op_hash_step (h, op); }

static htab_hash_t expr_hash (expr_t e) {
  size_t i, nops;
  int out_p;
  htab_hash_t h = mir_hash_init (0x42);
  
  h = mir_hash_step (h, (uint64_t) e->insn->code);
  nops = MIR_insn_nops (e->insn);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (e->insn, i, &out_p);
    if (out_p)
      continue;
    h = add_op_hash (h, e->insn->ops[i]);
  }
  return mir_hash_finish (h);
}

static int find_expr (MIR_insn_t insn, expr_t *e) {
  struct expr es;
  
  es.insn = insn;
  return HTAB_DO (expr_t, expr_tab, &es, HTAB_FIND, *e);
}

static void insert_expr (expr_t e) {
  expr_t e2;
  
  gen_assert (! find_expr (e->insn, &e2));
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

static void process_cse_ops (MIR_op_t op, expr_t e) {
  switch (op.mode) { // ???
  case MIR_OP_REG:
    process_var (reg2var (op.u.reg), e);
    break;
  case MIR_OP_HARD_REG:
    process_var (op.u.hard_reg, e);
    break;
  case MIR_OP_INT: case MIR_OP_UINT: case MIR_OP_FLOAT: case MIR_OP_DOUBLE: case MIR_OP_REF:
    break;
  case MIR_OP_MEM:
    if (op.u.mem.base != 0)
      process_var (reg2var (op.u.mem.base), e);
    if (op.u.mem.index != 0)
      process_var (reg2var (op.u.mem.index), e);
    bitmap_set_bit_p (memory_exprs, e->num);
    break;
  case MIR_OP_HARD_REG_MEM:
    if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
      process_var (op.u.hard_reg_mem.base, e);
    if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
      process_var (op.u.hard_reg_mem.index, e);
    bitmap_set_bit_p (memory_exprs, e->num);
    break;
  default:
    gen_assert (FALSE); /* we should not have all the rest operand here */
  }
}

static expr_t add_expr (MIR_insn_t insn) {
  size_t i, nops;
  int out_p;
  MIR_op_mode_t mode;
  expr_t e = gen_malloc (sizeof (struct expr));
  
  e->insn = insn; e->num = VARR_LENGTH (expr_t, exprs);
  mode = MIR_insn_op_mode (insn, 0, &out_p);
  e->temp_reg = gen_new_temp_reg (mode == MIR_OP_FLOAT ? MIR_T_F : mode == MIR_OP_DOUBLE ? MIR_T_D : MIR_T_I64,
				  curr_func_item->u.func);
  VARR_PUSH (expr_t, exprs, e);
  insert_expr (e);
  nops = MIR_insn_nops (insn);
  for (i = 0; i < nops; i++) {
    MIR_insn_op_mode (insn, i, &out_p);
    if (! out_p)
      process_cse_ops (insn->ops[i], e);
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
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      expr_t e;
      MIR_insn_t insn = bb_insn->insn;
      
      if (! MIR_branch_code_p (insn->code) && ! MIR_ret_code_p (insn->code)
	  && insn->code != MIR_LABEL && ! MIR_call_code_p (insn->code)
	  && insn->code != MIR_ALLOCA && insn->code != MIR_BSTART && insn->code != MIR_BEND
	  && ! move_p (insn) && ! imm_move_p (insn)
	  /* After simplification we have only one store form: mem = reg.
	     It is unprofitable to add the reg as an expression.  */
	  && insn->ops[0].mode != MIR_OP_MEM && insn->ops[0].mode != MIR_OP_HARD_REG_MEM
	  && ! find_expr (insn, &e))
	add_expr (insn);
    }
}

static bitmap_t curr_bb_av_gen, curr_bb_av_kill;

static void make_obsolete_var_exprs (size_t nel) {
  MIR_reg_t var = nel;
  bitmap_t b;
  
  if (var < VARR_LENGTH (bitmap_t, var2dep_expr)
      && (b = VARR_GET (bitmap_t, var2dep_expr, var)) != NULL) {
    if (curr_bb_av_gen != NULL)
      bitmap_and_compl (curr_bb_av_gen, curr_bb_av_gen, b);
    if (curr_bb_av_kill != NULL)
      bitmap_ior (curr_bb_av_kill, curr_bb_av_kill, b);
  }
}

static void create_av_bitmaps (void) {
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_clear (bb->av_in); bitmap_clear (bb->av_out);
    bitmap_clear (bb->av_kill); bitmap_clear (bb->av_gen);
    curr_bb_av_gen = bb->av_gen;
    curr_bb_av_kill = bb->av_kill;
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      size_t i, nops;
      int out_p;
      MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
      MIR_op_t op;
      expr_t e;
      bitmap_t b;
      MIR_insn_t insn = bb_insn->insn;
      
      if (MIR_branch_code_p (bb_insn->insn->code) || MIR_ret_code_p (insn->code) || insn->code == MIR_LABEL)
	continue;
      if (! MIR_call_code_p (insn->code) && insn->code != MIR_ALLOCA
	  && insn->code != MIR_BSTART && insn->code != MIR_BEND
	  && ! move_p (insn) && ! imm_move_p (insn)
	  /* See create_expr comments: */
	  && insn->ops[0].mode != MIR_OP_MEM && insn->ops[0].mode != MIR_OP_HARD_REG_MEM) {
	if (! find_expr (insn, &e)) {
	  gen_assert (FALSE);
	  continue;
	}
	bitmap_set_bit_p (bb->av_gen, e->num);
      }
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
	make_obsolete_var_exprs (early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
	make_obsolete_var_exprs (early_clobbered_hard_reg2);
      nops = MIR_insn_nops (insn);
      for (i = 0; i < nops; i++) {
	MIR_insn_op_mode (insn, i, &out_p);
	op = insn->ops[i];
	if (! out_p)
	  continue;
	if (op.mode == MIR_OP_MEM || op.mode == MIR_OP_HARD_REG_MEM) {
	  bitmap_and_compl (bb->av_gen, bb->av_gen, memory_exprs);
	  bitmap_ior (bb->av_kill, bb->av_kill, memory_exprs);
	} else if (op.mode == MIR_OP_REG || op.mode == MIR_OP_HARD_REG) {
	  make_obsolete_var_exprs (op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg));
	}
      }
      if (MIR_call_code_p (insn->code)) {
	gen_assert (bb_insn->call_hard_reg_args != NULL);
	bitmap_for_each (bb_insn->call_hard_reg_args, make_obsolete_var_exprs);
	bitmap_for_each (call_used_hard_regs, make_obsolete_var_exprs);
      }
    }
  }
}

static void cse_modify (void) {
  bb_insn_t bb_insn, new_bb_insn, next_bb_insn;
  bitmap_t av = temp_bitmap;
  
  curr_bb_av_gen = temp_bitmap;
  curr_bb_av_kill = NULL;
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (av, bb->av_in);
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      size_t i, nops;
      expr_t e;
      MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
      MIR_op_t op;
      int out_p;
      bitmap_t b;
      MIR_type_t type;
      MIR_insn_code_t move_code;
      MIR_insn_t new_insn, insn = bb_insn->insn;
      
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (MIR_branch_code_p (insn->code) || MIR_ret_code_p (insn->code) || insn->code == MIR_LABEL)
	continue;
      if (! MIR_call_code_p (insn->code) && insn->code != MIR_ALLOCA
	  && insn->code != MIR_BSTART && insn->code != MIR_BEND
	  && ! move_p (insn) && ! imm_move_p (insn)
	  /* See create_expr comments: */
	  && insn->ops[0].mode != MIR_OP_MEM && insn->ops[0].mode != MIR_OP_HARD_REG_MEM) {
	if (! find_expr (insn, &e)) {
	  gen_assert (FALSE);
	  continue;
	}
	op = MIR_new_reg_op (e->temp_reg);
	type = MIR_reg_type (e->temp_reg, curr_func_item->u.func);
	move_code = type == MIR_T_F ? MIR_FMOV : type == MIR_T_D ? MIR_DMOV : MIR_MOV;
#ifdef NDEBUG
	MIR_insn_op_mode (insn, 0, &out_p); /* result here is always 0-th op */
	gen_assert (out_p);
#endif
	if (! bitmap_bit_p (av, e->num)) {
	  bitmap_set_bit_p (av, e->num);
	  new_insn = MIR_new_insn (move_code, op, insn->ops[0]);
	  new_bb_insn = create_bb_insn (new_insn, bb);
	  MIR_insert_insn_after (curr_func_item, insn, new_insn);
	  DLIST_INSERT_AFTER (bb_insn_t, bb->bb_insns, bb_insn, new_bb_insn);
	  next_bb_insn = DLIST_NEXT (bb_insn_t, new_bb_insn);
#if MIR_GEN_DEBUG
	  if (debug_file != NULL) {
	    fprintf (debug_file, "  adding insn ");
	    MIR_output_insn (debug_file, new_insn, curr_func_item->u.func, FALSE);
	    fprintf (debug_file, "  after def insn ");
	    MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	  }
#endif
	} else {
	  new_insn = MIR_new_insn (move_code, insn->ops[0], op);
	  gen_add_insn_after (curr_func_item, insn, new_insn);
#if MIR_GEN_DEBUG
	  if (debug_file != NULL) {
	    fprintf (debug_file, "  adding insn ");
	    MIR_output_insn (debug_file, new_insn, curr_func_item->u.func, FALSE);
	    fprintf (debug_file, "  after use insn ");
	    MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	  }
#endif
	  insn = new_insn;
	}
      }
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
	make_obsolete_var_exprs (early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
	make_obsolete_var_exprs (early_clobbered_hard_reg2);
      nops = MIR_insn_nops (insn);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
	if (! out_p)
	  continue;
	if (op.mode == MIR_OP_MEM || op.mode == MIR_OP_HARD_REG_MEM) {
	  bitmap_and_compl (av, av, memory_exprs);
	} else if (op.mode == MIR_OP_REG || op.mode == MIR_OP_HARD_REG) {
	  make_obsolete_var_exprs (op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg));
	}
      }
      if (MIR_call_code_p (insn->code)) {
	gen_assert (bb_insn->call_hard_reg_args != NULL);
	bitmap_for_each (bb_insn->call_hard_reg_args, make_obsolete_var_exprs);
	bitmap_for_each (call_used_hard_regs, make_obsolete_var_exprs);
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
  fprintf (debug_file, "  Expressions:\n");
  for (size_t i = 0; i < VARR_LENGTH (expr_t, exprs); i++) {
    size_t nops;
    expr_t e = VARR_GET (expr_t, exprs, i);
    
    fprintf (debug_file, "  %3d: ", i);
    fprintf (debug_file, "%s _", MIR_insn_name (e->insn->code));
    nops = MIR_insn_nops (e->insn);
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

static void cse_clear (void) {
  HTAB_CLEAR (expr_t, expr_tab, NULL);
  while (VARR_LENGTH (expr_t, exprs) != 0)
    free (VARR_POP (expr_t, exprs));
  while (VARR_LENGTH (bitmap_t, var2dep_expr) != 0) {
    bitmap_t b = VARR_POP (bitmap_t, var2dep_expr);
    
    if (b != NULL)
      bitmap_destroy (b);
  }
  bitmap_clear (memory_exprs);
}

#undef av_in
#undef av_out
#undef av_kill
#undef av_gen



/* Sparse Conditional Constant Propagation.  Live info should exist.  */

#define live_in in
#define live_out out

enum ccp_val_kind {CCP_CONST = 0, CCP_VARYING, CCP_UNKNOWN};

enum place_type {OCC_INSN, OCC_BB_START, OCC_BB_END};

typedef struct {
  enum place_type type;
  union {
    MIR_insn_t insn;
    bb_t bb;
  } u;
} place_t;

typedef struct var_occ *var_occ_t;

DEF_DLIST_LINK (var_occ_t);
DEF_DLIST_TYPE (var_occ_t);

/* Occurences at BB start are defs, ones at BB end are uses.  */
typedef struct var_occ {
  MIR_reg_t var;
  enum ccp_val_kind val_kind : 8;
  unsigned int flag : 8;
  const_t val;
  place_t place;
  var_occ_t def;
  DLIST (var_occ_t) uses; /* Empty for def */
  DLIST_LINK (var_occ_t) use_link;
} *var_occ_t;

DEF_DLIST_CODE (var_occ_t, use_link);

typedef DLIST (var_occ_t) bb_start_occ_list_t;
DEF_VARR (bb_start_occ_list_t);
static VARR (bb_start_occ_list_t) *bb_start_occ_list_varr;
static bb_start_occ_list_t *bb_start_occ_lists;

DEF_VARR (var_occ_t);
static VARR (var_occ_t) *var_occs;

DEF_HTAB (var_occ_t);
static HTAB (var_occ_t) *var_occ_tab;

static htab_hash_t var_occ_hash (var_occ_t vo) {
  gen_assert (vo->place.type != OCC_INSN);
  return mir_hash_finish (mir_hash_step (mir_hash_step (mir_hash_step (mir_hash_init (0x54),
								       (uint64_t) vo->var),
							(uint64_t) vo->place.type),
					 (uint64_t) vo->place.u.bb));
}

static int var_occ_eq (var_occ_t vo1, var_occ_t vo2) {
  return (vo1->var == vo2->var
	  && vo1->place.type == vo2->place.type && vo1->place.u.bb == vo2->place.u.bb);
}

static void init_var_occ (var_occ_t var_occ, MIR_reg_t var,
			  enum place_type type, bb_t bb, MIR_insn_t insn) {
  var_occ->var = var;
  var_occ->val_kind = CCP_UNKNOWN;
  var_occ->place.type = type;
  if (bb == NULL)
    var_occ->place.u.insn = insn;
  else
    var_occ->place.u.bb = bb;
  var_occ->def = NULL;
  var_occ->flag = FALSE;
  DLIST_INIT (var_occ_t, var_occ->uses);
}

static var_occ_t new_insn_var_occ (MIR_reg_t var, MIR_insn_t insn) {
  var_occ_t var_occ = gen_malloc (sizeof (struct var_occ));

  init_var_occ (var_occ, var, OCC_INSN, NULL, insn);
  VARR_PUSH (var_occ_t, var_occs, var_occ);
  return var_occ;
}

static var_occ_t get_bb_var_occ (MIR_reg_t var, enum place_type type, bb_t bb) {
  struct var_occ vos;
  var_occ_t var_occ;
  
  init_var_occ (&vos, var, type, bb, NULL);
  if (HTAB_DO (var_occ_t, var_occ_tab, &vos, HTAB_FIND, var_occ))
    return var_occ;
  var_occ = gen_malloc (sizeof (struct var_occ));
  *var_occ = vos;
  VARR_PUSH (var_occ_t, var_occs, var_occ);
  HTAB_DO (var_occ_t, var_occ_tab, var_occ, HTAB_INSERT, var_occ);
  if (type == OCC_BB_START) {
    DLIST_APPEND (var_occ_t, bb_start_occ_lists[bb->index], var_occ);
    if (DLIST_EL (bb_t, curr_cfg->bbs, 0) == bb
	&& var_is_reg_p (var) && var2reg (var) <= curr_func_item->u.func->nargs) {
      var_occ->val_kind = CCP_VARYING;
    }
  }
  return var_occ;
}

typedef struct {
  int producer_age, op_age;
  var_occ_t producer; /* valid if producer_age == curr_producer_age */
  var_occ_t op_var_use; /* valid if op_age == curr_op_age */
} var_producer_t;

static int curr_producer_age, curr_op_age;
static var_producer_t *producers;
DEF_VARR (var_producer_t);
static VARR (var_producer_t) *producer_varr;

static var_occ_t get_var_def (MIR_reg_t var, bb_t bb) {
  var_occ_t var_occ;
  
  if (producers[var].producer_age == curr_producer_age) {
    var_occ = producers[var].producer; 
  } else { /* use w/o a producer insn in the block */
    producers[var].producer = var_occ = get_bb_var_occ (var, OCC_BB_START, bb);
    producers[var].producer_age = curr_producer_age;
  }
  return var_occ;
}

static void process_op_var_use (MIR_reg_t var, bb_insn_t bb_insn, MIR_op_t *op) {
  var_occ_t def, use;
  
  if (producers[var].op_age == curr_op_age) {
    op->data = producers[var].op_var_use;
    return; /* var was already another operand in the insn */
  }
  producers[var].op_age = curr_op_age;
  def = get_var_def (var, bb_insn->bb);
  producers[var].op_var_use = use = new_insn_var_occ (var, bb_insn->insn);
  op->data = use;
  use->def = def;
  DLIST_APPEND (var_occ_t, def->uses, use);
}

static void process_op_use (MIR_op_t *op, bb_insn_t bb_insn) {
  switch (op->mode) {
  case MIR_OP_REG:
    if (op->u.reg != 0)
      process_op_var_use (reg2var (op->u.reg), bb_insn, op);
    break;
  case MIR_OP_HARD_REG:
    if (op->u.hard_reg != MIR_NON_HARD_REG)
      process_op_var_use (op->u.hard_reg, bb_insn, op);
    break;
  case MIR_OP_MEM:
    if (op->u.mem.base != 0)
      process_op_var_use (reg2var (op->u.mem.base), bb_insn, op);
    if (op->u.mem.index != 0)
      process_op_var_use (reg2var (op->u.mem.index), bb_insn, op);
    break;
  case MIR_OP_HARD_REG_MEM:
    if (op->u.hard_reg_mem.base != MIR_NON_HARD_REG)
      process_op_var_use (op->u.hard_reg_mem.base, bb_insn, op);
    if (op->u.hard_reg_mem.index != MIR_NON_HARD_REG)
      process_op_var_use (op->u.hard_reg_mem.index, bb_insn, op);
    break;
  default:
    break;
  }
}

static bb_t ccp_end_bb;

static void process_bb_end (size_t el) {
  MIR_reg_t var = el;
  var_occ_t use = get_bb_var_occ (var, OCC_BB_END, ccp_end_bb), def = get_var_def (var, ccp_end_bb);

  use->def = def;
  DLIST_APPEND (var_occ_t, def->uses, use);
}

/* Build a web of def-use with auxiliary usages and definitions at BB
   borders to emulate SSA on which the sparse conditional propagation
   is usually done.  We could do non-sparse CCP w/o building the web
   but it is much slower algorithm.  */
static void build_var_occ_web (void) {
  MIR_op_t *op, *dst_op;
  MIR_insn_t insn;
  size_t i, nops;
  int out_p, dst_var_p;
  MIR_reg_t dst_var;
  var_occ_t var_occ;
  var_producer_t var_producer;
  bb_start_occ_list_t list;
  
  DLIST_INIT (var_occ_t, list);
  while (VARR_LENGTH (bb_start_occ_list_t, bb_start_occ_list_varr) < curr_bb_index)
    VARR_PUSH (bb_start_occ_list_t, bb_start_occ_list_varr, list);
  bb_start_occ_lists = VARR_ADDR (bb_start_occ_list_t, bb_start_occ_list_varr);
  var_producer.producer_age = var_producer.op_age = 0;
  var_producer.producer = var_producer.op_var_use = NULL;
  while (VARR_LENGTH (var_producer_t, producer_varr) < get_nvars ())
    VARR_PUSH (var_producer_t, producer_varr, var_producer);
  producers = VARR_ADDR (var_producer_t, producer_varr);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    curr_producer_age++;
    for (bb_insn_t bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      curr_op_age++;
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn);
      dst_var_p = FALSE;
      for (i = 0; i < nops; i++) {
	MIR_insn_op_mode (insn, i, &out_p);
	op = &insn->ops[i];
	if (out_p && (op->mode == MIR_OP_REG || op->mode == MIR_OP_HARD_REG)) {
	  gen_assert (! dst_var_p); /* Any MIR insn has one output at most */
	  dst_op = op;
	  dst_var_p = TRUE;
	  continue;
	}
	process_op_use (op, bb_insn);
      }
      if (dst_var_p) {
	dst_var = dst_op->mode == MIR_OP_HARD_REG ? dst_op->u.hard_reg : reg2var (dst_op->u.reg);
	producers[dst_var].producer_age = curr_producer_age;
	producers[dst_var].op_age = curr_op_age;
	producers[dst_var].producer = var_occ = new_insn_var_occ (dst_var, insn);
	dst_op->data = producers[dst_var].producer;
      }
    }
    ccp_end_bb = bb;
    bitmap_for_each (bb->live_out, process_bb_end);
  }
}

#undef live_in
#undef live_out

static void var_occs_clear (void) {
  HTAB_CLEAR (var_occ_t, var_occ_tab, NULL);
  while (VARR_LENGTH (var_occ_t, var_occs) != 0)
    free (VARR_POP (var_occ_t, var_occs));
  VARR_TRUNC (bb_start_occ_list_t, bb_start_occ_list_varr, 0);
  VARR_TRUNC (var_producer_t, producer_varr, 0);
}

static void init_var_occs (void) {
  VARR_CREATE (bb_start_occ_list_t, bb_start_occ_list_varr, 256);
  VARR_CREATE (var_occ_t, var_occs, 1024);
  curr_producer_age = curr_op_age = 0;
  VARR_CREATE (var_producer_t, producer_varr, 256);
  HTAB_CREATE (var_occ_t, var_occ_tab, 1024, var_occ_hash, var_occ_eq);
}

static void finish_var_occs (void) {
  VARR_DESTROY (bb_start_occ_list_t, bb_start_occ_list_varr);
  VARR_DESTROY (var_occ_t, var_occs);
  VARR_DESTROY (var_producer_t, producer_varr);
  HTAB_DESTROY (var_occ_t, var_occ_tab);
}

static bitmap_t bb_visited;

static VARR (bb_t) *ccp_bbs;
static VARR (var_occ_t) *ccp_var_occs;
DEF_VARR (bb_insn_t);
static VARR (bb_insn_t) *ccp_insns;

static void initiate_ccp_info (void) {
  bb_insn_t bb_insn;
  
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) != NULL
	&& MIR_branch_code_p (bb_insn->insn->code) && bb_insn->insn->code != MIR_JMP) {
      for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges);
	   e != NULL;
	   e = DLIST_NEXT (out_edge_t, e))
	if (DLIST_HEAD (out_edge_t, e->dst->out_edges) != NULL) /* ignore exit bb */
	  e->skipped_p = TRUE;
    }
  }
  bitmap_clear (bb_visited);
  VARR_TRUNC (var_occ_t, ccp_var_occs, 0);
  VARR_TRUNC (bb_insn_t, ccp_insns, 0);
  VARR_TRUNC (bb_t, ccp_bbs, 0);
  VARR_PUSH (bb_t, ccp_bbs, DLIST_HEAD (bb_t, curr_cfg->bbs)); /* entry bb */
}

static int var_op_p (MIR_insn_t insn, size_t nop) {
  return insn->ops[nop].mode == MIR_OP_HARD_REG || insn->ops[nop].mode == MIR_OP_REG;
}

static enum ccp_val_kind get_op (MIR_insn_t insn, size_t nop, const_t *val) {
  MIR_op_t op;
  var_occ_t var_occ, def;
  
  if (! var_op_p (insn, nop)) {
    if ((op = insn->ops[nop]).mode == MIR_OP_INT) {
      val->uns_p = FALSE; val->u.i = op.u.i;
      return CCP_CONST;
    } else if (op.mode == MIR_OP_UINT) {
      val->uns_p = TRUE; val->u.u = op.u.u;
      return CCP_CONST;
    }
    return CCP_VARYING;
  }
  var_occ = insn->ops[nop].data;
  def = var_occ->def;
  if (def->val_kind == CCP_CONST)
    *val = def->val;
  return def->val_kind;
}

static enum ccp_val_kind get_2ops (MIR_insn_t insn, const_t *val1, int out_p) {
  if (out_p && ! var_op_p (insn, 0))
    return CCP_UNKNOWN;
  return get_op (insn, 1, val1);
}

static enum ccp_val_kind get_3ops (MIR_insn_t insn, const_t *val1, const_t *val2, int out_p) {
  enum ccp_val_kind res1, res2;
  
  if (out_p && ! var_op_p (insn, 0))
    return CCP_UNKNOWN;
  if ((res1 = get_op (insn, 1, val1)) == CCP_VARYING)
    return CCP_VARYING;
  if ((res2 = get_op (insn, 2, val2)) == CCP_VARYING)
    return CCP_VARYING;
  return res1 == CCP_UNKNOWN || res2 == CCP_UNKNOWN ? CCP_UNKNOWN : CCP_CONST;
}

static enum ccp_val_kind get_2iops (MIR_insn_t insn, int64_t *p, int out_p) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, &val, out_p)))
    return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_2isops (MIR_insn_t insn, int32_t *p, int out_p) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, &val, out_p)))
    return res;
  *p = val.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_2usops (MIR_insn_t insn, uint32_t *p, int out_p) {
  const_t val;
  enum ccp_val_kind res;
  
  if ((res = get_2ops (insn, &val, out_p)))
    return res;
  *p = val.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3iops (MIR_insn_t insn, int64_t *p1, int64_t *p2, int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, &val1, &val2, out_p)))
    return res;
  *p1 = val1.u.i; *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3isops (MIR_insn_t insn, int32_t *p1, int32_t *p2, int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, &val1, &val2, out_p)))
    return res;
  *p1 = val1.u.i; *p2 = val2.u.i;
  return CCP_CONST;
}

static enum ccp_val_kind get_3uops (MIR_insn_t insn, uint64_t *p1, uint64_t *p2, int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, &val1, &val2, out_p)))
    return res;
  *p1 = val1.u.u; *p2 = val2.u.u;
  return CCP_CONST;
}

static enum ccp_val_kind get_3usops (MIR_insn_t insn, uint32_t *p1, uint32_t *p2, int out_p) {
  const_t val1, val2;
  enum ccp_val_kind res;
  
  if ((res = get_3ops (insn, &val1, &val2, out_p)))
    return res;
  *p1 = val1.u.u; *p2 = val2.u.u;
  return CCP_CONST;
}

#define EXT(tp) do { int64_t p;					                \
    if ((ccp_res = get_2iops (insn, &p, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = (tp) p;					\
  } while (0)

#define IOP2(op) do { int64_t p;			 			\
    if ((ccp_res = get_2iops (insn, &p, TRUE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = op p;	  	 	 			\
  } while (0)

#define IOP2S(op) do { int32_t p;		  	 			\
    if ((ccp_res = get_2isops (insn, &p, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = op p;	  	 	 			\
  } while (0)

#define UOP2S(op) do { uint32_t p;		  	 			\
    if ((ccp_res = get_2usops (insn, &p, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.u = op p;	  	 	 			\
  } while (0)

#define IOP3(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define IOP3S(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UOP3(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const;	\
    val.uns_p = TRUE; val.u.u = p1 op p2;	  	 				\
  } while (0)

#define UOP3S(op) do { uint32_t p1, p2;		  	 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = TRUE; val.u.u = p1 op p2;	  	 				\
  } while (0)

#define IOP30(op) do {					 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const0;	\
    IOP3(op);											\
  } while (0)

#define IOP3S0(op) do {					 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.i == 0) goto non_const0;	\
    IOP3S(op);											\
  } while (0)

#define UOP30(op) do {					 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const0;	\
    UOP3(op);											\
  } while (0)

#define UOP3S0(op) do {					 					\
    if ((ccp_res = get_op (insn, 2, &val)) != CCP_CONST || val.u.u == 0) goto non_const0;	\
    UOP3S(op);											\
  } while (0)

#define ICMP(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define ICMPS(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UCMP(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define UCMPS(op) do { uint32_t p1, p2;		  	 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, TRUE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BICMP(op) do { int64_t p1, p2;			 				\
    if ((ccp_res = get_3iops (insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BICMPS(op) do { int32_t p1, p2;		  	 				\
    if ((ccp_res = get_3isops (insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BUCMP(op) do { uint64_t p1, p2;			 				\
    if ((ccp_res = get_3uops (insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const;	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

#define BUCMPS(op) do { uint32_t p1, p2;		 				\
    if ((ccp_res = get_3usops (insn, &p1, &p2, FALSE)) != CCP_CONST) goto non_const; 	\
    val.uns_p = FALSE; val.u.i = p1 op p2;	  	 				\
  } while (0)

static int get_res_op (MIR_insn_t insn, MIR_op_t *op) {
  int out_p;
  MIR_op_t proto_op;
  MIR_proto_t proto;
  
  if (MIR_call_code_p (insn->code)) {
    proto_op = insn->ops[0];
    mir_assert (proto_op.mode == MIR_OP_REF && proto_op.u.ref->item_type == MIR_proto_item);
    proto = proto_op.u.ref->u.proto;
    if (proto->res_type == MIR_T_V)
      return FALSE;
    mir_assert (MIR_insn_nops (insn) >= 3);
    *op = insn->ops[2];
    return TRUE;
  }
  if (MIR_insn_nops (insn) < 1)
    return FALSE;
  MIR_insn_op_mode (insn, 0, &out_p);
  if (! out_p)
    return FALSE;
  *op = insn->ops[0];
  return TRUE;
}

static int ccp_insn_update (MIR_insn_t insn, const_t *res) { // ??? should we do CCP for FP too
  MIR_op_t op;
  int out_p;
  enum ccp_val_kind ccp_res;
  const_t val;
  var_occ_t var_occ;
  enum ccp_val_kind val_kind;
  
  switch (insn->code) {
  case MIR_MOV:  IOP2(+); break;
  case MIR_EXT8: EXT(int8_t); break;
  case MIR_EXT16: EXT(int16_t); break;
  case MIR_EXT32: EXT(int32_t); break;
  case MIR_UEXT8: EXT(uint8_t); break;
  case MIR_UEXT16: EXT(uint16_t); break;
  case MIR_UEXT32: EXT(uint32_t); break;
      
  case MIR_NEG:  IOP2(-); break;
  case MIR_NEGS: IOP2S(-); break;
      
  case MIR_ADD:  IOP3(+); break;
  case MIR_ADDS: IOP3S(+); break;
      
  case MIR_SUB:  IOP3(-); break; 
  case MIR_SUBS: IOP3S(-); break; 
      
  case MIR_MUL:   IOP3(*); break;
  case MIR_MULS:  IOP3S(*); break;

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
    
  case MIR_EQ:  ICMP(==); break;
  case MIR_EQS: ICMPS(==); break;
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
#ifdef NDEBUG
  {
    int out_p;

    MIR_insn_op_mode (insn, 0, &out_p); /* result here is always 0-th op */
    gen_assert (out_p);
  }
#endif
  var_occ = insn->ops[0].data;
  val_kind = var_occ->val_kind;
  gen_assert (var_occ->def == NULL && (val_kind == CCP_UNKNOWN || val_kind == CCP_CONST));
  var_occ->val_kind = CCP_CONST;
  var_occ->val = val;
  if (res != NULL)
    *res = val;
  return val_kind != CCP_CONST;
 non_const0:
  if (ccp_res == CCP_CONST && val.u.i == 0)
    ccp_res = CCP_VARYING;
 non_const:
  if (ccp_res == CCP_UNKNOWN)
    return FALSE;
  gen_assert (ccp_res == CCP_VARYING);
  if (! get_res_op (insn, &op) || (op.mode != MIR_OP_HARD_REG && op.mode != MIR_OP_REG))
    return FALSE;
  var_occ = op.data;
  gen_assert (var_occ->def == NULL);
  val_kind = var_occ->val_kind;
  var_occ->val_kind = CCP_VARYING;
  return val_kind != CCP_VARYING;
}

static enum ccp_val_kind ccp_branch_update (MIR_insn_t insn, int *res) {
  enum ccp_val_kind ccp_res;
  const_t val;
  
  switch (insn->code) {
  case MIR_BT: case MIR_BTS: case MIR_BF: case MIR_BFS:
    if ((ccp_res = get_op (insn, 1, &val)) != CCP_CONST)
      return ccp_res;
    if (insn->code == MIR_BTS || insn->code == MIR_BFS)
      *res = val.uns_p ? (uint32_t) val.u.u != 0 : (int32_t) val.u.i != 0;
    else
      *res = val.uns_p ? val.u.u != 0 : val.u.i != 0;
    if (insn->code == MIR_BF || insn->code == MIR_BFS)
      *res = ! *res;
    return CCP_CONST;
  case MIR_BEQ:  BICMP(==); break;
  case MIR_BEQS: BICMPS(==); break;
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
    return CCP_VARYING; // ??? should we do CCP for FP BCMP too
  }
  *res = val.u.i;
  return CCP_CONST;
 non_const:
  return ccp_res;
}

static void ccp_push_used_insns (var_occ_t def) {
  for (var_occ_t var_occ = DLIST_HEAD (var_occ_t, def->uses);
       var_occ != NULL;
       var_occ = DLIST_NEXT (var_occ_t, var_occ))
    if (var_occ->place.type == OCC_INSN) {
      bb_insn_t bb_insn = var_occ->place.u.insn->data;
      
      if (bb_insn->flag)
	continue; /* already in ccp_insns */
      VARR_PUSH (bb_insn_t, ccp_insns, bb_insn);
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (debug_file, "           pushing bb%d insn: ", bb_insn->bb->index);
	  MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, TRUE);
	}
#endif
      bb_insn->flag = TRUE;
    } else {
      struct var_occ vos;
      var_occ_t tab_var_occ;
      
      gen_assert (var_occ->place.type == OCC_BB_END);
      for (edge_t e = DLIST_HEAD (out_edge_t, var_occ->place.u.bb->out_edges);
	   e != NULL;
	   e = DLIST_NEXT (out_edge_t, e)) {
	if (e->skipped_p)
	  continue;
	vos = *var_occ;
	vos.place.type = OCC_BB_START;
	vos.place.u.bb = e->dst;
	if (! HTAB_DO (var_occ_t, var_occ_tab, &vos, HTAB_FIND, tab_var_occ) || tab_var_occ->flag)
	  continue; /* var_occ at the start of BB in subsequent BB is already in ccp_var_occs */
#if MIR_GEN_DEBUG
	if (debug_file != NULL)
	  fprintf (debug_file, "           pushing var%lu(%s) at start of bb%d\n",
		   (long unsigned) vos.var,
		   var_is_reg_p (vos.var)
		   ? MIR_reg_name (var2reg (vos.var), curr_func_item->u.func) : "",
		   e->dst->index);
#endif
	VARR_PUSH (var_occ_t, ccp_var_occs, tab_var_occ);
	tab_var_occ->flag = TRUE;
      }
    }
}

static void ccp_process_bb_start_var_occ (var_occ_t var_occ, bb_t bb, int from_bb_process_p) {
  struct var_occ vos;
  var_occ_t tab_var_occ, def;
  int change_p;
    
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
    fprintf (debug_file, "       %sprocessing var%lu(%s) at start of bb%d:",
	     from_bb_process_p ? "  " : "",
	     (long unsigned) var_occ->var,
	     var_is_reg_p (var_occ->var)
	     ? MIR_reg_name (var2reg (var_occ->var), curr_func_item->u.func) : "",
	     var_occ->place.u.bb->index);
#endif
  gen_assert (var_occ->place.type == OCC_BB_START && bb == var_occ->place.u.bb);
  if (var_occ->val_kind == CCP_VARYING) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL)
      fprintf (debug_file, " already varying\n");
#endif
    return;
  }
  change_p = FALSE;
  for (edge_t e = DLIST_HEAD (in_edge_t, bb->in_edges); e != NULL; e = DLIST_NEXT (in_edge_t, e)) {
    /* Update var_occ value: */
    if (e->skipped_p)
      continue;
    vos.place.type = OCC_BB_END;
    vos.place.u.bb = e->src;
    vos.var = var_occ->var;
    if (! HTAB_DO (var_occ_t, var_occ_tab, &vos, HTAB_FIND, tab_var_occ)) {
      gen_assert (FALSE);
      return;
    }
    def = tab_var_occ->def;
    gen_assert (def != NULL);
    if (def->val_kind == CCP_UNKNOWN)
      continue;
    gen_assert (def->def == NULL && var_occ->def == NULL);
    if (var_occ->val_kind == CCP_UNKNOWN || def->val_kind == CCP_VARYING) {
      change_p = var_occ->val_kind != def->val_kind;
      var_occ->val_kind = def->val_kind;
      if (def->val_kind == CCP_VARYING)
	break;
      if (def->val_kind == CCP_CONST)
	var_occ->val = def->val;
    } else {
      gen_assert (var_occ->val_kind == CCP_CONST && def->val_kind == CCP_CONST);
      if (var_occ->val.uns_p != def->val.uns_p
	  || (var_occ->val.uns_p && var_occ->val.u.u != def->val.u.u)
	  || (! var_occ->val.uns_p && var_occ->val.u.i != def->val.u.i)) {
	var_occ->val_kind = CCP_VARYING;
	change_p = TRUE;
	break;
      }
    }
  }
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    if (var_occ->val_kind != CCP_CONST) {
      fprintf (debug_file, "         %s%s\n", change_p ? "changed to " : "",
	       var_occ->val_kind == CCP_UNKNOWN ? "unknown" : "varying");
    } else {
      fprintf (debug_file, "         %sconst ", change_p ? "changed to " : "");
      print_const (debug_file, var_occ->val);
      fprintf (debug_file, "\n");
    }
  }
#endif
  if (change_p)
    ccp_push_used_insns (var_occ);
}

static void ccp_process_active_edge (edge_t e) {
  if (e->skipped_p && ! e->dst->flag) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL)
      fprintf (debug_file, "         Make edge bb%d->bb%d active\n", e->src->index, e->dst->index);
#endif
    e->dst->flag = TRUE; /* just activated edge whose dest is not in ccp_bbs */
    VARR_PUSH (bb_t, ccp_bbs, e->dst);
  }
  e->skipped_p = FALSE;
}

static void ccp_make_insn_update (MIR_insn_t insn) {
  MIR_op_t op;
  var_occ_t var_occ;

  if (! ccp_insn_update (insn, NULL)) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      if (get_res_op (insn, &op)) {
	var_occ = op.data;
	if (var_occ->val_kind == CCP_UNKNOWN) {
	  fprintf (debug_file, " -- make the result unknown");
	} else if (var_occ->val_kind == CCP_VARYING) {
	  fprintf (debug_file, " -- keep the result varying");
	} else {
	  gen_assert (var_occ->val_kind == CCP_CONST);
	  fprintf (debug_file, " -- keep the result a constant ");
	  print_const (debug_file, var_occ->val);
	}
      }
      fprintf (debug_file, "\n");
    }
#endif
  } else {
    if (! get_res_op (insn, &op))
      gen_assert (FALSE);
    var_occ = op.data;
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      if (var_occ->val_kind == CCP_VARYING) {
	fprintf (debug_file, " -- make the result varying\n");
      } else {
	gen_assert (var_occ->val_kind == CCP_CONST);
	fprintf (debug_file, " -- make the result a constant ");
	print_const (debug_file, var_occ->val);
	fprintf (debug_file, "\n");
      }
    }
#endif
    ccp_push_used_insns (var_occ);
  }
}

static void ccp_process_insn (bb_insn_t bb_insn) {
  int res;
  enum ccp_val_kind ccp_res;
  edge_t e;
  bb_t bb = bb_insn->bb;
  MIR_insn_t insn = bb_insn->insn;

#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "       processing bb%d insn: ", bb_insn->bb->index);
    MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
  }
#endif
  if (! MIR_branch_code_p (insn->code) || insn->code == MIR_JMP) {
    ccp_make_insn_update (insn);
    return;
  }
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
    fprintf (debug_file, "\n");
#endif
  if ((ccp_res = ccp_branch_update (insn, &res)) == CCP_CONST) {
    /* Remember about an edge to exit bb.  First edge is always for
       fall through and the 2nd edge is for jump bb. */
    gen_assert (DLIST_LENGTH (out_edge_t, bb->out_edges) >= 2);
    e = res ? DLIST_EL (out_edge_t, bb->out_edges, 1) : DLIST_EL (out_edge_t, bb->out_edges, 0);
    ccp_process_active_edge (e);
  } else if (ccp_res == CCP_VARYING) { /* activate all edges */
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
      ccp_process_active_edge (e);
  }
}

static void ccp_process_bb (bb_t bb) {
  bb_insn_t bb_insn;
  edge_t e;
  
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
    fprintf (debug_file, "       processing bb%d\n", bb->index);
#endif
  for (var_occ_t var_occ = DLIST_HEAD (var_occ_t, bb_start_occ_lists[bb->index]);
       var_occ != NULL;
       var_occ = DLIST_NEXT (var_occ_t, var_occ))
    ccp_process_bb_start_var_occ (var_occ, bb, TRUE);
  if (! bitmap_set_bit_p (bb_visited, bb->index))
    return;
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
       bb_insn != NULL;
       bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      fprintf (debug_file, "         processing insn: ");
      MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
    }
#endif
    ccp_make_insn_update (bb_insn->insn);
  }
  if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL
      || ! MIR_branch_code_p (bb_insn->insn->code) || bb_insn->insn->code == MIR_JMP) {
    for (e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e)) {
      gen_assert (! e->skipped_p);
      if (! bitmap_bit_p (bb_visited, e->dst->index) && ! e->dst->flag) {
	e->dst->flag = TRUE; /* first process of dest which is not in ccp_bbs */
	VARR_PUSH (bb_t, ccp_bbs, e->dst);
      }
      ccp_process_active_edge (e);
    }
  }
}

static void ccp_traverse (bb_t bb) {
  bb->flag = TRUE;
  for (edge_t e = DLIST_HEAD (out_edge_t, bb->out_edges); e != NULL; e = DLIST_NEXT (out_edge_t, e))
    if (! e->skipped_p && ! e->dst->flag)
      ccp_traverse (e->dst); /* visit unvisited active edge destination */
}

static int get_res_val (MIR_insn_t insn, const_t *val) {
  int out_p;
  var_occ_t var_occ;
  MIR_op_t op;
  
  if (! get_res_op (insn, &op))
    return FALSE;
  if (! var_op_p (insn, 0))
    return FALSE;
  var_occ = op.data;
  gen_assert (var_occ->def == NULL);
  if (var_occ->val_kind != CCP_CONST)
    return FALSE;
  *val = var_occ->val;
  return TRUE;
}

static int ccp_modify (void) {
  bb_t bb, next_bb;
  bb_insn_t bb_insn, next_bb_insn;
  const_t val;
  MIR_op_t op;
  MIR_insn_t insn;
  int res, change_p = FALSE;
  
#ifndef NDEBUG
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    gen_assert (! bb->flag);
#endif
  ccp_traverse (DLIST_HEAD (bb_t, curr_cfg->bbs)); /* entry */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = next_bb) {
    next_bb = DLIST_NEXT (bb_t, bb);
    if (! bb->flag) {
      change_p = TRUE;
#if MIR_GEN_DEBUG
      if (debug_file != NULL)
	fprintf (debug_file, "  deleting unreachable bb %d and its edges\n", bb->index);
#endif
      for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
	next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
	insn = bb_insn->insn;
	gen_delete_insn (curr_func_item, insn);
      }
      delete_bb (bb);
      continue;
    }
    bb->flag = FALSE; /* reset for the future use */
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      if (get_res_val (bb_insn->insn, &val) && (bb_insn->insn->code != MIR_MOV
						|| (bb_insn->insn->ops[1].mode != MIR_OP_INT
						    && bb_insn->insn->ops[1].mode != MIR_OP_UINT))) {
	change_p = TRUE;
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (debug_file, "  changing insn ");
	  MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
	}
#endif
	op = val.uns_p ? MIR_new_uint_op (val.u.u) : MIR_new_int_op (val.u.i);
#ifdef NDEBUG
	{
	  int out_p;
	  
	  MIR_insn_op_mode (insn, 0, &out_p); /* result here is always 0-th op */
	  gen_assert (out_p);
	}
#endif
	insn = MIR_new_insn (MIR_MOV, bb_insn->insn->ops[0], op);
	MIR_insert_insn_before (curr_func_item, bb_insn->insn, insn);
	MIR_remove_insn (curr_func_item, bb_insn->insn);
	insn->data = bb_insn;
	bb_insn->insn = insn;
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (debug_file, "    on insn ");
	  MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	}
#endif
      }
      // nulify/free op.data ???
    }
    if ((bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns)) == NULL)
      continue;
    insn = bb_insn->insn;
    if (! MIR_branch_code_p (insn->code) || insn->code == MIR_JMP
	|| ccp_branch_update (insn, &res) != CCP_CONST)
      continue;
    change_p = TRUE;
    if (! res) {
#if MIR_GEN_DEBUG
      if (debug_file != NULL) {
	fprintf (debug_file, "  removing branch insn ");
	MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, TRUE);
	fprintf (debug_file, "\n");
      }
#endif
      gen_delete_insn (curr_func_item, insn);
      delete_edge (DLIST_EL (out_edge_t, bb->out_edges, 1));
    } else {
      insn = MIR_new_insn (MIR_JMP, bb_insn->insn->ops[0]); /* label is always 0-th op */
#if MIR_GEN_DEBUG
      if (debug_file != NULL) {
	fprintf (debug_file, "  changing branch insn ");
	MIR_output_insn (debug_file, bb_insn->insn, curr_func_item->u.func, FALSE);
	fprintf (debug_file, " onto jump insn ");
	MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	fprintf (debug_file, "\n");
      }
#endif
      MIR_insert_insn_before (curr_func_item, bb_insn->insn, insn);
      MIR_remove_insn (curr_func_item, bb_insn->insn);
      insn->data = bb_insn;
      bb_insn->insn = insn;
      delete_edge (DLIST_EL (out_edge_t, bb->out_edges, 0));
    }
  }
  return change_p;
}

static int ccp (void) { /* conditional constant propagation */
#if MIR_GEN_DEBUG
  fprintf (stderr, "  CCP analysis:\n");
#endif
  build_var_occ_web ();
  bb_visited = temp_bitmap;
  initiate_ccp_info ();
  while (VARR_LENGTH (bb_t, ccp_bbs) != 0
	 || VARR_LENGTH (var_occ_t, ccp_var_occs) != 0
	 || VARR_LENGTH (bb_insn_t, ccp_insns) != 0) {
    while (VARR_LENGTH (bb_t, ccp_bbs) != 0) {
      bb_t bb = VARR_POP (bb_t, ccp_bbs);
      
      bb->flag = FALSE;
      ccp_process_bb (bb);
    }
    while (VARR_LENGTH (var_occ_t, ccp_var_occs) != 0) {
      var_occ_t var_occ = VARR_POP (var_occ_t, ccp_var_occs);

      var_occ->flag = FALSE;
      gen_assert (var_occ->place.type == OCC_BB_START);
      ccp_process_bb_start_var_occ (var_occ, var_occ->place.u.bb, FALSE);
    }
    while (VARR_LENGTH (bb_insn_t, ccp_insns) != 0) {
      bb_insn_t bb_insn = VARR_POP (bb_insn_t, ccp_insns);

      gen_assert (bb_insn->flag);
      bb_insn->flag = FALSE;
      ccp_process_insn (bb_insn);
    }
  }
#if MIR_GEN_DEBUG
  fprintf (stderr, "  CCP modification:\n");
#endif
  return ccp_modify ();
}

static void ccp_clear (void) {
  var_occs_clear ();
}

static void init_ccp (void) {
  init_var_occs ();
  VARR_CREATE (bb_t, ccp_bbs, 256);
  VARR_CREATE (var_occ_t, ccp_var_occs, 256);
  VARR_CREATE (bb_insn_t, ccp_insns, 256);
}

static void finish_ccp (void) {
  finish_var_occs ();
  VARR_DESTROY (bb_t, ccp_bbs);
  VARR_DESTROY (var_occ_t, ccp_var_occs);
  VARR_DESTROY (bb_insn_t, ccp_insns);
}

#undef live_in
#undef live_out



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

static void initiate_bb_live_info (bb_t bb, int moves_p) {
  MIR_insn_t insn;
  size_t nops, i, niter;
  MIR_reg_t nregs, n, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  MIR_op_t op;
  int out_p;
  mv_t mv, next_mv;
  reg_info_t *breg_infos;
  
  gen_assert (bb->live_in != NULL && bb->live_out != NULL
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
    nops = MIR_insn_nops (insn);
    /* Process output ops on 0-th iteration, then input ops. */
    for (niter = 0; niter <= 1; niter++) {
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
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
    get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
    if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG) {
      bitmap_clear_bit_p (bb->live_gen, early_clobbered_hard_reg1);
      bitmap_set_bit_p (bb->live_kill, early_clobbered_hard_reg1);
    }
    if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG) {
      bitmap_clear_bit_p (bb->live_gen, early_clobbered_hard_reg2);
      bitmap_set_bit_p (bb->live_kill, early_clobbered_hard_reg2);
    }
    if (MIR_call_code_p (insn->code)) {
      bitmap_ior (bb->live_kill, bb->live_kill, call_used_hard_regs);
      bitmap_and_compl (bb->live_gen, bb->live_gen, call_used_hard_regs);
      bitmap_ior (bb->live_gen, bb->live_gen, bb_insn->call_hard_reg_args);
    }
    if (moves_p && move_p (insn)) {
      mv = get_free_move ();
      mv->bb_insn = bb_insn;
      if (insn->ops[0].mode == MIR_OP_REG)
	DLIST_APPEND (dst_mv_t, breg_infos[reg2breg (insn->ops[0].u.reg)].dst_moves, mv);
      if (insn->ops[1].mode == MIR_OP_REG)
	DLIST_APPEND (src_mv_t, breg_infos[reg2breg (insn->ops[1].u.reg)].src_moves, mv);
    }
  }
}

static void initiate_live_info (int moves_p) {
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    initiate_bb_live_info (bb, moves_p);
}

static void calculate_func_cfg_live_info (int moves_p) {
  initiate_live_info (moves_p);
  solve_dataflow (FALSE, live_con_func_0, live_con_func_n, live_trans_func);
}

static void add_bb_insn_dead_vars (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t nops, i;
  MIR_reg_t var, var2, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  MIR_op_t op;
  int out_p, live_start1_p, live_start2_p;
  bitmap_t live;
  
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      clear_bb_insn_dead_vars (bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
	if (! out_p || (op.mode != MIR_OP_REG && op.mode != MIR_OP_HARD_REG))
	  continue;
	var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
	bitmap_clear_bit_p (live, var);
      }
      if (MIR_call_code_p (insn->code))
	bitmap_and_compl (live, live, call_used_hard_regs);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
	live_start1_p = live_start2_p = FALSE;
	switch (op.mode) {
	case MIR_OP_REG:
	  if (! out_p)
	    live_start1_p = bitmap_set_bit_p (live, var = reg2var (op.u.reg));
	  break;
	case MIR_OP_HARD_REG:
	  if (! out_p)
	    live_start1_p = bitmap_set_bit_p (live, var = op.u.hard_reg);
	  break;
	case MIR_OP_MEM:
	  if (op.u.mem.base != 0)
	    live_start1_p = bitmap_set_bit_p (live, var = reg2var (op.u.mem.base));
	  if (op.u.mem.index != 0)
	    live_start2_p = bitmap_set_bit_p (live, var2 = reg2var (op.u.mem.index));
	  break;
	case MIR_OP_HARD_REG_MEM:
	  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG)
	    live_start1_p = bitmap_set_bit_p (live, var = op.u.hard_reg_mem.base);
	  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG)
	    live_start2_p = bitmap_set_bit_p (live, var2 = op.u.hard_reg_mem.index);
	  break;
	default:
	  break;
	}
	if (live_start1_p)
	  add_bb_insn_dead_var (bb_insn, var);
	if (live_start2_p)
	  add_bb_insn_dead_var (bb_insn, var2);
      }
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
	bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
	bitmap_clear_bit_p (live, early_clobbered_hard_reg2);
      if (MIR_call_code_p (insn->code))
	bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
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

  gen_assert (finish < 0 || start <= finish);
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

  if (bitmap_clear_bit_p (live_vars, var)) {
    lr = VARR_GET (live_range_t, var_live_ranges, var); lr->finish = point;
  } else { /* insn with unused result: result still needs a register */
    VARR_SET (live_range_t, var_live_ranges, var,
	      create_live_range (point, point, VARR_GET (live_range_t, var_live_ranges, var)));
  }
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
  gen_assert (get_nvars () == VARR_LENGTH (live_range_t, var_live_ranges));
  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++) {
    if ((lr = VARR_GET (live_range_t, var_live_ranges, i)) == NULL)
      continue;
    fprintf (debug_file, "%lu", i);
    if (var_is_reg_p (i))
      fprintf (debug_file, " (%s:%s)", MIR_type_str (MIR_reg_type (var2reg (i), curr_func_item->u.func)),
	       MIR_reg_name (var2reg (i), curr_func_item->u.func));
    fprintf (debug_file, ":");
    for (; lr != NULL; lr = lr->next)
      fprintf (debug_file, " [%d..%d]", lr->start, lr->finish);
    fprintf (debug_file, "\n");
  }
}
#endif

static void build_live_ranges (void) {
  MIR_insn_t insn;
  MIR_reg_t nvars, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  size_t i, nops;
  int incr_p, out_p;
  MIR_op_t op;
  
  curr_point = 0;
  nvars = get_nvars ();
  gen_assert (VARR_LENGTH (live_range_t, var_live_ranges) == 0);
  for (i = 0; i < nvars; i++)
    VARR_PUSH (live_range_t, var_live_ranges, NULL);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL)
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
	if (debug_file != NULL) {
	  fprintf (debug_file, "  p%-5d", curr_point);
	  print_bb_insn (bb_insn, TRUE);
	}
#endif
      nops = MIR_insn_nops (insn);
      incr_p = FALSE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
	if (op.mode == MIR_OP_REG && out_p)
	  incr_p |= make_reg_dead (op.u.reg, FALSE, curr_point);
	else if (op.mode == MIR_OP_HARD_REG && out_p)
	  incr_p |= make_reg_dead (op.u.hard_reg, TRUE, curr_point);
      }
      if (MIR_call_code_p (insn->code)) {
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
	  MIR_insn_op_mode (insn, i, &out_p);
	  if (! out_p)
	    incr_p |= make_reg_live (op.u.reg, FALSE, curr_point);
	  break;
	case MIR_OP_HARD_REG:
	  MIR_insn_op_mode (insn, i, &out_p);
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
      }
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG) {
	incr_p |= make_reg_live (early_clobbered_hard_reg1, TRUE, curr_point);
	incr_p |= make_reg_dead (early_clobbered_hard_reg1, TRUE, curr_point);
      }
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG) {
	incr_p |= make_reg_live (early_clobbered_hard_reg2, TRUE, curr_point);
	incr_p |= make_reg_dead (early_clobbered_hard_reg2, TRUE, curr_point);
      }
      if (incr_p)
	curr_point++;
    }
    gen_assert (bitmap_equal_p (live_vars, bb->live_in));
    bitmap_for_each (live_vars, make_dead);
    if (! bitmap_empty_p (bb->live_in))
      curr_point++;
  }
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
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
  MIR_type_t type;
  int slots_num;
  int j, k;
  live_range_t lr;
  bitmap_t bm;
  size_t profit, best_profit;
  bitmap_t *point_used_locs_addr;
  
  if (nregs == 0)
    return;
  curr_breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  VARR_TRUNC (MIR_reg_t, breg_renumber, 0);
  for (i = 0; i < nregs; i++)
    VARR_PUSH (MIR_reg_t, breg_renumber, MIR_NON_HARD_REG);
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
  VARR_TRUNC (bitmap_t, point_used_locs, 0);
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
  for (i = 0; i < nregs; i++) { /* hard reg and stack slot assignment */
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
    type = MIR_reg_type (reg, curr_func_item->u.func);
    for (loc = 0; loc <= func_stack_slots_num + MAX_HARD_REG; loc++) {
      if (loc <= MAX_HARD_REG && ! hard_reg_type_ok_p (loc, type))
	continue;
      slots_num = locs_num (loc, type);
      for (k = 0; k < slots_num; k++)
	if ((loc + k <= MAX_HARD_REG
	     && (fixed_hard_reg_p (loc + k)
		 || (call_used_hard_reg_p (loc + k) && curr_breg_infos[breg].calls_num > 0)))
	    || bitmap_bit_p (conflict_locs, loc + k))
	 break;
      if (k < slots_num)
	continue;
      if (loc > MAX_HARD_REG && loc % slots_num != 0)
	continue; /* we align stack slots according to the type size */
      profit = VARR_GET (size_t, loc_profit_ages, loc) != curr_age ? 0 : VARR_GET (size_t, loc_profits, loc);
      if (best_loc == MIR_NON_HARD_REG || best_profit < profit) {
	best_loc = loc;
	best_profit = profit;
      }
      if (best_loc != MIR_NON_HARD_REG && loc == MAX_HARD_REG)
	break;
    }
    slots_num = locs_num (best_loc, type);
    if (best_loc <= MAX_HARD_REG) {
      for (k = 0; k < slots_num; k++)
	bitmap_set_bit_p (func_assigned_hard_regs, best_loc + k);
    } else if (best_loc == MIR_NON_HARD_REG) { /* Add stack slot ??? */
      for (k = 0; k < slots_num; k++) {
	best_loc = VARR_LENGTH (size_t, loc_profits);
	VARR_PUSH (size_t, loc_profits, 0);
	VARR_PUSH (size_t, loc_profit_ages, 0);
      }
      func_stack_slots_num = best_loc - MAX_HARD_REG;
    }
    VARR_SET (MIR_reg_t, breg_renumber, breg, best_loc);
    for (lr = VARR_GET (live_range_t, var_live_ranges, var); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
	for (k = 0; k < slots_num; k++)
	  bitmap_set_bit_p (point_used_locs_addr[j], best_loc + k);
  }
  for (i = 0; i <= curr_point; i++)
    bitmap_destroy (VARR_POP (bitmap_t, point_used_locs));
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++Disposition after assignment:");
    for (i = 0; i < nregs; i++) {
      if (i % 8 == 0)
	fprintf (debug_file, "\n");
      reg = breg2reg (i);
      fprintf (debug_file, " %3u=>%-2u", reg2var (reg), VARR_GET (MIR_reg_t, breg_renumber, i));
    }
    fprintf (debug_file, "\n");
  }
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
  
  gen_assert (loc != MIR_NON_HARD_REG);
  if (loc <= MAX_HARD_REG)
    return loc;
  offset = get_stack_slot_offset (loc - MAX_HARD_REG - 1);
  gen_assert (data_mode == MIR_OP_INT || data_mode == MIR_OP_FLOAT || data_mode == MIR_OP_DOUBLE);
  if (data_mode == MIR_OP_INT) {
    type = MIR_T_I64; code = MIR_MOV;
    hard_reg = first_p ? TEMP_INT_HARD_REG1 : TEMP_INT_HARD_REG2;
  } else if (data_mode == MIR_OP_FLOAT) {
    type = MIR_T_F; code = MIR_FMOV;
    hard_reg = first_p ? TEMP_FLOAT_HARD_REG1 : TEMP_FLOAT_HARD_REG2;
  } else {
    type = MIR_T_D; code = MIR_DMOV;
    hard_reg = first_p ? TEMP_DOUBLE_HARD_REG1 : TEMP_DOUBLE_HARD_REG2;
  }
  hard_reg_op = _MIR_new_hard_reg_op (hard_reg);
  mem_op = _MIR_new_hard_reg_mem_op (type, offset, BP_HARD_REG, MIR_NON_HARD_REG, 0);
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
  MIR_op_t *op, in_op, out_op;
  MIR_mem_t mem;
  MIR_op_mode_t data_mode;
  MIR_reg_t hard_reg;
  int out_p, first_in_p;

  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = next_bb_insn) {
      next_bb_insn = DLIST_NEXT (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn);
      first_in_p = TRUE;
      for (i = 0; i < nops; i++) {
	op = &insn->ops[i];
	data_mode = MIR_insn_op_mode (insn, i, &out_p);
	if (out_p)
	  out_op = *op;
	else
	  in_op = *op;
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
		      : change_reg (op->u.mem.base, MIR_OP_INT, FALSE, bb_insn, FALSE));
	  gen_assert (op->u.mem.index == 0);
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
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (stderr, "Deleting noop move ");
	  MIR_output_insn (debug_file, insn, curr_func_item->u.func, FALSE);
	  fprintf (stderr, " which was ");
	  insn->ops[0] = out_op; insn->ops[1] = in_op;
	  MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	}
#endif
	gen_delete_insn (curr_func_item, insn);
      }
    }
  }
}



/* Code selection */

struct hreg_ref { /* We keep track of the last hard reg ref in this struct. */
  MIR_insn_t insn;
  size_t insn_num;
  size_t nop;
  char def_p, del_p; /* def/use and deleted */
};

typedef struct hreg_ref hreg_ref_t;

DEF_VARR (hreg_ref_t);

static VARR (size_t) *hreg_ref_ages;
static VARR (hreg_ref_t) *hreg_refs;
static hreg_ref_t *hreg_refs_addr;
static size_t *hreg_ref_ages_addr;

static size_t curr_bb_hreg_ref_age;
static size_t last_mem_ref_insn_num;

/* Output registers of def insns to delete the def insns after the substitution */
static VARR (MIR_reg_t) *dead_def_regs;

static MIR_insn_code_t commutative_insn_code (MIR_insn_code_t insn_code) {
  switch (insn_code) {
  case MIR_ADD: case MIR_ADDS: case MIR_FADD: case MIR_DADD:
  case MIR_MUL: case MIR_MULS: case MIR_FMUL: case MIR_DMUL:
  case MIR_AND: case MIR_OR: case MIR_XOR:
  case MIR_ANDS: case MIR_ORS: case MIR_XORS:
  case MIR_EQ: case MIR_EQS: case MIR_FEQ: case MIR_DEQ:
  case MIR_NE: case MIR_NES: case MIR_FNE: case MIR_DNE:
  case MIR_BEQ: case MIR_BEQS: case MIR_FBEQ: case MIR_DBEQ:
  case MIR_BNE: case MIR_BNES: case MIR_FBNE: case MIR_DBNE:
    return insn_code;
    break;
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
  case MIR_FLT: return MIR_FGT;
  case MIR_DLT: return MIR_DGT;
  case MIR_FLE: return MIR_FGE;
  case MIR_DLE: return MIR_DGE;
  case MIR_FGT: return MIR_FLT;
  case MIR_DGT: return MIR_DLT;
  case MIR_FGE: return MIR_FLE;
  case MIR_DGE: return MIR_DLE;
  case MIR_FBLT: return MIR_FBGT;
  case MIR_DBLT: return MIR_DBGT;
  case MIR_FBLE: return MIR_FBGE;
  case MIR_DBLE: return MIR_DBGE;
  case MIR_FBGT: return MIR_FBLT;
  case MIR_DBGT: return MIR_DBLT;
  case MIR_FBGE: return MIR_FBLE;
  case MIR_DBGE: return MIR_DBLE;
  default: return MIR_INSN_BOUND;
  }
}

static int obsolete_hard_reg_p (MIR_reg_t hard_reg, size_t def_insn_num) {
  return (hreg_ref_ages_addr[hard_reg] == curr_bb_hreg_ref_age
	  && hreg_refs_addr[hard_reg].insn_num > def_insn_num);
}

static int obsolete_hard_reg_op_p (MIR_op_t op, size_t def_insn_num) {
  return op.mode == MIR_OP_HARD_REG && obsolete_hard_reg_p (op.u.hard_reg, def_insn_num);
}

static int obsolete_op_p (MIR_op_t op, size_t def_insn_num) {
  if (obsolete_hard_reg_op_p (op, def_insn_num))
    return TRUE;
  if (op.mode != MIR_OP_HARD_REG_MEM)
    return FALSE;
  if (op.u.hard_reg_mem.base != MIR_NON_HARD_REG
      && obsolete_hard_reg_p (op.u.hard_reg_mem.base, def_insn_num))
    return TRUE;
  if (op.u.hard_reg_mem.index != MIR_NON_HARD_REG
      && obsolete_hard_reg_p (op.u.hard_reg_mem.index, def_insn_num))
    return TRUE;
  return last_mem_ref_insn_num > def_insn_num;
}

static int safe_hreg_substitution_p (MIR_reg_t hr, bb_insn_t bb_insn) {
  return (hr != MIR_NON_HARD_REG && hreg_ref_ages_addr[hr] == curr_bb_hreg_ref_age
	  /* It is not safe to substitute if there is another use after def insn before
	     the current insn as we delete def insn after the substitution. */
	  && hreg_refs_addr[hr].def_p && find_bb_insn_dead_var (bb_insn, hr) != NULL);
}

static int substitute_op_p (MIR_insn_t insn, size_t nop, int first_p) {
  MIR_insn_t def_insn = NULL;
  bb_insn_t bb_insn = insn->data;
  MIR_op_t src_op, op = insn->ops[nop];
  MIR_reg_t def_hr = MIR_NON_HARD_REG;
  size_t def_insn_num;
  int successfull_change_p = FALSE;
  
  if (first_p && op.mode == MIR_OP_HARD_REG && safe_hreg_substitution_p (op.u.hard_reg, bb_insn)) {
     /* It is not safe to substitute if there is another use after def insn before
	the current as we delete def insn after	substitution. */
    def_hr = op.u.hard_reg;
    if (! hreg_refs_addr[def_hr].def_p)
      return FALSE;
    gen_assert (! hreg_refs_addr[def_hr].del_p);
    def_insn = hreg_refs_addr[def_hr].insn;
    if (def_insn->code != MIR_MOV && def_insn->code != MIR_FMOV && def_insn->code != MIR_DMOV)
      return FALSE;
    if (obsolete_op_p (def_insn->ops[1], hreg_refs_addr[def_hr].insn_num))
      return FALSE; /* hr0 = ... hr1 ...; ...; hr1 = ...; ...; insn */
    gen_assert (hreg_refs_addr[def_hr].nop == 0);
    insn->ops[nop] = def_insn->ops[1];
    successfull_change_p = insn_ok_p (insn);
  } else if (op.mode == MIR_OP_HARD_REG_MEM) {
    MIR_op_t src_op2;
    int change_p = FALSE;

    if (! first_p && safe_hreg_substitution_p (op.u.hard_reg_mem.index, bb_insn)) {
      def_hr = op.u.hard_reg_mem.index;
      def_insn = hreg_refs_addr[def_hr].insn;
      def_insn_num = hreg_refs_addr[def_hr].insn_num;
      gen_assert (hreg_refs_addr[def_hr].nop == 0 && ! hreg_refs_addr[def_hr].del_p);
      src_op = def_insn->ops[1];
      if (src_op.mode != MIR_OP_HARD_REG || obsolete_hard_reg_op_p (src_op, def_insn_num))
	;
      else if (def_insn->code == MIR_ADD) { /* index = r + const */
	gen_assert (src_op.u.hard_reg != MIR_NON_HARD_REG);
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
	gen_assert (src_op.u.hard_reg != MIR_NON_HARD_REG && src_op2.u.i != 1);
	insn->ops[nop].u.hard_reg_mem.index = src_op.u.hard_reg;
	insn->ops[nop].u.hard_reg_mem.scale *= src_op2.u.i;
	change_p = TRUE;
      }
    } else if (first_p && safe_hreg_substitution_p (op.u.hard_reg_mem.base, bb_insn)) {
      def_hr = op.u.hard_reg_mem.base;
      def_insn = hreg_refs_addr[def_hr].insn;
      def_insn_num = hreg_refs_addr[def_hr].insn_num;
      gen_assert (MIR_call_code_p (def_insn->code) || hreg_refs_addr[def_hr].nop == 0);
      gen_assert (! hreg_refs_addr[def_hr].del_p);
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
	gen_assert (src_op.u.hard_reg != MIR_NON_HARD_REG);
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
	gen_assert (src_op.u.hard_reg != MIR_NON_HARD_REG && src_op2.u.i != 1);
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
  else {
    gen_assert (def_insn != NULL);
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      fprintf (stderr, "      changing to ");
      MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
    }
#endif
    VARR_PUSH (MIR_reg_t, dead_def_regs, def_hr); /* to delete def_insn */
  }
  return successfull_change_p;
}

static int combine_op (MIR_insn_t insn, size_t nop) {
  int first_p, op_change_p, change_p = FALSE;

  for (first_p = TRUE;; first_p = !first_p) {
    /* Memory can have 2 susbtitutions (base and index registers).  */
    if (! (op_change_p = substitute_op_p (insn, nop, first_p)) && ! first_p)
      break;
    if (op_change_p)
      change_p = TRUE;
  }
  return change_p;
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
  case MIR_UGES: return true_p ? MIR_UBGES : MIR_UBLTS;
    /* Cannot revert in the false case for IEEE754: */
  case MIR_FEQ: return true_p ? MIR_FBEQ : MIR_INSN_BOUND;
  case MIR_DEQ: return true_p ? MIR_DBEQ : MIR_INSN_BOUND;
  case MIR_FNE: return true_p ? MIR_FBNE : MIR_INSN_BOUND;
  case MIR_DNE: return true_p ? MIR_DBNE : MIR_INSN_BOUND;
  case MIR_FLT: return true_p ? MIR_FBLT : MIR_INSN_BOUND;
  case MIR_DLT: return true_p ? MIR_DBLT : MIR_INSN_BOUND;
  case MIR_FLE: return true_p ? MIR_FBLE : MIR_INSN_BOUND;
  case MIR_DLE: return true_p ? MIR_DBLE : MIR_INSN_BOUND;
  case MIR_FGT: return true_p ? MIR_FBGT : MIR_INSN_BOUND;
  case MIR_DGT: return true_p ? MIR_DBGT : MIR_INSN_BOUND;
  case MIR_FGE: return true_p ? MIR_FBGE : MIR_INSN_BOUND;
  case MIR_DGE: return true_p ? MIR_DBGE : MIR_INSN_BOUND;
  default: return MIR_INSN_BOUND;
  }
}

static MIR_insn_t combine_branch_and_cmp (bb_insn_t bb_insn) {
  MIR_insn_t def_insn, new_insn, insn = bb_insn->insn;
  MIR_insn_code_t code = insn->code;
  MIR_op_t op;

  if (code != MIR_BT && code != MIR_BF && code != MIR_BTS && code != MIR_BFS)
    return NULL;
  op = insn->ops[1];
  if (! safe_hreg_substitution_p (op.u.hard_reg, bb_insn))
    return NULL;
  def_insn = hreg_refs_addr[op.u.hard_reg].insn;
  if ((code = get_combined_br_code (code == MIR_BT || code == MIR_BTS, def_insn->code)) == MIR_INSN_BOUND)
    return NULL;
  if (obsolete_op_p (def_insn->ops[1], hreg_refs_addr[op.u.hard_reg].insn_num)
      || obsolete_op_p (def_insn->ops[2], hreg_refs_addr[op.u.hard_reg].insn_num))
    return NULL;
  new_insn = MIR_new_insn (code, insn->ops[0], def_insn->ops[1], def_insn->ops[2]);
  MIR_insert_insn_before (curr_func_item, insn, new_insn);
  if (! insn_ok_p (new_insn)) {
    MIR_remove_insn (curr_func_item, new_insn);
    return NULL;
  } else {
    MIR_remove_insn (curr_func_item, insn);
    new_insn->data = bb_insn;
    bb_insn->insn = new_insn;
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      fprintf (stderr, "      changing to ");
      MIR_output_insn (debug_file, new_insn, curr_func_item->u.func, TRUE);
    }
#endif
    VARR_PUSH (MIR_reg_t, dead_def_regs, op.u.hard_reg); /* to delete def_insn */
    return new_insn;
  }
}

static void setup_hreg_ref (MIR_reg_t hr, MIR_insn_t insn, size_t nop, size_t insn_num, int def_p) {
  if (hr == MIR_NON_HARD_REG)
    return;
  hreg_ref_ages_addr[hr] = curr_bb_hreg_ref_age;
  hreg_refs_addr[hr].insn = insn;
  hreg_refs_addr[hr].nop = nop;
  hreg_refs_addr[hr].insn_num = insn_num;
  hreg_refs_addr[hr].def_p = def_p;
  hreg_refs_addr[hr].del_p = FALSE;
}

static void combine (void) {
  MIR_insn_code_t code, new_code;
  MIR_insn_t insn, new_insn, def_insn;
  bb_insn_t bb_insn;
  size_t nops, i, curr_insn_num;
  MIR_op_t temp_op, *op;
  MIR_reg_t hr, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  int iter, out_p, change_p;

  hreg_refs_addr = VARR_ADDR (hreg_ref_t, hreg_refs);
  hreg_ref_ages_addr = VARR_ADDR (size_t, hreg_ref_ages);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    curr_bb_hreg_ref_age++;
    last_mem_ref_insn_num = 0; /* means undef */
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns), curr_insn_num = 1;
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn), curr_insn_num++) {
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn);
#if MIR_GEN_DEBUG
      if (debug_file != NULL) {
	fprintf (stderr, "  Processing ");
	MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
      }
#endif
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
	setup_hreg_ref (early_clobbered_hard_reg1, insn, 0 /* whatever */, curr_insn_num, TRUE);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
	setup_hreg_ref (early_clobbered_hard_reg2, insn, 0 /* whatever */, curr_insn_num, TRUE);
      VARR_TRUNC (MIR_reg_t, dead_def_regs, 0);
      if (MIR_call_code_p ((code = insn->code))) {
	for (size_t hr = 0; hr <= MAX_HARD_REG; hr++)
	  if (bitmap_bit_p (call_used_hard_regs, hr)) {
	    setup_hreg_ref (hr, insn, 0 /* whatever */, curr_insn_num, TRUE);
	  }
      } else if ((new_insn = combine_branch_and_cmp (bb_insn)) != NULL) {
	insn = new_insn;
	nops = MIR_insn_nops (insn);
      } else {
	for (iter = 0; iter < 2; iter++) {
	  change_p = FALSE;
	  for (i = 0; i < nops; i++) {
	    MIR_insn_op_mode (insn, i, &out_p);
	    if ((! out_p || insn->ops[i].mode != MIR_OP_HARD_REG) && combine_op (insn, i))
	      change_p = TRUE;
	  }
	  if (iter == 0) {
	    if ((new_code = commutative_insn_code (insn->code)) == MIR_INSN_BOUND)
	      break;
	    insn->code = new_code;
	    temp_op = insn->ops[1]; insn->ops[1] = insn->ops[2]; insn->ops[2] = temp_op;
	  } else if (! change_p) {
	    gen_assert (commutative_insn_code (insn->code) == code);
	    insn->code = code;
	    temp_op = insn->ops[1]; insn->ops[1] = insn->ops[2]; insn->ops[2] = temp_op;
	  }
	}
      }
      
      for (size_t i = 0; i < VARR_LENGTH (MIR_reg_t, dead_def_regs); i++) {
	hr = VARR_GET (MIR_reg_t, dead_def_regs, i);
	if (hreg_ref_ages_addr[hr] != curr_bb_hreg_ref_age || hreg_refs_addr[hr].del_p)
	  continue;
	def_insn = hreg_refs_addr[hr].insn;
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (stderr, "      deleting now dead insn ");
	  MIR_output_insn (debug_file, def_insn, curr_func_item->u.func, TRUE);
    }
#endif
	/* We should delete the def insn here because of possible
	   substitution of the def insn 'r0 = ... r0 ...'.  We still
	   need valid entry for def her to find obsolete definiton,
	   e.g. "hr1 = hr0; hr0 = ...; hr0 = ... (deleted); ...= ...hr1..." */
	gen_delete_insn (curr_func_item, def_insn);
	hreg_refs_addr[hr].del_p = TRUE; /* to exclude repetitive deletion */
      }
      for (iter = 0; iter < 2; iter++) {
	for (i = 0; i < nops; i++) {
	  op = &insn->ops[i];
	  MIR_insn_op_mode (insn, i, &out_p);
	  if (op->mode == MIR_OP_HARD_REG && ! iter == ! out_p) {
	    /* process in ops on 0th iteration and out ops on 1th iteration */
	    setup_hreg_ref (op->u.hard_reg, insn, i, curr_insn_num, iter == 1);
	  } else if (op->mode == MIR_OP_HARD_REG_MEM) {
	    if (out_p && iter == 1)
	      last_mem_ref_insn_num = curr_insn_num;
	    else if (iter == 0) {
	      setup_hreg_ref (op->u.hard_reg_mem.base, insn, i, curr_insn_num, FALSE);
	      setup_hreg_ref (op->u.hard_reg_mem.index, insn, i, curr_insn_num, FALSE);
	    }
	  }
	}
      }
      clear_bb_insn_dead_vars (bb_insn); /* dead notes are outdated now -- remove them */
    }
  }
}



/* Dead code elimnination */

#define live_out out

static void dead_code_elimination (MIR_item_t func) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t nops, i;
  MIR_reg_t var, early_clobbered_hard_reg1, early_clobbered_hard_reg2;
  MIR_op_t op;
  int out_p, reg_def_p, dead_p;
  bitmap_t live;
  
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
    fprintf (debug_file, "+++++++++++++Dead code elimination:\n");
#endif
  live = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  for (bb_t bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn);
      reg_def_p = FALSE; dead_p = TRUE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
	if (! out_p || (op.mode != MIR_OP_REG && op.mode != MIR_OP_HARD_REG))
	  continue;
	reg_def_p = TRUE;
	var = op.mode == MIR_OP_HARD_REG ? op.u.hard_reg : reg2var (op.u.reg);
	if (bitmap_clear_bit_p (live, var))
	  dead_p = FALSE;
      }
      if (! reg_def_p)
	dead_p = FALSE;
      if (dead_p && ! MIR_call_code_p (insn->code) && insn->code != MIR_ALLOCA
	  && insn->code != MIR_BSTART && insn->code != MIR_BEND
	  && ! (insn->ops[0].mode == MIR_OP_HARD_REG
	        && (insn->ops[0].u.hard_reg == BP_HARD_REG || insn->ops[0].u.hard_reg == SP_HARD_REG))) {
#if MIR_GEN_DEBUG
	if (debug_file != NULL) {
	  fprintf (debug_file, "  Removing dead insn");
	  MIR_output_insn (debug_file, insn, curr_func_item->u.func, TRUE);
	}
#endif
	gen_delete_insn (func, insn);
	continue;
      }
      if (MIR_call_code_p (insn->code))
	bitmap_and_compl (live, live, call_used_hard_regs);
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn, i, &out_p);
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
      get_early_clobbered_hard_reg (insn, &early_clobbered_hard_reg1, &early_clobbered_hard_reg2);
      if (early_clobbered_hard_reg1 != MIR_NON_HARD_REG)
	bitmap_clear_bit_p (live, early_clobbered_hard_reg1);
      if (early_clobbered_hard_reg2 != MIR_NON_HARD_REG)
	bitmap_clear_bit_p (live, early_clobbered_hard_reg2);
      if (MIR_call_code_p (insn->code))
	bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
}

#undef live_out

#if MIR_GEN_DEBUG

#include <sys/types.h>
#include <unistd.h>

static void print_code (uint8_t *code, size_t code_len, void *start_addr) {
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
	   cfname, cfname, (unsigned long) start_addr, cfname, cfname, cfname);
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
  
  gen_assert (func_item->item_type == MIR_func_item && func_item->data == NULL);
  if (func_item->machine_code != NULL) {
    _MIR_redirect_thunk (func_item->addr, func_item->machine_code);
#if MIR_GEN_DEBUG
    fprintf (stderr, "+++++++++++++The code for %s has been already generated\n",
	     MIR_item_name (func_item));
#endif
    return func_item->addr;
  }
  MIR_simplify_func (func_item, TRUE);
#if MIR_GEN_DEBUG
  fprintf (stderr, "+++++++++++++MIR after simplification:\n");
  MIR_output (stderr);
#endif
  curr_func_item = func_item;
  curr_cfg = func_item->data = gen_malloc (sizeof (struct func_cfg));
  build_func_cfg ();
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after building CFG:\n");
    print_CFG (TRUE, TRUE, NULL);
  }
#endif
#ifndef NO_CSE
#if MIR_GEN_DEBUG
  if (debug_file != NULL)
    fprintf (debug_file, "+++++++++++++CSE:\n");
#endif
  cse ();
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    print_exprs ();
    fprintf (debug_file, "+++++++++++++MIR after CSE:\n");
    print_CFG (TRUE, TRUE, output_bb_cse_info);
  }
#endif
  cse_clear ();
#endif /* #ifndef NO_CSE */
  calculate_func_cfg_live_info (FALSE);
#ifndef NO_CSE
  dead_code_elimination (func_item);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after dead code elimination after CSE:\n");
    print_CFG (TRUE, TRUE, output_bb_live_info);
  }
#endif
#endif
#ifndef NO_CCP
  if (ccp ()) {
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      fprintf (debug_file, "+++++++++++++MIR after CCP:\n");
      print_CFG (TRUE, TRUE, NULL);
    }
#endif
    dead_code_elimination (func_item);
#if MIR_GEN_DEBUG
    if (debug_file != NULL) {
      fprintf (debug_file, "+++++++++++++MIR after dead code elimination after CCP:\n");
      print_CFG (TRUE, TRUE, output_bb_live_info);
    }
#endif
  }
#endif /* #ifndef NO_CCP */
  ccp_clear ();
  make_2op_insns (func_item);
  machinize (func_item);
  add_new_bb_insns (func_item);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after machinize:\n");
    print_CFG (FALSE, TRUE, NULL);
  }
#endif
  calculate_func_cfg_live_info (TRUE);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    add_bb_insn_dead_vars ();
    fprintf (debug_file, "+++++++++++++MIR after building live_info:\n");
    print_CFG (TRUE, FALSE, output_bb_live_info);
  }
#endif
  build_live_ranges ();
  assign ();
  rewrite (); /* After rewrite the BB live info is still valid */
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after rewrite:\n");
    print_CFG (FALSE, TRUE, NULL);
  }
#endif
  calculate_func_cfg_live_info (FALSE);
  add_bb_insn_dead_vars ();
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR before combine:\n");
    print_CFG (FALSE, TRUE, NULL);
  }
#endif
#ifndef NO_COMBINE
  combine (); /* After combine the BB live info is still valid */
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after combine:\n");
    print_CFG (FALSE, TRUE, NULL);
  }
#endif
  dead_code_elimination (func_item);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after dead code elimination after combine:\n");
    print_CFG (TRUE, TRUE, output_bb_live_info);
  }
#endif
#endif /* #ifndef NO_COMBINE */
  make_prolog_epilog (func_item, func_assigned_hard_regs, func_stack_slots_num);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    fprintf (debug_file, "+++++++++++++MIR after forming prolog/epilog:\n");
    print_CFG (FALSE, TRUE, NULL);
  }
#endif
  code = target_translate (func_item, &code_len);
  func_item->machine_code = _MIR_publish_code (code, code_len);
#if MIR_GEN_DEBUG
  if (debug_file != NULL) {
    print_code (code, code_len, func_item->machine_code);
    fprintf (debug_file, "code size = %lu:\n", (unsigned long) code_len);
  }
#endif 
  _MIR_redirect_thunk (func_item->addr, func_item->machine_code);
  destroy_func_live_ranges ();
  destroy_func_cfg ();
  return func_item->addr;
}

#if MIR_GEN_DEBUG
void MIR_gen_set_debug_file (FILE *f) {
  debug_file = f;
}
#endif

void MIR_gen_init (void) {
  MIR_reg_t i;
  static hreg_ref_t hreg_ref = {NULL, 0, 0};
    
#ifdef TEST_MIR_GEN
  fprintf (stderr, "Page size = %lu\n", (unsigned long) page_size);
#endif
  init_dead_vars ();
  VARR_CREATE (bb_t, worklist, 0);
  VARR_CREATE (bb_t, pending, 0);
  VARR_CREATE (expr_t, exprs, 512);
  VARR_CREATE (bitmap_t, var2dep_expr, 512);
  memory_exprs = bitmap_create2 (DEFAULT_INIT_BITMAP_BITS_NUM);
  init_ccp ();
  VARR_CREATE (live_range_t, var_live_ranges, 0);
  HTAB_CREATE (expr_t, expr_tab, 1024, expr_hash, expr_eq);
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
  curr_bb_hreg_ref_age = 0;
  VARR_CREATE (size_t, hreg_ref_ages, MAX_HARD_REG + 1);
  VARR_CREATE (hreg_ref_t, hreg_refs, MAX_HARD_REG + 1);
  VARR_CREATE (MIR_reg_t, dead_def_regs, MAX_HARD_REG + 1);
  conflict_locs = bitmap_create2 (3 * MAX_HARD_REG / 2);
  call_used_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (hreg_ref_t, hreg_refs, hreg_ref);
    VARR_PUSH (size_t, hreg_ref_ages, 0);
    if (call_used_hard_reg_p (i))
      bitmap_set_bit_p (call_used_hard_regs, i);
  }
  func_assigned_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  insn_to_consider = bitmap_create2 (1024);
  target_init ();
}

void MIR_gen_finish (void) {
  VARR_DESTROY (bb_t, worklist);
  VARR_DESTROY (expr_t, exprs);
  bitmap_destroy (memory_exprs);
  VARR_DESTROY (bitmap_t, var2dep_expr);
  VARR_DESTROY (bb_t, pending);
  VARR_DESTROY (live_range_t, var_live_ranges);
  HTAB_DESTROY (expr_t, expr_tab);
  finish_ccp ();
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
  VARR_DESTROY (size_t, hreg_ref_ages);
  VARR_DESTROY (hreg_ref_t, hreg_refs);
  VARR_DESTROY (MIR_reg_t, dead_def_regs);
  bitmap_destroy (conflict_locs);
  bitmap_destroy (call_used_hard_regs);
  bitmap_destroy (func_assigned_hard_regs);
  bitmap_destroy (insn_to_consider);
  target_finish ();
  finish_dead_vars ();
}

void MIR_set_gen_interface (MIR_item_t func_item) { MIR_gen (func_item); }
