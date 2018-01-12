#include <stdlib.h>
#include <string.h>
#include "mir.h"
#include "mir-dlist.h"
#include "mir-bitmap.h"

#ifdef x86_64
#include "x86_64-target.c"
#else
#error "undefined or unsupported generation target"
#endif

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
};

DEF_DLIST (in_edge_t, in_link);
DEF_DLIST (out_edge_t, out_link);

struct bb_insn {
  MIR_insn_t insn;
  DLIST_LINK (bb_insn_t) bb_insn_link;
  bb_t bb;
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost;
  DLIST_LINK (bb_t) bb_link;
  DLIST (in_edge_t) in_edges;
  DLIST (out_edge_t) out_edges;
  DLIST (bb_insn_t) bb_insns;
  size_t freq;
  bitmap_t live_in, live_out, gen, kill;
};

DEF_DLIST (bb_t, bb_link);

typedef struct func_cfg *func_cfg_t;

DEF_DLIST_LINK (func_cfg_t);

DEF_VARR (size_t);

struct func_cfg {
  MIR_reg_t min_reg, max_reg;
  VARR (size_t) *reg_freq;
  DLIST (bb_t) bbs;
};

static MIR_item_t curr_func;
static func_cfg_t curr_cfg;

static bb_insn_t create_bb_insn (MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = malloc (sizeof (struct bb_insn));

  insn->data = bb_insn;
  DLIST_APPEND (bb_insn_t, bb->bb_insns, bb_insn);
  bb_insn->bb = bb;
  return bb_insn;
}

static size_t curr_bb_index;

static bb_t create_bb (MIR_insn_t insn) {
  bb_t bb = malloc (sizeof (struct bb));

  DLIST_APPEND (bb_t, curr_cfg->bbs, bb);
  bb->index = curr_bb_index++;
  bb->pre = bb->rpost = 0;
  DLIST_INIT (bb_insn_t, bb->bb_insns);
  DLIST_INIT (in_edge_t, bb->in_edges);
  DLIST_INIT (out_edge_t, bb->out_edges);
  bb->live_in = bb->live_out = bb->gen = bb->kill = NULL;
  if (insn != NULL)
    create_bb_insn (insn, bb);
  return bb;
}

static edge_t create_edge (bb_t src, bb_t dst) {
  edge_t e = malloc (sizeof (struct edge));

  e->src = src; e->dst = dst;
  DLIST_APPEND (in_edge_t, dst->in_edges, e);
  DLIST_APPEND (out_edge_t, src->out_edges, e);
  return e;
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

static MIR_reg_t get_nregs (void) {
  return curr_cfg->max_reg == 0 ? 0 : curr_cfg->max_reg - curr_cfg->min_reg + 1;
}

static void build_func_cfg (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, label_bb_insn;
  size_t i, nops;
  MIR_op_t *op;
  bb_t bb, prev_bb, entry_bb, exit_bb;
  int new_bb_p, fall_through_p;
  MIR_reg_t nregs;
  
  DLIST_INIT (bb_t, curr_cfg->bbs);
  curr_cfg->max_reg = 0;
  curr_cfg->min_reg = 0;
  curr_bb_index = 0;
  entry_bb = create_bb (NULL);
  exit_bb = create_bb (NULL);
  new_bb_p = TRUE;
  fall_through_p = FALSE;
  bb = NULL;
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func->u.func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    if (insn->code == MIR_LABEL) {
      prev_bb = bb;
      if ((bb_insn = insn->data) == NULL)
	bb = create_bb (insn);
      else
	bb = bb_insn->bb;
      if (fall_through_p)
	create_edge (prev_bb, bb);
    } else if (new_bb_p) {
      prev_bb = bb;
      bb = create_bb (insn);
      if (fall_through_p)
	create_edge (prev_bb, bb);
    } else {
      create_bb_insn (insn, bb);
    }
    nops = MIR_insn_nops (insn->code);
    for (i = 0; i < nops; i++)
      if ((op = &insn->ops[i])->mode == MIR_OP_LABEL) {
	if ((label_bb_insn = op->u.label->data) == NULL) {
	  bb = create_bb (op->u.label);
	  label_bb_insn = op->u.label->data;
	} else if (op->mode == MIR_OP_REG) {
	  update_min_max_reg (op->u.reg);
	} else if (op->mode == MIR_OP_MEM) {
	  update_min_max_reg (op->u.mem.base);
	  update_min_max_reg (op->u.mem.index);
	}
	bb_insn = insn->data;
	create_edge (bb_insn->bb, label_bb_insn->bb);
      }
    new_bb_p = MIR_branch_code_p (insn->code) || MIR_ret_code_p (insn->code);
    fall_through_p = insn->code != MIR_JMP && ! MIR_ret_code_p (insn->code);
  }
  /* Add additional edges with entry and exit */
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    if (bb != entry_bb && DLIST_HEAD (in_edge_t, bb->in_edges) == NULL)
      create_edge (entry_bb, bb);
    if (bb != exit_bb && DLIST_HEAD (out_edge_t, bb->out_edges) == NULL)
      create_edge (bb, exit_bb);
  }
  enumerate_bbs ();
  nregs = get_nregs ();
  VARR_CREATE (size_t, curr_cfg->reg_freq, nregs);
  VARR_EXPAND (size_t, curr_cfg->reg_freq, nregs);
  memset (VARR_ADDR (size_t, curr_cfg->reg_freq), 0, nregs * sizeof (size_t));
}

static void destroy_func_cfg (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t last_bb;
  edge_t e, next_e;
  
  assert (curr_func->func_p && curr_func->data != NULL);
  free (curr_func->data);
  curr_func->data = NULL;
  last_bb = NULL;
  for (insn = DLIST_HEAD (MIR_insn_t, curr_func->u.func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    bb_insn = insn->data;
    assert (bb_insn != NULL && bb_insn->bb != NULL);
    if (last_bb != bb_insn->bb) {
      last_bb = bb_insn->bb;
      for (e = DLIST_HEAD (out_edge_t, last_bb->out_edges); e != NULL; e = next_e) {
	next_e = DLIST_NEXT (out_edge_t, e);
	free (e);
      }
      free (last_bb);
    }
    bb_insn->insn->data = NULL;
    free (bb_insn);
  }
  VARR_DESTROY (size_t, curr_cfg->reg_freq);
}

static int rpost_cmp (const void *a1, const void *a2) {
  return ((const struct bb *) a1)->rpost - ((const struct bb *) a2)->rpost;
}

static int post_cmp (const void *a1, const void *a2) { return -rpost_cmp (a1, a2); }

DEF_VARR (bb_t);

static VARR (bb_t) *worklist, *pending;
static bitmap_t bb_to_consider;

static void
solve_dataflow (int forward_p, void (*con_func_0) (bb_t), int (*con_func_n) (edge_t),
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
      edge_t head, e;
      
      bb = addr[i];
      if (forward_p) {
	if ((head = DLIST_HEAD (in_edge_t, bb->in_edges)) == NULL)
	  con_func_0 (bb);
	else {
	  for (e = head; e != NULL; e = DLIST_NEXT (in_edge_t, e))
	    changed_p |= con_func_n (e);
	}
      } else {
	if ((head = DLIST_HEAD (out_edge_t, bb->out_edges)) == NULL)
	  con_func_0 (bb);
	else {
	  for (e = head; e != NULL; e = DLIST_NEXT (out_edge_t, e))
	    changed_p |= con_func_n (e);
	}
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

static void live_con_func_0 (bb_t bb) {bitmap_clear (bb->live_in); }

static int live_con_func_n (edge_t e) {
  return bitmap_ior (e->src->live_out, e->src->live_out, e->dst->live_in);
}

static int live_trans_func (bb_t bb) {
  return bitmap_ior_and_compl (bb->live_in, bb->gen, bb->live_out, bb->kill);
}

static void initiate_bb_live_info (bb_t bb) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  size_t nops, i;
  MIR_op_t op;
  int out_p;
  size_t *reg_freqs;
  
  assert (bb->live_in == NULL && bb->live_out == NULL && bb->gen == NULL && bb->kill == NULL);
  bb->live_in = bitmap_create (); bb->live_out = bitmap_create ();
  bb->gen = bitmap_create (); bb->kill = bitmap_create ();
  reg_freqs = VARR_ADDR (size_t, curr_cfg->reg_freq);
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
    insn = bb_insn->insn;
    nops = MIR_insn_nops (insn->code);
    for (i = 0; i < nops; i++) {
      op = insn->ops[i];
      switch (op.mode) {
      case MIR_OP_REG:
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (! out_p)
	  bitmap_set_bit_p (bb->gen, op.u.reg - curr_cfg->min_reg);
	else {
	  bitmap_clear_bit_p (bb->gen, op.u.reg - curr_cfg->min_reg);
	  bitmap_set_bit_p (bb->kill, op.u.reg - curr_cfg->min_reg);
	}
	reg_freqs[op.u.reg]++;
	break;
      case MIR_OP_MEM:
	if (op.u.mem.base != 0) {
	  bitmap_set_bit_p (bb->gen, op.u.mem.base - curr_cfg->min_reg);
	  reg_freqs[op.u.mem.base]++;
	}
	if (op.u.mem.index != 0) {
	  bitmap_set_bit_p (bb->gen, op.u.mem.index - curr_cfg->min_reg);
	  reg_freqs[op.u.mem.index]++;
	}
	break;
      }
    }
  }
}

static void initiate_live_info (void) {
  bb_t bb;
  
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    initiate_bb_live_info (bb);
}

void build_func_cfg_live_info (void) {
  initiate_live_info ();
  solve_dataflow (FALSE, live_con_func_0, live_con_func_n, live_trans_func);
}

static void destroy_bb_live_info (bb_t bb) {
  if (bb->live_in != NULL)
    bitmap_destroy (bb->live_in);
  if (bb->live_out != NULL)
    bitmap_destroy (bb->live_out);
  if (bb->gen != NULL)
    bitmap_destroy (bb->gen);
  if (bb->kill != NULL)
    bitmap_destroy (bb->kill);
  bb->live_in = bb->live_out = bb->gen = bb->kill = NULL;
}

void destroy_func_cfg_live_info (void) {
  bb_t bb;
  
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb))
    destroy_bb_live_info (bb);
}

typedef struct live_range *live_range_t;

struct live_range {
  int start, finish;
  live_range_t next;
};

static int curr_point;
static bitmap_t live_regs;

DEF_VARR (live_range_t);

static VARR (live_range_t) *reg_live_ranges;

static live_range_t create_live_range (int start, int finish, live_range_t next) {
  live_range_t lr = malloc (sizeof (struct live_range));

  assert (start <= finish);
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

static int make_reg_dead (MIR_reg_t reg, int point) {
  live_range_t lr;

  reg = reg - curr_cfg->min_reg;
  if (bitmap_clear_bit_p (live_regs, reg))
    return FALSE;
  lr = VARR_GET (live_range_t, reg_live_ranges, reg); lr->finish = point;
  return TRUE;
}

static int make_reg_live (MIR_reg_t reg, int point) {
  live_range_t lr;

  reg = reg - curr_cfg->min_reg;
  if (bitmap_set_bit_p (live_regs, reg))
    return FALSE;
  if ((lr = VARR_GET (live_range_t, reg_live_ranges, reg)) == NULL
      || (lr->finish != point && lr->finish + 1 != point))
    VARR_SET (live_range_t, reg_live_ranges, reg, create_live_range (point, -1, lr));
  return TRUE;
}

static void make_live (size_t nb) { make_reg_live (nb, curr_point); }
static void make_dead (size_t nb) { make_reg_dead (nb, curr_point); }

static void build_live_ranges (void) {
  bb_t bb;
  bb_insn_t bb_insn;
  MIR_insn_t insn;
  MIR_reg_t nregs;
  size_t i, nops;
  int incr_p, out_p;
  MIR_op_t op;
  
  curr_point = 0;
  nregs = get_nregs ();
  VARR_EXPAND (live_range_t, reg_live_ranges, nregs);
  memset (VARR_ADDR (live_range_t, reg_live_ranges), 0, nregs * sizeof (live_range_t));
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live_regs, bb->live_out);
    bitmap_for_each (live_regs, make_live);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_PREV (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      incr_p = FALSE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	if (op.mode == MIR_OP_REG) {
	  MIR_insn_op_mode (insn->code, i, &out_p);
	  if (out_p)
	    incr_p |= make_reg_dead (op.u.reg, curr_point);
	}
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
	    incr_p |= make_reg_live (op.u.reg, curr_point);
	  break;
	case MIR_OP_MEM:
	  if (op.u.mem.base != 0)
	    incr_p |= make_reg_live (op.u.mem.base, curr_point);
	  if (op.u.mem.index != 0)
	    incr_p |= make_reg_live (op.u.mem.index, curr_point);
	  break;
	}
	if (incr_p)
	  curr_point++;
      }
    }
    bitmap_for_each (live_regs, make_dead);
    if (! bitmap_empty_p (live_regs))
      curr_point++;
  }
}

static void destroy_func_live_ranges (void) {
  size_t i;
  
  for (i = 0; i < VARR_LENGTH (live_range_t, reg_live_ranges); i++)
    destroy_live_range (VARR_GET (live_range_t, reg_live_ranges, i));
}

DEF_VARR (MIR_reg_t);

static VARR (MIR_reg_t) *reg_renumber;

static VARR (MIR_reg_t) *sorted_regs;

DEF_VARR (bitmap_t);

static VARR (bitmap_t) *point_used_hard_regs;
  
static bitmap_t conflict_hard_regs;

static int reg_freq_compare_func (const void *a1, const void *a2) {
  MIR_reg_t r1 = *(const MIR_reg_t *) a1, r2 = *(const MIR_reg_t *) a2;
  return ((int) VARR_GET (size_t, curr_cfg->reg_freq, r2)
	  - (int) VARR_GET (size_t, curr_cfg->reg_freq, r1));
}

static void assign (void) {
  MIR_reg_t hard_reg, i, reg, nregs = get_nregs ();
  int j;
  live_range_t lr;
  int hard_reg_bitmap_nw;
  bitmap_t bm;
  
  if (nregs == 0)
    return;
  VARR_TRUNC (MIR_reg_t, reg_renumber, 0);
  for (i = 0; i < nregs; i++)
    VARR_PUSH (MIR_reg_t, reg_renumber, -1);
  /* min_reg, max_reg for func */
  VARR_TRUNC (MIR_reg_t, sorted_regs, 0);
  for (i = 0; i < nregs; i++)
    VARR_PUSH (MIR_reg_t, sorted_regs, i);
  for (i = 0; i <= curr_point; i++) {
    bm = bitmap_create2 (MAX_HARD_REG + 1);
    VARR_PUSH (bitmap_t, point_used_hard_regs, bm);
  }
  qsort (VARR_ADDR (MIR_reg_t, sorted_regs), nregs, sizeof (MIR_reg_t), reg_freq_compare_func);
  for (i = 0; i < nregs; i++) {
    reg = VARR_GET (MIR_reg_t, sorted_regs, i) + curr_cfg->min_reg;
    bitmap_clear (conflict_hard_regs);
    for (lr = VARR_GET (live_range_t, reg_live_ranges, i); lr != NULL; lr = lr->next)
	for (j = lr->start; j <= lr->finish; j++)
	  bitmap_ior (conflict_hard_regs, conflict_hard_regs, VARR_GET (bitmap_t, point_used_hard_regs, j));
      for (hard_reg = 0; hard_reg <= MAX_HARD_REG; hard_reg++) {
	if (fixed_hard_reg_p (hard_reg)
	    || bitmap_bit_p (conflict_hard_regs, hard_reg)
	    || ! hard_reg_mode_ok_p (hard_reg, MIR_reg_mode (reg)))
	  continue;
	VARR_SET (MIR_reg_t, reg_renumber, i, hard_reg);
	for (lr = VARR_GET (live_range_t, reg_live_ranges, i); lr != NULL; lr = lr->next)
	  for (j = lr->start; j <= lr->finish; j++)
	    bitmap_set_bit_p (VARR_GET (bitmap_t, point_used_hard_regs, j), hard_reg);
      }
  }
  for (i = 0; i <= curr_point; i++)
    bitmap_destroy (VARR_POP (bitmap_t, point_used_hard_regs));
}

static void rewrite (void) {
}

void MIR_gen (MIR_item_t func) {
  assert (func->func_p && func->data == NULL);
  curr_func = func;
  curr_cfg = func->data = malloc (sizeof (struct func_cfg));
  build_func_cfg ();
  build_func_cfg_live_info ();
  build_live_ranges ();
  assign ();
  rewrite ();
  destroy_func_live_ranges ();
  destroy_func_cfg_live_info ();
  destroy_func_cfg ();
  
}

void MIR_init_gen (void) {
  VARR_CREATE (bb_t, worklist, 0);
  VARR_CREATE (bb_t, pending, 0);
  bb_to_consider = bitmap_create ();
  VARR_CREATE (MIR_reg_t, reg_renumber, 0);
  VARR_CREATE (MIR_reg_t, sorted_regs, 0);
  conflict_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
}

void MIR_finish_gen (void) {
  VARR_DESTROY (bb_t, worklist);
  VARR_DESTROY (bb_t, pending);
  bitmap_destroy (bb_to_consider);
  VARR_DESTROY (MIR_reg_t, reg_renumber);
  VARR_DESTROY (MIR_reg_t, sorted_regs);
  bitmap_destroy (conflict_hard_regs);
}
