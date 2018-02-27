/* Terminolagy:
   reg - MIR (pseudo-)register (their numbers are in MIR_OP_REG and MIR_OP__MEM)
   hard reg - MIR hard register (their numbers are in MIR_OP_HARD_REG and MIR_OP_HARD_REG_MEM)
   breg (based reg) - function pseudo registers whose numbers start with zero
   var - pseudo and hard register (var numbers for psedo-registers are based reg numbers + MAX_HARD_REG + 1)
   loc - hard register and stack locations (stack slot numbers start with MAX_HARD_REG + 1). 
*/

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
  bitmap_t call_hard_reg_args; /* non-null for calls */
};

DEF_DLIST (bb_insn_t, bb_insn_link);

struct bb {
  size_t index, pre, rpost;
  DLIST_LINK (bb_t) bb_link;
  DLIST (in_edge_t) in_edges;
  DLIST (out_edge_t) out_edges;
  DLIST (bb_insn_t) bb_insns;
  size_t freq;
  bitmap_t live_in, live_out, gen, kill; /* vars */
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

struct func_cfg {
  MIR_reg_t min_reg, max_reg;
  VARR (reg_info_t) *breg_info; /* bregs */
  DLIST (bb_t) bbs;
  DLIST (mv_t) moves;
};

static bitmap_t call_used_hard_regs;
static MIR_item_t curr_func;
static func_cfg_t curr_cfg;

static bb_insn_t create_bb_insn (MIR_insn_t insn, bb_t bb) {
  bb_insn_t bb_insn = malloc (sizeof (struct bb_insn));

  insn->data = bb_insn;
  bb_insn->bb = bb;
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
    add_new_bb_insn (insn, bb);
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

static void build_func_cfg (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn, label_bb_insn;
  size_t i, nops;
  MIR_op_t *op;
  bb_t bb, prev_bb, entry_bb, exit_bb;
  int new_bb_p, fall_through_p;
  MIR_reg_t nregs, n;
  
  DLIST_INIT (bb_t, curr_cfg->bbs);
  DLIST_INIT (mv_t, curr_cfg->moves);
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
      add_new_bb_insn (insn, bb);
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
  VARR_CREATE (reg_info_t, curr_cfg->breg_info, nregs);
  VARR_EXPAND (reg_info_t, curr_cfg->breg_info, nregs);
  for (n = 0; n < nregs; n++) {
    reg_info_t *ri = &VARR_ADDR (reg_info_t, curr_cfg->breg_info)[n];

    ri->freq = ri->calls_num = 0;
    DLIST_INIT (dst_mv_t, ri->dst_moves);
    DLIST_INIT (src_mv_t, ri->src_moves);
  }
}

static void destroy_func_cfg (void) {
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  bb_t last_bb;
  edge_t e, next_e;
  mv_t mv, next_mv;
  
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
    if (bb_insn->call_hard_reg_args != NULL)
      bitmap_destroy (bb_insn->call_hard_reg_args);
    free (bb_insn);
  }
  for (mv = DLIST_HEAD (mv_t, curr_cfg->moves); mv != NULL; mv = next_mv) {
    next_mv = DLIST_NEXT (mv_t, mv);
    free (mv);
  }
  VARR_DESTROY (reg_info_t, curr_cfg->breg_info);
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
  reg_info_t *breg_infos;
  
  assert (bb->live_in == NULL && bb->live_out == NULL && bb->gen == NULL && bb->kill == NULL);
  bb->live_in = bitmap_create (); bb->live_out = bitmap_create ();
  bb->gen = bitmap_create (); bb->kill = bitmap_create ();
  breg_infos = VARR_ADDR (reg_info_t, curr_cfg->breg_info);
  for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
    insn = bb_insn->insn;
    nops = MIR_insn_nops (insn->code);
    for (i = 0; i < nops; i++) {
      op = insn->ops[i];
      MIR_insn_op_mode (insn->code, i, &out_p);
      switch (op.mode) {
      case MIR_OP_REG:
	if (! out_p)
	  bitmap_set_bit_p (bb->gen, reg2var (op.u.reg));
	else {
	  bitmap_clear_bit_p (bb->gen, reg2var (op.u.reg));
	  bitmap_set_bit_p (bb->kill, reg2var (op.u.reg));
	}
	breg_infos[op.u.reg].freq++;
	break;
      case MIR_OP_HARD_REG:
	if (! out_p)
	  bitmap_set_bit_p (bb->gen, op.u.hard_reg);
	else {
	  bitmap_clear_bit_p (bb->gen, op.u.hard_reg);
	  bitmap_set_bit_p (bb->kill, op.u.hard_reg);
	}
	break;
      case MIR_OP_MEM:
	if (op.u.mem.base != 0) {
	  bitmap_set_bit_p (bb->gen, reg2var (op.u.mem.base));
	  breg_infos[op.u.mem.base].freq++;
	}
	if (op.u.mem.index != 0) {
	  bitmap_set_bit_p (bb->gen, reg2var (op.u.mem.index));
	  breg_infos[op.u.mem.index].freq++;
	}
	break;
      case MIR_OP_HARD_REG_MEM:
	if (op.u.hard_reg_mem.base != 0)
	  bitmap_set_bit_p (bb->gen, op.u.hard_reg_mem.base);
	if (op.u.hard_reg_mem.index != 0)
	  bitmap_set_bit_p (bb->gen, op.u.hard_reg_mem.index);
	break;
      default: /* do nothing */
	break;
      }
    }
    if (insn->code == MIR_CALL || insn->code == MIR_CALL_C) {
      bitmap_ior (bb->kill, bb->kill, call_used_hard_regs);
      bitmap_and_compl (bb->gen, bb->gen, call_used_hard_regs);
      bitmap_ior (bb->gen, bb->gen, bb_insn->call_hard_reg_args);
    }
    if ((insn->code == MIR_MOV || insn->code == MIR_FMOV || insn->code == MIR_DMOV)
	&& (insn->ops[0].mode == MIR_OP_REG || insn->ops[0].mode == MIR_OP_HARD_REG)
	&& (insn->ops[1].mode == MIR_OP_REG || insn->ops[1].mode == MIR_OP_HARD_REG)) {
      mv_t mv = malloc (sizeof (struct mv));

      mv->bb_insn = bb_insn;
      DLIST_APPEND (mv_t, curr_cfg->moves, mv);
      if (insn->ops[0].mode == MIR_OP_REG)
	DLIST_APPEND (dst_mv_t, breg_infos[insn->ops[0].u.reg].dst_moves, mv);
      if (insn->ops[1].mode == MIR_OP_REG)
	DLIST_APPEND (src_mv_t, breg_infos[insn->ops[1].u.reg].src_moves, mv);
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

static int make_var_dead (MIR_reg_t var, int point) {
  live_range_t lr;

  if (bitmap_clear_bit_p (live_vars, var))
    return FALSE;
  lr = VARR_GET (live_range_t, var_live_ranges, var); lr->finish = point;
  return TRUE;
}

static int make_var_live (MIR_reg_t var, int point) {
  live_range_t lr;

  if (bitmap_set_bit_p (live_vars, var))
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

static void build_live_ranges (void) {
  bb_t bb;
  bb_insn_t bb_insn;
  MIR_insn_t insn;
  MIR_reg_t nvars;
  size_t i, nops;
  int incr_p, out_p;
  MIR_op_t op;
  
  curr_point = 0;
  nvars = get_nvars ();
  VARR_EXPAND (live_range_t, var_live_ranges, nvars);
  memset (VARR_ADDR (live_range_t, var_live_ranges), 0, nvars * sizeof (live_range_t));
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live_vars, bb->live_out);
    bitmap_for_each (live_vars, make_live);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_PREV (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
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
	  if (op.u.hard_reg_mem.base != 0)
	    incr_p |= make_reg_live (op.u.hard_reg_mem.base, TRUE, curr_point);
	  if (op.u.hard_reg_mem.index != 0)
	    incr_p |= make_reg_live (op.u.hard_reg_mem.index, TRUE, curr_point);
	  break;
	default: /* do nothing */
	  break;
	}
	if (incr_p)
	  curr_point++;
      }
    }
    bitmap_for_each (live_vars, make_dead);
    if (! bitmap_empty_p (live_vars))
      curr_point++;
  }
}

static void destroy_func_live_ranges (void) {
  size_t i;
  
  for (i = 0; i < VARR_LENGTH (live_range_t, var_live_ranges); i++)
    destroy_live_range (VARR_GET (live_range_t, var_live_ranges, i));
}

DEF_VARR (MIR_reg_t);

static VARR (MIR_reg_t) *breg_renumber;

static VARR (MIR_reg_t) *sorted_bregs;

DEF_VARR (bitmap_t);

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
  else if ((loc = VARR_GET (MIR_reg_t, breg_renumber, op.u.reg)) == MIR_NON_HARD_REG)
    return;
  if (curr_loc_profit_ages[loc] == curr_age)
    curr_loc_profits[loc]++; /* should be freq */
  else {
    curr_loc_profit_ages[loc] = curr_age;
    curr_loc_profits[loc] = 1; /* should be freq */
  }
}

static void setup_loc_profits (MIR_reg_t bre) {
  mv_t mv;
  
  for (mv = DLIST_HEAD (dst_mv_t, curr_breg_infos[bre].dst_moves); mv != NULL; mv = DLIST_NEXT (dst_mv_t, mv))
    setup_loc_profit_from_op (mv->bb_insn->insn->ops[1]);
  for (mv = DLIST_HEAD (src_mv_t, curr_breg_infos[bre].src_moves); mv != NULL; mv = DLIST_NEXT (src_mv_t, mv))
    setup_loc_profit_from_op (mv->bb_insn->insn->ops[1]);
}

static void assign (void) {
  MIR_reg_t max_loc, loc, best_loc, i, reg, breg, nregs = get_nregs ();
  int j;
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
  max_loc = MAX_HARD_REG;
  for (i = 0; i < nregs; i++) {
    breg = VARR_GET (MIR_reg_t, sorted_bregs, i);
    reg = breg2reg (breg);
    bitmap_clear (conflict_locs);
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next)
	for (j = lr->start; j <= lr->finish; j++)
	  bitmap_ior (conflict_locs, conflict_locs, point_used_locs_addr[j]);
    curr_age++;
    setup_loc_profits (breg);
    best_loc = MIR_NON_HARD_REG;
    for (loc = 0; loc <= max_loc && best_loc <= MAX_HARD_REG; loc++) {
      if ((loc <= MAX_HARD_REG
	   && (fixed_hard_reg_p (loc)
	       || ! hard_reg_mode_ok_p (loc, MIR_reg_mode (reg))
	       || (call_used_hard_reg_p (loc) && curr_breg_infos[breg].calls_num > 0)))
	  || bitmap_bit_p (conflict_locs, loc))
	continue;
      profit = VARR_GET (size_t, loc_profit_ages, loc) != curr_age ? 0 : VARR_GET (size_t, loc_profits, loc);
      if (best_loc == MIR_NON_HARD_REG || best_profit < profit) {
	best_loc = loc;
	best_profit = profit;
      }
    }
    if (best_loc == MIR_NON_HARD_REG) { /* Add stack slot */
      max_loc = best_loc = VARR_LENGTH (size_t, loc_profits);
      VARR_PUSH (size_t, loc_profits, 0);
      VARR_PUSH (size_t, loc_profit_ages, 0);
    }
    VARR_SET (MIR_reg_t, breg_renumber, i, best_loc);
    for (lr = VARR_GET (live_range_t, var_live_ranges, i); lr != NULL; lr = lr->next)
      for (j = lr->start; j <= lr->finish; j++)
	bitmap_set_bit_p (point_used_locs_addr[j], best_loc);
  }
  for (i = 0; i <= curr_point; i++)
    bitmap_destroy (VARR_POP (bitmap_t, point_used_locs));
}

static MIR_reg_t change_reg (MIR_reg_t reg, MIR_op_mode_t data_mode, int first_p, bb_insn_t bb_insn, int out_p) {
  MIR_reg_t loc = VARR_GET (MIR_reg_t, breg_renumber, reg);
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
    MIR_insert_insn_after (curr_func, bb_insn->insn, insn);
  } else {
    insn = MIR_new_insn (code, hard_reg_op, mem_op);
    MIR_insert_insn_before (curr_func, bb_insn->insn, insn);
  }
  new_bb_insn = create_bb_insn (insn, bb_insn->bb);
  if (out_p) 
    DLIST_INSERT_AFTER (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
  else
    DLIST_INSERT_BEFORE (bb_insn_t, bb_insn->bb->bb_insns, bb_insn, new_bb_insn);
  return hard_reg;
}

static void rewrite (void) {
  bb_t bb;
  MIR_insn_t insn;
  bb_insn_t bb_insn, next_bb_insn;
  size_t nops, i;
  MIR_op_t *op;
  MIR_mem_t mem;
  MIR_op_mode_t data_mode;
  MIR_reg_t hard_reg;
  int out_p, first_in_p;

  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
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
	DLIST_REMOVE (MIR_insn_t, curr_func->u.func->insns, insn);
	free (insn);
      }
    }
  }
}

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

struct op_def {
  /* Sources of hard regs of an insn operand.  insn2/nop2 is used for
     index reg of memory operand and insn1/nop1 for all other
     cases. */
  MIR_insn_t insn1, insn2;
  size_t insn1_num, insn2_num;
  size_t nop1, nop2;
};

typedef struct op_def *op_def_t;

static void create_op_defs (MIR_op_t *op, MIR_insn_t def_insn1, size_t def_insn1_num, size_t def_nop1,
			    MIR_insn_t def_insn2, size_t def_insn2_num, size_t def_nop2) {
  op_def_t op_def = malloc (sizeof (struct op_def));

  op->data = op_def;
  op_def->insn1 = def_insn1;
  op_def->insn1_num = def_insn1_num;
  op_def->nop1 = def_nop1;
  op_def->insn2 = def_insn2;
  op_def->insn2_num = def_insn2_num;
  op_def->nop2 = def_nop2;
}

static int substitute_op_p (MIR_insn_t insn, size_t nop, int first_p) {
  MIR_insn_t def_insn;
  MIR_op_t src_op, op = insn->ops[nop];
  op_def_t op_def = op.data;
  int successfull_change_p = FALSE;
  
  if (op_def == NULL)
    return FALSE;
  if (op.mode == MIR_OP_HARD_REG) {
    def_insn = op_def->insn1;
    assert (op_def->nop1 == 0);
    if (def_insn->code != MIR_MOV && def_insn->code != MIR_FMOV && def_insn->code != MIR_DMOV)
      return FALSE;
    insn->ops[nop] = def_insn->ops[1];
    successfull_change_p = insn_ok_p (insn);
  } else if (op.mode == MIR_OP_HARD_REG_MEM)  {
    MIR_op_t src_op2;
    int change_p = FALSE;
    
    if (!first_p && op.u.mem.index != MIR_NON_HARD_REG) {
      def_insn = op_def->insn2;
      assert (op_def->nop2 == 0);
      src_op = def_insn->ops[1];
      if (def_insn->code == MIR_ADD) { /* index = r + const */
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
    } else if (first_p && op.u.hard_reg_mem.base != MIR_NON_HARD_REG) {
      def_insn = op_def->insn1;
      assert (op_def->nop1 == 0);
      src_op = def_insn->ops[1];
      if (def_insn->code == MIR_MOV) {
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
	if ((src_op2 = def_insn->ops[2]).mode == MIR_OP_HARD_REG
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

static int latest_op_defs_p (MIR_op_t *op) {
  op_def_t op_def = op->data;
  MIR_reg_t hreg1 = MIR_NON_HARD_REG, hreg2 = MIR_NON_HARD_REG;
  
  if (op->mode == MIR_OP_HARD_REG) {
    hreg1 = op->u.hard_reg;
  } else if (op->mode == MIR_OP_HARD_REG_MEM)  {
    hreg1 = op->u.hard_reg_mem.base;
    hreg2 = op->u.hard_reg_mem.index;
  }
  if (op_def->insn1 != NULL) {
    assert (hreg1 != MIR_NON_HARD_REG && hreg_def_ages_addr[hreg1] == curr_bb_hreg_def_age);
    if (hreg_defs_addr[hreg1].insn_num > op_def->insn1_num)
      return FALSE;
  }
  if (op_def->insn2 != NULL) {
    assert (hreg2 != MIR_NON_HARD_REG && hreg_def_ages_addr[hreg2] == curr_bb_hreg_def_age);
    if (hreg_defs_addr[hreg2].insn_num > op_def->insn2_num)
      return FALSE;
  }
  return TRUE;
}

static void combine_op (MIR_insn_t insn, size_t nop) {
  int first_p;
  MIR_op_t new_op = insn->ops[nop], temp_op;

  for (first_p = TRUE;; first_p = !first_p) {
    if (! substitute_op_p (insn, nop, first_p) && ! first_p)
      break;
    temp_op = insn->ops[nop];
    if (latest_op_defs_p (&temp_op))
      new_op = temp_op;
  }
  insn->ops[nop] = new_op;
}

static void combine (void) {
  bb_t bb;
  MIR_insn_t insn;
  bb_insn_t bb_insn;
  size_t nops, i, curr_insn_num;
  MIR_op_t *op;
  int out_p;

  hreg_defs_addr = VARR_ADDR (hreg_def_t, hreg_defs);
  hreg_def_ages_addr = VARR_ADDR (size_t, hreg_def_ages);
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    curr_bb_hreg_def_age++;
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns), curr_insn_num = 0;
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn), curr_insn_num++) {
      ;
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      for (i = 0; i < nops; i++) {
	op = &insn->ops[i];
	op->data = NULL;
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (! out_p) {
	  if (op->mode == MIR_OP_HARD_REG
	      && hreg_def_ages_addr[op->u.hard_reg] == curr_bb_hreg_def_age)
	    create_op_defs (op, hreg_defs_addr[op->u.hard_reg].insn,
			    hreg_defs_addr[op->u.hard_reg].insn_num,
			    hreg_defs_addr[op->u.hard_reg].nop, NULL, 0, 0);
	  else if (op->mode == MIR_OP_HARD_REG_MEM) {
	    MIR_insn_t insn1 = NULL, insn2 = NULL;
	    size_t nop1 = 0, nop2 = 0, insn1_num = 0, insn2_num = 0;
	    
	    if (op->u.hard_reg_mem.base == MIR_NON_HARD_REG
		&& hreg_def_ages_addr[op->u.hard_reg_mem.base] == curr_bb_hreg_def_age) {
	      insn1 = hreg_defs_addr[op->u.hard_reg_mem.base].insn;
	      insn1_num = hreg_defs_addr[op->u.hard_reg_mem.base].insn_num;
	      nop1 = hreg_defs_addr[op->u.hard_reg_mem.base].nop;
	    }
	    if (op->u.hard_reg_mem.index == MIR_NON_HARD_REG
		&& hreg_def_ages_addr[op->u.hard_reg_mem.index] == curr_bb_hreg_def_age) {
	      insn2 = hreg_defs_addr[op->u.hard_reg_mem.index].insn;
	      insn2_num = hreg_defs_addr[op->u.hard_reg_mem.index].insn_num;
	      nop2 = hreg_defs_addr[op->u.hard_reg_mem.index].nop;
	    }
	    if (insn1 != NULL || insn2 != NULL)
	      create_op_defs (op, insn1, insn1_num, nop1, insn2, insn2_num, nop2);
	  }
	  if (op->data == NULL)
	    combine_op (insn, i);
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
    /* Free op data.  */
    for (bb_insn = DLIST_HEAD (bb_insn_t, bb->bb_insns);
	 bb_insn != NULL;
	 bb_insn = DLIST_NEXT (bb_insn_t, bb_insn)) {
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      for (i = 0; i < nops; i++)
	if ((op = &insn->ops[i])->data != NULL) {
	  free (op->data);
	  op->data = NULL;
	}
    }
  }
}

static void
dead_code_elimination (MIR_item_t func) {
  bb_t bb;
  MIR_insn_t insn;
  bb_insn_t bb_insn, prev_bb_insn;
  size_t nops, i;
  MIR_op_t op;
  int out_p, hard_reg_def_p, dead_p;
  bitmap_t live;
  
  live = bitmap_create ();
  for (bb = DLIST_HEAD (bb_t, curr_cfg->bbs); bb != NULL; bb = DLIST_NEXT (bb_t, bb)) {
    bitmap_copy (live, bb->live_out);
    for (bb_insn = DLIST_TAIL (bb_insn_t, bb->bb_insns); bb_insn != NULL; bb_insn = prev_bb_insn) {
      prev_bb_insn = DLIST_PREV (bb_insn_t, bb_insn);
      insn = bb_insn->insn;
      nops = MIR_insn_nops (insn->code);
      hard_reg_def_p = FALSE; dead_p = TRUE;
      for (i = 0; i < nops; i++) {
	op = insn->ops[i];
	MIR_insn_op_mode (insn->code, i, &out_p);
	if (! out_p || op.mode != MIR_OP_HARD_REG)
	  continue;
	hard_reg_def_p = TRUE;
	if (bitmap_clear_bit_p (live, op.u.hard_reg))
	  dead_p = FALSE;
      }
      if (! hard_reg_def_p)
	dead_p = FALSE;
      if (dead_p) {
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
	case MIR_OP_HARD_REG:
	  if (! out_p)
	    bitmap_set_bit_p (live, op.u.hard_reg);
	  break;
	case MIR_OP_HARD_REG_MEM:
	  if (op.u.hard_reg_mem.base != 0)
	    bitmap_set_bit_p (live, op.u.hard_reg_mem.base);
	  if (op.u.hard_reg_mem.index != 0)
	    bitmap_set_bit_p (live, op.u.hard_reg_mem.index);
	  break;
	default:
	  assert (op.mode != MIR_OP_REG && op.mode != MIR_OP_MEM);
	}
      }
      if (insn->code == MIR_CALL || insn->code == MIR_CALL_C)
	bitmap_ior (live, live, bb_insn->call_hard_reg_args);
    }
  }
  bitmap_destroy (live);
}


void MIR_gen (MIR_item_t func) {
  assert (func->func_p && func->data == NULL);
  machinize (func);
  curr_func = func;
  curr_cfg = func->data = malloc (sizeof (struct func_cfg));
  build_func_cfg ();
  build_func_cfg_live_info ();
  build_live_ranges ();
  assign ();
  rewrite (); /* After rewrite the BB live info is still valid */
  combine (); /* After combine the BB live info is still valid */
  dead_code_elimination (func);
  target_translate (func);
  destroy_func_live_ranges ();
  destroy_func_cfg_live_info ();
  destroy_func_cfg ();
}

void MIR_init_gen (void) {
  MIR_reg_t i;
  
  VARR_CREATE (bb_t, worklist, 0);
  VARR_CREATE (bb_t, pending, 0);
  bb_to_consider = bitmap_create ();
  VARR_CREATE (MIR_reg_t, breg_renumber, 0);
  VARR_CREATE (MIR_reg_t, sorted_bregs, 0);
  VARR_CREATE (size_t, loc_profits, 0);
  VARR_CREATE (size_t, loc_profit_ages, 0);
  curr_bb_hreg_def_age = 0;
  VARR_CREATE (size_t, hreg_def_ages, MAX_HARD_REG + 1);
  VARR_CREATE (hreg_def_t, hreg_defs, MAX_HARD_REG + 1);
  VARR_EXPAND (hreg_def_t, hreg_defs, MAX_HARD_REG + 1);
  conflict_locs = bitmap_create2 (3 * MAX_HARD_REG / 2);
  call_used_hard_regs = bitmap_create2 (MAX_HARD_REG + 1);
  for (i = 0; i <= MAX_HARD_REG; i++) {
    VARR_PUSH (size_t, hreg_def_ages, 0);
    if (call_used_hard_reg_p (i))
      bitmap_set_bit_p (call_used_hard_regs, i);
  }
  target_init ();
}

void MIR_finish_gen (void) {
  VARR_DESTROY (bb_t, worklist);
  VARR_DESTROY (bb_t, pending);
  bitmap_destroy (bb_to_consider);
  VARR_DESTROY (MIR_reg_t, breg_renumber);
  VARR_DESTROY (MIR_reg_t, sorted_bregs);
  VARR_DESTROY (size_t, loc_profits);
  VARR_DESTROY (size_t, loc_profit_ages);
  VARR_DESTROY (size_t, hreg_def_ages);
  VARR_DESTROY (hreg_def_t, hreg_defs);
  bitmap_destroy (conflict_locs);
  bitmap_destroy (call_used_hard_regs);
  target_finish ();
}
