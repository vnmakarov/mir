/* This file is a part of MIR project.

   Regression test for ssa_combine folding a memory operand's base through a
   LOOP-header PHI (issue #467).  The function below (adapted from the
   API-level reducer reported by ThePeiLin) is the minimal shape:

     - an outer loop with a pointer PHI `p` at its head;
     - an inner loop whose memory ops address `p` at a constant offset from
       the OUTER loop-head snapshot;
     - make_conventional_ssa places the outer PHI's backedge copy so the
       inner loop body executes AFTER the copy.

   Folding the inner-loop accesses onto the backedge-updated register makes
   them land one byte past the intended cell: before the fix the function
   segfaulted (or looped forever in a sibling shape) at optimize level 2 and
   returned 0 correctly at level 1.  The fixed cycle_phi_p recognizes any
   loop-header PHI (a block with an incoming back edge), not only single-BB
   self-loops.  This test runs the function at levels 1 and 2 and requires
   the correct return value from both. */

#include <mir-gen.h>
#include <mir.h>
#include <stdio.h>
#include <stdlib.h>

#define MEM(B, D) MIR_new_mem_op (ctx, MIR_T_U8, D, B, 0, 0)
#define OPR(T, V) MIR_new_##T##_op (ctx, V)
#define LAB(L) MIR_new_label_op (ctx, L)
#define REG(R) MIR_new_reg_op (ctx, R)
#define APP(I) MIR_append_insn (ctx, f, I)
#define INSN(OP, ...)                                                        \
  APP (MIR_new_insn_arr (ctx, MIR_##OP,                                      \
                         sizeof ((MIR_op_t[]) {__VA_ARGS__}) / sizeof (MIR_op_t), \
                         (MIR_op_t[]) {__VA_ARGS__}))

static MIR_item_t build (MIR_context_t ctx) {
  MIR_item_t f = MIR_new_func (ctx, "min", 1, (MIR_type_t[]) {MIR_T_I64}, 0);
  MIR_reg_t p = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "p");
  MIR_reg_t r = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "r");
  MIR_type_t ret_ptr = MIR_T_P;
  MIR_item_t pc_proto
    = MIR_new_proto (ctx, "pc", 1, &ret_ptr, 2, MIR_T_U64, "n", MIR_T_U64, "s");
  MIR_item_t pc_imp = MIR_new_import (ctx, "calloc");
  MIR_load_external (ctx, "calloc", calloc);
  /* p = calloc (4096, 1) */
  INSN (INLINE, MIR_new_ref_op (ctx, pc_proto), MIR_new_ref_op (ctx, pc_imp), REG (p),
        OPR (uint, 4096), OPR (uint, 1));
  /* *(p) = 1  (outer counter) */
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, 1));
  INSN (MOV, MEM (p, 0), REG (r));
  /* *(p+1) = 3  (inner counter) */
  INSN (ADD, REG (p), REG (p), OPR (int, 1));
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, 3));
  INSN (MOV, MEM (p, 0), REG (r));
  INSN (ADD, REG (p), REG (p), OPR (int, -1));

  MIR_label_t L1 = MIR_new_label (ctx), E1 = MIR_new_label (ctx);
  /* L1 (outer head): r = *p; beq E1, r, 0 */
  APP (L1);
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (BEQ, LAB (E1), REG (r), OPR (uint, 0));
  /* outer body: *p -= 1; p += 1; *p += 1; p += 2; *p += 1; p -= 2
     (p ends the body at loop-head + 1) */
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, -1));
  INSN (MOV, MEM (p, 0), REG (r));
  INSN (ADD, REG (p), REG (p), OPR (int, 1));
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, 1));
  INSN (MOV, MEM (p, 0), REG (r));
  INSN (ADD, REG (p), REG (p), OPR (int, 2));
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, 1));
  INSN (MOV, MEM (p, 0), REG (r));
  INSN (ADD, REG (p), REG (p), OPR (int, -2));
  /* L2 (inner head): r = *p; beq L1, r, 0 */
  MIR_label_t L2 = MIR_new_label (ctx);
  APP (L2);
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (BEQ, LAB (L1), REG (r), OPR (uint, 0));
  /* inner body (executes after the outer PHI's backedge copy): *p -= 1 */
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (ADD, REG (r), REG (r), OPR (int, -1));
  INSN (MOV, MEM (p, 0), REG (r));
  INSN (JMP, LAB (L2));
  /* E1: ret *p */
  APP (E1);
  INSN (MOV, REG (r), MEM (p, 0));
  INSN (RET, REG (r));
  MIR_finish_func (ctx);
  return f;
}

typedef int64_t (*fn_t) (void);

static int run_at_level (int opt) {
  MIR_context_t ctx = MIR_init ();
  MIR_module_t mod = MIR_new_module (ctx, "min");
  MIR_item_t f = build (ctx);
  int64_t v;

  MIR_finish_module (ctx);
  MIR_load_module (ctx, mod);
  MIR_gen_init (ctx);
  MIR_gen_set_optimize_level (ctx, opt);
  MIR_link (ctx, MIR_set_gen_interface, NULL);
  v = ((fn_t) MIR_gen (ctx, f)) ();
  printf ("OPT%d: ret=%lld\n", opt, (long long) v);
  MIR_gen_finish (ctx);
  MIR_finish (ctx);
  return v == 0;
}

int main (void) {
  int ok1 = run_at_level (1);
  int ok2 = run_at_level (2);
  if (ok1 && ok2) {
    printf ("ssa-combine-loop-phi test OK\n");
    return 0;
  }
  return 1;
}
