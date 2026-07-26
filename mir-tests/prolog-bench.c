/* Cost of the function prolog/epilog callee-saved reg save/restore.

   heavy keeps HEAVY_N_INT ints and HEAVY_N_DBL doubles live across a call,
   so the allocator runs out of caller-saved regs and spills them into the
   whole callee-saved set: its prolog saves and restores all of them.
   leaf has no calls and one live value, so it keeps the empty-prolog leaf
   fast path -- the control, which prolog codegen changes must not move.
   Both are padded past MIR's call-inline threshold (50 insns, see
   MIR_MAX_INSNS_FOR_CALL_INLINE) so the calls to them survive to codegen.

   Each is called PROLOG_BENCH_N times from a MIR loop, timed PROLOG_BENCH_REPS
   times; min/median/max are reported so a busy machine shows up as a spread
   rather than a shifted minimum. */

#include <inttypes.h>
#include <stdlib.h>
#include <sys/time.h>
#include "mir-gen.h"

#define HEAVY_N_INT 20
#define HEAVY_N_DBL 10
#ifndef PROLOG_BENCH_REPS
#define PROLOG_BENCH_REPS 15
#endif
#ifndef PROLOG_BENCH_N
#define PROLOG_BENCH_N 30000000
#endif
#define PAD_INSNS 60

static MIR_item_t i64_i64_proto (MIR_context_t ctx, const char *name) {
  MIR_type_t res = MIR_T_I64;
  return MIR_new_proto (ctx, name, 1, &res, 1, MIR_T_I64, "a");
}

static void append (MIR_context_t ctx, MIR_item_t f, MIR_insn_code_t code, MIR_op_t a, MIR_op_t b,
                    MIR_op_t c) {
  MIR_append_insn (ctx, f, MIR_new_insn (ctx, code, a, b, c));
}

/* A leaf of PAD_INSNS chained adds on one reg: over the inline threshold,
   still one live value.  Used for both sink (heavy's callee) and leaf. */
static MIR_item_t new_pad_func (MIR_context_t ctx, const char *mod, const char *name) {
  MIR_item_t f;
  MIR_reg_t a;
  MIR_type_t res = MIR_T_I64;

  MIR_new_module (ctx, mod);
  MIR_new_export (ctx, name);
  f = MIR_new_func (ctx, name, 1, &res, 1, MIR_T_I64, "a");
  a = MIR_reg (ctx, "a", f->u.func);
  for (int i = 0; i < PAD_INSNS; i++)
    append (ctx, f, MIR_ADD, MIR_new_reg_op (ctx, a), MIR_new_reg_op (ctx, a),
            MIR_new_int_op (ctx, 1));
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, a)));
  MIR_finish_func (ctx);
  MIR_finish_module (ctx);
  return f;
}

static MIR_item_t new_heavy_func (MIR_context_t ctx) {
  MIR_item_t f, proto, imp;
  MIR_reg_t a, ir[HEAVY_N_INT], dr[HEAVY_N_DBL], isum, dsum, tmp;
  MIR_type_t res = MIR_T_I64;
  char nm[32];

  MIR_new_module (ctx, "m_heavy");
  MIR_new_export (ctx, "heavy");
  proto = i64_i64_proto (ctx, "p_sink");
  imp = MIR_new_import (ctx, "sink");
  f = MIR_new_func (ctx, "heavy", 1, &res, 1, MIR_T_I64, "a");
  a = MIR_reg (ctx, "a", f->u.func);
  isum = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "isum");
  dsum = MIR_new_func_reg (ctx, f->u.func, MIR_T_D, "dsum");
  tmp = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "tmp");
  for (int i = 0; i < HEAVY_N_INT; i++) {
    snprintf (nm, sizeof (nm), "i%d", i);
    ir[i] = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, nm);
  }
  for (int i = 0; i < HEAVY_N_DBL; i++) {
    snprintf (nm, sizeof (nm), "d%d", i);
    dr[i] = MIR_new_func_reg (ctx, f->u.func, MIR_T_D, nm);
  }
  /* Independent values so none can be rematerialized after the call. */
  for (int i = 0; i < HEAVY_N_INT; i++)
    append (ctx, f, MIR_ADD, MIR_new_reg_op (ctx, ir[i]), MIR_new_reg_op (ctx, a),
            MIR_new_int_op (ctx, i + 1));
  for (int i = 0; i < HEAVY_N_DBL; i++) {
    MIR_append_insn (ctx, f,
                     MIR_new_insn (ctx, MIR_I2D, MIR_new_reg_op (ctx, dr[i]),
                                   MIR_new_reg_op (ctx, a)));
    append (ctx, f, MIR_DADD, MIR_new_reg_op (ctx, dr[i]), MIR_new_reg_op (ctx, dr[i]),
            MIR_new_double_op (ctx, (double) (i + 1) * 0.5));
  }
  /* Everything above is live across this; the call clobbers the
     caller-saved regs, so they all land in callee-saved ones. */
  MIR_append_insn (ctx, f,
                   MIR_new_call_insn (ctx, 4, MIR_new_ref_op (ctx, proto),
                                      MIR_new_ref_op (ctx, imp), MIR_new_reg_op (ctx, tmp),
                                      MIR_new_reg_op (ctx, a)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, isum),
                                 MIR_new_reg_op (ctx, tmp)));
  for (int i = 0; i < HEAVY_N_INT; i++)
    append (ctx, f, MIR_ADD, MIR_new_reg_op (ctx, isum), MIR_new_reg_op (ctx, isum),
            MIR_new_reg_op (ctx, ir[i]));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_DMOV, MIR_new_reg_op (ctx, dsum),
                                 MIR_new_double_op (ctx, 0.0)));
  for (int i = 0; i < HEAVY_N_DBL; i++)
    append (ctx, f, MIR_DADD, MIR_new_reg_op (ctx, dsum), MIR_new_reg_op (ctx, dsum),
            MIR_new_reg_op (ctx, dr[i]));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_D2I, MIR_new_reg_op (ctx, tmp),
                                 MIR_new_reg_op (ctx, dsum)));
  append (ctx, f, MIR_ADD, MIR_new_reg_op (ctx, isum), MIR_new_reg_op (ctx, isum),
          MIR_new_reg_op (ctx, tmp));
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, isum)));
  MIR_finish_func (ctx);
  MIR_finish_module (ctx);
  return f;
}

/* Caller: xor the results so neither the call nor the loop folds away. */
static MIR_item_t new_call_loop (MIR_context_t ctx, const char *name, const char *callee) {
  MIR_item_t f, proto, imp;
  MIR_reg_t n, i, acc, tmp;
  MIR_label_t loop, fin;
  MIR_type_t res = MIR_T_I64;
  char pn[32];

  MIR_new_module (ctx, name);
  MIR_new_export (ctx, name);
  snprintf (pn, sizeof (pn), "p_%s", callee);
  proto = i64_i64_proto (ctx, pn);
  imp = MIR_new_import (ctx, callee);
  f = MIR_new_func (ctx, name, 1, &res, 1, MIR_T_I64, "n");
  n = MIR_reg (ctx, "n", f->u.func);
  i = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "i");
  acc = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "acc");
  tmp = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "tmp");
  loop = MIR_new_label (ctx);
  fin = MIR_new_label (ctx);
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, i), MIR_new_int_op (ctx, 0)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, acc), MIR_new_int_op (ctx, 0)));
  MIR_append_insn (ctx, f, loop);
  append (ctx, f, MIR_BGE, MIR_new_label_op (ctx, fin), MIR_new_reg_op (ctx, i),
          MIR_new_reg_op (ctx, n));
  MIR_append_insn (ctx, f,
                   MIR_new_call_insn (ctx, 4, MIR_new_ref_op (ctx, proto),
                                      MIR_new_ref_op (ctx, imp), MIR_new_reg_op (ctx, tmp),
                                      MIR_new_reg_op (ctx, i)));
  append (ctx, f, MIR_XOR, MIR_new_reg_op (ctx, acc), MIR_new_reg_op (ctx, acc),
          MIR_new_reg_op (ctx, tmp));
  append (ctx, f, MIR_ADD, MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, i),
          MIR_new_int_op (ctx, 1));
  MIR_append_insn (ctx, f, MIR_new_insn (ctx, MIR_JMP, MIR_new_label_op (ctx, loop)));
  MIR_append_insn (ctx, f, fin);
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, acc)));
  MIR_finish_func (ctx);
  MIR_finish_module (ctx);
  return f;
}

static double usec (void) {
  struct timeval tv;
  gettimeofday (&tv, NULL);
  return tv.tv_sec * 1000000.0 + tv.tv_usec;
}

static int cmp_double (const void *a, const void *b) {
  double x = *(const double *) a, y = *(const double *) b;
  return x < y ? -1 : x > y ? 1 : 0;
}

static void report (const char *name, double *t, int n) {
  qsort (t, n, sizeof (double), cmp_double);
  fprintf (stderr, "%-20s min=%8.1f ms  median=%8.1f ms  max=%8.1f ms\n", name, t[0] / 1000.0,
           t[n / 2] / 1000.0, t[n - 1] / 1000.0);
}

int main (void) {
  MIR_context_t ctx = MIR_init ();
  MIR_item_t items[5];
  uint64_t (*call[2]) (uint64_t);
  double t[2][PROLOG_BENCH_REPS], start;
  const char *names[2] = {"heavy (full saves)", "leaf (no saves)"};

  items[0] = new_pad_func (ctx, "m_sink", "sink");
  items[1] = new_heavy_func (ctx);
  items[2] = new_pad_func (ctx, "m_leaf", "leaf");
  items[3] = new_call_loop (ctx, "call_heavy", "heavy");
  items[4] = new_call_loop (ctx, "call_leaf", "leaf");
  for (int i = 0; i < 5; i++) MIR_load_module (ctx, items[i]->module);
  MIR_gen_init (ctx);
  MIR_link (ctx, MIR_set_gen_interface, NULL);
  call[0] = items[3]->addr;
  call[1] = items[4]->addr;

  for (int k = 0; k < 2; k++) call[k] (1000); /* warm up */
  for (int rep = 0; rep < PROLOG_BENCH_REPS; rep++)
    for (int k = 0; k < 2; k++) {
      start = usec ();
      call[k] (PROLOG_BENCH_N);
      t[k][rep] = usec () - start;
    }
  fprintf (stderr, "\n%d reps, %" PRIu64 " calls per rep:\n", PROLOG_BENCH_REPS,
           (uint64_t) PROLOG_BENCH_N);
  for (int k = 0; k < 2; k++) report (names[k], t[k], PROLOG_BENCH_REPS);
  MIR_gen_finish (ctx);
  MIR_finish (ctx);
  return 0;
}
