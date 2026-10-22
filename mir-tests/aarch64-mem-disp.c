/* This file is a part of MIR project.

   target_memory_ok_p's displacement gate, checked against what the encoder
   can actually emit.

   The aarch64 scaled forms -- "M0".."M3" (ldr Rd,[Rn,#imm12]) and "m0".."m3"
   (ldr Rd,[Rn,Rm{,#N}]) -- scale by the access size in BYTES; pattern_match_p
   tests them with `1 << (ch - '0')`. target_memory_ok_p instead compared
   against gen_int_log2 (size), so for an 8-byte access it used 3 where the
   encoder uses 8. That disagrees in both directions, and this file checks
   both:

     PART 1 (correctness): disp 12 satisfies 12 % 3 == 0, so the gate accepts
       it, but no pattern can encode an unaligned 64-bit offset -- the
       generator dies with "fatal failure in matching insn". Legal MIR in, no
       code out.

     PART 2 (code quality): disp 8 fails 8 % 3, so the gate rejects a
       displacement the encoder handles perfectly. ssa_combine's addressing
       mode reconstruction is refused and the offset stays a separate ADD.
       Only displacements divisible by 3 survived -- for 8-byte accesses, just
       the multiples of 24.

   Both parts are self-contained: run it, read the verdict.  */

#include "../mir-gen.h"
#include "../real-time.h"
#include <inttypes.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if !defined(_WIN32)
#include <sys/wait.h>
#include <unistd.h>
#endif

static jmp_buf err_jmp;
static char err_msg[512];

static void MIR_NO_RETURN catch_error (MIR_error_type_t error_type, const char *format, ...) {
  va_list ap;
  va_start (ap, format);
  vsnprintf (err_msg, sizeof (err_msg), format, ap);
  va_end (ap);
  (void) error_type;
  longjmp (err_jmp, 1);
}

/* p = *(int64_t *) ((char *) p + disp), n times, then return p.

   A dependent chain on purpose: a run of identical independent loads is CSE'd
   to one, which measures the optimiser rather than the addressing mode.  */
static MIR_item_t build_chase (MIR_context_t ctx, const char *name, int n, int64_t disp) {
  MIR_type_t res = MIR_T_I64;
  MIR_item_t f = MIR_new_func (ctx, name, 1, &res, 1, MIR_T_I64, "base");
  MIR_reg_t base = MIR_reg (ctx, "base", f->u.func);
  MIR_reg_t p = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "p");

  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, p),
                                 MIR_new_reg_op (ctx, base)));
  for (int i = 0; i < n; i++)
    MIR_append_insn (ctx, f,
                     MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, p),
                                   MIR_new_mem_op (ctx, MIR_T_I64, disp, p, 0, 1)));
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, p)));
  MIR_finish_func (ctx);
  return f;
}

/* Generate `name` and return its machine-code size in bytes, or 0 if
   generation failed (message left in err_msg).

   The size comes from the generator's own level-0 debug line,
   "Code generation for F: N MIR insns (addr=..., len=...)", since MIR_func
   exposes the code address but not its length.  */
static size_t gen_size (const char *name, int n, int64_t disp) {
  MIR_context_t ctx;
  FILE *dbg;
  char buf[1024];
  size_t len = 0;

  if (setjmp (err_jmp) != 0) return 0; /* generator bailed out */
  ctx = MIR_init ();
  MIR_set_error_func (ctx, catch_error);
  dbg = tmpfile ();
  MIR_module_t m = MIR_new_module (ctx, "m");
  MIR_item_t f = build_chase (ctx, name, n, disp);
  MIR_finish_module (ctx);
  MIR_gen_init (ctx);
  MIR_gen_set_optimize_level (ctx, 2);
  if (dbg != NULL) {
    MIR_gen_set_debug_file (ctx, dbg);
    MIR_gen_set_debug_level (ctx, 0);
  }
  MIR_load_module (ctx, m);
  MIR_link (ctx, MIR_set_gen_interface, NULL);
  (void) MIR_gen (ctx, f);
  if (dbg != NULL) {
    fflush (dbg);
    rewind (dbg);
    while (fgets (buf, sizeof (buf), dbg) != NULL) {
      char *q = strstr (buf, "len=");
      if (q != NULL) { len = (size_t) strtoul (q + 4, NULL, 10); break; }
    }
    fclose (dbg);
  }
  MIR_gen_finish (ctx);
  MIR_finish (ctx);
  return len;
}

/* Sum four fields of each struct in an array -- the ordinary object/record
   access shape. Offsets 0 and 24 already folded before the fix (both are
   divisible by 3), so only half of these accesses change: the benchmark is
   deliberately conservative.  */
static MIR_item_t build_field_sum (MIR_context_t ctx) {
  MIR_type_t res = MIR_T_I64;
  MIR_item_t f
    = MIR_new_func (ctx, "field_sum", 1, &res, 2, MIR_T_I64, "arr", MIR_T_I64, "n");
  MIR_reg_t arr = MIR_reg (ctx, "arr", f->u.func), n = MIR_reg (ctx, "n", f->u.func);
  MIR_reg_t i = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "i");
  MIR_reg_t s = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "s");
  MIR_reg_t q = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "q");
  MIR_reg_t t = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "t");
  MIR_label_t loop = MIR_new_label (ctx), fin = MIR_new_label (ctx);

  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, s), MIR_new_int_op (ctx, 0)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, i), MIR_new_int_op (ctx, 0)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_BGE, MIR_new_label_op (ctx, fin),
                                 MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, n)));
  MIR_append_insn (ctx, f, loop);
  /* q = arr + i * 32 */
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MUL, MIR_new_reg_op (ctx, q), MIR_new_reg_op (ctx, i),
                                 MIR_new_int_op (ctx, 32)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_ADD, MIR_new_reg_op (ctx, q), MIR_new_reg_op (ctx, q),
                                 MIR_new_reg_op (ctx, arr)));
  for (int off = 0; off < 32; off += 8) {
    MIR_append_insn (ctx, f,
                     MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, t),
                                   MIR_new_mem_op (ctx, MIR_T_I64, off, q, 0, 1)));
    MIR_append_insn (ctx, f,
                     MIR_new_insn (ctx, MIR_ADD, MIR_new_reg_op (ctx, s), MIR_new_reg_op (ctx, s),
                                   MIR_new_reg_op (ctx, t)));
  }
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_ADD, MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, i),
                                 MIR_new_int_op (ctx, 1)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_BLT, MIR_new_label_op (ctx, loop),
                                 MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, n)));
  MIR_append_insn (ctx, f, fin);
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, s)));
  MIR_finish_func (ctx);
  return f;
}

/* A cache-resident circular list chased through its `next` field.

   Where the extra ADD actually costs: a dependent chain. Each link is
   load-use latency plus, before the fix, one more ALU op that the loads
   cannot be reordered around, so it lands directly on the critical path.
   The streaming field_sum above is the opposite case -- independent loads
   with slack for the out-of-order engine to hide the ADD in -- and it
   barely moves. Both are reported because a change that only helps one
   shape should say so.  */
static MIR_item_t build_chase_loop (MIR_context_t ctx) {
  MIR_type_t res = MIR_T_I64;
  MIR_item_t f = MIR_new_func (ctx, "chase_loop", 1, &res, 2, MIR_T_I64, "head", MIR_T_I64, "n");
  MIR_reg_t head = MIR_reg (ctx, "head", f->u.func), n = MIR_reg (ctx, "n", f->u.func);
  MIR_reg_t i = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "i");
  MIR_reg_t p = MIR_new_func_reg (ctx, f->u.func, MIR_T_I64, "p");
  MIR_label_t loop = MIR_new_label (ctx), fin = MIR_new_label (ctx);

  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, p),
                                 MIR_new_reg_op (ctx, head)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, i), MIR_new_int_op (ctx, 0)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_BGE, MIR_new_label_op (ctx, fin),
                                 MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, n)));
  MIR_append_insn (ctx, f, loop);
  /* p = p->next, at offset 8 */
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_MOV, MIR_new_reg_op (ctx, p),
                                 MIR_new_mem_op (ctx, MIR_T_I64, 8, p, 0, 1)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_ADD, MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, i),
                                 MIR_new_int_op (ctx, 1)));
  MIR_append_insn (ctx, f,
                   MIR_new_insn (ctx, MIR_BLT, MIR_new_label_op (ctx, loop),
                                 MIR_new_reg_op (ctx, i), MIR_new_reg_op (ctx, n)));
  MIR_append_insn (ctx, f, fin);
  MIR_append_insn (ctx, f, MIR_new_ret_insn (ctx, 1, MIR_new_reg_op (ctx, p)));
  MIR_finish_func (ctx);
  return f;
}

#define NELEM 4096
#define REPS 20000
#define CHASE_NODES 1024 /* 32 KB of nodes: cache-resident, so this measures
                            the dependent chain, not memory latency */
#define CHASE_STEPS 2000000

int main (void) {
  int status = 0;

  printf ("== part 1: does a legal i64 load at a misaligned disp generate? ==\n");
#if defined(_WIN32)
  printf ("  skipped: needs fork() to survive the generator's exit(1)\n");
#else
  /* find_insn_pattern_replacement's failure path calls exit(1) directly
     (mir-gen-aarch64.c), not the MIR error func, so it cannot be caught in
     process -- run each case in a child and report its status.  */
  for (int64_t disp = 8; disp <= 16; disp += 4) {
    pid_t pid = fork ();
    if (pid == 0) {
      fclose (stderr); /* the generator's own message would interleave */
      _exit (gen_size ("chase", 8, disp) != 0 ? 0 : 1);
    }
    int wstat = 0;
    waitpid (pid, &wstat, 0);
    int ok = WIFEXITED (wstat) && WEXITSTATUS (wstat) == 0;
    printf ("  disp %2" PRId64 ":  %s\n", disp,
            ok ? "ok" : "GENERATION FAILED (generator called exit)");
    if (!ok) status = 1;
  }
  if (status)
    printf ("  ^ the gate accepted a displacement no pattern can encode.\n");
#endif

  printf ("\n== part 2: is the displacement folded into the load? ==\n");
  printf ("  8 dependent i64 loads; 4 bytes/load means the disp is in the\n"
          "  addressing mode, 8 means an extra address-forming instruction.\n");
  for (int64_t disp = 0; disp <= 24; disp += 8) {
    size_t a = gen_size ("chase_a", 4, disp);
    size_t b = gen_size ("chase_b", 20, disp);
    if (a == 0 || b == 0) {
      printf ("  disp %2" PRId64 ":  (generation failed -- see part 1)\n", disp);
      continue;
    }
    double per = (double) (b - a) / 16.0;
    printf ("  disp %2" PRId64 ":  %.1f bytes/load  %s\n", disp, per,
            per <= 4.5 ? "folded" : "NOT folded (extra ADD)");
  }

  printf ("\n== part 3: what it costs on ordinary field access ==\n");
  {
    MIR_context_t ctx = MIR_init ();
    if (setjmp (err_jmp) != 0) {
      fprintf (stderr, "unexpected generator failure: %s\n", err_msg);
      return 2;
    }
    MIR_set_error_func (ctx, catch_error);
    MIR_module_t m = MIR_new_module (ctx, "bench");
    MIR_item_t f = build_field_sum (ctx);
    MIR_finish_module (ctx);
    MIR_gen_init (ctx);
    MIR_gen_set_optimize_level (ctx, 2);
    MIR_load_module (ctx, m);
    MIR_link (ctx, MIR_set_gen_interface, NULL);
    int64_t (*fun) (int64_t, int64_t) = MIR_gen (ctx, f);

    int64_t *arr = malloc (sizeof (int64_t) * 4 * NELEM);
    for (int i = 0; i < 4 * NELEM; i++) arr[i] = i;

    int64_t res = fun ((int64_t) arr, NELEM); /* warm up */
    double best = 1e18;
    for (int r = 0; r < 5; r++) {
      double t0 = real_usec_time ();
      for (int k = 0; k < REPS; k++) res += fun ((int64_t) arr, NELEM);
      double dt = real_usec_time () - t0;
      if (dt < best) best = dt; /* min: contention only ever slows a run down */
    }
    printf ("  field_sum  (independent loads): best %.0f usec (checksum %" PRId64 ")\n",
            best, res);
    free (arr);

    /* dependent chase over the same context */
    MIR_module_t m2 = MIR_new_module (ctx, "bench2");
    MIR_item_t f2 = build_chase_loop (ctx);
    MIR_finish_module (ctx);
    MIR_load_module (ctx, m2);
    MIR_link (ctx, MIR_set_gen_interface, NULL);
    int64_t (*chase) (int64_t, int64_t) = MIR_gen (ctx, f2);
    int64_t *nodes = malloc (sizeof (int64_t) * 4 * CHASE_NODES);
    for (int k = 0; k < CHASE_NODES; k++) {
      nodes[4 * k] = k;
      nodes[4 * k + 1] = (int64_t) (nodes + 4 * ((k + 1) % CHASE_NODES)); /* next */
      nodes[4 * k + 2] = nodes[4 * k + 3] = 0;
    }
    int64_t r2 = chase ((int64_t) nodes, 1000); /* warm up */
    double best2 = 1e18;
    for (int r = 0; r < 5; r++) {
      double t0 = real_usec_time ();
      r2 += chase ((int64_t) nodes, CHASE_STEPS);
      double dt = real_usec_time () - t0;
      if (dt < best2) best2 = dt;
    }
    printf ("  chase_loop (dependent chain): best %.0f usec for %d steps"
            " (%.2f ns/step)\n",
            best2, CHASE_STEPS, best2 * 1000.0 / CHASE_STEPS);
    (void) r2;
    free (nodes);
    MIR_gen_finish (ctx);
    MIR_finish (ctx);
  }
  return status;
}
