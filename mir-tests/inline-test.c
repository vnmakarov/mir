#include "mir.h"
#include "c2mir/c2mir.h"

static const char *c_source
  = "static inline int add(int a, int b) { return a + b; }\n\
int main(void) { return add(3, 4); }\n";

static const char *pos;

static int source_getc (void *data) {
  (void) data;
  return *pos == '\0' ? EOF : *pos++;
}

int main (void) {
  MIR_context_t ctx = MIR_init ();
  c2mir_init (ctx);
  struct c2mir_options ops = {0};

  pos = c_source;
  if (!c2mir_compile (ctx, &ops, source_getc, NULL, "inline-test", NULL)) return 1;

  int found_inline = 0;
  for (MIR_module_t m = DLIST_HEAD (MIR_module_t, *MIR_get_module_list (ctx)); m != NULL;
       m = DLIST_NEXT (MIR_module_t, m))
    for (MIR_item_t item = DLIST_HEAD (MIR_item_t, m->items); item != NULL;
         item = DLIST_NEXT (MIR_item_t, item))
      if (item->item_type == MIR_func_item)
        for (MIR_insn_t insn = DLIST_HEAD (MIR_insn_t, item->u.func->insns); insn != NULL;
             insn = DLIST_NEXT (MIR_insn_t, insn))
          if (insn->code == MIR_INLINE) found_inline = 1;

  c2mir_finish (ctx);
  MIR_finish (ctx);
  return !found_inline;
}
