#include "../mir.h"
#include "../mir-interp.h"
#include "../mir-gen.h"

static void create_program (void) {
  const char *str = "\n\
m_sieve:  module\n\
          export sieve\n\
sieve:    func i32, 819000, i32:N\n\
          local i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags\n\
          mov flags, fp\n\
          mov iter, 0\n\
loop:     bge fin, iter, N\n\
          mov count, 0;  mov i, 0\n\
loop2:    bge fin2, i, 819000\n\
          mov u8:(flags, i), 1;  add i, i, 1\n\
          jmp loop2\n\
fin2:     mov i, 0\n\
loop3:    bge fin3, i, 819000\n\
          beq cont3, u8:(flags,i), 0\n\
          add temp, i, i;  add prime, temp, 3;  add k, i, prime\n\
loop4:    bge fin4, k, 819000\n\
          mov u8:(flags, k), 0;  add k, k, prime\n\
          jmp loop4\n\
fin4:     add count, count, 1\n\
cont3:    add i, i, 1\n\
          jmp loop3\n\
fin3:     add iter, iter, 1\n\
          jmp loop\n\
fin:      ret count\n\
          endfunc\n\
          endmodule\n\
m_ex100:  module\n\
format:   string \"sieve (10) = %d\\n\"\n\
p_printf: proto v, p, i32\n\
p_sieve:  proto i32, i32\n\
          export ex100\n\
          import sieve, printf\n\
ex100:    func v, 0\n\
          local i64:r\n\
          call p_sieve, sieve, r, 100\n\
          call p_printf, printf, format, r\n\
          endfunc\n\
          endmodule\n\
";
  
  MIR_scan_string (str);
}

#include "real-time.h"
#include <inttypes.h>
#include <unistd.h>

int main (void) {
  double start_time = real_usec_time ();
  double start_execution_time;
  MIR_module_t m1, m2;
  MIR_item_t f1, f2;
  uint64_t res;

  MIR_init ();
  fprintf (stderr, "MIR_init end -- %.0f usec\n", real_usec_time () - start_time);
  create_program ();
  fprintf (stderr, "MIR program creation end -- %.0f usec\n", real_usec_time () - start_time);
  m1 = DLIST_HEAD (MIR_module_t, MIR_modules); m2 = DLIST_NEXT (MIR_module_t, m1);
  f1 = DLIST_TAIL (MIR_item_t, m1->items); f2 = DLIST_TAIL (MIR_item_t, m2->items);
  MIR_load_module (m2); MIR_load_module (m1);
  MIR_load_external ("printf", printf);
  MIR_interp_init ();
  MIR_link (MIR_set_interp_interface);
  MIR_gen_init ();
  MIR_gen (f1);
  MIR_interp (f2, 0);
  MIR_gen_finish ();
  MIR_interp_finish ();
  MIR_finish ();
  fprintf (stderr, "MIR_finish end -- %.0f usec\n", real_usec_time () - start_time);
  return 0;
}
