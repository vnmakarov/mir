#include <string.h>

MIR_item_t create_mir_func_sieve (size_t *len, MIR_module_t *m_res) {
  MIR_module_t m;
  const char *str = "\n\
m_sieve: module\n\
sieve:   func i64, 819000\n\
         local i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags\n\
         mov flags, fp\n\
         mov iter, 0\n\
loop:    bge fin, iter, 1000\n\
         mov count, 0;  mov i, 0\n\
loop2:   bge fin2, i, 819000\n\
         mov u8:(flags, i), 1;  add i, i, 1\n\
         jmp loop2\n\
fin2:    mov i, 0\n\
loop3:   bge fin3, i, 819000\n\
         beq cont3, u8:(flags,i), 0\n\
         add temp, i, i;  add prime, temp, 3;  add k, i, prime\n\
loop4:   bge fin4, k, 819000\n\
         mov u8:(flags, k), 0;  add k, k, prime\n\
         jmp loop4\n\
fin4:    add count, count, 1\n\
cont3:   add i, i, 1\n\
         jmp loop3\n\
fin3:    add iter, iter, 1\n\
         jmp loop\n\
fin:     ret count\n\
         endfunc\n\
         endmodule\n\
";
  
  if (len != NULL)
    *len = strlen (str);
  MIR_scan_string (str);
  m = DLIST_TAIL (MIR_module_t, MIR_modules);
  if (m_res != NULL)
    *m_res = DLIST_TAIL (MIR_module_t, MIR_modules);
  return DLIST_TAIL (MIR_item_t, m->items);
}
