/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* ??? Rewrite to ppc64 */
/* *to = from; rax = 8; jump *handler  */
void *_MIR_get_interp_shim (MIR_item_t from, MIR_item_t *to, void *handler) {
  static unsigned char pattern[] = {
    0x49, 0xba, 0,    0,    0,    0,    0,    0, 0, 0, /* 0: movabsq 0, r10 */
    0x49, 0xbb, 0,    0,    0,    0,    0,    0, 0, 0, /* 10: movabsq 0, r11 */
    0x4d, 0x89, 0x13,                                  /* 20: mov r10, (r11) */
    0x49, 0xba, 0,    0,    0,    0,    0,    0, 0, 0, /* 23: movabsq 0, r10 */
    0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,          /* 33: mov $8, rax -- to save xmm varargs */
    0x41, 0xff, 0xe2,                                  /* 40: jmpq   *%r10 */
  };
  uint8_t *addr = MIR_publish_code (pattern, sizeof (pattern));

  MIR_update_code (addr, 3, 2, from, 12, to, 25, handler);
  return addr;
}

/* r10=<address>; jump *r10  */
void *_MIR_get_thunk (void) {
  static unsigned char pattern[] = {
    0x49, 0xba, 0,    0, 0, 0, 0, 0, 0, 0, /* 0: movabsq 0, r10 */
    0x41, 0xff, 0xe2,                      /* 40: jmpq   *%r10 */
  };
  return _MIR_publish_code (pattern, sizeof (pattern));
}

void _MIR_redirect_thunk (void *thunk, void *to) { _MIR_update_code (thunk, 1, 2, to); }
