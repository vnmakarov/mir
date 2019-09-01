/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* *to = from; jump *handler  */
void *_MIR_get_interp_shim (MIR_item_t from, MIR_item_t *to, void *handler) {
  static const uint32_t pattern[] = {
    0xd2800009, /*  0: mov x9, xxxx(0-15) -- 3bits from last byte, 5bits from 2nd byte */
    0xf2a00009, /*  4: movk x9, xxxx(16-31) */
    0xf2c00009, /*  8: movk x9, xxxx(32-47) */
    0xf2e00009, /* 12: movk x9, xxxx(48-63) */
    0xd280000a, /* 16: mov x10, xxxx(0-15) */
    0xf2a0000a, /* 20: movk x10, xxxx(16-31) */
    0xf2c0000a, /* 24: movk x10, xxxx(32-47) */
    0xf2e0000a, /* 28: movk x10, xxxx(48-63) */
    0xf9000149, /* 32: str	x9, [x10] */
    0xd2800009, /*  36: mov x9, xxxx(0-15) */
    0xf2a00009, /*  40: movk x9, xxxx(16-31) */
    0xf2c00009, /*  44: movk x9, xxxx(32-47) */
    0xf2e00009, /* 48: movk x9, xxxx(48-63) */
    0xd61f0120, /* 52: br x9 */
  };
  uint8_t *addr = MIR_publish_code ((unsigned char *) pattern, sizeof (pattern));
  uint32_t *u;
  uint64_t f = (uint64_t) from, t = (uint64_t) to, h = (uint64_t) handler;

  u = (uint32_t *) addr;
  *u++ |= (f & 0xffff) << 5;
  *u++ |= ((f >> 16) & 0xffff) << 5;
  *u++ |= ((f >> 32) & 0xffff) << 5;
  *u++ |= ((f >> 48) & 0xffff) << 5;
  *u++ |= (t & 0xffff) << 5;
  *u++ |= ((t >> 16) & 0xffff) << 5;
  *u++ |= ((t >> 32) & 0xffff) << 5;
  *u++ |= ((t >> 48) & 0xffff) << 5;
  u = (uint32_t *) addr + 9;
  *u++ |= (h & 0xffff) << 5;
  *u++ |= ((h >> 16) & 0xffff) << 5;
  *u++ |= ((h >> 32) & 0xffff) << 5;
  *u++ |= ((h >> 48) & 0xffff) << 5;
  return addr;
}

/* r10=<address>; jump *r10  */
void *_MIR_get_thunk (void) {
  static const uint32_t pattern[] = {
    0xd2800009, /*  0: mov x9, xxxx(0-15) */
    0xf2a00009, /*  4: movk x9, xxxx(16-31) */
    0xf2c00009, /*  8: movk x9, xxxx(32-47) */
    0xf2e00009, /* 12: movk x9, xxxx(48-63) */
    0xd61f0120, /* 16: br x9 */
  };
  return _MIR_publish_code (pattern, sizeof (pattern));
}

void _MIR_redirect_thunk (void *thunk, void *to) {
  uint32_t *u = (uint32_t *) thunk, mask = ~(0xffff << 5);
  uint64_t t = (uint64_t) to;

  u[0] = u[0] & mask | (t & 0xffff) << 5;
  u[1] = u[1] & mask | ((t >> 16) & 0xffff) << 5;
  u[2] = u[2] & mask | ((t >> 32) & 0xffff) << 5;
  u[3] = u[3] & mask | ((t >> 48) & 0xffff) << 5;
}
