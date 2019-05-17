/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* _MIR_called_func = r10; rax = 8; jump *handler  */
void *_MIR_get_interp_shim (void *handler) {
  static unsigned char pattern[] =
    {
     0x49, 0xbb, 0, 0, 0, 0, 0, 0, 0, 0,       /* 0x0: movabsq 0, r11 */
     0x4d, 0x89, 0x13,                         /* 0xa: mov r10, (r11) */
     0x49, 0xba, 0, 0, 0, 0, 0, 0, 0, 0,       /* 0xd: movabsq 0, r10 */
     0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00, /* 0x17: mov $8, rax -- to save xmm varargs */
     0x41, 0xff, 0xe2,                         /* 0x21: jmpq   *%r10 */
    };
  uint8_t *addr = _MIR_publish_code (pattern, sizeof (pattern));

  _MIR_update_code (addr, 2, 2, &_MIR_called_func, 15, handler);
  return addr;
}

/* r11=<address to go to>; r10=<address of func item>; jump *r11  */
void *_MIR_get_thunk (MIR_item_t item) {
  void *res;
  static unsigned char pattern[] =
    {
     0x49, 0xbb, 0, 0, 0, 0, 0, 0, 0, 0, /* 0x0: movabsq 0, r11 */
     0x49, 0xba, 0, 0, 0, 0, 0, 0, 0, 0, /* 0xa: movabsq 0, r10 */
     0x41, 0xff, 0xe3, /* 0x14: jmpq   *%r11 */
    };
  res = _MIR_publish_code (pattern, sizeof (pattern));
  _MIR_update_code (res, 1, 12, item);
  return res;
}

void _MIR_redirect_thunk (void *thunk, void *to) {
  _MIR_update_code (thunk, 1, 2, to);
}

void *_MIR_get_thunk_target (void *thunk) {
  void *res;
  
  memcpy (&res, (char *) thunk + 2, sizeof (void *));
  return res;
}

MIR_item_t _MIR_get_thunk_func (void *thunk) {
  MIR_item_t res;
  
  memcpy (&res, (char *) thunk + 12, sizeof (MIR_item_t));
  return res;
}

/* save regs; _MIR_called_func = r10; r10 = call hook_address (); restore regs; jmp *r10  */
void *_MIR_get_wrapper (void *hook_address) {
  static unsigned char pattern[] =
    {
     /* 0:*/	0x50,                   		/*push   %rax                      */
     /* 1:*/	0x57,                   		/*push   %rdi			   */
     /* 2:*/	0x56,                   		/*push   %rsi			   */
     /* 3:*/	0x52,                   		/*push   %rdx			   */
     /* 4:*/	0x51,                   		/*push   %rcx			   */
     /* 5:*/	0x41, 0x50,                		/*push   %r8			   */
     /* 7:*/	0x41, 0x51,                		/*push   %r9			   */
     /* 9:*/	0x48, 0x81, 0xec, 0x80, 0, 0, 0, 	/*sub    $0x80,%rsp		   */
     /*10:*/	0xf3, 0x0f, 0x7f, 0x04, 0x24,       	/*movdqu %xmm0,(%rsp)		   */
     /*15:*/	0xf3, 0x0f, 0x7f, 0x4c, 0x24, 0x10,    	/*movdqu %xmm1,0x10(%rsp)	   */
     /*1b:*/	0xf3, 0x0f, 0x7f, 0x54, 0x24, 0x20,    	/*movdqu %xmm2,0x20(%rsp)	   */
     /*21:*/	0xf3, 0x0f, 0x7f, 0x5c, 0x24, 0x30,    	/*movdqu %xmm3,0x30(%rsp)	   */
     /*27:*/	0xf3, 0x0f, 0x7f, 0x64, 0x24, 0x40,    	/*movdqu %xmm4,0x40(%rsp)	   */
     /*2d:*/	0xf3, 0x0f, 0x7f, 0x6c, 0x24, 0x50,    	/*movdqu %xmm5,0x50(%rsp)	   */
     /*33:*/	0xf3, 0x0f, 0x7f, 0x74, 0x24, 0x60,    	/*movdqu %xmm6,0x60(%rsp)	   */
     /*39:*/	0xf3, 0x0f, 0x7f, 0x7c, 0x24, 0x70,    	/*movdqu %xmm7,0x70(%rsp)	   */
     /*3f:*/	0x49, 0xbb, 0, 0, 0, 0, 0, 0, 0, 0,	/*movabs &_MIR_call_func,%r11  	   */
     /*49:*/    0x4d, 0x89, 0x13,                       /*mov %r10, (%r11) 		   */
     /*4c:*/	0x49, 0xba, 0, 0, 0, 0, 0, 0, 0, 0,	/*movabs <hook_address>,%r10  	   */
     /*56:*/	0x41, 0xff, 0xd2,             		/*callq  *%r10			   */
     /*59:*/	0x49, 0x89, 0xc2,             		/*mov    %rax,%r10		   */
     /*5c:*/	0xf3, 0x0f, 0x6f, 0x04, 0x24,       	/*movdqu (%rsp),%xmm0		   */
     /*61:*/	0xf3, 0x0f, 0x6f, 0x4c, 0x24, 0x10,    	/*movdqu 0x10(%rsp),%xmm1	   */
     /*67:*/	0xf3, 0x0f, 0x6f, 0x54, 0x24, 0x20,    	/*movdqu 0x20(%rsp),%xmm2	   */
     /*6d:*/	0xf3, 0x0f, 0x6f, 0x5c, 0x24, 0x30,    	/*movdqu 0x30(%rsp),%xmm3	   */
     /*73:*/	0xf3, 0x0f, 0x6f, 0x64, 0x24, 0x40,    	/*movdqu 0x40(%rsp),%xmm4	   */
     /*79:*/	0xf3, 0x0f, 0x6f, 0x6c, 0x24, 0x50,    	/*movdqu 0x50(%rsp),%xmm5	   */
     /*7f:*/	0xf3, 0x0f, 0x6f, 0x74, 0x24, 0x60,    	/*movdqu 0x60(%rsp),%xmm6	   */
     /*85:*/	0xf3, 0x0f, 0x6f, 0x7c, 0x24, 0x70,    	/*movdqu 0x70(%rsp),%xmm7	   */
     /*8b:*/	0x48, 0x81, 0xc4, 0x80, 0, 0, 0, 	/*add    $0x80,%rsp		   */
     /*92:*/	0x41, 0x59,                		/*pop    %r9			   */
     /*94:*/	0x41, 0x58,                		/*pop    %r8			   */
     /*96:*/	0x59,                   		/*pop    %rcx			   */
     /*97:*/	0x5a,                   		/*pop    %rdx			   */
     /*98:*/	0x5e,                   		/*pop    %rsi			   */
     /*99:*/	0x5f,                   		/*pop    %rdi			   */
     /*9a:*/	0x58,                   		/*pop    %rax			   */
     /*9b:*/	0x41, 0xff, 0xe2             		/*jmpq   *%r10			   */
    };
  uint8_t *addr = _MIR_publish_code (pattern, sizeof (pattern));

  _MIR_update_code (addr, 2, 0x41, &_MIR_called_func, 0x4e, hook_address);
  return addr;
}
