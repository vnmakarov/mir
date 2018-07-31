/* expr extensions */

#include <assert.h>
#include <string.h>
#include <ctype.h>
#include <float.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>

#define MIR_VARR_ERROR error
#define MIR_HTAB_ERROR MIR_VARR_ERROR 

#define FALSE 0
#define TRUE 1

typedef enum {
  C_alloc_error, C_unfinished_comment, C_absent_exponent, C_wrong_octal_int, C_out_of_range_number,
  C_invalid_char_constant, C_no_string_end, C_invalid_str_constant, C_invalid_char,
} C_error_code_t;

static void (*error_func) (C_error_code_t code, const char *message);
static void error (const char *message) { error_func (C_alloc_error, message); }

#include "mir-varr.h"
#include "mir-dlist.h"
#include "mir-htab.h"
#include "mir-mum.h"

typedef struct node *node_t;

enum basic_type {
  TP_UNDEF, TP_VOID,
  /* Integer types: the first should be BOOL and the last should be
     ULONG_LONG.  The order is important -- do not change it.  */
  TP_BOOL, TP_CHAR, TP_SCHAR, TP_UCHAR, TP_SHORT, TP_USHORT, TP_INT, TP_UINT,
  TP_LONG, TP_ULONG, TP_LONG_LONG, TP_ULONG_LONG,
  TP_FLOAT, TP_DOUBLE, TP_LONG_DOUBLE, TP_FLOAT_COMPLEX, TP_DOUBLE_COMPLEX, TP_LONG_DOUBLE_COMPLEX, 
};

struct type_qual {
  unsigned int const_p : 1, restrict_p : 1, volatile_p : 1, atomic_p : 1; /* Type qualifiers */
};

static const struct type_qual zero_type_qual = {0, 0, 0, 0};

struct arr_type {
  unsigned int static_p : 1;
  struct type *el_type;
  struct type_qual ind_type_qual;
  node_t size;
};

struct func_type {
  unsigned int dots_p : 1;
  struct type *ret_type;
  node_t param_list; /* w/o N_DOTS */
};

enum type_mode {
  TM_UNDEF, TM_BASIC, TM_ENUM, TM_PTR, TM_STRUCT, TM_UNION, TM_ARR, TM_FUNC,
};

struct type {
  struct type_qual type_qual;
  node_t pos_node; /* set up and used only for checking type correctness */
  unsigned int incomplete_p : 1;
  enum type_mode mode;
  union {
    enum basic_type basic_type;
    node_t tag_type; /* struct/union/enum */
    struct type *ptr_type;
    struct arr_type *arr_type;
    struct func_type *func_type;
  } u;
};

static unsigned long long raw_type_size (struct type *type);

#ifdef __x86_64__
#include "mir-cx86_64.h"
#else
#error "undefined or unsupported generation target for C"
#endif

typedef void *void_ptr_t;
DEF_VARR (void_ptr_t);
static VARR (void_ptr_t) *reg_memory;

static void *reg_malloc (size_t s) {
  void *mem = malloc (s);

  if (mem == NULL) error ("no memory");
  VARR_PUSH (void_ptr_t, reg_memory, mem);
  return mem;
}

static void reg_memory_finish (void) {
  for (size_t i = 0; i < VARR_LENGTH (void_ptr_t, reg_memory); i++)
    free (VARR_GET (void_ptr_t, reg_memory, i));
    VARR_DESTROY (void_ptr_t, reg_memory);
}

static void reg_memory_init (void) {
  VARR_CREATE (void_ptr_t, reg_memory, 4096);
}

enum str_flag { FLAG_EXT = 1, FLAG_C89, FLAG_EXT89 };

typedef struct {
  const char *s;
  size_t key, flags;
} str_t;

DEF_HTAB (str_t);
static HTAB (str_t) *str_tab;
static HTAB (str_t) *str_key_tab;

static int str_eq (str_t str1, str_t str2) { return strcmp (str1.s, str2.s) == 0; }
static htab_hash_t str_hash (str_t str) { return mum_hash (str.s, strlen (str.s), 0x42); }
static int str_key_eq (str_t str1, str_t str2) { return str1.key == str2.key; }
static htab_hash_t str_key_hash (str_t str) { return mum_hash64 (str.key, 0x24); }

static void str_init (void) {
  HTAB_CREATE (str_t, str_tab, 1000, str_hash, str_eq);
  HTAB_CREATE (str_t, str_key_tab, 200, str_key_hash, str_key_eq);
}

static str_t str_add (const char *s, size_t key, size_t flags, int key_p) {
  char *heap_s;
  str_t el, str;
  
  str.s = s;
  if (HTAB_DO (str_t, str_tab, str, HTAB_FIND, el))
    return el;
  heap_s = reg_malloc (strlen (s) + 1);
  strcpy (heap_s, s); str.s = heap_s; str.key = key; str.flags = flags;
  HTAB_DO (str_t, str_tab, str, HTAB_INSERT, el);
  if (key_p)
    HTAB_DO (str_t, str_key_tab, str, HTAB_INSERT, el);
  return str;
}

static const char *find_str_by_key (size_t key) {
  str_t el, str;
  
  str.key = key;
  if (! HTAB_DO (str_t, str_key_tab, str, HTAB_FIND, el))
    return NULL;
  return el.s;
}

static void str_finish (void) {
  HTAB_DESTROY (str_t, str_tab);
  HTAB_DESTROY (str_t, str_key_tab);
}



/* ------------------------- Scanner/Parser Start ------------------------------ */

typedef enum {
  T_CONSTANT = 256, T_STR, T_ID, T_ASSIGN, T_DIVOP, T_ADDOP, T_SH, T_CMP, T_EQNE,
  T_ANDAND, T_OROR, T_INCDEC, T_ARROW, T_UNOP, T_DOTS,
  T_BOOL, T_COMPLEX, T_ALIGNOF,
  T_ALIGNAS, T_ATOMIC, T_GENERIC, T_NO_RETURN, T_STATIC_ASSERT, T_THREAD_LOCAL, T_THREAD,
  T_AUTO, T_BREAK, T_CASE, T_CHAR, T_CONST, T_CONTINUE, T_DEFAULT,
  T_DO, T_DOUBLE, T_ELSE, T_ENUM, T_EXTERN, T_FLOAT, T_FOR,
  T_GOTO, T_IF, T_INLINE, T_INT, T_LONG, T_REGISTER, T_RESTRICT, T_RETURN,
  T_SHORT, T_SIGNED, T_SIZEOF, T_STATIC, T_STRUCT, T_SWITCH, T_TYPEDEF, T_TYPEOF,
  T_UNION, T_UNSIGNED, T_VOID, T_VOLATILE, T_WHILE,
} token_code_t;

typedef enum {
  N_IGNORE, N_I, N_L, N_LL, N_U, N_UL, N_ULL, N_F, N_D, N_LD, N_CH, N_STR, N_ID,
  N_COMMA, N_ANDAND, N_OROR, N_EQ, N_NE, N_LT, N_LE, N_GT, N_GE, N_ASSIGN,
  N_BITWISE_NOT, N_NOT, N_AND, N_AND_ASSIGN, N_OR, N_OR_ASSIGN, N_XOR, N_XOR_ASSIGN,
  N_LSH, N_LSH_ASSIGN, N_RSH, N_RSH_ASSIGN, N_ADD, N_ADD_ASSIGN, N_SUB, N_SUB_ASSIGN,
  N_MUL, N_MUL_ASSIGN, N_DIV, N_DIV_ASSIGN, N_MOD, N_MOD_ASSIGN,
  N_IND, N_FIELD, N_ADDR, N_DEREF, N_DEREF_FIELD, N_COND, N_INC, N_DEC, N_POST_INC, N_POST_DEC,
  N_ALIGNOF, N_SIZEOF, N_EXPR_SIZEOF, N_CAST, N_COMPOUND_LITERAL, N_CALL,
  N_GENERIC, N_GENERIC_ASSOC,
  N_IF, N_SWITCH, N_WHILE, N_DO, N_FOR, N_GOTO, N_CONTINUE, N_BREAK, N_RETURN, N_EXPR,
  N_BLOCK, N_CASE, N_DEFAULT, N_LABEL, N_LIST, N_SPEC_DECL, N_SHARE,
  N_TYPEDEF, N_EXTERN, N_STATIC, N_AUTO, N_REGISTER, N_THREAD_LOCAL, N_DECL,
  N_VOID, N_CHAR, N_SHORT, N_INT, N_LONG, N_FLOAT, N_DOUBLE, N_SIGNED, N_UNSIGNED,
  N_BOOL, N_COMPLEX, N_STRUCT, N_UNION, N_ENUM, N_ENUM_CONST, N_MEMBER,
  N_CONST, N_RESTRICT, N_VOLATILE, N_ATOMIC, N_INLINE, N_NO_RETURN, N_ALIGNAS,
  N_FUNC, N_STAR, N_POINTER, N_DOTS, N_ARR, N_INIT, N_FIELD_ID, N_TYPE, N_ST_ASSERT, N_FUNC_DEF
} node_code_t;

DEF_DLIST_LINK (node_t);
DEF_DLIST_TYPE (node_t);

typedef struct pos {
  int lno, ln_pos;
} pos_t;

static const pos_t no_pos = {-1, -1};

struct node {
  node_code_t code;
  unsigned long uid;
  pos_t pos;
  DLIST_LINK (node_t) op_link;
  DLIST (node_t) ops;
  union {
    const char *s;
    mir_char ch;
    mir_long l;
    mir_long_long ll;
    mir_ulong ul;
    mir_ulong_long ull;
    mir_float f;
    mir_double d;
    mir_long_double ld;
    node_t scope;
  } u;
  void *attr;
};

DEF_DLIST_CODE (node_t, op_link);

static struct node err_node;

typedef struct token {
  token_code_t code;
  pos_t pos;
  node_code_t node_code;
  node_t node;
} token_t;

static void op_append (node_t n, node_t op) {
  DLIST_APPEND (node_t, n->ops, op);
  if (n->pos.lno < 0) n->pos = op->pos;
}

static void op_flat_append (node_t n, node_t op) {
  node_t el, next_el;
  
  if (op->code != N_LIST) {
    op_append (n, op);
    return;
  }
  for (el = DLIST_HEAD (node_t, op->ops); el != NULL; el = next_el) {
    next_el = DLIST_NEXT (node_t, el);
    DLIST_REMOVE (node_t, op->ops, el);
    op_append (n, el);
  }
}

static unsigned long curr_uid;

static node_t new_node (node_code_t node_code) {
  node_t n = reg_malloc (sizeof (struct node));

  n->code = node_code;
  n->uid = curr_uid++;
  DLIST_INIT (node_t, n->ops);
  n->attr = NULL;
  n->pos = no_pos;
  return n;
}

static node_t add_pos (node_t n, pos_t pos) { if (n->pos.lno < 0) n->pos = pos; return n; }

static node_t new_pos_node (node_code_t node_code, pos_t pos) {
  return add_pos (new_node (node_code), pos);
}

static node_t new_node1 (node_code_t node_code, node_t op1) {
  node_t r = new_node (node_code);
  op_append (r, op1); r->pos = op1->pos; return r;
}

static node_t new_pos_node1 (node_code_t node_code, pos_t pos, node_t op1) {
  return add_pos (new_node1 (node_code, op1), pos);
}

static node_t new_node2 (node_code_t node_code, node_t op1, node_t op2) {
  node_t r = new_node1 (node_code, op1);
  op_append (r, op2);
  if (r->pos.lno < 0) r->pos = op2->pos;
  return r;
}

static node_t new_pos_node2 (node_code_t node_code, pos_t pos, node_t op1, node_t op2) {
  return add_pos (new_node2 (node_code, op1, op2), pos);
}

static node_t new_node3 (node_code_t node_code, node_t op1, node_t op2, node_t op3) {
  node_t r = new_node2 (node_code, op1, op2);
  op_append (r, op3);
  if (r->pos.lno < 0) r->pos = op3->pos;
  return r;
}

static node_t new_pos_node3 (node_code_t node_code, pos_t pos, node_t op1, node_t op2, node_t op3) {
  return add_pos (new_node3 (node_code, op1, op2, op3), pos);
}

static node_t new_node4 (node_code_t node_code, node_t op1, node_t op2, node_t op3, node_t op4) {
  node_t r = new_node3 (node_code, op1, op2, op3);
  op_append (r, op4);
  if (r->pos.lno < 0) r->pos = op4->pos;
  return r;
}

static node_t new_pos_node4 (node_code_t node_code, pos_t pos, node_t op1, node_t op2, node_t op3, node_t op4) {
  return add_pos (new_node4 (node_code, op1, op2, op3, op4), pos);
}

static node_t new_str_node (node_code_t node_code, pos_t pos, const char *s) {
  node_t n = new_pos_node (node_code, pos); n->u.s = s; return n;
}

static node_t new_ch_node (int ch, pos_t pos) { node_t n = new_pos_node (N_CH, pos); n->u.ch = ch; return n; }
static node_t new_f_node (float f, pos_t pos) { node_t n = new_pos_node (N_F, pos); n->u.f = f; return n; }
static node_t new_d_node (double d, pos_t pos) { node_t n = new_pos_node (N_D, pos); n->u.d = d; return n; }
static node_t new_ld_node (long double ld, pos_t pos) { node_t n = new_pos_node (N_LD, pos); n->u.ld = ld; return n; }
static node_t new_i_node (long l, pos_t pos) { node_t n = new_pos_node (N_I, pos); n->u.l = l; return n; }
static node_t new_l_node (long l, pos_t pos) { node_t n = new_pos_node (N_L, pos); n->u.l = l; return n; }
static node_t new_ll_node (long long ll, pos_t pos) { node_t n = new_pos_node (N_LL, pos); n->u.ll = ll; return n; }
static node_t new_u_node (unsigned long ul, pos_t pos) { node_t n = new_pos_node (N_U, pos); n->u.ul = ul; return n; }
static node_t new_ul_node (unsigned long ul, pos_t pos) {
  node_t n = new_pos_node (N_UL, pos); n->u.ul = ul; return n;
}
static node_t new_ull_node (unsigned long long ull, pos_t pos) {
  node_t n = new_pos_node (N_ULL, pos); n->u.ull = ull; return n;
}

static node_t get_op (node_t n, int nop) {
  n = DLIST_HEAD (node_t, n->ops);
  for (; nop > 0; nop--)
    n = DLIST_NEXT (node_t, n);
  return n;
}

static pos_t curr_pos;
static token_t curr_token, prev_token;

static void setup_curr_token (pos_t pos, int token_code, node_code_t node_code) {
  curr_token.pos = pos; curr_token.code = token_code;
  curr_token.node_code = node_code; curr_token.node = NULL;
}

static void setup_curr_node_token (pos_t pos, int token_code, node_t node) {
  curr_token.pos = pos; curr_token.code = token_code;
  curr_token.node_code = N_IGNORE; curr_token.node = node;
}

static int (*c_getc) (void);
static void (*c_ungetc) (int c);
#define TAB_STOP 8

static int p_getc (void) {
  curr_pos.ln_pos++; return c_getc ();
}

static void p_ungetc (int c) {
  curr_pos.ln_pos--; c_ungetc (c);
}

static int read_str_code (int curr_c, int *newln_p, int *wrong_escape_p) {
  int ch, i, c;

  /* `current_position' corresponds position at the read char here. */
  if (curr_c == EOF || curr_c == '\n') {
    p_ungetc (curr_c); return (-1);
  }
  *newln_p = *wrong_escape_p = FALSE;
  if (curr_c == '\\') {
    curr_c = p_getc ();
    switch (curr_c) {
    case 'a': curr_c = '\a'; break;
    case 'b': curr_c = '\b'; break;
    case 'n': curr_c = '\n'; break;
    case 'f': curr_c = '\f'; break;
    case 'r': curr_c = '\r'; break;
    case 't': curr_c = '\t'; break;
    case 'v': curr_c = '\v'; break;
    case '\\': case '\'': case '\?': case '\"': break;
    case '\n': curr_pos.ln_pos = 0; curr_pos.lno++; *newln_p = TRUE; break;
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': {
      ch = curr_c - '0'; curr_c = p_getc ();
      if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9')
	p_ungetc (curr_c);
      else {
	 ch = (ch * 8 + curr_c - '0'); curr_c = p_getc ();
	 if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9') {
	   p_ungetc (curr_c);
	 } else {
	   ch = (ch * 8 + curr_c - '0');
	 }
      }
      curr_c = ch;
      break;
    }
    case 'x': case 'X': {
      ch = 0; curr_c = p_getc ();
      for (ch = i = 0; isxdigit (curr_c); i++) {
	c = isdigit (curr_c) ? curr_c - '0' : islower (curr_c) ? curr_c - 'a' + 10 : curr_c - 'A' + 10;
	ch = (ch << 4) | c; curr_c = p_getc ();
      }
      p_ungetc (curr_c); curr_c = ch; *wrong_escape_p = i == 0;
    }
    default: *wrong_escape_p = TRUE; break;
    }
  }
  return curr_c;
}

DEF_VARR (char);
static VARR (char) *symbol_text;

static void get_next_token (void) {
  int start_c, curr_c, error_chars_num = 0;
  pos_t pos;
  
  VARR_TRUNC (char, symbol_text, 0);
  for (;;) {
    curr_c = p_getc ();
    switch (start_c = curr_c) {
    case ' ': case '\f':
      break;
    case '\t':
      curr_pos.ln_pos = ((curr_pos.ln_pos - 1) / TAB_STOP + 1) * TAB_STOP; break;
    case '\n':
      curr_pos.ln_pos = 0; curr_pos.lno++; break;
    case '\r':
      break;
    case '~':
      setup_curr_token (curr_pos, T_UNOP, N_BITWISE_NOT); return;
    case '+': case '-':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == start_c) {
	setup_curr_token (pos, T_INCDEC, start_c == '+' ? N_INC : N_DEC);
      } else if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, start_c == '+' ? N_ADD_ASSIGN : N_SUB_ASSIGN);
      } else if (start_c == '-' && curr_c == '>') {
	setup_curr_token (pos, T_ARROW, N_DEREF_FIELD);
      } else if (isdigit (curr_c)) {
	p_ungetc (curr_c); curr_c = start_c;
	goto number;
      } else if (curr_c == '.') {
	curr_c = p_getc ();
	if (isdigit (curr_c)){
	  p_ungetc (curr_c); p_ungetc ('.'); curr_c = start_c;
	  goto number;
	} else {
	  p_ungetc (curr_c); p_ungetc ('.');
	  setup_curr_token (pos, T_ADDOP, start_c == '+' ? N_ADD : N_SUB);
	}
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, T_ADDOP, start_c == '+' ? N_ADD : N_SUB);
      }
      return;
    case '=':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_EQNE, N_EQ);
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, '=', N_ASSIGN);
      }
      return;
    case '<': case '>':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == start_c) {
	curr_c = p_getc (); 
	if (curr_c == '=') {
	  setup_curr_token (pos, T_ASSIGN, start_c == '<' ? N_LSH_ASSIGN : N_RSH_ASSIGN);
	} else {
	  p_ungetc (curr_c); setup_curr_token (pos, T_SH, start_c == '<' ? N_LSH : N_RSH);
	}
      } else if (curr_c == '=') {
	setup_curr_token (pos, T_CMP, start_c == '<' ? N_LE : N_GE);
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, T_CMP, start_c == '<' ? N_LT : N_GT);
      }
      return;
    case '*':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_MUL_ASSIGN);
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, '*', N_MUL);
      }
      return;
    case '/':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_DIV_ASSIGN);
      } else if (curr_c == '/') { /* comment // */
	while ((curr_c = p_getc ()) != '\n' && curr_c != EOF)
	  ;
	curr_pos.ln_pos = 0; curr_pos.lno++; break;      
      } else if (curr_c == '*') { /* usual C comment */
	for (;;) {
	  if ((curr_c = p_getc ()) == EOF)
	    error_func (C_unfinished_comment, "unfinished comment");
	  if (curr_c == '*') {
	    if ((curr_c = p_getc ()) == '/') {
	      break;
	    } else {
	      p_ungetc (curr_c);
	    }
	  }
	}
	break;
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, '*', N_MUL);
      }
      return;
    case '%':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_MOD_ASSIGN);
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, T_DIVOP, N_MOD);
      }
      return;
    case '&': case '|':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, start_c == '&' ? N_AND_ASSIGN : N_OR_ASSIGN);
      } else if (curr_c == start_c) {
	setup_curr_token (pos, start_c == '&' ? T_ANDAND : T_OROR, start_c == '&' ? N_ANDAND : N_OROR);
      } else {
	p_ungetc (curr_c); setup_curr_token (pos, start_c, start_c == '&' ? N_AND : N_OR);
      }
      return;
    case '^': case '!':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, start_c == '^' ? T_ASSIGN : T_EQNE, start_c == '^' ? N_XOR_ASSIGN : N_NE);
      } else {
	p_ungetc (curr_c);
	setup_curr_token (pos, start_c == '^' ? '^' : T_UNOP, start_c == '^' ? N_XOR : N_NOT);
      }
      return;
    case ';': case '?': case ':': case '(': case ')': case '{': case '}': case ']': case EOF:
      setup_curr_token (curr_pos, curr_c, N_IGNORE); return;
    case ',':
      setup_curr_token (curr_pos, ',', N_COMMA); return;
    case '[':
      setup_curr_token (curr_pos, '[', N_IND); return;
    case '.':
      pos = curr_pos; curr_c = p_getc ();
      if (curr_c == '.') {
	curr_c = p_getc ();
	if (curr_c == '.') {
	  setup_curr_token (pos, T_DOTS, N_IGNORE);
	} else {
	  p_ungetc (curr_c); p_ungetc ('.'); setup_curr_token (pos, '.', N_FIELD);
	}
	return;
      } else if (! isdigit (curr_c)) {
	p_ungetc (curr_c); setup_curr_token (pos, '.', N_FIELD);
	return;
      }
      p_ungetc (curr_c); curr_c = '.';
    number:
      /* Fall through: */
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
      int base = 10, err_p = FALSE, float_p = FALSE, double_p = FALSE, long_double_p = FALSE;
      int uns_p = FALSE, long_p = FALSE, long_long_p = FALSE, dec_p = FALSE, hex_p = FALSE, hex_char_p;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0);
      if (curr_c == '+' || curr_c == '-') {
	VARR_PUSH (char, symbol_text, curr_c); curr_c = p_getc ();
      }
      if (curr_c == '.' && VARR_LENGTH (char, symbol_text) == 0) {
	VARR_PUSH (char, symbol_text, '0');
      }
      if (curr_c == '0') {
	curr_c = p_getc ();
	if (curr_c != 'x' && curr_c != 'X') {
	base = 8; p_ungetc (curr_c); curr_c = '0';
	} else {
	  VARR_PUSH (char, symbol_text, '0'); VARR_PUSH (char, symbol_text, 'x');
	  curr_c = p_getc (); base = 16;
	}
      }
      for (;;) {
	VARR_PUSH (char, symbol_text, curr_c);
	curr_c = p_getc ();
	if (curr_c == '8' || curr_c == '9')
	  dec_p = TRUE;
	hex_char_p = isxdigit (curr_c);
	if (! isdigit (curr_c) && (base != 16 || ! hex_char_p))
	  break;
	if (hex_char_p && ! isdigit (curr_c))
	  hex_p = TRUE;
      }
      assert (base == 16 || ! hex_p);
      if (curr_c == '.') {
	double_p = TRUE;
	do {
	  VARR_PUSH (char, symbol_text, curr_c); curr_c = p_getc ();
	} while (isdigit (curr_c));
      }
      if ((base != 16 && (curr_c == 'e' || curr_c == 'E'))
	  || (base == 16 && (curr_c == 'p' || curr_c == 'P'))) {
	double_p = TRUE; curr_c = p_getc ();
	if (curr_c != '+' && curr_c != '-' && ! isdigit (curr_c)) {
	  error_func (C_absent_exponent, "absent exponent"); err_p = TRUE;
	} else {
	  VARR_PUSH (char, symbol_text, base == 16 ? 'p' : 'e');
	  if (curr_c == '+' || curr_c == '-') {
	    VARR_PUSH (char, symbol_text, curr_c); curr_c = p_getc ();
	    if (! isdigit (curr_c)) {
	      error_func (C_absent_exponent, "absent exponent"); err_p = TRUE;
	    }
	  }
	  if (! err_p) {
	    do {
	      VARR_PUSH (char, symbol_text, curr_c); curr_c = p_getc ();
	    } while (isdigit (curr_c));
	  }
	}
      } else if (! double_p && (curr_c == 'l' || curr_c == 'L')) {
	long_p = TRUE; curr_c = p_getc ();
      }
      if (double_p) {
	if (curr_c == 'f' || curr_c == 'F') {
	  double_p = FALSE; float_p = TRUE; curr_c = p_getc ();
	} else if (curr_c == 'l' || curr_c == 'L') {
	  double_p = FALSE; long_double_p = TRUE; curr_c = p_getc ();
	}
      } else {
	int c2 = p_getc (), c3 = p_getc ();
	
	if ((curr_c == 'u' || curr_c == 'U') && (c2 == 'l' || c2 == 'L')  && (c3 == 'l' || c3 == 'L')
	    || (curr_c == 'l' || curr_c == 'L') && (c2 == 'l' || c2 == 'L')  && (c3 == 'u' || c3 == 'u')) {
	  uns_p = long_long_p = TRUE; curr_c = p_getc ();
	} else if ((curr_c == 'u' || curr_c == 'U') && (c2 == 'l' || c2 == 'L')
		   || (curr_c == 'l' || curr_c == 'L') && (c2 == 'u' || c2 == 'u')) {
	  uns_p = long_p = TRUE; curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L') && (c2 == 'l' || c2 == 'L')) {
	  long_p = TRUE; curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L')) {
	  long_p = TRUE; p_ungetc (c3); curr_c = c2;
	} else if ((curr_c == 'u' || curr_c == 'U')) {
	  uns_p = TRUE; p_ungetc (c3); curr_c = c2;
	} else {
	  p_ungetc (c3); p_ungetc (c2);
	}
      }
      VARR_PUSH (char, symbol_text, '\0');
      p_ungetc (curr_c);
      if (err_p)
	return;
      errno = 0;
      if (float_p) {
	float f = strtof (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_f_node (f, pos));
      } else if (double_p) {
	double d = strtod (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_d_node (d, pos));
      } else if (long_double_p) {
	long double ld = strtod (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_ld_node (ld, pos));
      } else if (base == 8 && dec_p) {
	error_func (C_wrong_octal_int, "wrong octal integer"); err_p = TRUE;
      } else if (uns_p) {
	if (long_long_p) {
	  unsigned long long ull = strtoul (VARR_ADDR (char, symbol_text), NULL, base);
	  setup_curr_node_token (pos, T_CONSTANT, new_ull_node (ull, pos));
	} else {
	  unsigned long ul = strtoul (VARR_ADDR (char, symbol_text), NULL, base);
	  setup_curr_node_token (pos, T_CONSTANT, new_ul_node (ul, pos));  /* ??? unsigned int */
	}
      } else if (long_long_p) {
	long long ll = strtoll (VARR_ADDR (char, symbol_text), NULL, base);
	setup_curr_node_token (pos, T_CONSTANT, new_ll_node (ll, pos));
      } else {
	long l = strtol (VARR_ADDR (char, symbol_text), NULL, base);
	setup_curr_node_token (pos, T_CONSTANT, new_l_node (l, pos)); /* ??? int */
      }
      if (errno) {
	error_func (C_out_of_range_number, "number is out of range"); err_p = TRUE;
      }
      return;
    }
    case '\'': { /* ??? unicode and wchar */
      int ch, newln_p, wrong_escape_p, err_p = FALSE;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0); curr_c = p_getc ();
      if (curr_c == '\'') {
	error_func (C_invalid_char_constant, "empty character"); err_p = TRUE;
      } else {
	ch = read_str_code (curr_c, &newln_p, &wrong_escape_p);
	if (ch < 0 || newln_p) {
	  error_func (C_invalid_char_constant, "invalid character"); err_p = TRUE;
	} else if (wrong_escape_p) {
	  error_func (C_invalid_char_constant, "invalid escape sequence"); err_p = TRUE;
	}
      }
      curr_c = p_getc ();
      if (curr_c != '\'') {
	p_ungetc (curr_c);
	error_func (C_invalid_char_constant, "more one character in char"); err_p = TRUE;
      }
      setup_curr_node_token (pos, T_CONSTANT, new_ch_node (ch, pos));
      return;
    }
    case '\"': { /* ??? unicode and wchar */
      int ch, newln_p, wrong_escape_p, err_p = FALSE;
      str_t str;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0);
      for (;;) {
	curr_c = p_getc ();
	if (curr_c == '\"')
	  break;
	ch = read_str_code (curr_c, &newln_p, &wrong_escape_p);
	if (ch < 0) {
	  error_func (C_no_string_end, "no string end"); err_p = TRUE; break;
	}
	if (wrong_escape_p) {
	  error_func (C_invalid_str_constant, "invalid escape sequence"); err_p = TRUE; continue;
	}
	if (! newln_p) {
	  VARR_PUSH (char, symbol_text, ch);
	}
      }
      VARR_PUSH (char, symbol_text, '\0');
      str = str_add (VARR_ADDR (char, symbol_text), T_STR, 0, FALSE);
      setup_curr_node_token (pos, T_STR, new_str_node (N_STR, pos, str.s));
      return;
    }
    default:
      if (isalpha (curr_c) || curr_c == '_' ) {
	str_t str;
	
	pos = curr_pos;
	do {
	  VARR_PUSH (char, symbol_text, curr_c); curr_c = p_getc ();
	} while (isalnum (curr_c) || curr_c == '_');
	p_ungetc (curr_c);
	VARR_PUSH (char, symbol_text, '\0');
	str = str_add (VARR_ADDR (char, symbol_text), T_STR, 0, FALSE);
	if (str.key != T_STR) {
	  setup_curr_token (pos, str.key, N_IGNORE);
	} else {
	  setup_curr_node_token (pos, T_ID, new_str_node (N_ID, pos, str.s));
	}
	return;
      } else {
	error_chars_num++;
	if (error_chars_num == 1)
	  error_func (C_invalid_char, "invalid input character");
      }
    }
  }
}

DEF_VARR (token_t);
static VARR (token_t) *recorded_tokens, *buffered_tokens;
static int record_level;

static void read_token (void) {
  if (record_level > 0)
    VARR_PUSH (token_t, recorded_tokens, curr_token);
  prev_token = curr_token;
  if (VARR_LENGTH (token_t, buffered_tokens) == 0)
    get_next_token ();
  else
    curr_token = VARR_POP (token_t, buffered_tokens);
}

static size_t record_start (void) {
  size_t mark = VARR_LENGTH (token_t, recorded_tokens);

  assert (record_level >= 0);
  record_level++;
  return mark;
}

static void record_stop (size_t mark, int restore_p) {
  assert (record_level > 0);
  record_level--;
  if (! restore_p) {
    if (record_level == 0)
      VARR_TRUNC (token_t, recorded_tokens, mark);
    return;
  }
  VARR_PUSH (token_t, buffered_tokens, curr_token);
  while (VARR_LENGTH (token_t, recorded_tokens) > mark) {
    curr_token = VARR_POP (token_t, recorded_tokens);
    VARR_PUSH (token_t, buffered_tokens, curr_token);
  }
  curr_token = VARR_POP (token_t, buffered_tokens);
}

static const char *get_token_name (int token_code) {
  static char buf[30];
  const char *s;
  
  switch (token_code) {
  case T_CONSTANT: return "constant";
  case T_STR: return "string";
  case T_ID: return "identifier";
  case T_ASSIGN: return "assign op";
  case T_DIVOP: return "/ or %";
  case T_ADDOP: return "+ or -";
  case T_SH: return "shift op";
  case T_CMP: return "comparison op";
  case T_EQNE: return "equality op";
  case T_ANDAND: return "&&";
  case T_OROR: return "||";
  case T_INCDEC: return "++ or --";
  case T_ARROW: return "->";
  case T_UNOP: return "unary op";
  case T_DOTS: return "...";
  default:
    if ((s = find_str_by_key (token_code)) != NULL)
    return s;
    if (isprint (token_code))
      sprintf (buf, "%c", token_code);
    else
      sprintf (buf, "%d", token_code);
    return buf;
  }
}

static void print_pos (pos_t pos) { if (pos.lno >= 0) fprintf (stderr, "%d:%d: ", pos.lno, pos.ln_pos); }

static void syntax_error (const char *expected_name) {
  static int context_len = 30;
  char buf[context_len + 1];
  int i, c;
  
  print_pos (curr_token.pos);
  fprintf (stderr, "syntax error on %s", get_token_name (curr_token.code));
  fprintf (stderr, " (expected '%s'):", expected_name);
  for (i = 0; (c = c_getc ()) != EOF && c != '\n' && i < context_len; i++)
    buf[i] = c;
  buf[i] = '\0';
  c_ungetc (c);
  for (i--; i >= 0; i--)
    c_ungetc (buf[i]);
  fprintf (stderr, " `%s'\n", buf);
}

static void print_error (pos_t pos, const char *format, ...) {
  va_list args;
   
  va_start (args, format);
  print_pos (pos);
  vfprintf (stderr, format, args);
  va_end (args);
}

static node_t curr_scope;

typedef struct {
  node_t id, scope;
} tpname_t;

DEF_HTAB (tpname_t);
static HTAB (tpname_t) *tpname_tab;

static int tpname_eq (tpname_t tpname1, tpname_t tpname2) {
  return tpname1.id->u.s == tpname2.id->u.s && tpname1.scope == tpname2.scope;
}

static htab_hash_t tpname_hash (tpname_t tpname) {
  return (mum_hash_finish
	  (mum_hash_step
	   (mum_hash_step (mum_hash_init (0x42),
			   (uint64_t) tpname.id->u.s),
	    (uint64_t) tpname.scope)));
}

static void tpname_init (void) {
  HTAB_CREATE (tpname_t, tpname_tab, 1000, tpname_hash, tpname_eq);
}

static int tpname_find (node_t id, node_t scope, tpname_t *res) {
  int found_p;
  tpname_t el, tpname;
  
  tpname.id = id; tpname.scope = scope;
  found_p = HTAB_DO (tpname_t, tpname_tab, tpname, HTAB_FIND, el);
  if (res != NULL && found_p)
    *res = el;
  return found_p;
}

static tpname_t tpname_add (node_t id, node_t scope) {
  tpname_t el, tpname;
  
  tpname.id = id; tpname.scope = scope;
  if (HTAB_DO (tpname_t, tpname_tab, tpname, HTAB_FIND, el))
    return el;
  HTAB_DO (tpname_t, tpname_tab, tpname, HTAB_INSERT, el);
  return el;
}

static void tpname_finish (void) {
  HTAB_DESTROY (tpname_t, tpname_tab);
}

#define P(f) do { if ((r = (f) (no_err_p)) == &err_node) return r; } while (0)
#define PA(f, a) do { if ((r = (f) (no_err_p, a)) == &err_node) return r; } while (0)
#define PT(t) do {                              		\
    if (! M(t)) {						\
    if (record_level == 0) syntax_error (get_token_name (t));	\
    return &err_node;						\
  }								\
} while (0)

#define PTP(t, pos) do {                              		\
    if (! MP(t, pos)) {						\
    if (record_level == 0) syntax_error (get_token_name (t));	\
    return &err_node;						\
  }								\
} while (0)

#define PTN(t) do {                             		\
  if (! MN(t, r)) {						\
    if (record_level == 0) syntax_error (get_token_name (t));	\
    return &err_node;						\
  }								\
} while (0)

#define PE(f, l) do {if ((r = (f) (no_err_p)) == &err_node) goto l; } while (0)
#define PTE(t, pos, l) do {if (! MP(t, pos)) goto l; } while (0)

typedef node_t (*nonterm_func_t) (int);

#define D(f) static node_t f (int no_err_p)
#define DA(f) static node_t f (int no_err_p, node_t arg)

static int C (int c) { return curr_token.code == c; }

static int match (int c, pos_t *pos, node_code_t *node_code, node_t *node) {
  if (curr_token.code != c)
    return FALSE;
  if (pos != NULL)
    *pos = curr_token.pos;
  if (node_code != NULL)
    *node_code = curr_token.node_code;
  if (node != NULL)
    *node = curr_token.node;
  read_token ();
  return TRUE;
}

#define M(c) match (c, NULL, NULL, NULL)
#define MP(c, pos) match (c, &(pos), NULL, NULL)
#define MC(c, pos, code) match (c, &(pos), &(code), NULL)
#define MN(c, node) match (c, NULL, NULL, &(node))

static node_t try (nonterm_func_t f) {
  node_t r;
  size_t mark;
  
  mark = record_start ();
  r = (f) (TRUE);
  record_stop (mark, r == &err_node);
  return r;
}

#define TRY(f) try (f)

/* Expressions: */
D (type_name); D (expr); D (assign_expr); D (initializer_list);

D (par_type_name) {
  node_t r;

  PT ('('); P (type_name); PT (')');
  return r;
}

D (primary_expr) {
  node_t r, n, op, gn, list;
  pos_t pos;
  
  if (MN (T_ID, r) || MN (T_CONSTANT, r) || MN (T_STR, r)) {
    return r;
  } else if (M ('(')) {
    P (expr);
    if (M (')')) return r;
  } else if (MP (T_GENERIC, pos)) {
    PT ('('); P (assign_expr); PT (',');
    list = new_node (N_LIST);
    n = new_pos_node2 (N_GENERIC, pos, r, list);
    for (;;) { /* generic-assoc-list , generic-association */
      if (MP (T_DEFAULT, pos)) {
	op = new_node (N_IGNORE);
      } else {
	P (type_name); op = r; pos = op->pos;
      }
      PT (':'); P (assign_expr);
      gn = new_pos_node2 (N_GENERIC_ASSOC, pos, op, r);
      op_append (list, gn);
      if (! M (','))
	break;
    }
    PT (')');
    return n;
  }
  return &err_node;
}

DA (post_expr_part) {
  node_t r, n, op, list;
  node_code_t code;
  pos_t pos;
  
  r = arg;
  for (;;) {
    if (MC (T_INCDEC, pos, code)) {
      code = code == N_INC ? N_POST_INC : N_POST_DEC;
      op = r; r = NULL;
    } else if (MC ('.', pos, code) || MC (T_ARROW, pos, code)) {
      op = r;
      if (! MN (T_ID, r))
	return &err_node;
    } else if (MC ('[', pos, code)) {
      op = r; P (expr); PT (']');
    } else if (MP ('(', pos)) {
      op = r; r = NULL; code = N_CALL; list = new_node (N_LIST);
      if (! C (')')) {
	for (;;) {
	  P (assign_expr); op_append (list, r);
	  if ( ! M (','))
	    break;
	}
      }
      r = list;
      PT (')');
    } else break;
    n = new_pos_node1 (code, pos, op);
    if (r != NULL)
      op_append (n, r);
    r = n;
  }
  return r;
}

D (post_expr) {
  node_t r, n, op, list;
  node_code_t code;
  pos_t pos;
  
  P (primary_expr); PA (post_expr_part, r);
  return r;
}

D (unary_expr) {
  node_t r, t;
  node_code_t code;
  pos_t pos;
  
  if ((r = TRY (par_type_name)) != &err_node) {
    t = r;
    if (! MP ('{', pos)) {
      P (unary_expr); r = new_node2 (N_CAST, t, r);
    } else {
      P (initializer_list);
      if (! M ('}')) return &err_node;
      r = new_pos_node2 (N_COMPOUND_LITERAL, pos, t, r);
      PA (post_expr_part, r);
    }
    return r;
  } else if (MP (T_SIZEOF, pos)) {
    if ((r = TRY (par_type_name)) != &err_node) {
      r = new_pos_node1 (N_SIZEOF, pos, r); return r;
    }
    code = N_EXPR_SIZEOF;
  } else if (MP (T_ALIGNOF, pos)) {
    if ((r = TRY (par_type_name)) != &err_node) {
      r = new_pos_node1 (N_ALIGNOF, pos, r);
    } else {
      P (unary_expr); /* error recovery */
      r = new_pos_node1 (N_ALIGNOF, pos, new_node (N_IGNORE));
    }
    return r;
  } else if (! MC (T_INCDEC, pos, code) && ! MC (T_UNOP, pos, code) && ! MC (T_ADDOP, pos, code)
	     && ! MC ('*', pos, code)  && ! MC ('&', pos, code)) {
    P (post_expr); return r;
  } else if (code == N_AND) {
    code = N_ADDR;
  } else if (code == N_MUL) {
    code = N_DEREF;
  }
  P (unary_expr); r = new_pos_node1 (code, pos, r); return r;
}

static node_t left_op (int no_err_p, int token, int token2, nonterm_func_t f) {
  node_code_t code;
  node_t r, n;
  pos_t pos;
  
  P (f);
  while (MC (token, pos, code) || (token2 >= 0 && MC (token2, pos, code))) {
    n = new_pos_node1 (code, pos, r);
    P (f); op_append (n, r); r = n;
  }
  return r;
}

static node_t right_op (int no_err_p, int token, int token2, nonterm_func_t left, nonterm_func_t right) {
  node_code_t code;
  node_t r, n;
  pos_t pos;
  
  P (left);
  if (MC (token, pos, code) || (token2 >= 0 && MC (token2, pos, code))) {
    n = new_pos_node1 (code, pos, r); P (right); op_append (n, r); r = n;
  }
  return r;
}

D (mul_expr) { return left_op (no_err_p, T_DIVOP, '*', unary_expr); }
D (add_expr) { return left_op (no_err_p, T_ADDOP, -1, mul_expr); }
D (sh_expr) { return left_op (no_err_p, T_SH, -1, add_expr); }
D (rel_expr) { return left_op (no_err_p, T_CMP, -1, sh_expr); }
D (eq_expr) { return left_op (no_err_p, T_EQNE, -1, rel_expr); }
D (and_expr) { return left_op (no_err_p, '&', -1, eq_expr); }
D (xor_expr) { return left_op (no_err_p, '^', -1, and_expr); }
D (or_expr) { return left_op (no_err_p, '|', -1, xor_expr); }
D (land_expr) { return left_op (no_err_p, T_ANDAND, -1, or_expr); }
D (lor_expr) { return left_op (no_err_p, T_OROR, -1, land_expr); }

D (cond_expr) {
  node_t r, n, pn;
  pos_t pos;
  
  P (lor_expr);
  if (! MP ('?', pos)) return r;
  n = new_pos_node1 (N_COND, pos, r);
  P (expr); op_append (n, r);
  if (! M (':')) return &err_node;
  P (cond_expr); op_append (n, r);
  return n;
}

#define const_expr cond_expr

D (assign_expr) { return right_op (no_err_p, T_ASSIGN, '=', cond_expr, assign_expr); }
D (expr) { return right_op (no_err_p, ',', -1, assign_expr, expr); }

/* Declarations; */
D (declaration_specs); D (sc_spec); D (type_spec); D (struct_declaration_list); D (struct_declaration);
D (spec_qual_list); D (type_qual); D (func_spec); D (align_spec); D (declarator); D (direct_declarator);
D (pointer); D (type_qual_list); D (param_type_list); D (id_list); D (abstract_declarator);
D (direct_abstract_declarator); D (typedef_name); D (initializer);
D (st_assert);

D (declaration) {
  int typedef_p;
  node_t op, list, decl, spec, r;
  
  if (C (T_STATIC_ASSERT)) {
    P (st_assert);
  } else {
    P (declaration_specs); spec = r; list = new_node (N_LIST);
    if (C (';')) {
      op_append (list, new_node3 (N_SPEC_DECL, spec, new_node (N_IGNORE), new_node (N_IGNORE)));
    } else { /* init-declarator-list */
      for (op = DLIST_HEAD (node_t, spec->ops); op != NULL; op = DLIST_NEXT (node_t, op))
	if (op->code == N_TYPEDEF)
	  break;
      typedef_p = op != NULL;
      for (;;) { /* init-declarator */
	P (declarator); decl = r; assert (decl->code == N_DECL);
	if (typedef_p) {
	  op = DLIST_HEAD (node_t, decl->ops); tpname_add (op, curr_scope);
	}
	if (M ('=')) {
	  P (initializer);
	} else {
	  r = new_node (N_IGNORE);
	}
	op_append (list, new_pos_node3 (N_SPEC_DECL, decl->pos, new_node1 (N_SHARE, spec), decl, r));
	if ( ! M (','))
	  break;
      }
    }
    r = list; PT (';');
  }
  return r;
}

D (declaration_specs) {
  node_t list, r;
  int first_p;
  
  list = new_node (N_LIST);
  for (first_p = TRUE;; first_p = FALSE) {
    if (C (T_ALIGNAS)) {
      P (align_spec);
    } else if ((r = TRY (sc_spec)) != &err_node) {
    } else if ((r = TRY (type_qual)) != &err_node) {
    } else if ((r = TRY (func_spec)) != &err_node) {
    } else if (first_p) {
      P (type_spec);
    } else if ((r = TRY (type_spec)) != &err_node) {
    } else break;
    op_append (list, r);
  }
  return list;
}

D (sc_spec) {
  node_t r;
  pos_t pos;
  
  if (MP (T_TYPEDEF, pos)) {
    r = new_pos_node (N_TYPEDEF, pos);
  } else if (MP (T_EXTERN, pos)) {
    r = new_pos_node (N_EXTERN, pos);
  } else if (MP (T_STATIC, pos)) {
    r = new_pos_node (N_STATIC, pos);
  } else if (MP (T_AUTO, pos)) {
    r = new_pos_node (N_AUTO, pos);
  } else if (MP (T_REGISTER, pos)) {
    r = new_pos_node (N_REGISTER, pos);
  } else if (MP (T_THREAD_LOCAL, pos)) {
    r = new_pos_node (N_THREAD_LOCAL, pos);
  } else {
    if (record_level == 0) syntax_error ("a storage specifier");
    return &err_node;
  }
  return r;
}

D (type_spec) {
  node_t op1, op2, op3, op4, r;
  int struct_p, id_p = FALSE;
  pos_t pos;
  
  if (MP (T_VOID, pos)) {
    r = new_pos_node (N_VOID, pos);
  } else if (MP (T_CHAR, pos)) {
    r = new_pos_node (N_CHAR, pos);
  } else if (MP (T_SHORT, pos)) {
    r = new_pos_node (N_SHORT, pos);
  } else if (MP (T_INT, pos)) {
    r = new_pos_node (N_INT, pos);
  } else if (MP (T_LONG, pos)) {
    r = new_pos_node (N_LONG, pos);
  } else if (MP (T_FLOAT, pos)) {
    r = new_pos_node (N_FLOAT, pos);
  } else if (MP (T_DOUBLE, pos)) {
    r = new_pos_node (N_DOUBLE, pos);
  } else if (MP (T_SIGNED, pos)) {
    r = new_pos_node (N_SIGNED, pos);
  } else if (MP (T_UNSIGNED, pos)) {
    r = new_pos_node (N_UNSIGNED, pos);
  } else if (MP (T_BOOL, pos)) {
    r = new_pos_node (N_BOOL, pos);
  } else if (MP (T_COMPLEX, pos)) {
    r = new_pos_node (N_COMPLEX, pos);
  } else if (MP (T_ATOMIC, pos)) { /* atomic-type-specifier */
    PT ('('); P (type_name); PT (')');
    print_error (pos, "Atomic types are not supported\n"); 
  } else if ((struct_p = MP (T_STRUCT, pos)) || MP (T_UNION, pos)) { /* struct-or-union-specifier, struct-or-union */
    if (! MN (T_ID, op1)) {
      op1 = new_node (N_IGNORE);
    } else {
      id_p = TRUE;
    }
    if (M ('{')) {
      P (struct_declaration_list); PT ('}');
    } else if (! id_p) {
      return &err_node;
    } else {
      r = new_node (N_IGNORE);
    }
    r = new_pos_node2 (struct_p ? N_STRUCT : N_UNION, pos, op1, r);
  } else if (MP (T_ENUM, pos)) { /* enum-specifier */
    if (! MN (T_ID, op1)) {
      op1 = new_node (N_IGNORE);
    } else {
      id_p = TRUE;
    }
    op2 = new_node (N_LIST);
    if (M ('{')) { /* enumerator-list */
      for (;;) { /* enumerator */
	PTN (T_ID); op3 = r; /* enumeration-constant */
	if (! M ('=')) {
	  op4 = new_node (N_IGNORE);
	} else {
	  P (const_expr); op4 = r;
	}
	op_append (op2, new_node2 (N_ENUM_CONST, op3, op4));
	if (! M (','))
	  break;
      }
      PT ('}');
    } else if (! id_p) {
      return &err_node;
    } else {
      op2 = new_node (N_IGNORE);
    }
    r = new_pos_node2 (N_ENUM, pos, op1, op2);
  } else {
    P (typedef_name);
  }
  return r;
}

D (struct_declaration_list) {
  node_t r, res, el, next_el;
  
  res = new_node (N_LIST);
  for (;;) {
    P (struct_declaration);
    if (r->code != N_LIST) {
      op_append (res, r);
    } else {
      for (el = DLIST_HEAD (node_t, r->ops); el != NULL; el = next_el) {
	next_el = DLIST_NEXT (node_t, el);
	DLIST_REMOVE (node_t, r->ops, el);
	op_append (res, el);
      }
    }
    if (C ('}')) break;
  }
  return res;
}

D (struct_declaration) {
  node_t list, spec, op, r;
  
  if (C (T_STATIC_ASSERT)) {
    P (st_assert);
  } else {
    P (spec_qual_list); spec = r; list = new_node (N_LIST);
    if (! M (';')) { /* struct-declarator-list */
      for (;;) { /* struct-declarator */
	if (! C (':')) {
	  P (declarator); op = r;
	} else {
	  op = new_node (N_IGNORE);
	}
	if (M (':')) {
	  P (const_expr);
	} else {
	  r = new_node (N_IGNORE);
	}
	op = new_pos_node3 (N_MEMBER, op->pos, spec, op, r);
	op_append (list, op);
	if (! M (','))
	  break;
      }
      PT (';');
    }
    r = list;
  }
  return r;
}

D (spec_qual_list) {
  node_t list, op, r;
  int first_p;
  
  list = new_node (N_LIST);
  for (first_p = TRUE;; first_p = FALSE) {
    if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
      P (type_qual); op = r;
    } else if ((op = TRY (type_spec)) != &err_node) {
    } else if (first_p) {
      return &err_node;
    } else {
      break;
    }
    op_append (list, op);
  }
  return list;
}

D (type_qual) {
  node_t r;
  pos_t pos;
  
  if (MP (T_CONST, pos)) {
    r = new_pos_node (N_CONST, pos);
  } else if (MP (T_RESTRICT, pos)) {
    r = new_pos_node (N_RESTRICT, pos);
  } else if (MP (T_VOLATILE, pos)) {
    r = new_pos_node (N_VOLATILE, pos);
  } else if (MP (T_ATOMIC, pos)) {
    r = new_pos_node (N_ATOMIC, pos);
  } else {
    if (record_level == 0) syntax_error ("a type qualifier");
    r = &err_node;
  }
  return r;
}

D (func_spec) {
  node_t r;
  pos_t pos;
  
  if (MP (T_INLINE, pos)) {
    r = new_pos_node (N_INLINE, pos);
  } else if (MP (T_NO_RETURN, pos)) {
    r = new_pos_node (N_NO_RETURN, pos);
  } else {
    if (record_level == 0) syntax_error ("a function specifier");
    r = &err_node;
  }
  return r;
}

D (align_spec) {
  node_t r;
  pos_t pos;
  
  PTP (T_ALIGNAS, pos); PT ('(');
  if ((r = TRY (type_name)) != &err_node) {
  } else {
    P (const_expr);
  }
  PT (')'); r = new_pos_node1 (N_ALIGNAS, pos, r);
  return r;
}

D (declarator) {
  node_t list, p = NULL, r, el, next_el;
  
  if (C ('*')) {
    P (pointer); p = r;
  }
  P (direct_declarator);
  if (p != NULL) {
    list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, r->ops));
    assert (list->code == N_LIST);
    for (el = DLIST_HEAD (node_t, p->ops); el != NULL; el = next_el) {
      next_el = DLIST_NEXT (node_t, el);
      DLIST_REMOVE (node_t, p->ops, el);
      op_append (list, el);
    }
  }
  return r;
}

D (direct_declarator) {
  node_t list, tql, ae, res, r;
  pos_t pos, static_pos;
  
  if (MN (T_ID, r)) {
    res = new_node2 (N_DECL, r, new_node (N_LIST));
  } else if (M ('(')) {
    P (declarator); res = r; PT (')');
  } else {
    return &err_node;
  }
  list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, res->ops));
  assert (list->code == N_LIST);
  for (;;) {
    if (MP ('(', pos)) {
      if ((r = TRY (param_type_list)) != &err_node) {
      } else {
	P (id_list);
      }
      PT (')'); op_append (list, new_pos_node1 (N_FUNC, pos, r));
    } else if (M ('[')) {
      int static_p = FALSE;
      
      if (MP (T_STATIC, static_pos)) {
	static_p = TRUE;
      }
      if (! C (T_CONST) && !C (T_RESTRICT) && !C (T_VOLATILE) && !C (T_ATOMIC)) {
	tql = new_node (N_LIST);
      } else {
	P (type_qual_list); tql = r;
	if (! static_p && M (T_STATIC)) {
	  static_p = TRUE;
	}	
      }
      if (static_p) {
	P (assign_expr); ae = r;
      } else if (MP ('*', pos)) {
	ae = new_pos_node (N_STAR, pos);
      } else if (! C (']')) {
	P (assign_expr); ae = r;
      } else {
	ae = new_node (N_IGNORE);
      }
      PT (']'); op_append (list, new_node3 (N_ARR,
					    static_p ? new_pos_node (N_STATIC, static_pos)
					    : new_node (N_IGNORE),
					    tql, ae));
    } else break;
  }
  return res;
}

D (pointer) {
  node_t op, r;
  pos_t pos;
  
  PTP ('*', pos);
  if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
    P (type_qual_list);
  } else {
    r = new_node (N_LIST);
  }
  op = new_pos_node1 (N_POINTER, pos, r);
  if (C ('*')) {
    P (pointer);
  } else {
    r = new_node (N_LIST); 
  }
  op_append (r, op);
  return r;
}

D (type_qual_list) {
  node_t list, r;
  
  list = new_node (N_LIST);
  for (;;) {
    P (type_qual); op_append (list, r);
    if (! C (T_CONST) && ! C (T_RESTRICT) && ! C (T_VOLATILE) && ! C (T_ATOMIC))
      break;
  }
  return list;
}

D (param_type_list) {
  node_t list, op1, op2, r = &err_node;
  int comma_p;
  pos_t pos;
  
  list = new_node (N_LIST);
  for (;;) { /* parameter-list, parameter-declaration */
    P (declaration_specs); op1 = r;
    if ((op2 = TRY (declarator)) != &err_node) {
      r = new_pos_node3 (N_SPEC_DECL, op2->pos, op1, op2, new_node (N_IGNORE));
    } else if (! C (',') && ! C (')')) {
      P (abstract_declarator);
      r = new_node2 (N_TYPE, op1, r);
    } else {
      r = new_node2 (N_TYPE, op1, new_node2 (N_DECL, new_node (N_IGNORE), new_node (N_LIST)));
    }
    op_append (list, r);
    comma_p = FALSE;
    if (! M (','))
      break;
    comma_p = TRUE;
    if (C (T_DOTS))
      break;
  }
  if (comma_p) {
    PTP (T_DOTS, pos); op_append (list, new_pos_node (N_DOTS, pos));
  }
  return list;
}
 
D (id_list) {
  node_t list, r;
  
  list = new_node (N_LIST);
  if (C (')'))
    return list;
  for (;;) {
    PTN (T_ID); op_append (list, r);
    if (! M (','))
      break;
  }
  return list;
}

D (abstract_declarator) {
  node_t list, p = NULL, r, el, next_el;
  
  if (C ('*')) {
    P (pointer); p = r;
    if ((r = TRY (direct_abstract_declarator)) == &err_node)
      r = new_pos_node2 (N_DECL, p->pos, new_node (N_IGNORE), new_node (N_LIST));
  } else {
    P (direct_abstract_declarator);
  }
  if (p != NULL) {
    list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, r->ops));
    assert (list->code == N_LIST);
    for (el = DLIST_HEAD (node_t, p->ops); el != NULL; el = next_el) {
      next_el = DLIST_NEXT (node_t, el);
      DLIST_REMOVE (node_t, p->ops, el);
      op_append (list, el);
    }
  }
  return r;
}

D (par_abstract_declarator) {
  node_t r;
  
  PT ('('); P (abstract_declarator); PT (')');
  return r;
}

D (direct_abstract_declarator) {
  node_t res, list, tql, ae, r;
  pos_t pos, pos2;
  
  if ((res = TRY (par_abstract_declarator)) != &err_node) {
    if (! C ('(') && ! C ('['))
      return res;
  } else {
    res = new_node2 (N_DECL, new_node (N_IGNORE), new_node (N_LIST));
  }
  list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, res->ops));
  assert (list->code == N_LIST);
  for (;;) {
    if (MP ('(', pos)) {
      P (param_type_list); PT (')'); op_append (list, new_pos_node1 (N_FUNC, pos, r));
    } else {
      PTP ('[', pos);
      if (MP ('*', pos2)) {
	r = new_pos_node3 (N_ARR, pos, new_node (N_IGNORE), new_node (N_IGNORE), new_pos_node (N_STAR, pos2));
      } else {
	int static_p = FALSE;
	
	if (MP (T_STATIC, pos2)) {
	  static_p = TRUE;
	}
	if (! C (T_CONST) && !C (T_RESTRICT) && !C (T_VOLATILE) && !C (T_ATOMIC)) {
	  tql = new_node (N_LIST);
	} else {
	  P (type_qual_list); tql = r;
	  if (! static_p && M (T_STATIC)) {
	    static_p = TRUE;
	  }
	}
	if (! C (']')) {
	  P (assign_expr); ae = r;
	} else {
	  ae = new_node (N_IGNORE);
	}
	r = new_pos_node3 (N_ARR, pos, static_p ? new_pos_node (N_STATIC, pos2) : new_node (N_IGNORE), tql, ae);
      }
      PT (']'); op_append (list, r);
    }
    if (! C ('(') && ! C ('['))
      break;
  }
  add_pos (res, list->pos);
  return res;
}

D (typedef_name) {
  node_t scope, r;
  
  PTN (T_ID);
  for (scope = curr_scope; ; scope = scope->u.scope) {
    if (tpname_find (r, scope, NULL))
      return r;
    if (scope == NULL)
      break;
  }
  return &err_node;
}

D (initializer) {
  node_t r;
  
  if (! M ('{')) {
    P (assign_expr);
  } else {
    P (initializer_list);
    if (M (','))
      ;
    PT ('}');
  }
  return r;
}

D (initializer_list) {
  node_t list, list2, r;
  int first_p;
  pos_t pos;
  
  list = new_node (N_LIST);
  for (;;) { /* designation */
    list2 = new_node (N_LIST);
    for (first_p = TRUE;; first_p = FALSE) {  /* designator-list, designator */
      if (M ('[')) {
	P (const_expr); PT (']');
      }	else if (M ('.')) {
	PTN (T_ID); r = new_node1 (N_FIELD_ID, r);
      } else break;
      op_append (list2, r);
    }
    if (! first_p) {
      PT ('=');
    }
    P (initializer);
    op_append (list, new_node2 (N_INIT, list2, r));
    if (! M (','))
      break;
  }
  return list;
}

D (type_name) {
  node_t op, r;

  P (spec_qual_list); op = r;
  if (! C (')') && ! C (':')) {
    P (abstract_declarator);
  } else {
    r = new_pos_node2 (N_DECL, op->pos, new_node (N_IGNORE), new_node (N_LIST));
  }
  return new_node2 (N_TYPE, op, r);
}

D (st_assert) {
  node_t op1, r;
  pos_t pos;
  
  PTP (T_STATIC_ASSERT, pos); PT ('('); P (const_expr); op1 = r; PT (','); PTN (T_STR); PT (')');  PT (';');
  r = new_pos_node2 (N_ST_ASSERT, pos, op1, r);
  return r;
}

/* Statements: */
D (compound_stmt);

D (label) {
  node_t r;
  pos_t pos;
  
  if (MP (T_CASE, pos)) {
    P (expr); r = new_pos_node1 (N_CASE, pos, r);
  } else if (MP (T_DEFAULT, pos)) {
    r = new_pos_node (N_DEFAULT, pos);
  } else {
    PTN (T_ID); r = new_node1 (N_LABEL, r);
  }
  PT (':');
  return r;
}
 
D (stmt) {
  node_t l, n, op1, op2, op3, r;
  pos_t pos;
  
  l = new_node (N_LIST);
  while ((op1 = TRY (label)) != &err_node) {
    op_append (l, op1);
  }
  if (C ('{')) {
    P (compound_stmt);
  } else if (MP (T_IF, pos)) { /* selection-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt); op2 = r;
    if (! M (T_ELSE)) {
      r = new_node (N_IGNORE);
    } else {
      P (stmt);
    }
    r = new_pos_node4 (N_IF, pos, l, op1, op2, r);
  } else if (MP (T_SWITCH, pos)) { /* selection-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt);
    r = new_pos_node3 (N_SWITCH, pos, l, op1, r);
  } else if (MP (T_WHILE, pos)) {  /* iteration-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt);
    r = new_pos_node3 (N_WHILE, pos, l, op1, r);
  } else if (M (T_DO)) {  /* iteration-statement */
    P (stmt); op1 = r; PTP (T_WHILE, pos); PT ('('); P (expr); PT (')'); PT (';');
    r = new_pos_node3 (N_DO, pos, l, r, op1);
  } else if (MP (T_FOR, pos)) {  /* iteration-statement */
    PT ('(');
    n = new_pos_node (N_FOR, pos); n->u.scope = curr_scope; curr_scope = n;
    if ((r = TRY (declaration)) != &err_node) {
      op1 = r;
      curr_scope = n->u.scope;
    } else {
      curr_scope = n->u.scope;
      if (! M (';')) {
	P (expr); op1 = r; PT (';');
      } else {
	op1 = new_node (N_IGNORE);
      }
    }
    if (M (';')) {
      op2 = new_node (N_IGNORE);
    } else {
      P (expr); op2 = r; PT (';');
    }
    if (C (')')) {
      op3 = new_node (N_IGNORE);
    } else {
      P (expr); op3 = r;
    }
    PT (')'); P (stmt);
    op_append (n, l); op_append (n, op1); op_append (n, op2); op_append (n, op3); op_append (n, r); r = n;
  } else if (MP (T_GOTO, pos)) {  /* jump-statement */
    PTN (T_ID); PT (';'); r = new_pos_node2 (N_GOTO, pos, l, r);
  } else if (MP (T_CONTINUE, pos)) {  /* continue-statement */
    PT (';'); r = new_pos_node1 (N_CONTINUE, pos, l);
  } else if (MP (T_BREAK, pos)) {  /* break-statement */
    PT (';'); r = new_pos_node1 (N_BREAK, pos, l);
  } else if (MP (T_RETURN, pos)) {  /* return-statement */
    if (M (';')) {
      r = new_node (N_IGNORE);
    } else {
      P (expr); PT (';');
    }
    r = new_pos_node2 (N_RETURN, pos, l, r);
  } else { /* expression-statement */
    if (C (';')) {
      r = new_node (N_IGNORE);
    } else {
      P (expr);
    }
    PT (';'); r = new_pos_node2 (N_EXPR, r->pos, l, r);
  }
  return r;
}
 
static void error_recovery (int par_lev) {
  fprintf (stderr, "error recovery: skipping");
  for (;;) {
    if (curr_token.code == EOF || (par_lev == 0 && curr_token.code == ';'))
      break;
    if (curr_token.code == '{') {
      par_lev++;
    } else if (curr_token.code == '}') {
      if (--par_lev <= 0)
	break;
    }
    fprintf (stderr, " %s(%d:%d)", get_token_name (curr_token.code), curr_token.pos.lno, curr_token.pos.ln_pos);
    read_token ();
  }
  fprintf (stderr, " %s", get_token_name (curr_token.code));
  read_token ();
  fprintf (stderr, "\n");
}

D (compound_stmt) {
  node_t n, list, r;
  pos_t pos;
  
  PTE ('{', pos, err0); list = new_node (N_LIST);
  n = new_pos_node1 (N_BLOCK, pos, list); n->u.scope = curr_scope; curr_scope = n;
  while (! C ('}') && ! C (EOF)) { /* block-item-list, block_item */
    if ((r = TRY (declaration)) != &err_node) {
    } else {
      PE (stmt, err1);
    }
    op_flat_append (list, r);
    continue;
  err1: error_recovery (1);
  }
  curr_scope = n->u.scope;
  if (! C (EOF))
    PT ('}');
  return n;
 err0:  error_recovery (0);
  return &err_node;
}
 
D (transl_unit) {
  node_t list, ds, d, dl, r;

  curr_token.code = ';'; /* for error recovery */
  read_token ();
  list = new_node (N_LIST);
  while (! C (EOF)) { /* external-declaration */
    if ((r = TRY (declaration)) != &err_node) {
    } else {
      PE (declaration_specs, err); ds = r; PE (declarator, err); d = r;
      dl = new_node (N_LIST); d->u.scope = curr_scope; curr_scope = d;
      while (! C ('{')) { /* declaration-list */
	PE (declaration, decl_err); op_flat_append (dl, r);
      }
      P (compound_stmt); r = new_pos_node4 (N_FUNC_DEF, d->pos, ds, d, dl, r);
      curr_scope = d->u.scope;
    }
    op_flat_append (list, r);
    continue;
  decl_err:
    curr_scope = d->u.scope;
  err:
    error_recovery (0);
  }
  return list;
}

static void fatal_error (C_error_code_t code, const char *message) {
  fprintf (stderr, "%s\n", message); exit (1);
}

static void kw_add (const char *name, token_code_t tc, size_t flags) { str_add (name, tc, flags, TRUE); }

static void parse_init (void) {
  error_func = fatal_error;
  record_level = 0;
  reg_memory_init ();
  curr_uid = 0;
  curr_pos.lno = 1; curr_pos.ln_pos = 0;
  VARR_CREATE (char, symbol_text, 100);
  VARR_CREATE (token_t, buffered_tokens, 32);
  VARR_CREATE (token_t, recorded_tokens, 32);
  str_init ();
  kw_add ("_Bool", T_BOOL, 0); kw_add ("_Complex", T_COMPLEX, 0); kw_add ("_Alignas", T_ALIGNAS, 0);
  kw_add ("_Alignof", T_ALIGNOF, 0); kw_add ("_Atomic", T_ATOMIC, 0); kw_add ("_Generic", T_GENERIC, 0);
  kw_add ("_Noreturn", T_NO_RETURN, 0); kw_add ("_Static_assert", T_STATIC_ASSERT, 0);
  kw_add ("_Thread_local", T_THREAD_LOCAL, 0); kw_add ("auto", T_AUTO, 0); kw_add ("break", T_BREAK, 0);
  kw_add ("case", T_CASE, 0); kw_add ("char", T_CHAR, 0); kw_add ("const", T_CONST, 0);
  kw_add ("continue", T_CONTINUE, 0); kw_add ("default", T_DEFAULT, 0); kw_add ("do", T_DO, 0);
  kw_add ("double", T_DOUBLE, 0); kw_add ("else", T_ELSE, 0); kw_add ("enum", T_ENUM, 0);
  kw_add ("extern", T_EXTERN, 0); kw_add ("float", T_FLOAT, 0); kw_add ("for", T_FOR, 0);
  kw_add ("goto", T_GOTO, 0); kw_add ("if", T_IF, 0); kw_add ("inline", T_INLINE, FLAG_EXT89);
  kw_add ("int", T_INT, 0); kw_add ("long", T_LONG, 0); kw_add ("register", T_REGISTER, 0);
  kw_add ("restrict", T_RESTRICT, FLAG_C89); kw_add ("return", T_RETURN, 0); kw_add ("short", T_SHORT, 0);
  kw_add ("signed", T_SIGNED, 0); kw_add ("sizeof", T_SIZEOF, 0); kw_add ("static", T_STATIC, 0);
  kw_add ("struct", T_STRUCT, 0); kw_add ("switch", T_SWITCH, 0); kw_add ("typedef", T_TYPEDEF, 0);
  kw_add ("typeof", T_TYPEOF, FLAG_EXT); kw_add ("union", T_UNION, 0); kw_add ("unsigned", T_UNSIGNED, 0);
  kw_add ("void", T_VOID, 0); kw_add ("volatile", T_VOLATILE, 0); kw_add ("while", T_WHILE, 0);
  tpname_init ();
  curr_scope = NULL;
}

static node_t parse (void) {
  return transl_unit (FALSE);
}

static void parse_finish (void) {
  VARR_DESTROY (char, symbol_text);
  VARR_DESTROY (token_t, buffered_tokens);
  VARR_DESTROY (token_t, recorded_tokens);
  str_finish ();
  tpname_finish ();
  reg_memory_finish ();
}

#undef P
#undef PT
#undef PTP
#undef PTN
#undef PE
#undef PTE
#undef D
#undef M
#undef MP
#undef MC
#undef MN
#undef TRY

/* ------------------------- Scanner/Parser End ------------------------------ */


/* We generate the following AST nodes:

expr : N_I | N_L | N_LL | N_U | N_UL | N_ULL | N_F | N_D | N_LD | N_CH | N_STR | N_ID
     | N_ADD (expr) | N_SUB (expr) | N_ADD (expr, expr) | N_SUB (expr, expr)
     | N_MUL (expr, expr) | N_DIV (expr, expr) | N_MOD (expr, expr)
     | N_LSH (expr, expr) | N_RSH (expr, expr)
     | N_NOT (expr) | N_BITWISE_NOT (expr)
     | N_INC (expr) | N_DEC (expr) | N_POST_INC (expr)| N_POST_DEC (expr)
     | N_ALIGNOF (type_name?) | N_SIZEOF (type_name) | N_EXPR_SIZEOF (expr) | N_CAST (type_name, expr)
     | N_COMMA (expr, expr) | N_ANDAND (expr, expr) | N_OROR (expr, expr)
     | N_EQ (expr, expr) | N_NE (expr, expr)
     | N_LT (expr, expr) | N_LE (expr, expr) | N_GT (expr, expr) | N_GE (expr, expr)
     | N_AND (expr, expr) | N_OR (expr, expr) | N_XOR (expr, expr)
     | N_ASSIGN (expr, expr) | N_ADD_ASSIGN (expr, expr) | N_SUB_ASSIGN (expr, expr)
     | N_MUL_ASSIGN (expr, expr) | N_DIV_ASSIGN (expr, expr) | N_MOD_ASSIGN (expr, expr)
     | N_LSH_ASSIGN (expr, expr) | N_RSH_ASSIGN (expr, expr)
     | N_AND_ASSIGN (expr, expr) | N_OR_ASSIGN (expr, expr) | N_XOR_ASSIGN (expr, expr)
     | N_DEREF (expr) | | N_ADDR (expr) | N_IND (expr, expr) | N_FIELD (expr, N_ID) | | N_DEREF_FIELD (expr, N_ID)
     | N_COND (expr, expr, expr)
     | N_COMPOUND_LITERAL (type_name, initializer)
     | N_CALL (expr, N_LIST:(expr)*)
     | N_GENERIC (expr, N_LIST:(N_GENERIC_ASSOC (type_name?, expr))+ )
label: N_CASE(expr) | N_DEFAULT | N_LABEL(N_ID)
stmt: compound_stmt | N_IF(N_LIST:(label)*, expr, stmt, stmt?)
    | N_SWITCH(N_LIST:(label)*, expr, stmt) | (N_WHILE|N_DO) (N_LIST:(label)*, expr, stmt)
    | N_FOR(N_LIST:(label)*,(N_LIST: declaration+ | expr)?, expr?, expr?, stmt)
    | N_GOTO(N_LIST:(label)*, N_ID) | (N_CONTINUE|N_BREAK) (N_LIST:(label)*)
    | N_RETURN(N_LIST:(label)*, expr?) | N_EXPR(N_LIST:(label)*, expr)
compound_stmt: N_BLOCK(N_LIST:(declaration | stmt)*)
declaration: N_SPEC_DECL(N_SHARE(declaration_specs), declarator?, initializer?) | st_assert
st_assert: N_ST_ASSERT(const_expr, N_STR)
declaration_specs: N_LIST:(align_spec|sc_spec|type_qual|func_spec|type_spec)*
align_spec: N_ALIGNAS(type_name|const_expr)
sc_spec: N_TYPEDEF|N_EXTERN|N_STATIC|N_AUTO|N_REGISTER|N_THREAD_LOCAL
type_qual: N_CONST|N_RESTRICT|N_VOLATILE|N_ATOMIC
func_spec: N_INLINE|N_NO_RETURN
type_spec: N_VOID|N_CHAR|N_SHORT|N_INT|N_LONG|N_FLOAT|N_DOUBLE|N_SIGNED|N_UNSIGNED|N_BOOL|N_COMPLEX
         | (N_STRUCT|N_UNION) (N_ID?, struct_declaration_list?)
	 | N_ENUM(N_ID?, N_LIST?: N_ENUM_COST(N_ID, const_expr?)*) | typedef_name
struct_declaration_list: N_LIST: struct_declaration+
struct_declaration: st_assert | N_MEMBER(spec_qual_list, declarator?, const_expr?)
spec_qual_list: N_LIST:(type_qual|type_spec)*
declarator: the same as direct declarator
direct_declarator: N_DECL(N_ID, N_LIST:(N_POINTER(type_qual_list) | N_FUNC(id_list|parameter_list)
                                          | N_ARR(N_STATIC?, type_qual_list, (assign_expr|N_STAR)?))*)
-pointer: N_LIST: N_POINTER(type_qual_list)*
type_qual_list : N_LIST: type_qual*
parameter_type_list: N_LIST:(N_SPEC_DECL(declaration_specs, declarator, ignore)
                             | N_TYPE(declaration_specs, abstract_declarator))+ [N_DOTS]
id_list: N_LIST: N_ID*
initializer: assign_expr | initialize_list
initialize_list: N_LIST: N_INIT(N_LIST:(const_expr | N_FIELD_ID (N_ID))* initializer)+
type_name: N_TYPE(spec_qual_list, abstract_declarator)
abstract_declarator: the same as abstract direct declarator
abstract_direct_declarator: N_DECL(ignore, N_LIST:(N_POINTER(type_qual_list) | N_FUNC(parameter_list)
                                                    | N_ARR(N_STATIC?, type_qual_list, (assign_expr|N_STAR)?))*)
typedef_name: N_ID
transl_unit: N_LIST:(declaration | N_FUNC_DEF(declaration_specs, declarator, N_LIST: declaration*, compound_stmt))*

Here ? means it can be N_IGNORE, * means 0 or more elements in the list, + means 1 or more.

*/

/* ---------------------------- Checker Start -------------------------------- */

static int supported_alignment_p (mir_long_long align) {
  return TRUE;
}

enum symbol_mode {S_REGULAR, S_TAG, S_LABEL};

typedef struct {
  enum symbol_mode mode;
  node_t id;
  node_t scope;
  node_t def_node, aux_node;
} symbol_t;

DEF_HTAB (symbol_t);
static HTAB (symbol_t) *symbol_tab;

static int symbol_eq (symbol_t s1, symbol_t s2) {
  return s1.mode == s2.mode && s1.id->u.s == s2.id->u.s && s1.scope == s2.scope;
}

static htab_hash_t symbol_hash (symbol_t s) {
  return (mum_hash_finish
	  (mum_hash_step
	   (mum_hash_step
	    (mum_hash_step (mum_hash_init (0x42), (uint64_t) s.mode),
	     (uint64_t) s.id->u.s),
	    (uint64_t) s.scope)));
}

static void symbol_init (void) {
  HTAB_CREATE (symbol_t, symbol_tab, 5000, symbol_hash, symbol_eq);
}

static int symbol_find (enum symbol_mode mode, node_t id, node_t scope, symbol_t *res) {
  int found_p;
  symbol_t el, symbol;
  
  symbol.mode = mode; symbol.id = id; symbol.scope = scope;
  found_p = HTAB_DO (symbol_t, symbol_tab, symbol, HTAB_FIND, el);
  if (res != NULL && found_p)
    *res = el;
  return found_p;
}

static void symbol_delete (enum symbol_mode mode, node_t id, node_t scope) {
  symbol_t el, symbol;
  
  symbol.mode = mode; symbol.id = id; symbol.scope = scope;
  HTAB_DO (symbol_t, symbol_tab, symbol, HTAB_DELETE, el);
}

static void symbol_insert (enum symbol_mode mode, node_t id, node_t scope,
			   node_t def_node, node_t aux_node) {
  symbol_t el, symbol;
  
  symbol.mode = mode; symbol.id = id; symbol.scope = scope;
  symbol.def_node = def_node; symbol.aux_node = aux_node;
  HTAB_DO (symbol_t, symbol_tab, symbol, HTAB_INSERT, el);
}

static void symbol_finish (void) {
  HTAB_DESTROY (symbol_t, symbol_tab);
}

DEF_VARR (node_t);
static VARR (node_t) *gotos;

static node_t func_block_scope;

enum basic_type get_int_basic_type (size_t s) {
  return (s == sizeof (mir_int) ? TP_INT
	  : s == sizeof (mir_short) ? TP_SHORT
	  : s == sizeof (mir_long) ? TP_LONG
	  : s == sizeof (mir_schar) ? TP_SCHAR : TP_LONG_LONG);
}

static int type_qual_eq_p (const struct type_qual *tq1, const struct type_qual *tq2) {
  return (tq1->const_p == tq2->const_p && tq1->restrict_p == tq2->restrict_p
	  && tq1->volatile_p == tq2->volatile_p && tq1->atomic_p == tq2->atomic_p);
}

static void clear_type_qual (struct type_qual *tq) {
  tq->const_p = tq->restrict_p = tq->volatile_p = tq->atomic_p = FALSE;
}

static int type_qual_subset_p (struct type_qual *tq1, struct type_qual *tq2) {
  return (tq1->const_p <= tq2->const_p && tq1->restrict_p <= tq2->restrict_p
	  && tq1->volatile_p <= tq2->volatile_p && tq1->atomic_p <= tq2->atomic_p);
}

static struct type_qual type_qual_union (struct type_qual *tq1, struct type_qual *tq2) {
  struct type_qual res;

  res.const_p = tq1->const_p || tq2->const_p; res.restrict_p = tq1->restrict_p || tq2->restrict_p;
  res.volatile_p = tq1->volatile_p || tq2->volatile_p; res.atomic_p = tq1->atomic_p || tq2->atomic_p;
  return res;
}

static void init_type (struct type *type) {
  clear_type_qual (&type->type_qual);
  type->pos_node = NULL; type->incomplete_p = FALSE;
}

static void set_type_pos_node (struct type *type, node_t n) { if (type->pos_node == NULL) type->pos_node = n; }

static int standard_integer_type_p (struct type *type) {
  return type->mode == TM_BASIC && type->u.basic_type >= TP_BOOL && type->u.basic_type <= TP_ULONG_LONG;
}

static int integer_type_p (struct type *type) {
  return standard_integer_type_p (type) || type->mode == TM_ENUM;
}

static int char_is_signed_p (void) {
  return MIR_CHAR_MAX == MIR_SCHAR_MAX;
}

static int signed_integer_type_p (struct type *type) {
  if (standard_integer_type_p (type)) {
    enum basic_type tp = type->u.basic_type;
    
    return ((tp == TP_CHAR && char_is_signed_p ())
	    || tp == TP_SCHAR || tp == TP_SHORT || tp == TP_INT || tp == TP_LONG || tp == TP_LONG_LONG);
  }
  if (type->mode == TM_ENUM) { // ???
    return TRUE;
  }
  return FALSE;
}

static int floating_type_p (struct type *type) {
  return type->mode == TM_BASIC && (type->u.basic_type == TP_FLOAT
				    || type->u.basic_type == TP_DOUBLE
				    || type->u.basic_type == TP_LONG_DOUBLE);
}

static int arithmetic_type_p (struct type *type) {
  return integer_type_p (type) || floating_type_p (type);
}

static int scalar_type_p (struct type *type) {
  return arithmetic_type_p (type) || type->mode == TM_PTR;
}

static struct type integer_promotion (struct type *type) {
  struct type res;
  
  assert (integer_type_p (type));
  init_type (&res); res.mode = TM_BASIC;
  if (type->mode == TM_BASIC && TP_LONG <= type->u.basic_type && type->u.basic_type <= TP_ULONG_LONG) {
    res.u.basic_type = type->u.basic_type; return res;
  }
  if (type->mode == TM_BASIC
      && ((type->u.basic_type == TP_CHAR && MIR_CHAR_MAX > MIR_INT_MAX)
	  || (type->u.basic_type == TP_UCHAR && MIR_UCHAR_MAX > MIR_INT_MAX)
	  || (type->u.basic_type == TP_USHORT && MIR_USHORT_MAX > MIR_INT_MAX)))
    res.u.basic_type = TP_UINT;
  else
    res.u.basic_type = TP_INT; /* including ENUM */
  return res;
}

#define SWAP(a1, a2, t) do {\
  t = a1; a1 = a2; a2 = t;  \
} while (0)

static struct type arithmetic_conversion (struct type *type1, struct type *type2) {
  struct type res, t1, t2;

  assert (arithmetic_type_p (type1) && arithmetic_type_p (type2));
  init_type (&res);
  res.mode = TM_BASIC;
  if (floating_type_p (type1) || floating_type_p (type2)) {
    if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_LONG_DOUBLE)
	|| (type2->mode == TM_BASIC && type2->u.basic_type == TP_LONG_DOUBLE)) {
      res.u.basic_type = TP_LONG_DOUBLE;
    } else if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_DOUBLE)
	       || (type2->mode == TM_BASIC && type2->u.basic_type == TP_DOUBLE)) {
      res.u.basic_type = TP_DOUBLE;
    } else if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_FLOAT)
	       || (type2->mode == TM_BASIC && type2->u.basic_type == TP_FLOAT)) {
      res.u.basic_type = TP_FLOAT;
    }
    return res;
  }
  t1 = integer_promotion (type1); t2 = integer_promotion (type2);
  if (signed_integer_type_p (&t1) == signed_integer_type_p (&t2)) {
    res.u.basic_type = t1.u.basic_type < t2.u.basic_type ? t2.u.basic_type : t1.u.basic_type;
  } else {
    struct type t;
    
    if (signed_integer_type_p (&t1))
      SWAP (t1, t2, t);
    assert (! signed_integer_type_p (&t1) && signed_integer_type_p (&t2));
    if ((t1.u.basic_type == TP_ULONG && t2.u.basic_type < TP_LONG)
	|| (t1.u.basic_type == TP_ULONG_LONG && t2.u.basic_type < TP_LONG_LONG)) {
      res.u.basic_type = t1.u.basic_type;
    } else if ((t1.u.basic_type == TP_UINT && t2.u.basic_type >= TP_LONG
		&& MIR_LONG_MAX >= MIR_UINT_MAX)
	       || (t1.u.basic_type == TP_ULONG && t2.u.basic_type >= TP_LONG_LONG
		   && MIR_LONG_LONG_MAX >= MIR_ULONG_MAX)) {
      res.u.basic_type = t2.u.basic_type;
    } else {
      res.u.basic_type = t1.u.basic_type;
    }
  }
  return res;
}

static struct type composite_type (struct type *tp1, struct type *tp2) {
  return *tp1; // ???
}

static struct type *create_type (struct type *copy) {
  struct type *res = reg_malloc (sizeof (struct type));

  if (copy == NULL)
    init_type (res);
  else
    *res = *copy;
  return res;
}

struct decl_spec {
  unsigned int typedef_p : 1, extern_p : 1, static_p : 1, auto_p : 1, register_p : 1, thread_local_p : 1;
  unsigned int inline_p : 1, no_return_p : 1; /* func specifiers  */
  int align; // negative value means undefined
  node_t align_node; //  strictest valid N_ALIGNAS node
  node_code_t linkage; // N_IGNORE - none, N_STATIC - internal, N_EXTERN - external
  node_t align_spec;
  struct type *type;
};

struct enum_value {
  mir_int val;
};

struct expr {
  unsigned int const_p : 1;
  node_t lvalue_node;
  struct type *type;
  union {
    mir_long_long i_val;
    mir_ulong_long u_val;
    mir_long_double d_val;
  } u;
};

struct node_scope {
  node_t scope;
};

struct decl {
  unsigned long long offset; /* field, ??? var */
  struct decl_spec decl_spec;
};

typedef struct case_attr *case_t;

DEF_DLIST_LINK (case_t);

struct case_attr {
  node_t case_node;
  DLIST_LINK (case_t) case_link;
};

DEF_DLIST (case_t, case_link);

struct switch_attr {
  struct type type; /* integer promoted type */
  DLIST (case_t) case_labels; /* default if any is always a tail */
};

static int basic_type_size (enum basic_type bt) {
  switch (bt) {
  case TP_BOOL: return sizeof (mir_bool);
  case TP_CHAR: return sizeof (mir_char);
  case TP_SCHAR: return sizeof (mir_schar);
  case TP_UCHAR: return sizeof (mir_uchar);
  case TP_SHORT: return sizeof (mir_short);
  case TP_USHORT: return sizeof (mir_ushort);
  case TP_INT: return sizeof (mir_int);
  case TP_UINT: return sizeof (mir_uint);
  case TP_LONG: return sizeof (mir_long);
  case TP_ULONG: return sizeof (mir_ulong);
  case TP_LONG_LONG: return sizeof (mir_long_long);
  case TP_ULONG_LONG: return sizeof (mir_ulong_long);
  case TP_FLOAT: return sizeof (mir_float);
  case TP_DOUBLE: return sizeof (mir_double);
  case TP_LONG_DOUBLE: return sizeof (mir_long_double);
  default: abort ();
  }
}

static int basic_type_align (enum basic_type bt) {
  return basic_type_size (bt);
}

static int type_align (struct type *type) {
  int align, member_align;
  
  if (type->mode == TM_BASIC) {
    align = basic_type_align (type->u.basic_type);
  } else if (type->mode == TM_PTR) {
    align = sizeof (mir_size_t);
  } else if (type->mode == TM_ENUM) {
    align = basic_type_align (TP_INT);
  } else if (type->mode == TM_FUNC) {
    align = sizeof (mir_size_t); // ???
  } else if (type->mode == TM_ARR) {
    align = type_align (type->u.arr_type->el_type);
  } else {
    assert (type->mode == TM_STRUCT || type->mode == TM_UNION);
    for (node_t member = DLIST_HEAD (node_t, DLIST_EL (node_t, type->u.tag_type->ops, 1)->ops);
         member != NULL;
         member = DLIST_NEXT (node_t, member))
      if (member->code == N_MEMBER) {
        struct decl *decl = member->attr;
	
	member_align = type_align (decl->decl_spec.type);
	if (align < member_align)
	  align = member_align;
      }
  }
#ifdef ADJUST_TYPE_ALIGNMENT
  align = ADJUST_TYPE_ALIGNMENT (align, type);
#endif
  return align;
}

static unsigned long long type_size (struct type *type);

static unsigned long long type_size_1 (struct type *type, int align_adjust_p) {
  int align;
  unsigned long long size;

  if (type->mode == TM_BASIC) {
    size = basic_type_size (type->u.basic_type);
  } else if (type->mode == TM_PTR) {
    size = sizeof (mir_size_t);
  } else if (type->mode == TM_ENUM) {
    size = basic_type_size (TP_INT);
  } else if (type->mode == TM_FUNC) {
    size = sizeof (mir_size_t); // ???
  } else if (type->mode == TM_ARR) {
    struct arr_type *arr_type = type->u.arr_type;
    struct expr *cexpr = arr_type->size->attr;
    unsigned long long nel = arr_type->size->code == N_IGNORE || ! cexpr->const_p ? 1 : cexpr->u.i_val;

    size = type_size (arr_type->el_type) * nel;
  } else {
    assert (type->mode == TM_STRUCT || type->mode == TM_UNION);
    size = 0;
    for (node_t member = DLIST_HEAD (node_t, DLIST_EL (node_t, type->u.tag_type->ops, 1)->ops);
         member != NULL;
         member = DLIST_NEXT (node_t, member))
      if (member->code == N_MEMBER) {
        struct decl *decl = member->attr;
	int bit_offset = 0, member_align = type_align (decl->decl_spec.type);
	unsigned long long offset, len, member_size = type_size (decl->decl_spec.type);
	node_t width = DLIST_EL (node_t, member->ops, 2);
	struct expr *expr;
	
	if (width->code == N_IGNORE || !(expr = width->attr)->const_p) {
	  if (type->mode == TM_STRUCT) {
	    offset = (size + member_align - 1) / member_align * member_align;
	    size = offset + member_size;
	  } else {
	    offset = 0;
	    if (size < member_size)
	      size =  member_size;
	  }
	  decl->offset = offset;
	} else {
	  int unit_size, bit_len = expr->u.u_val;
	  
	  if (type->mode == TM_UNION)
	    bit_offset = offset = 0;
	  /* Get byte and bit offsets (offset, bit_offset) and storage
	     unit size for the bit field. */
	  unit_size = get_bit_field_info (bit_len, &offset, &bit_offset);
	  len = (offset * MIR_CHAR_BIT + bit_offset + bit_len - 1) / MIR_CHAR_BIT / unit_size * unit_size;
	  if (type->mode == TM_STRUCT) size = len;
	  else if (size < len) size = len;
	  decl->offset = 0; /* ??? */
	}
      }
  }
  if (align_adjust_p) {
    align = type_align (type);
    size = (size + align - 1) / align * align;
  }
  return size;
}

static unsigned long long type_size (struct type *type) { return type_size_1 (type,  TRUE); }
static unsigned long long raw_type_size (struct type *type) { return type_size_1 (type,  FALSE); }

static int int_bit_size (struct type *type) {
  assert (type->mode == TM_BASIC);
  return basic_type_size (type->u.basic_type) * MIR_CHAR_BIT;
}

static int void_ptr_p (struct type *type) {
  return type->mode == TM_PTR && type->u.ptr_type->mode == TM_BASIC && type->u.ptr_type->u.basic_type == TP_VOID;
}

static int null_const_p (struct expr *expr, struct type *type) {
  return  (void_ptr_p (type) && expr->const_p && expr->u.u_val == 0
	   && type_qual_eq_p (&type->type_qual, &zero_type_qual));
}

static void convert_value (struct expr *e, struct type *t) {
}

static int non_reg_decl_spec_p (struct decl_spec *ds) {
  return (ds->typedef_p || ds->extern_p || ds->static_p || ds->auto_p
	  || ds->thread_local_p || ds->inline_p || ds->no_return_p || ds->align_spec);
}

static void create_node_scope (node_t node) {
  struct node_scope *ns = reg_malloc (sizeof (struct node_scope));
  
  assert (node != curr_scope);
  node->attr = ns; ns->scope = curr_scope; curr_scope = node;
}

static void set_type_qual (node_t r, struct type_qual *tq, enum type_mode tmode) {
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    switch (n->code) {
      /* Type qualifiers: */
    case N_CONST:
      tq->const_p = TRUE;
      break;
    case N_RESTRICT:
      tq->restrict_p = TRUE;
      if (tmode != TM_PTR && tmode != TM_UNDEF)
	print_error (n->pos, "restrict requires a pointer\n");
      break;
    case N_VOLATILE:
      tq->volatile_p = TRUE;
      break;
    case N_ATOMIC:
      tq->atomic_p = TRUE;
      if (tmode == TM_ARR)
	print_error (n->pos, "_Atomic qualifying array\n");
      else if (tmode == TM_FUNC)
	print_error (n->pos, "_Atomic qualifying function\n");
      break;
    }
}

static void check_type_duplication (struct type *type, node_t n, const char *name, int size, int sign) {
  if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
    print_error (n->pos, "%s with another type\n", name);
  else if (type->mode != TM_BASIC && size != 0)
    print_error (n->pos, "size with non-numeric type\n");
  else if (type->mode != TM_BASIC && sign != 0)
    print_error (n->pos, "sign attribute with non-integer type\n");
}

static node_t find_def (enum symbol_mode mode, node_t id, node_t scope, node_t *aux_node) {
  symbol_t sym;

  for (;;) {
    if (! symbol_find (mode, id, scope, &sym)) {
      if (scope == NULL)
	return NULL;
      scope = ((struct node_scope *) scope->attr)->scope;
    } else {
      if (aux_node)
	*aux_node = sym.aux_node;
      return sym.def_node;
    }
  }
}

static node_t process_tag (node_t r, node_t id, node_t decl_list) {
  symbol_t sym;
  int found_p;
  node_t tab_decl_list;
  
  if (id->code != N_ID)
    return r;
  if (decl_list->code != N_IGNORE) {
    found_p = symbol_find (S_TAG, id, curr_scope, &sym);
  } else {
    sym.def_node = find_def (S_TAG, id, curr_scope, NULL);
    found_p = sym.def_node != NULL;
  }
  if (! found_p) {
    symbol_insert (S_TAG, id, curr_scope, r, NULL);
  } else if (sym.def_node->code != r->code) {
    print_error (id->pos, "kind of tag %s is unmatched with previous declaration\n", id->u.s);
  } else if ((tab_decl_list = DLIST_EL (node_t, sym.def_node->ops, 1))->code != N_IGNORE
	     && decl_list->code != N_IGNORE) {
    print_error (id->pos, "tag %s redeclaration\n", id->u.s);
  } else {
    if (decl_list->code != N_IGNORE) { /* swap */
      DLIST (node_t) temp = r->ops;
      
      r->ops = sym.def_node->ops;
      sym.def_node->ops = temp;
    }
    r = sym.def_node;
  }
  return r;
}

static int compatible_types_p (struct type *type1, struct type *type2, int ignore_quals_p) {
  if (type1->mode != type2->mode) return FALSE;
  if (type1->mode == TM_BASIC) {
    return (type1->u.basic_type == type2->u.basic_type
	    && (ignore_quals_p || type_qual_eq_p (&type1->type_qual, &type2->type_qual)));
  } else if (type1->mode == TM_PTR) {
    return ((ignore_quals_p || type_qual_eq_p (&type1->type_qual, &type2->type_qual))
	    && compatible_types_p (type1->u.ptr_type, type2->u.ptr_type, ignore_quals_p));
  } else if (type1->mode == TM_ARR) {
    struct expr *cexpr1, *cexpr2;
    struct arr_type *at1 = type1->u.arr_type, *at2 = type2->u.arr_type;
    
    if (! compatible_types_p (at1->el_type, at2->el_type, ignore_quals_p))
      return FALSE;
    if (at1->size->code == N_IGNORE || at2->size->code == N_IGNORE)
      return TRUE;
    if ((cexpr1 = at1->size->attr)->const_p && (cexpr2 = at2->size->attr)->const_p
	&& integer_type_p (cexpr2->type) && integer_type_p (cexpr2->type))
      return cexpr1->u.i_val == cexpr2->u.i_val;
    return TRUE;
  } else if (type1->mode == TM_FUNC) {
    struct func_type *ft1 = type1->u.func_type, *ft2 = type2->u.func_type;

    if (DLIST_LENGTH (node_t, ft1->param_list->ops) != DLIST_LENGTH (node_t, ft2->param_list->ops))
      return FALSE;
    // ???
  }
  return TRUE;
}

static int assignment_compatible_types_p (struct type *type1, struct type *type2) {
  return TRUE; // ???
}

static int func_param_decl_p;

static void def_symbol (enum symbol_mode mode, node_t id, node_t scope,
			node_t def_node, node_code_t linkage) {
  symbol_t sym;
  struct decl_spec tab_decl_spec, decl_spec;
  
  if (id->code == N_IGNORE)
    return;
  assert (id->code == N_ID);
  assert (scope == NULL || scope->code == N_BLOCK || scope->code == N_STRUCT
	  || scope->code == N_UNION || scope->code == N_FUNC || scope->code == N_FOR);
  decl_spec = ((struct decl *) def_node->attr)->decl_spec;
  if (scope != NULL && decl_spec.thread_local_p && ! decl_spec.static_p && ! decl_spec.extern_p)
    print_error (id->pos, "auto %s is declared as thread local\n", id->u.s);
  if (! symbol_find (mode, id, scope, &sym)) {
    symbol_insert (mode, id, scope, def_node, NULL);
    return;
  }
  tab_decl_spec = ((struct decl *) sym.def_node->attr)->decl_spec;
  if (linkage == N_IGNORE) {
    if (! decl_spec.typedef_p || ! tab_decl_spec.typedef_p
	|| decl_spec.type != tab_decl_spec.type)
      print_error (id->pos, "repeated declaration %s\n", id->u.s);
  } else if (! compatible_types_p (decl_spec.type, tab_decl_spec.type, FALSE)) {
    print_error (id->pos, "incompatible types of %s declarations\n", id->u.s);
  }
  if (tab_decl_spec.thread_local_p != decl_spec.thread_local_p) {
    print_error (id->pos, "thread local and non-thread local declarations of %s\n", id->u.s);
  }
}

static int in_params_p;

static int check (node_t node, node_t context);
    
static struct decl_spec check_decl_spec (node_t r, node_t decl) {
  int n_sc = 0, sign = 0, size = 0;
  struct decl_spec *res;
  struct type *type;
  
  if (r->attr != NULL)
    return *(struct decl_spec *) r->attr;
  r->attr = res = reg_malloc (sizeof (struct decl_spec));
  res->typedef_p = res->extern_p = res->static_p = res->auto_p = res->register_p = res->thread_local_p = FALSE;
  res->inline_p = res->no_return_p = FALSE; res->align = -1; res->align_node = NULL;
  res->type = type = create_type (NULL); type->pos_node = r;
  type->mode = TM_BASIC; type->u.basic_type = TP_UNDEF;
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    if (n->code == N_SIGNED || n->code == N_UNSIGNED) {
      if (sign != 0) print_error (n->pos, "more than one sign qualifier\n");
      else sign = n->code == N_SIGNED ? 1 : -1;
    } else if (n->code == N_SHORT) {
      if (size != 0) print_error (n->pos, "more than one type\n");
      else size = 1;
    } else if (n->code == N_LONG) {
      if (size == 2) size = 3;
      else if (size == 3) print_error (n->pos, "more than two long\n");
      else if (size == 1) print_error (n->pos, "short with long\n");
      else size = 2;
    } else if (n->code == N_COMPLEX) {
      print_error (n->pos, "complex numbers are not supported\n");
    }
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    switch (n->code) {
      /* Type qualifiers are already processed. */
    case N_CONST: case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: break;
      /* Func specifiers: */
    case N_INLINE:
      if (decl->code != N_FUNC_DEF)
	print_error (n->pos, "non-function declaration with inline\n");
      else
	res->inline_p = TRUE;
      break;
    case N_NO_RETURN:
      if (decl->code != N_FUNC_DEF)
	print_error (n->pos, "non-function declaration with _Noreturn\n");
      else
	res->no_return_p = TRUE;
      break;
      /* Storage specifiers: */
    case N_TYPEDEF:
    case N_AUTO:
    case N_REGISTER:
      if (n_sc != 0) print_error (n->pos, "more than one storage specifier\n");
      else if (n->code == N_TYPEDEF) res->typedef_p = TRUE;
      else if (n->code == N_AUTO) res->auto_p = TRUE;
      else res->register_p = TRUE;
      n_sc++;
      break;
    case N_EXTERN:
    case N_STATIC:
      if (n_sc != 0 && (n_sc != 1 || !res->thread_local_p))
	print_error (n->pos, "more than one storage specifier\n");
      else if (n->code == N_EXTERN) res->extern_p = TRUE;
      else res->static_p = TRUE;
      n_sc++;
      break;
    case N_THREAD_LOCAL:
      if (n_sc != 0 && (n_sc != 1 || (!res->extern_p && !res->static_p)))
	print_error (n->pos, "more than one storage specifier\n");
      else res->thread_local_p = TRUE;
      n_sc++;
      break;
    case N_VOID:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	print_error (n->pos, "void with another type\n");
      else if (sign != 0) print_error (n->pos, "void with sign qualifier\n");
      else if (size != 0) print_error (n->pos, "void with short or long\n");
      else {
	type->u.basic_type = TP_VOID;
	type->incomplete_p = TRUE;
      }
      break;
    case N_UNSIGNED:
    case N_SIGNED:
    case N_COMPLEX:
    case N_SHORT:
    case N_LONG:
      set_type_pos_node (type, n);
      break;
    case N_CHAR:
    case N_INT:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) {
	print_error (n->pos, "char or int with another type\n");
      } else if (n->code == N_CHAR) {
	if (size != 0) print_error (n->pos, "char with short or long\n");
	else type->u.basic_type = sign == 0 ? TP_CHAR : sign < 0 ? TP_UCHAR : TP_SCHAR;
      } else if (size == 0)
	type->u.basic_type = sign >= 0 ? TP_INT : TP_UINT;
      else if (size == 1)
	type->u.basic_type = sign >= 0 ? TP_SHORT : TP_USHORT;
      else if (size == 2)
	type->u.basic_type = sign >= 0 ? TP_LONG : TP_ULONG;
      else
	type->u.basic_type = sign >= 0 ? TP_LONG_LONG : TP_ULONG_LONG;
      break;
    case N_BOOL:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	print_error (n->pos, "_Bool with another type\n");
      else if (sign != 0) print_error (n->pos, "_Bool with sign qualifier\n");
      else if (size != 0) print_error (n->pos, "_Bool with short or long\n");
      type->u.basic_type = TP_BOOL;
      break;
    case N_FLOAT:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	print_error (n->pos, "float with another type\n");
      else if (sign != 0) print_error (n->pos, "float with sign qualifier\n");
      else if (size != 0) print_error (n->pos, "float with short or long\n");
      else type->u.basic_type = TP_FLOAT;
      break;
    case N_DOUBLE:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	print_error (n->pos, "double with another type\n");
      else if (sign != 0) print_error (n->pos, "double with sign qualifier\n");
      else if (size == 0)
	type->u.basic_type = TP_DOUBLE;
      else if (size == 2)
	type->u.basic_type = TP_LONG_DOUBLE;
      else print_error (n->pos, "double with short\n");
      break;
    case N_ID: {
      node_t def = find_def (S_REGULAR, n, curr_scope, NULL);
      struct decl *decl;
      
      set_type_pos_node (type, n);
      assert (def != NULL && def->code == N_SPEC_DECL);
      decl = def->attr;
      assert (decl->decl_spec.typedef_p);
      *type = *decl->decl_spec.type;
      break;
    }
    case N_STRUCT:
    case N_UNION: {
      node_t res, id = DLIST_HEAD (node_t, n->ops);
      node_t decl_list = DLIST_NEXT (node_t, id);

      set_type_pos_node (type, n);
      res = process_tag (n, id, decl_list);
      check_type_duplication (type, n, n->code == N_STRUCT ? "struct" : "union", size, sign);
      type->mode = n->code == N_STRUCT ? TM_STRUCT : TM_UNION; type->u.tag_type = res;
      type->incomplete_p = DLIST_EL (node_t, res->ops, 1)->code == N_IGNORE;
      if (decl_list->code != N_IGNORE) {
	create_node_scope (res);
	check (decl_list, n);
	curr_scope = ((struct node_scope *) res->attr)->scope;
      }
      break;
    }
    case N_ENUM: {
      node_t res, id = DLIST_HEAD (node_t, n->ops);
      node_t enum_list = DLIST_NEXT (node_t, id);
      
      set_type_pos_node (type, n);
      res = process_tag (n, id, enum_list); check_type_duplication (type, n, "enum", size, sign);
      type->mode = TM_ENUM; type->u.tag_type = res;
      type->incomplete_p = DLIST_EL (node_t, res->ops, 1)->code == N_IGNORE;
      if (enum_list->code == N_IGNORE) {
	if (type->incomplete_p)
	  print_error (n->pos, "enum storage size is unknown\n");
      } else {
	mir_int curr_val = 0;
	
	for (node_t en = DLIST_HEAD (node_t, enum_list->ops); en != NULL; en = DLIST_NEXT (node_t, en)) { // ??? id
	  node_t id, const_expr;
	  symbol_t sym;
	  struct enum_value *enum_value;

	  assert (en->code == N_ENUM_CONST);
	  id = DLIST_HEAD (node_t, en->ops); const_expr = DLIST_NEXT (node_t, id);
	  check (const_expr, n);
	  if (symbol_find (S_REGULAR, id, curr_scope, &sym)) {
	    print_error (id->pos, "enum constant %s redeclaration\n", id->u.s);
	  } else {
	    symbol_insert (S_REGULAR, id, curr_scope, en, n);
	  }
	  if (const_expr->code != N_IGNORE) {
	    struct expr *cexpr = const_expr->attr;
	    
	    if (! cexpr->const_p)
	      print_error (const_expr->pos, "non-constant value in enum const expression\n");
	    else if (! integer_type_p (cexpr->type))
	      print_error (const_expr->pos, "enum const expression is not of an integer type\n");
	    else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val > MIR_INT_MAX)
		     || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val > MIR_INT_MAX))
	      print_error (const_expr->pos, "enum const expression is not represented by int\n");
	    else
	      curr_val = cexpr->u.i_val;
	  }
	  en->attr = enum_value = reg_malloc (sizeof (struct enum_value));
	  enum_value->val = curr_val;
	  curr_val++;
	}
      }
      break;
    }
    case N_ALIGNAS: {
      node_t el;
      int align = -1;
      
      if (decl->code == N_FUNC_DEF) {
	print_error (n->pos, "_Alignas for function\n");
      } else if (decl->code == N_MEMBER && (el = DLIST_EL (node_t, decl->ops, 3)) != NULL
		 && el->code != N_IGNORE) {
	print_error (n->pos, "_Alignas for a bit-field\n");
      } else if (decl->code == N_SPEC_DECL && in_params_p) {
	print_error (n->pos, "_Alignas for a function parameter\n");
      } else {
	node_t op = DLIST_HEAD (node_t, n->ops);

	check (op, n);
	if (op->code == N_TYPE) {
	  struct decl_spec *decl_spec = op->attr;
	  
	  align = type_align (decl_spec->type);
	} else {
	  struct expr *cexpr = op->attr;

	  if (! cexpr->const_p) {
	    print_error (op->pos, "non-constant value in _Alignas\n");
	  } else if (! integer_type_p (cexpr->type)) {
	    print_error (op->pos, "constant value in _Alignas is not of an integer type\n");
	  } else if (! signed_integer_type_p (cexpr->type) || ! supported_alignment_p (cexpr->u.i_val)) {
	    print_error (op->pos, "constant value in _Alignas specifies unspported alignment\n");
	  } else if (invalid_alignment (cexpr->u.i_val)) {
	    print_error (op->pos, "unsupported alignmnent\n");
	  } else {
	    align = cexpr->u.i_val;
	  }
	}
	if (align != 0 && res->align < align) {
	  res->align = align; res->align_node = n;
	}
      }
      break;
    }
    default:
      abort ();
    }
  if (type->mode == TM_BASIC && type->u.basic_type == TP_UNDEF) {
    if (size == 0 && sign == 0)
      print_error (r->pos, "no any type specifier\n");
    else if (size == 0) type->u.basic_type = sign >= 0 ? TP_INT : TP_UINT;
    else if (size == 1) type->u.basic_type = sign >= 0 ? TP_SHORT : TP_USHORT;
    else if (size == 2) type->u.basic_type = sign >= 0 ? TP_LONG : TP_ULONG;
    else type->u.basic_type = sign >= 0 ? TP_LONG_LONG : TP_ULONG_LONG;
  }
  set_type_qual (r, &type->type_qual, type->mode);
  if (res->align_node) {
    if (res->typedef_p)
      print_error (res->align_node->pos, "_Alignas in typedef\n");
    else if (res->register_p)
      print_error (res->align_node->pos, "_Alignas with register\n");
  }
  return *res;
}

static struct type *append_type (struct type *head, struct type *el) {
  struct type **holder;
  
  if (head == NULL)
    return el;
  if (head->mode == TM_PTR) {
    holder = &head->u.ptr_type;
  } else if (head->mode == TM_ARR) {
    holder = &head->u.arr_type->el_type;
  } else {
    assert (head->mode == TM_FUNC);
    holder = &head->u.func_type->ret_type;
  }
  *holder = append_type (*holder, el);
  if (head->mode != TM_PTR && (*holder)->incomplete_p)
    head->incomplete_p = TRUE;
  return head;
}

static int void_param_p (node_t param) {
  struct decl_spec *decl_spec;
  struct type *type;

  if (param != NULL && param->code == N_TYPE) {
    decl_spec = param->attr; type = decl_spec->type;
    if (type->mode == TM_BASIC && type->u.basic_type == TP_VOID)
      return TRUE;
  }
  return FALSE;
}

static struct type *check_declarator (node_t r, int func_def_p) {
  struct type *type, *res = NULL;
  node_t list = DLIST_EL (node_t, r->ops, 1);
  
  assert (r->code == N_DECL);
  if (DLIST_HEAD (node_t, list->ops) == NULL)
    return NULL;
  for (node_t n = DLIST_HEAD (node_t, list->ops); n != NULL; n = DLIST_NEXT (node_t, n)) {
    type = create_type (NULL); type->pos_node = n;
    switch (n->code) {
    case N_POINTER: {
      node_t type_qual = DLIST_HEAD (node_t, n->ops);
      
      type->mode = TM_PTR; type->pos_node = n; type->u.ptr_type = NULL;
      set_type_qual (type_qual, &type->type_qual, TM_PTR);
      break;
    }
    case N_ARR: {
      struct arr_type *arr_type;
      node_t static_node = DLIST_HEAD (node_t, n->ops);
      node_t type_qual = DLIST_NEXT (node_t, static_node);
      node_t size = DLIST_NEXT (node_t, type_qual);
      
      type->mode = TM_ARR; type->pos_node = n;
      type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
      set_type_qual (type_qual, &arr_type->ind_type_qual, TM_UNDEF);
      check (size, n);
      arr_type->size = size;
      arr_type->static_p = static_node->code == N_STATIC; arr_type->el_type = NULL;
      break;
    }
    case N_FUNC: {
      struct func_type *func_type;
      node_t first_param, param_list = DLIST_HEAD (node_t, n->ops);
      node_t last = DLIST_TAIL (node_t, param_list->ops);
      int saved_in_params_p = in_params_p;
      
      n->attr = type;
      type->mode = TM_FUNC; type->pos_node = n;
      type->u.func_type = func_type = reg_malloc (sizeof (struct func_type));
      func_type->ret_type = NULL;
      if ((func_type->dots_p = last != NULL && last->code == N_DOTS))
	DLIST_REMOVE (node_t, param_list->ops, last);
      if (! func_def_p)
	create_node_scope (n);
      func_type->param_list = param_list;
      in_params_p = TRUE;
      first_param = DLIST_HEAD (node_t, param_list->ops);
      if (first_param != NULL && first_param->code != N_ID)
	check (first_param, n);
      if (void_param_p (first_param)) {
	struct decl_spec *ds = first_param->attr;
	
	if (non_reg_decl_spec_p (ds) || ds->register_p
	    || ! type_qual_eq_p (&ds->type->type_qual, &zero_type_qual)) {
	  print_error (first_param->pos, "qualified void parameter\n");
	}
	if (DLIST_NEXT (node_t, first_param) != NULL) {
	  print_error (first_param->pos, "void must be the only parameter\n");
	}
      } else {
	for (node_t p = first_param; p != NULL; p = DLIST_NEXT (node_t, p)) {
	  struct decl_spec *decl_spec_ptr;
	  struct type *type;
	  
	  if (p->code == N_ID) {
	    if (! func_def_p)
	      print_error (p->pos, "parameters identifier list can be only in function definition\n");
	    break;
	  } else {
	    if (p != first_param)
	      check (p, n);
	    if (p->code == N_TYPE) {
	      decl_spec_ptr = p->attr;
	    } else {
	      node_t declarator = DLIST_EL (node_t, p->ops, 1);
	      
	      assert (p->code == N_SPEC_DECL && declarator != NULL && declarator->code == N_DECL);
	      decl_spec_ptr = &((struct decl *) p->attr)->decl_spec;
	    }
	    type = decl_spec_ptr->type;
	    /* Parameter adjustments: */
	    if (type->mode == TM_ARR) { // ??? static, old type qual
	      struct arr_type *arr_type = type->u.arr_type;
	      
	      type->mode = TM_PTR;
	      type->incomplete_p = FALSE;
	      type->u.ptr_type = arr_type->el_type;
	      type->type_qual = arr_type->ind_type_qual;
	    } else if (type->mode == TM_FUNC) {
	      struct type *par_type = create_type (NULL);
	      
	      par_type->mode = TM_PTR;
	      type->incomplete_p = FALSE;
	      par_type->pos_node = type->pos_node; par_type->u.ptr_type = decl_spec_ptr->type;
	    }
	  }
	}
      }
      in_params_p = saved_in_params_p;
      curr_scope = ((struct node_scope *) n->attr)->scope;
      break;
    }
    default:
      abort ();
    }
    res = append_type (res, type);
  }
  return res;
}

static node_t curr_switch;

static void check_labels (node_t labels, node_t target) {
  for (node_t l = DLIST_HEAD (node_t, labels->ops); l != NULL; l = DLIST_NEXT (node_t, l)) {
    if (l->code == N_LABEL) {
      symbol_t sym;
      node_t id = DLIST_HEAD (node_t, labels->ops);
      
      if (symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	print_error (id->pos, "label %s redeclaration\n", id->u.s);
      } else {
	symbol_insert (S_LABEL, id, func_block_scope, target, NULL);
      }
    } else if (curr_switch == NULL) {
      print_error (l->pos, "%s not witin a switch-stmt\n", l->code == N_CASE ? "case label" : "default label");
    } else {
      struct switch_attr *switch_attr = curr_switch->attr;
      struct type *type = &switch_attr->type;
      node_t case_expr = l->code == N_CASE ? DLIST_HEAD (node_t, l->ops) : NULL;
      case_t case_attr, tail = DLIST_TAIL (case_t, switch_attr->case_labels);
      int ok_p = FALSE, default_p = tail != NULL && tail->case_node->code == N_DEFAULT;
      struct expr *expr;
      
      if (case_expr == NULL) {
	if (default_p) {
	  print_error (l->pos, "multiple default labels in one switch\n");
	} else {
	  ok_p = TRUE;
	}
      } else {
	check (case_expr, target);
	expr = case_expr->attr;
	if (! expr->const_p) {
	  print_error (case_expr->pos, "case-expr is not a constant expression\n");
	} else if (! integer_type_p (expr->type)) {
	  print_error (case_expr->pos, "case-expr is not an integer type expression\n");
	} else {
	  convert_value (expr, type);
	  ok_p = TRUE;
	}
      }
      if (ok_p) {
	case_attr = reg_malloc (sizeof (struct case_attr));
	case_attr->case_node = l;
	if (default_p)
	  DLIST_INSERT_BEFORE (case_t, switch_attr->case_labels, tail, case_attr);
	else 
	  DLIST_APPEND (case_t, switch_attr->case_labels, case_attr);
      }
    }
  }
}

static node_code_t get_id_linkage (int func_p, node_t id, node_t scope, struct decl_spec decl_spec) {
  node_code_t linkage;
  node_t def = find_def (S_REGULAR, id, scope, NULL);
  
  if (decl_spec.typedef_p)
    return N_IGNORE; // p6: no linkage
  if (decl_spec.static_p && scope == NULL)
    return N_STATIC; // p3: internal linkage
  if (decl_spec.extern_p && def != NULL && (linkage = ((struct decl *) def->attr)->decl_spec.linkage) != N_IGNORE)
    return linkage; // p4: previous linkage
  if (decl_spec.extern_p && (def == NULL || ((struct decl *) def->attr)->decl_spec.linkage == N_IGNORE))
    return N_EXTERN; // p4: external linkage
  if (! decl_spec.static_p && ! decl_spec.extern_p && (scope == NULL || func_p))
    return N_EXTERN; // p5
  if (! decl_spec.extern_p && scope != NULL && ! func_p)
    return N_IGNORE; // p6: no linkage
  return N_IGNORE;
}

static void check_type (struct type *type, int level, int func_def_p) {
  switch (type->mode) {
  case TM_PTR:
    check_type (type->u.ptr_type, level + 1, FALSE);
    break;
  case TM_STRUCT:
  case TM_UNION: {
    node_t id = DLIST_HEAD (node_t, type->u.tag_type->ops);
    node_t decl_list = DLIST_NEXT (node_t, id);

    if (decl_list->code == N_IGNORE)
      type->incomplete_p = TRUE;
    break;
  }
  case TM_ARR: {
    struct arr_type *arr_type = type->u.arr_type;
    node_t size_node = arr_type->size;
    struct type *el_type = arr_type->el_type;

    if (size_node->code == N_IGNORE) {
      type->incomplete_p = TRUE;
    } else if (size_node->code == N_STAR) {
      print_error (size_node->pos, "variable size arrays are not supported\n");
    } else {
      struct expr *cexpr = size_node->attr;
      
      if (! integer_type_p (cexpr->type)) {
	print_error (size_node->pos, "non-integer array size type\n");
      } else if (! cexpr->const_p) {
	print_error (size_node->pos, "variable size arrays are not supported\n");
      } else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val <= 0)
		 || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val == 0)) {
	print_error (size_node->pos, "array size should be positive\n");
      }
    }
    check_type (el_type, level + 1, FALSE);
    if (el_type->mode == TM_FUNC) {
      print_error (type->pos_node->pos, "array of functions\n");
    } else if (el_type->incomplete_p) {
      print_error (type->pos_node->pos, "incomplete array element type\n");
      type->incomplete_p = TRUE;
    } else if (! in_params_p || level != 0) {
      if (arr_type->static_p)
	print_error (type->pos_node->pos, "static should be only in parameter outermost\n");
      else if (! type_qual_eq_p (&arr_type->ind_type_qual, &zero_type_qual))
	print_error (type->pos_node->pos, "type qualifiers should be only in parameter outermost array\n");
    }
    break;
  }
  case TM_FUNC: {
    struct decl_spec decl_spec;
    struct func_type *func_type = type->u.func_type;
    struct type *ret_type = func_type->ret_type;
    node_t first_param, param_list = func_type->param_list;
    
    check_type (ret_type, level + 1, FALSE);
    if (ret_type->mode == TM_FUNC) {
      print_error (ret_type->pos_node->pos, "function returning a function\n");
    } else if (ret_type->mode == TM_ARR) {
      print_error (ret_type->pos_node->pos, "function returning an array\n");
    }
    first_param = DLIST_HEAD (node_t, param_list->ops);
    if (! void_param_p (first_param)) {
      for (node_t p = first_param; p != NULL; p = DLIST_NEXT (node_t, p)) {
	if (p->code == N_TYPE) {
	  decl_spec = *((struct decl_spec *) p->attr);
	  check_type (decl_spec.type, level + 1, FALSE);
	} else if (p->code == N_SPEC_DECL) {
	  decl_spec = ((struct decl *) p->attr)->decl_spec;
	  check_type (decl_spec.type, level + 1, FALSE);
	} else {
	  assert (p->code == N_ID);
	  break;
	}
	if (non_reg_decl_spec_p (&decl_spec)) {
	  print_error (p->pos, "prohibited specifier in a function parameter\n");
	} else if (func_def_p) {
	  if (p->code == N_TYPE)
	    print_error (p->pos, "parameter type without a name in function definition\n");
	  else if (decl_spec.type->incomplete_p)
	    print_error (p->pos, "incomplete parameter type in function definition\n");
	}
      }
    }
    break;
  }
  default:
    break; // ???
  }
}

static void check_initializer (struct type *type, node_t initializer, int const_only_p, int top_p) {
  struct expr *cexpr;
  node_t des_list, curr_des, init, last_member, value, size_node, temp;
  mir_long_long last_index, max_index, size_val;
  symbol_t sym;
  struct expr *sexpr;
  
 scalar:
  if (initializer->code != N_LIST) {
    if (type->mode == TM_ARR || type->mode == TM_STRUCT  || type->mode == TM_UNION) {
      print_error (initializer->pos, "invalid initializer -- {} should be used\n");
      return;
    }
    if (! (cexpr = initializer->attr)->const_p && const_only_p) {
      print_error (initializer->pos,
		   "initializer of static or thread local object should be a constant expression\n");
      return;
    }
    if (! assignment_compatible_types_p (cexpr->type, type)) {
      print_error (initializer->pos, "incompatible assignment types\n");
      return;
    }
    return;
  }
  init = DLIST_HEAD (node_t, initializer->ops);
  assert (init->code == N_INIT);
  des_list = DLIST_HEAD (node_t, init->ops);
  assert (des_list->code == N_LIST);
  if (type->mode != TM_ARR && type->mode != TM_STRUCT  && type->mode != TM_UNION) {
    if ((temp = DLIST_NEXT (node_t, init)) != NULL) {
      print_error (temp->pos, "excess elements in scalar initializer\n");
      return;
    }
    if ((temp = DLIST_HEAD (node_t, des_list->ops)) != NULL) {
      print_error (temp->pos, "designator in scalar initializer\n");
      return;
    }
    initializer = DLIST_NEXT (node_t, des_list);
    if (! top_p) {
      print_error (init->pos, "braces around scalar initializer\n");
      return;
    }
    top_p = FALSE;
    goto scalar;
  }
  last_member = NULL; size_val = -1;
  if (type->mode == TM_ARR) {
    size_node = type->u.arr_type->size; sexpr = size_node->attr;
    size_val = size_node->code != N_IGNORE && sexpr->const_p && integer_type_p (sexpr->type) ? sexpr->u.i_val : -1;
  }
  max_index = last_index = -1; last_member = NULL;
  for (; init != NULL; init = DLIST_NEXT (node_t, init)) {
    assert (init->code == N_INIT);
    des_list = DLIST_HEAD (node_t, init->ops);
    value = DLIST_NEXT (node_t, des_list);
    if (0&&value->code == N_LIST && type->mode != TM_ARR && type->mode != TM_STRUCT  && type->mode != TM_UNION) {
      print_error (init->pos, "braces around scalar initializer\n");
      continue;
    }
    if (value->code != N_LIST && ! ((struct expr *) value->attr)->const_p && const_only_p) {
      print_error (init->pos, "initializer of static or thread local object should be a constant expression\n");
      continue;
    }
    if ((curr_des = DLIST_HEAD (node_t, des_list->ops)) == NULL) {
      if (type->mode == TM_ARR) {
	check_initializer (type->u.arr_type->el_type, value, const_only_p, FALSE);
	last_index++;
	if (max_index < last_index)
	  max_index = last_index;
	if (last_index >= 0 && size_val >= 0 && size_val <= last_index)
	  print_error (init->pos, "excess elements in array initializer\n");
      } else if (type->mode == TM_STRUCT || type->mode == TM_UNION) {
	int first_p = last_member == NULL;
	
	if (last_member != NULL) {
	  last_member = DLIST_NEXT (node_t, last_member);
	} else {
	  node_t declaration_list = DLIST_EL (node_t, type->u.tag_type->ops, 1);

	  assert (declaration_list != NULL && declaration_list->code == N_LIST);
	  last_member = DLIST_HEAD (node_t, declaration_list->ops);
	}
	while (last_member != NULL && last_member->code != N_MEMBER)
	  last_member = DLIST_NEXT (node_t, last_member);
	if (last_member == NULL || (! first_p && type->mode == TM_UNION)) {
	  print_error (init->pos, "excess elements in struct/union initializer\n");
	} else {
	  check_initializer (((struct decl *) last_member->attr)->decl_spec.type, value, const_only_p, FALSE);
	}
      }
    } else {
      for (; curr_des != NULL; curr_des = DLIST_NEXT (node_t, curr_des)) {
	if (curr_des->code == N_FIELD_ID) {
	  node_t id = DLIST_HEAD (node_t, curr_des->ops);
	  
	  if (type->mode != TM_STRUCT && type->mode != TM_UNION) {
	    print_error (curr_des->pos, "field name not in struct or union initializer\n");
	  } else if (! symbol_find (S_REGULAR, id, type->u.tag_type, &sym)) {
	    print_error (curr_des->pos, "unknown field %s in initializer\n", id->u.s);
	  } else {
	    last_member = sym.def_node;
	    assert (last_member->code == N_MEMBER);
	    check_initializer (((struct decl *) last_member->attr)->decl_spec.type, value, const_only_p, FALSE);
	  }
	} else if (type->mode != TM_ARR) {
	  print_error (curr_des->pos, "array index in initializer for non-array\n");
	} else if (! (cexpr = curr_des->attr)->const_p) {
	  print_error (curr_des->pos, "nonconstant array index in initializer\n");
	} else if (integer_type_p (cexpr->type)) {
	  print_error (curr_des->pos, "array index in initializer not of integer type\n");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  print_error (curr_des->pos, "negative array index in initializer\n");
	} else if (size_val >= 0 && (! signed_integer_type_p (cexpr->type) || size_val <= cexpr->u.i_val)) {
	  print_error (curr_des->pos, "array index in initializer exceeds array bounds\n");
	} else {
	  check_initializer (type->u.arr_type->el_type, value, const_only_p, FALSE);
	  last_index = cexpr->u.i_val;
	  if (max_index < last_index)
	    max_index = last_index;
	}
      }
    }
  }
  if (type->mode == TM_ARR && size_val < 0 && max_index >= 0) {  /* array w/o size: define it.  */
    size_node = type->u.arr_type->size;
    type->u.arr_type->size = (max_index < MIR_INT_MAX ? new_i_node (max_index + 1, size_node->pos)
			      : max_index < MIR_LONG_MAX ? new_l_node (max_index + 1, size_node->pos)
			      : new_ll_node (max_index + 1, size_node->pos));
    check (type->u.arr_type->size, NULL);
  }
  return;
}

static void check_decl_align (struct decl_spec *decl_spec) {
  if (decl_spec->align < 0) return;
  if (decl_spec->align < type_align (decl_spec->type))
    print_error (decl_spec->align_node->pos,  "requested alignment is less than minimum alignment for the type\n");
}

static void create_decl (node_t scope, node_t decl_node, struct decl_spec decl_spec,
			 node_t width, node_t initializer) {
  int func_def_p = decl_node->code == N_FUNC_DEF, func_p = FALSE;
  node_t id, list_head, declarator, def;
  struct type *type;
  struct decl *decl = reg_malloc (sizeof (struct decl));
  
  assert (decl_node->code == N_MEMBER || decl_node->code == N_SPEC_DECL || decl_node->code == N_FUNC_DEF);
  declarator = DLIST_EL (node_t, decl_node->ops, 1);
  if (declarator->code == N_IGNORE) {
    assert (decl_node->code == N_MEMBER);
    type = decl_spec.type;
    decl_spec.linkage = N_IGNORE;
  } else {
    assert (declarator->code == N_DECL);
    type = check_declarator (declarator, func_def_p);
    type = append_type (type, decl_spec.type);
    decl_spec.type = type;
  }
  check_type (type, 0, func_def_p);
  check_decl_align (&decl_spec);
  if (declarator->code == N_DECL) {
    id = DLIST_HEAD (node_t, declarator->ops);
    list_head = DLIST_HEAD (node_t, DLIST_NEXT (node_t, id)->ops);
    func_p = list_head && list_head->code == N_FUNC;
    decl_spec.linkage = get_id_linkage (func_p, id, scope, decl_spec);
  }
  decl->decl_spec = decl_spec;
  decl_node->attr = decl;
  if (declarator->code == N_DECL) {
    if (scope == NULL)
      def_symbol (S_REGULAR, id, NULL, decl_node, decl_spec.linkage);
    else {
      def_symbol (S_REGULAR, id, scope, decl_node, decl_spec.linkage);
      if (decl_spec.linkage == N_EXTERN)
	def_symbol (S_REGULAR, id, NULL, decl_node, N_EXTERN);
    }
    if (func_p && decl_spec.thread_local_p) {
      print_error (id->pos, "thread local function declaration");
      if (id->code != N_IGNORE)
	fprintf (stderr, " of %s", id->u.s);
      fprintf (stderr, "\n");
    }
  }
  if (initializer == NULL || initializer->code == N_IGNORE)
    return;
  if (type->incomplete_p && (type->mode != TM_ARR || type->u.arr_type->el_type->incomplete_p)) {
    print_error (initializer->pos, "initialization of incomplete type variable\n");
    return;
  }
  if (decl_spec.linkage != N_IGNORE && scope != NULL) {
    print_error (initializer->pos, "initialization for block scope identifier with external or internal linkage\n");
    return;
  }
  check (initializer, decl_node);
  check_initializer (type, initializer, decl_spec.static_p || decl_spec.thread_local_p, TRUE);
}

static struct type *adjust_type (struct type *type) {
  struct type *res = type;
  
  if (type->mode == TM_ARR) {
    res = create_type (NULL);
    res->mode = TM_PTR;
    res->incomplete_p = FALSE;
    res->u.ptr_type = type->u.arr_type->el_type;
    res->type_qual = type->u.arr_type->ind_type_qual;
  } else if (type->mode == TM_FUNC) {
    res = create_type (NULL);
    res->mode = TM_PTR;
    res->incomplete_p = FALSE;
    res->pos_node = type->pos_node; res->u.ptr_type = type;
  }
  return res;
}

static void process_unop (node_t r, node_t *op, struct expr **e, struct type **t, node_t context) {
  *op = DLIST_HEAD (node_t, r->ops); check (*op, context);
  *e = (*op)->attr; *t = (*e)->type;
}

static void process_bin_ops (node_t r, node_t *op1, node_t *op2, struct expr **e1, struct expr **e2,
			     struct type **t1, struct type **t2, node_t context) {
  *op1 = DLIST_HEAD (node_t, r->ops); *op2 = DLIST_NEXT (node_t, *op1);
  check (*op1, context); check (*op2, context);
  *e1 = (*op1)->attr; *e2 = (*op2)->attr; *t1 = (*e1)->type; *t2 = (*e2)->type;
}

static void process_type_bin_ops (node_t r, node_t *op1, node_t *op2, struct expr **e2, struct type **t2,
				  node_t context) {
  *op1 = DLIST_HEAD (node_t, r->ops); *op2 = DLIST_NEXT (node_t, *op1);
  check (*op1, context); check (*op2, context);
  *e2 = (*op2)->attr; *t2 = (*e2)->type;
}

static struct expr *create_expr (node_t r) {
  struct expr *e = reg_malloc (sizeof (struct expr));
  
  r->attr = e; e->type = create_type (NULL); e->type->pos_node = r;
  e->lvalue_node = NULL; e->const_p = FALSE;
  return e;
}

static struct expr *create_basic_type_expr (node_t r, enum basic_type bt) {
  struct expr *e = create_expr (r);
  
  e->type->mode = TM_BASIC; e->type->u.basic_type = bt;
  return e;
}

static node_t n_i1_node;

static void get_one_node (node_t *op, struct expr **e, struct type **t) {
  *op = n_i1_node; *e = (*op)->attr; *t = (*e)->type; init_type (*t);
  (*e)->type->mode = TM_BASIC; (*e)->type->u.basic_type = TP_INT; (*e)->u.i_val = 1;
}

static void check_assign_op (node_t r, node_t op1, node_t op2, struct expr *e1, struct expr *e2,
			     struct type *t1, struct type *t2) {
  struct expr *e, *te;
  struct type t, *tt;

  switch (r->code) {
  case N_AND: case N_OR: case N_XOR:
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN:
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! integer_type_p (t1) || ! integer_type_p (t2)) {
      print_error (r->pos, "bitwise operation operands should be of an integer type\n");
    } else {
      t = arithmetic_conversion (t1, t2); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	convert_value (e1, &t); convert_value (e2, &t);
	e->const_p = TRUE;
	if (signed_integer_type_p (&t))
	  e->u.i_val = (r->code == N_AND ? e1->u.i_val & e2->u.i_val
			: r->code == N_OR ? e1->u.i_val | e2->u.i_val
			: e1->u.i_val ^ e2->u.i_val);
	else
	  e->u.u_val = (r->code == N_AND ? e1->u.u_val & e2->u.u_val
			: r->code == N_OR ? e1->u.u_val | e2->u.u_val
			: e1->u.u_val ^ e2->u.u_val);
      }
    }
    break;
  case N_LSH: case N_RSH: 
  case N_LSH_ASSIGN: case N_RSH_ASSIGN: 
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! integer_type_p (t1) || ! integer_type_p (t2)) {
      print_error (r->pos, "shift operands should be of an integer type\n");
    } else {
      t = integer_promotion (t1); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	struct type rt = integer_promotion (t2);
	
	convert_value (e1, &t); convert_value (e2, &rt);
	e->const_p = TRUE;
	if (signed_integer_type_p (&t)) {
	  if (signed_integer_type_p (&rt))
	    e->u.i_val = r->code == N_LSH ? e1->u.i_val << e2->u.i_val : e1->u.i_val >> e2->u.i_val;
	  else
	    e->u.i_val = r->code == N_LSH ? e1->u.i_val << e2->u.u_val : e1->u.i_val >> e2->u.u_val;
	} else if (signed_integer_type_p (&rt)) {
	  e->u.u_val = r->code == N_LSH ? e1->u.u_val << e2->u.i_val : e1->u.u_val >> e2->u.i_val;
	} else {
	  e->u.u_val = r->code == N_LSH ? e1->u.u_val << e2->u.u_val : e1->u.u_val >> e2->u.u_val;
	}
      }
    }
    break;
  case N_INC: case N_DEC: case N_POST_INC: case N_POST_DEC:
  case N_ADD: case N_SUB: case N_ADD_ASSIGN: case N_SUB_ASSIGN: {
    mir_size_t size;
    int add_p = r->code == N_ADD || r->code == N_ADD_ASSIGN || r->code == N_INC || r->code == N_POST_INC;
    
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (arithmetic_type_p (t1) && arithmetic_type_p (t2)) {
      t = arithmetic_conversion (t1, t2); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	convert_value (e1, &t); convert_value (e2, &t);
	if (floating_type_p (&t))
	  e->u.d_val = (add_p ? e1->u.d_val + e2->u.d_val : e1->u.d_val - e2->u.d_val);
	else if (signed_integer_type_p (&t))
	  e->u.i_val = (add_p ? e1->u.i_val + e2->u.i_val : e1->u.i_val - e2->u.i_val);
	else
	  e->u.u_val = (add_p ? e1->u.u_val + e2->u.u_val : e1->u.u_val - e2->u.u_val);
      }
    } else if (add_p) {
      if (t2->mode == TM_PTR) { SWAP (t1, t2, tt); SWAP (e1, e2, te); }
      if (t1->mode != TM_PTR || ! integer_type_p (t2)) {
	print_error (r->pos, "invalid operand types of +\n");
      } else if (t1->u.ptr_type->incomplete_p) {
	print_error (r->pos, "pointer to incomplete type as an operand of +\n");
      } else {
	*e->type = *t1;
	if (e1->const_p && e2->const_p) {
	  size = type_size (t1->u.ptr_type);
	  e->const_p = TRUE;
	  e->u.u_val = (signed_integer_type_p (t2)
			? e1->u.u_val + e2->u.i_val * size : e1->u.u_val + e2->u.u_val * size);
	}
      }
    } else if (t1->mode == TM_PTR && integer_type_p (t2)) {
      if (t1->u.ptr_type->incomplete_p) {
	print_error (r->pos, "pointer to incomplete type as an operand of -\n");
      } else {
	*e->type = *t1;
	if (e1->const_p && e2->const_p) {
	  size = type_size (t1->u.ptr_type);
	  e->const_p = TRUE;
	  e->u.u_val = (signed_integer_type_p (t2)
			? e1->u.u_val - e2->u.i_val * size : e1->u.u_val - e2->u.u_val * size);
	}
      }
    } else if (t1->mode == TM_PTR && t2->mode == TM_PTR && compatible_types_p (t1, t2, TRUE)) {
      if (t1->u.ptr_type->incomplete_p && t2->u.ptr_type->incomplete_p) {
	print_error (r->pos, "pointer to incomplete type as an operand of -\n");
      } else if (t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p) {
	print_error (r->pos, "pointer to atomic type as an operand of -\n");
      } else {
	e->type->mode = TM_BASIC;
	e->type->u.basic_type = get_int_basic_type (sizeof (mir_ptrdiff_t));
	if (e1->const_p && e2->const_p) {
	  size = type_size (t1->u.ptr_type);
	  e->const_p = TRUE;
	  e->u.i_val = (e1->u.u_val > e2->u.u_val
			? (mir_ptrdiff_t) ((e1->u.u_val - e2->u.u_val) / size)
			: -(mir_ptrdiff_t) ((e2->u.u_val - e1->u.u_val) / size));
	}
      }
    } else {
      print_error (r->pos, "invalid operand types of -\n");
    }
    break;
  }
  case N_MUL: case N_DIV: case N_MOD:
  case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN:
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_MOD && (! integer_type_p (t1) || ! integer_type_p (t2))) {
      print_error (r->pos, "invalid operand types of %%\n");
    } else if (r->code != N_MOD && (! arithmetic_type_p (t1) || ! arithmetic_type_p (t2))) {
      print_error (r->pos, "invalid operand types of %s\n", r->code == N_MUL ? "*" : "/");
    } else {
      t = arithmetic_conversion (t1, t2); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	convert_value (e1, &t); convert_value (e2, &t);
	if (r->code != N_MOD && floating_type_p (&t))
	  e->u.d_val = (r->code == N_MUL ? e1->u.d_val * e2->u.d_val : e1->u.d_val / e2->u.d_val);
	else if (signed_integer_type_p (&t))
	  e->u.i_val = (r->code == N_MUL ? e1->u.i_val * e2->u.i_val
			: r->code == N_DIV ? e1->u.i_val / e2->u.i_val : e1->u.i_val % e2->u.i_val);
	else
	  e->u.u_val = (r->code == N_MUL ? e1->u.u_val * e2->u.u_val
			: r->code == N_DIV ? e1->u.u_val / e2->u.u_val : e1->u.u_val % e2->u.u_val);
      }
    }
    break;
  default:
    assert (FALSE);
  }
}

static void check_assignment_types (struct type *left, struct type *right, node_t assign_node) {
  node_code_t code = assign_node->code;
  pos_t pos = assign_node->pos;
  
  if (arithmetic_type_p (left)) {
    if (! arithmetic_type_p (right)
	&& (left->mode != TM_BASIC || left->u.basic_type != TP_BOOL || right->mode != TM_PTR)) {
      print_error (pos, (code == N_CALL ? "incompatible argument type for arithemtic type parameter\n"
			 : code == N_RETURN ? "incompatible return-expr type in function returning an arithemtic value\n"
			 : "incompatible types in assignment to an arithemtic type lvalue\n"));
    }
  } else if (left->mode == TM_STRUCT || left->mode == TM_UNION) {
    if ((right->mode != TM_STRUCT && right->mode != TM_UNION)
	|| ! compatible_types_p (left, right, TRUE)) {
      print_error (pos, (code == N_CALL ? "incompatible argument type for struct/union type parameter\n"
			 : code == N_RETURN ? "incompatible return-expr type in function returning a struct/union\n"
			 : "incompatible types in assignment to struct/union\n"));
    }
  } else if (left->mode == TM_PTR) {
    if (right->mode != TM_PTR
	|| (! compatible_types_p (left->u.ptr_type, right->u.ptr_type, TRUE)
	    && ! void_ptr_p (left) && ! void_ptr_p (right))) {
      print_error (pos, (code == N_CALL ? "incompatible argument type for pointer type parameter\n"
			 : code == N_RETURN ? "incompatible return-expr type in function returning a pointer\n"
			 : "incompatible types in assignment to a pointer\n"));
    } else if (right->u.ptr_type->type_qual.atomic_p) {
      print_error (pos, (code == N_CALL ? "passing a pointer of an atomic type\n"
			 : code == N_RETURN ? "returning a pointer of an atomic type\n"
			 : "assignment of pointer of an atomic type\n"));
    } else if (! type_qual_subset_p (&right->u.ptr_type->type_qual, &left->u.ptr_type->type_qual)) {
      print_error (pos, (code == N_CALL ? "discarding type qualifiers in passing argument\n"
			 : code == N_RETURN ? "return discards a type qualifier from a pointer\n"
			 : "assignment discards a type qualifier from a pointer\n"));
    }
  }
}

DEF_HTAB (case_t);
static HTAB (case_t) *case_tab;

static unsigned case_hash (case_t el) {
  node_t case_expr = DLIST_HEAD (node_t, el->case_node->ops);
  struct expr *expr;
  
  assert (el->case_node->code == N_CASE);
  expr = case_expr->attr;
  assert (expr->const_p);
  if (signed_integer_type_p (expr->type))
    return mum_hash (&expr->u.i_val, sizeof (expr->u.i_val), 0x42);
  return mum_hash (&expr->u.u_val, sizeof (expr->u.u_val), 0x42);
}

static int case_eq (case_t el1, case_t el2) {
  node_t case_expr1 = DLIST_HEAD (node_t, el1->case_node->ops);
  node_t case_expr2 = DLIST_HEAD (node_t, el2->case_node->ops);
  struct expr *expr1, *expr2;
  
  assert (el1->case_node->code == N_CASE && el2->case_node->code == N_CASE);
  expr1 = case_expr1->attr; expr2 = case_expr2->attr;
  assert (expr1->const_p && expr2->const_p);
  assert (signed_integer_type_p (expr1->type) == signed_integer_type_p (expr2->type));
  if (signed_integer_type_p (expr1->type))
    return expr1->u.i_val == expr2->u.i_val;
  return expr1->u.u_val == expr2->u.u_val;
}

static node_t curr_func_def, curr_loop, curr_loop_switch;

 static int check (node_t r, node_t context) {
  node_t op1, op2;
  struct expr *e = NULL, *e1, *e2;
  struct type t, *t1, *t2;
  
  switch (r->code) {
  case N_IGNORE: case N_STAR: case N_FIELD_ID:
    break; /* do nothing */
  case N_LIST: {
    for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
      check (n, r);
    break;
  }
  case N_I:
  case N_L:
    e = create_basic_type_expr (r, r->code == N_I ? TP_INT : TP_LONG); e->const_p = TRUE; e->u.i_val = r->u.l;
    break;
  case N_LL:
    e = create_basic_type_expr (r, TP_LONG_LONG); e->const_p = TRUE; e->u.i_val = r->u.ll;
    break;
  case N_U:
  case N_UL:
    e = create_basic_type_expr (r, r->code == N_U ? TP_UINT : TP_ULONG); e->const_p = TRUE; e->u.u_val = r->u.ul;
    break;
  case N_ULL:
    e = create_basic_type_expr (r, TP_ULONG_LONG); e->const_p = TRUE; e->u.u_val = r->u.ull;
    break;
  case N_F:
    e = create_basic_type_expr (r, TP_FLOAT); e->const_p = TRUE; e->u.d_val = r->u.f;
    break;
  case N_D:
    e = create_basic_type_expr (r, TP_DOUBLE); e->const_p = TRUE; e->u.d_val = r->u.d;
    break;
  case N_LD:
    e = create_basic_type_expr (r, TP_LONG_DOUBLE); e->const_p = TRUE; e->u.d_val = r->u.ld;
    break;
  case N_CH:
    e = create_basic_type_expr (r, TP_CHAR); e->const_p = TRUE;
    if (char_is_signed_p ())
      e->u.i_val = r->u.ch;
    else
      e->u.u_val = r->u.ch;
    break;
  case N_STR: {
    struct arr_type *arr_type;
    
    e = create_expr (r); e->lvalue_node = r;
    e->type->mode = TM_ARR; e->type->pos_node = r;
    e->type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
    clear_type_qual (&arr_type->ind_type_qual); arr_type->static_p = FALSE;
    arr_type->el_type = create_type (NULL); arr_type->el_type->pos_node = r;
    arr_type->el_type->mode = TM_BASIC; arr_type->el_type->u.basic_type = TP_CHAR;
    break;
  }
  case N_ID: {
    node_t aux_node = NULL;
    
    op1 = find_def (S_REGULAR, r, curr_scope, &aux_node); e = create_expr (r);
    if (op1 == NULL) {
      print_error (r->pos, "undeclared identifier %s\n", r->u.s);
    } else if (op1->code == N_IGNORE) {
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    } else if (op1->code == N_SPEC_DECL) {
      struct decl *decl = op1->attr;
      
      if (decl->decl_spec.typedef_p) {
	print_error (r->pos, "typedef name %s as an operand\n", r->u.s);
      }
      *e->type = *decl->decl_spec.type;
      e->lvalue_node = op1;
    } else if (op1->code == N_FUNC_DEF) {
      struct decl *decl = op1->attr;

      assert (decl->decl_spec.type->mode == TM_FUNC);
      *e->type = *decl->decl_spec.type;
    } else {
      assert (op1->code == N_ENUM_CONST && aux_node && aux_node->code == N_ENUM);
      e->type->mode = TM_ENUM; e->type->pos_node = r; e->type->u.tag_type = aux_node;
      e->const_p = TRUE; e->u.i_val = ((struct enum_value *) op1->attr)->val;
    }
    break;
  }
  case N_COMMA:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r); e = create_expr (r);
    *e->type = *e2->type;
    break;
  case N_ANDAND: case N_OROR:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1) || ! scalar_type_p (t2)) {
      print_error (r->pos, "invalid operand types of %s\n", r->code == N_ANDAND ? "&&" : "||");
    } else if (e1->const_p) {
      int v;
      
      if (floating_type_p (t1))
	v = e1->u.d_val != 0.0;
      else if (signed_integer_type_p (t1))
	v = e1->u.i_val != 0;
      else
	v = e1->u.u_val != 0;
      if (v && r->code == N_OROR) {
	e->const_p = TRUE;
	e->u.i_val = v;
      } else if (! v && r->code == N_ANDAND) {
	e->const_p = TRUE;
	e->u.i_val = v;
      } else if (e2->const_p) {
	e->const_p = TRUE;
	if (floating_type_p (t2))
	  v = e2->u.d_val != 0.0;
	else if (signed_integer_type_p (t2))
	  v = e2->u.i_val != 0;
	else
	  v = e2->u.u_val != 0;
	 e->u.i_val = v;
      }
    }
    break;
  case N_EQ: case N_NE: case N_LT: case N_LE: case N_GT: case N_GE:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode == TM_PTR && t2->mode == TM_PTR) {
      if (! compatible_types_p (t1, t2, TRUE)
	  && ((r->code != N_EQ && r->code != N_NE)
	      || (! void_ptr_p (t1) && ! void_ptr_p (t2)
		  && ! null_const_p (e1, t1) && ! null_const_p (e2, t2)))) {
	print_error (r->pos, "incompatible pointer types in comparison\n");
      } else if ((t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p)
		 && ((r->code != N_EQ && r->code != N_NE)
		     || ! null_const_p (e1, t1) && ! null_const_p (e2, t2))) {
	print_error (r->pos, "pointer to atomic type as a comparison operand\n");
      } else if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	e->u.i_val = (r->code == N_EQ ? e1->u.u_val == e2->u.u_val : r->code == N_NE ? e1->u.u_val != e2->u.u_val
		      : r->code == N_LT ? e1->u.u_val < e2->u.u_val : r->code == N_LE ? e1->u.u_val <= e2->u.u_val
		      : r->code == N_GT ? e1->u.u_val > e2->u.u_val : e1->u.u_val >= e2->u.u_val);
      }
    } else if (arithmetic_type_p (t1) && arithmetic_type_p (t2)) {
      if (e1->const_p && e2->const_p) {
	t = arithmetic_conversion (t1, t2); convert_value (e1, &t); convert_value (e2, &t);
	e->const_p = TRUE;
	if (floating_type_p (&t))
	  e->u.i_val = (r->code == N_EQ ? e1->u.d_val == e2->u.d_val : r->code == N_NE ? e1->u.d_val != e2->u.d_val
			: r->code == N_LT ? e1->u.d_val < e2->u.d_val : r->code == N_LE ? e1->u.d_val <= e2->u.d_val
			: r->code == N_GT ? e1->u.d_val > e2->u.d_val : e1->u.d_val >= e2->u.d_val);
	else if (signed_integer_type_p (&t))
	  e->u.i_val = (r->code == N_EQ ? e1->u.i_val == e2->u.i_val : r->code == N_NE ? e1->u.i_val != e2->u.i_val
			: r->code == N_LT ? e1->u.i_val < e2->u.i_val : r->code == N_LE ? e1->u.i_val <= e2->u.i_val
			: r->code == N_GT ? e1->u.i_val > e2->u.i_val : e1->u.i_val >= e2->u.i_val);
	else
	  e->u.i_val = (r->code == N_EQ ? e1->u.u_val == e2->u.u_val : r->code == N_NE ? e1->u.u_val != e2->u.u_val
			: r->code == N_LT ? e1->u.u_val < e2->u.u_val : r->code == N_LE ? e1->u.u_val <= e2->u.u_val
			: r->code == N_GT ? e1->u.u_val > e2->u.u_val : e1->u.u_val >= e2->u.u_val);
      }
    } else {
      print_error (r->pos, "invalid types of comparison operands\n");
    }
    break;
  case N_BITWISE_NOT:
  case N_NOT:
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_BITWISE_NOT && ! integer_type_p (t1)) {
      print_error (r->pos, "bitwise-not operand should be of an integer type\n");
    } else if (r->code == N_NOT && ! scalar_type_p (t1)) {
      print_error (r->pos, "not operand should be of a scalar type\n");
    } else if (r->code == N_BITWISE_NOT) {
      t = integer_promotion (t1); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p) {
	convert_value (e1, &t);
	e->const_p = TRUE;
	if (signed_integer_type_p (&t))
	  e->u.i_val = ~e1->u.i_val;
	else
	  e->u.u_val = ~e1->u.u_val;
      }
    } else if (e1->const_p) {
      e->const_p = TRUE;
      if (floating_type_p (t1))
	e->u.i_val = e1->u.d_val == 0.0;
      else if (signed_integer_type_p (t1))
	e->u.i_val = e1->u.i_val == 0;
      else
	e->u.i_val = e1->u.u_val == 0;
    }
    break;
  case N_INC: case N_DEC: case N_POST_INC: case N_POST_DEC: {
    struct expr saved_expr;
    
    process_unop (r, &op1, &e1, &t1, NULL);
    saved_expr = *e1; t1 = e1->type = adjust_type (e1->type);
    get_one_node (&op2, &e2, &t2);
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    t2 = ((struct expr *) r->attr)->type; *e1 = saved_expr; t1 = e1->type;
    goto assign;
    break;
  }
  case N_ADD: case N_SUB:
    if (DLIST_NEXT (node_t, DLIST_HEAD (node_t, r->ops)) == NULL) { /* unary */
      process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      if (! arithmetic_type_p (t1)) {
	print_error (r->pos, "unary + or - operand should be of an arithmentic type\n");
      } else {
	if (e1->const_p)
	  e->const_p = TRUE;
	if (floating_type_p (t1)) {
	  e->type->u.basic_type = t1->u.basic_type;
	  if (e->const_p)
	    e->u.d_val = (r->code == N_ADD ? +e1->u.d_val : -e1->u.d_val);
	} else {
	  t = integer_promotion (t1); e->type->u.basic_type = t.u.basic_type;
	  if (e1->const_p) {
	    convert_value (e1, &t);
	    if (signed_integer_type_p (&t)) 
	      e->u.i_val = (r->code == N_ADD ? +e1->u.i_val : -e1->u.i_val);
	    else
	      e->u.u_val = (r->code == N_ADD ? +e1->u.u_val : -e1->u.u_val);
	  }
	}
      }
      break;
    }
    /* Fall through: */
  case N_AND: case N_OR: case N_XOR: case N_LSH: case N_RSH:
  case N_MUL: case N_DIV: case N_MOD:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    break;
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN:
  case N_LSH_ASSIGN: case N_RSH_ASSIGN:
  case N_ADD_ASSIGN: case N_SUB_ASSIGN: case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN: {
    struct expr saved_expr;
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, NULL);
    saved_expr = *e1; 
    t1 = e1->type = adjust_type (e1->type); t2 = e2->type = adjust_type (e2->type);
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    t2 = ((struct expr *) r->attr)->type; *e1 = saved_expr; t1 = e1->type;
    goto assign;
    break;
  }
  case N_ASSIGN:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, NULL);
    t2 = e2->type = adjust_type (e2->type);
  assign:
    e = create_expr (r);
    if (! e1->lvalue_node) {
      print_error (r->pos, "lvalue required as left operand of assignment\n");
    }
    check_assignment_types (t1, t2, r);
    *e->type = *t1;
    break;
  case N_IND:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r); e = create_expr (r);
    e->lvalue_node = r; e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR && t1->mode != TM_ARR) {
      print_error (r->pos, "subscripted value is neither array nor pointer\n");
    } else if (t1->mode == TM_PTR) {
      *e->type = *t1->u.ptr_type;
      if (t1->u.ptr_type->incomplete_p) {
	print_error (r->pos, "pointer to incomplete type in array subscription\n");
      }
    } else {
      *e->type = *t1->u.arr_type->el_type;
      e->type->type_qual = t1->u.arr_type->ind_type_qual;
      if (e->type->incomplete_p) {
	print_error (r->pos, "array type has incomplete element type\n");
      }
    }
    if (! integer_type_p (t2)) {
      print_error (r->pos, "array subscript is not an integer\n");
    }
    break;
  case N_ADDR:
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    if (op1->code == N_DEREF) {
      node_t deref_op = DLIST_HEAD (node_t, op1->ops);
      
      *e->type = *((struct expr *) deref_op->attr)->type;
      break;
    } else if (e1->type->mode == TM_PTR && e1->type->u.ptr_type->mode == TM_FUNC) {
      *e->type = *e1->type;
      break;
    } else if (! e1->lvalue_node) {
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      print_error (r->pos, "lvalue required as unary & operand\n");
      break;
    }
    if (op1->code == N_IND) {
      t2 = create_type (t1);
    } else if (op1->code == N_ID) {
      node_t decl_node = e1->lvalue_node;
      struct decl *decl = decl_node->attr;

      if (decl->decl_spec.register_p) {
	print_error (r->pos, "address of register variable %s requested\n", op1->u.s);
      }
      t2 = create_type (decl->decl_spec.type);
    } else if (e1->lvalue_node->code == N_MEMBER) {
      node_t declarator = DLIST_EL (node_t, e1->lvalue_node->ops, 1);
      node_t width = DLIST_NEXT (node_t, declarator);
      struct decl *decl = e1->lvalue_node->attr;
      
      assert (declarator->code == N_DECL);
      if (width->code != N_IGNORE) {
	print_error (r->pos, "cannot take address of bit-field %s\n", DLIST_HEAD (node_t, declarator->ops)->u.s);
      }
      t2 = create_type (decl->decl_spec.type);
      if (op1->code == N_DEREF_FIELD && (e2 = DLIST_HEAD (node_t, op1->ops)->attr)->const_p) {
	e->const_p = TRUE;
	e->u.u_val = e2->u.u_val + decl->offset;
      }
    }
    e->type->mode = TM_PTR; e->type->u.ptr_type = t2;
    break;
  case N_DEREF:
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR) {
      print_error (r->pos, "invalid type argument of unary *\n");
    } else {
      *e->type = *t1->u.ptr_type;
    }
    break;
  case N_FIELD: case N_DEREF_FIELD: {
    symbol_t sym;
    struct decl *decl;
    
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    op2 = DLIST_NEXT (node_t, op1);
    assert (op2->code == N_ID);
    if (r->code == N_DEREF_FIELD && t1->mode == TM_PTR) {
      t1 = t1->u.ptr_type;
    }
    if (t1->mode != TM_STRUCT && t1->mode != TM_UNION) {
      print_error (r->pos, "request for member %s in something not a structure or union\n", op2->u.s);
    } else if (! symbol_find (S_REGULAR, op2, t1->u.tag_type, &sym)) {
      print_error (r->pos, "%s has no member %s\n", t1->mode == TM_STRUCT ? "struct" : "union", op2->u.s);
    } else {
      assert (sym.def_node->code == N_MEMBER);
      decl = sym.def_node->attr;
      *e->type = *decl->decl_spec.type;
      e->lvalue_node = sym.def_node;
    }
    break;
  }
  case N_COND: {
    node_t op3;
    struct expr *e3;
    struct type *t3;
    int v, first_p;
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    op3 = DLIST_NEXT (node_t, op2); check (op3, r);
    e3 = op3->attr; e3->type = adjust_type (e3->type); t3 = e3->type; e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1)) {
      print_error (r->pos, "condition should be of a scalar type\n");
      break;
    }
    if (e1->const_p) {
      if (floating_type_p (t1))
	v = e1->u.d_val != 0.0;
      else if (signed_integer_type_p (t1))
	v = e1->u.i_val != 0;
      else
	v = e1->u.u_val != 0;
    }
    if (arithmetic_type_p (t2) && arithmetic_type_p (t3)) {
      t = arithmetic_conversion (t2, t3); *e->type = t;
      if (e1->const_p) {
	if (v && e2->const_p) {
	  e->const_p = TRUE; convert_value (e2, &t); e->u = e2->u;
	} else if (! v && e3->const_p) {
	  e->const_p = TRUE; convert_value (e3, &t); e->u = e3->u;
	}
      }
      break;
    }
    if (t2->mode == TM_BASIC && t3->mode == TM_BASIC
	&& t2->u.basic_type == TP_VOID && t3->u.basic_type == TP_VOID) {
      e->type->u.basic_type = TP_VOID;
    } else if ((t2->mode == TM_STRUCT || t2->mode == TM_UNION) && (t3->mode == TM_STRUCT || t3->mode == TM_UNION)
	       && t2->u.tag_type == t3->u.tag_type) {
      *e->type = *t2;
    } else if (t2->mode != TM_PTR && t3->mode != TM_PTR) {
      print_error (r->pos, "incompatible types in true and false parts of cond-expression\n");
      break;
    } else if (compatible_types_p (t2, t3, TRUE)) {
      t = composite_type (t2->u.ptr_type, t3->u.ptr_type);
      e->type->mode = TM_PTR; e->type->pos_node = r; e->type->u.ptr_type = create_type (&t);
      e->type->u.ptr_type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual, &t3->u.ptr_type->type_qual);
      if ((t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p)
	  && ! null_const_p (e2, t2) && ! null_const_p (e3, t3)) {
	print_error (r->pos, "pointer to atomic type in true or false parts of cond-expression\n");
      }
    } else if ((first_p = void_ptr_p (t2)) || void_ptr_p (t3)) {
      e->type->mode = TM_PTR; e->type->pos_node = r;
      e->type->u.ptr_type = create_type (NULL); e->type->u.ptr_type->pos_node = r;
      if (first_p && null_const_p (e2, t2)) {
	e->type->u.ptr_type = e2->type->u.ptr_type;
      } else if (null_const_p (e3, t3)) {
	e->type->u.ptr_type = e3->type->u.ptr_type;
      } else {
	if (t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p) {
	  print_error (r->pos, "pointer to atomic type in true or false parts of cond-expression\n");
	}
	e->type->u.ptr_type->mode = TM_BASIC; e->type->u.ptr_type->u.basic_type = TP_VOID;
      }
      e->type->u.ptr_type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual, &t3->u.ptr_type->type_qual);
    } else {
      print_error (r->pos, "incompatible pointer types in true and false parts of cond-expression\n");
      break;
    }
    if (e1->const_p) {
      if (v && e2->const_p) {
	e->const_p = TRUE; e->u = e2->u;
      } else if (! v && e3->const_p) {
	e->const_p = TRUE; e->u = e3->u;
      }
    }
    break;
  }
  case N_ALIGNOF: case N_SIZEOF: {
    struct decl_spec *decl_spec;

    op1 = DLIST_HEAD (node_t, r->ops); check (op1, r);
    e = create_expr (r); e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_ALIGNOF && op1->code == N_IGNORE) {
      print_error (r->pos, "_Alignof of non-type\n");
      break;
    }
    assert (op1->code == N_TYPE);
    decl_spec = op1->attr;
    if (decl_spec->type->incomplete_p) {
      print_error (r->pos, "%s of incomplete type requested\n", r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else if (decl_spec->type->mode == TM_FUNC) {
      print_error (r->pos, "%s of function type requested\n", r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else {
      e->const_p = TRUE;
      e->u.i_val = r->code == N_SIZEOF ? type_size (decl_spec->type) : type_align  (decl_spec->type);
    }
    break;
  }
  case N_EXPR_SIZEOF:
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->incomplete_p) {
      print_error (r->pos, "sizeof of incomplete type requested\n");
    } else if (t1->mode == TM_FUNC) {
      print_error (r->pos, "sizeof of function type requested\n");
    } else if (e1->lvalue_node && e1->lvalue_node->code == N_MEMBER) {
      node_t declarator = DLIST_EL (node_t, e1->lvalue_node->ops, 1);
      node_t width = DLIST_NEXT (node_t, declarator);
      
      assert (declarator->code == N_DECL);
      if (width->code != N_IGNORE) {
	print_error (r->pos, "sizeof applied to a bit-field %s\n", DLIST_HEAD (node_t, declarator->ops)->u.s);
      }
    }
    e->const_p = TRUE;
    e->u.i_val = type_size (t1);
    break;
  case N_CAST: {
    struct decl_spec *decl_spec;
    int void_p;
    
    process_type_bin_ops (r, &op1, &op2, &e2, &t2, r); e = create_expr (r);
    assert (op1->code == N_TYPE);
    decl_spec = op1->attr;
    *e->type = *decl_spec->type;
    void_p = decl_spec->type->mode == TM_BASIC && decl_spec->type->u.basic_type == TP_VOID;
    if (! void_p && ! scalar_type_p (decl_spec->type)) {
      print_error (r->pos, "conversion to non-scalar type requested\n");
    } else if (! scalar_type_p (t2)) {
      print_error (r->pos, "conversion of non-scalar value requested\n");
    } else if (t2->mode == TM_PTR && floating_type_p (decl_spec->type)) {
      print_error (r->pos, "conversion of a pointer to floating value requested\n");
    } else if (decl_spec->type->mode == TM_PTR && floating_type_p (t2)) {
      print_error (r->pos, "conversion of floating point value to a pointer requested\n");
    } else if (e2->const_p && ! void_p) {
#define CONV(TP, cast, mto, mfrom) case TP: e->u.mto = (cast) e2->u.mfrom; break;
#define BASIC_FROM_CONV(mfrom)										\
      switch (decl_spec->type->u.basic_type) {								\
	CONV (TP_BOOL, mir_bool, u_val, mfrom) CONV (TP_UCHAR, mir_uchar, u_val, mfrom);		\
	CONV (TP_USHORT, mir_ushort, u_val, mfrom) CONV (TP_UINT, mir_uint, u_val, mfrom);		\
	CONV (TP_ULONG, mir_ulong, u_val, mfrom) CONV (TP_ULONG_LONG, mir_ulong_long, u_val, mfrom);	\
	CONV (TP_SCHAR, mir_char, i_val, mfrom);							\
	CONV (TP_SHORT, mir_short, i_val, mfrom) CONV (TP_INT, mir_int, i_val, mfrom);			\
	CONV (TP_LONG, mir_long, i_val, mfrom) CONV (TP_LONG_LONG, mir_long_long, i_val, mfrom);	\
	CONV (TP_FLOAT, mir_float, d_val, mfrom) CONV (TP_DOUBLE, mir_double, d_val, mfrom);		\
	CONV (TP_LONG_DOUBLE, mir_long_double, d_val, mfrom);						\
      case TP_CHAR:											\
	if (char_is_signed_p ())									\
	  e->u.i_val = (mir_char) e2->u.mfrom;								\
	else												\
	  e->u.u_val = (mir_char) e2->u.mfrom;								\
	break;												\
      default:												\
	assert (FALSE);											\
      }
      
#define BASIC_TO_CONV(cast, mto)									\
      switch (t2->u.basic_type) {									\
      case TP_BOOL: case TP_UCHAR: case TP_USHORT: case TP_UINT: case TP_ULONG: case TP_ULONG_LONG:	\
	e->u.mto = (cast) e2->u.u_val; break;								\
      case TP_CHAR:											\
	if (! char_is_signed_p ()) {									\
	  e->u.mto = (cast) e2->u.u_val; break;								\
	}												\
	/* Fall through: */										\
      case TP_SCHAR: case TP_SHORT: case TP_INT: case TP_LONG: case TP_LONG_LONG:			\
	e->u.mto = (cast) e2->u.i_val; break;								\
      case TP_FLOAT: case TP_DOUBLE: case TP_LONG_DOUBLE:						\
	e->u.mto = (cast) e2->u.d_val; break;								\
      default:												\
	assert (FALSE);											\
      }

      e->const_p = TRUE;
      if (decl_spec->type->mode == t2->mode && (t2->mode == TM_PTR || t2->mode == TM_ENUM)) {
	e->u = e2->u;
      } else if (t2->mode == TM_PTR) {
	if (decl_spec->type->mode == TM_ENUM) {
	  e->u.i_val = (mir_int) e2->u.u_val;
	} else {
	  BASIC_FROM_CONV (u_val);
	}
      } else if (t2->mode == TM_ENUM) {
	if (decl_spec->type->mode == TM_PTR) {
	  e->u.u_val = (mir_size_t) e2->u.i_val;
	} else {
	  BASIC_FROM_CONV (i_val);
	}
      } else if (decl_spec->type->mode == TM_PTR) {
        BASIC_TO_CONV (mir_size_t, u_val);
      } else if (decl_spec->type->mode == TM_ENUM) {
        BASIC_TO_CONV (mir_int, i_val);
      } else {
	switch (t2->u.basic_type) {
	case TP_BOOL: case TP_UCHAR: case TP_USHORT: case TP_UINT: case TP_ULONG: case TP_ULONG_LONG:
	  BASIC_FROM_CONV (u_val); break;
	case TP_CHAR:
	  if (! char_is_signed_p ()) {
	    BASIC_FROM_CONV (u_val); break;
	  }
	  /* Fall through: */
	case TP_SCHAR: case TP_SHORT: case TP_INT: case TP_LONG: case TP_LONG_LONG:
	  BASIC_FROM_CONV (i_val); break;
	case TP_FLOAT: case TP_DOUBLE: case TP_LONG_DOUBLE:
	  BASIC_FROM_CONV (d_val); break;
	default:
	  assert (FALSE);
	}
      }
#undef CONV
#undef BASIC_FROM_CONV
#undef BASIC_TO_CONV
    }
    break;
  }
  case N_COMPOUND_LITERAL: {
    node_t list;
    struct decl_spec *decl_spec;
    
    op1 = DLIST_HEAD (node_t, r->ops); list = DLIST_NEXT (node_t, op1);
    assert (op1->code == N_TYPE && list->code == N_LIST);
    check (op1, r); decl_spec = op1->attr; t1 = decl_spec->type; check (list, r);
    if (t1->incomplete_p && (t1->mode != TM_ARR || t1->u.arr_type->size != N_IGNORE
			     || t1->u.arr_type->el_type->incomplete_p)) {
      print_error (r->pos, "compound literal of incomplete type\n");
      break;
    }
    check_initializer (t1, list, decl_spec->static_p || decl_spec->thread_local_p, FALSE);
    e = create_expr (r); e->lvalue_node = r;
    *e->type = *t1;
    break;
  }
  case N_CALL: {
    struct func_type *func_type;
    struct type *ret_type;
    node_t param_list, start_param, param, arg_list, arg;
    struct decl_spec *decl_spec;
    
    op1 = DLIST_HEAD (node_t, r->ops);
    check (op1, r); e1 = op1->attr; t1 = e1->type;
    if (t1->mode != TM_PTR || (t1 = t1->u.ptr_type)->mode != TM_FUNC) {
      print_error (r->pos, "called object is not a function or function pointer\n");
      break;
    }
    func_type = t1->u.func_type;
    ret_type = func_type->ret_type;
    e = create_expr (r); *e->type = *ret_type;
    if ((ret_type->mode != TM_BASIC || ret_type->u.basic_type != TP_VOID) && ret_type->incomplete_p) {
      print_error (r->pos, "function return type is incomplete\n");
    }
    param_list = func_type->param_list; param = start_param = DLIST_HEAD (node_t, param_list->ops);
    arg_list = DLIST_NEXT (node_t, op1);
    if (void_param_p (start_param)) { /* f(void) */
      if (DLIST_HEAD (node_t, arg_list->ops) != NULL)
	print_error (arg->pos, "too many arguments\n");
      break;
    }
    for (node_t arg = DLIST_HEAD (node_t, arg_list->ops); arg != NULL; arg = DLIST_NEXT (node_t, arg)) {
      check (arg, r); e2 = arg->attr;
      if (start_param == NULL || start_param->code == N_ID)
	continue;  /* no params or ident list */
      if (param == NULL) {
	if (! func_type->dots_p)
	  print_error (arg->pos, "too many arguments\n");
	start_param = NULL; /* ignore the rest args */
	continue;
      }
      assert (param->code == N_SPEC_DECL || param->code == N_TYPE);
      decl_spec = param->code == N_TYPE ? param->attr : &((struct decl *) param->attr)->decl_spec;
      check_assignment_types (decl_spec->type, e2->type, r);
      param = DLIST_NEXT (node_t, param);
    }
    if (param != NULL) {
      print_error (r->pos, "too few arguments\n");
    }
    break;
  }
  case N_GENERIC: {
    node_t list, ga, ga2, type_name, type_name2, expr;
    node_t default_case = NULL, ga_case = NULL;
    struct decl_spec *decl_spec;
    
    op1 = DLIST_HEAD (node_t, r->ops);
    check (op1, r); e1 = op1->attr; t = *e1->type;
    if (integer_type_p (&t))
      t = integer_promotion (&t);
    list = DLIST_NEXT (node_t, op1);
    for (ga = DLIST_HEAD (node_t, list->ops); ga != NULL; ga = DLIST_NEXT (node_t, ga)) {
      assert (ga->code == N_GENERIC_ASSOC);
      type_name = DLIST_HEAD (node_t, ga->ops); expr = DLIST_NEXT (node_t, type_name);
      check (type_name, r); check (expr, r);
      if (type_name->code == N_IGNORE) {
	if (default_case)
	  print_error (ga->pos, "duplicate default case in _Generic\n");
	default_case = ga;
	continue;
      }
      assert (type_name->code == N_TYPE);
      decl_spec = type_name->attr;
      if (decl_spec->type->incomplete_p) {
	print_error (ga->pos, "_Generic case has incomplete type\n");
      } else if (compatible_types_p (&t, decl_spec->type, TRUE)) {
	if (ga_case)
	  print_error (ga_case->pos,
		       "_Generic expr type is compatible with more than one generic association type\n");
	ga_case = ga;
      } else {
	for (ga2 = DLIST_HEAD (node_t, list->ops); ga2 != ga; ga2 = DLIST_NEXT (node_t, ga2)) {
	  type_name2 = DLIST_HEAD (node_t, ga2->ops);
	  if (type_name2->code != N_IGNORE
	      && ! (t2 = ((struct decl_spec *) type_name2->attr)->type)->incomplete_p
	      && compatible_types_p (t2, decl_spec->type, TRUE)) {
	    print_error (ga->pos, "two or more compatible generic association types\n");
	    break;
	  }
	}
      }
    }
    e = create_expr (r);
    if (default_case == NULL && ga_case == NULL) {
      print_error (r->pos, "expression type is not compatible with generic association\n");
    } else { /* make compatible association a list head  */
      if (ga_case == NULL)
	ga_case = default_case;
      DLIST_REMOVE (node_t, list->ops, ga_case);
      DLIST_PREPEND (node_t, list->ops, ga_case);
      t2 = e->type;
      *e = *(struct expr *) DLIST_EL (node_t, ga_case->ops, 1)->attr;
      *t2 = *e->type; e->type = t2;
	
    }
    break;
  }
  case N_SPEC_DECL: {
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t initializer = DLIST_NEXT (node_t, declarator);
    node_t unshared_specs = specs->code != N_SHARE ? specs : DLIST_HEAD (node_t, specs->ops);
    struct decl_spec decl_spec = check_decl_spec (unshared_specs, r);
    
    if (declarator->code != N_IGNORE) {
      create_decl (curr_scope, r, decl_spec, NULL, initializer);
    } else if (decl_spec.type->mode == TM_STRUCT || decl_spec.type->mode == TM_UNION) {
      if (DLIST_HEAD (node_t, decl_spec.type->u.tag_type->ops)->code != N_ID)
	print_error (r->pos, "unnamed struct/union with no instances\n");
    } else if (decl_spec.type->mode != TM_ENUM) {
      print_error (r->pos, "useless declaration\n");
    }
    /* We have at least one enum constant according to the syntax. */
    break;
  }
  case N_ST_ASSERT: {
    int ok_p;
    
    op1 = DLIST_HEAD (node_t, r->ops); check (op1, r); e1 = op1->attr; t1 = e1->type;
    if (! e1->const_p) {
      print_error (r->pos, "expression in static assertion is not constant\n");
    } else if (! integer_type_p (t1)) {
      print_error (r->pos, "expression in static assertion is not an integer\n");
    } else {
      if (signed_integer_type_p (t1))
	ok_p = e1->u.i_val != 0;
      else
	ok_p = e1->u.u_val != 0;
      if (! ok_p) {
	assert (DLIST_NEXT (node_t, op1) != NULL && DLIST_NEXT (node_t, op1)->code == N_STR);
	print_error (r->pos, "static assertion failed: \"%s\"\n", DLIST_NEXT (node_t, op1)->u.s);
      }
    }
    break;
  }
  case N_MEMBER: {
    struct type *type;
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t const_expr = DLIST_NEXT (node_t, declarator);
    struct decl_spec decl_spec = check_decl_spec (specs, r);
    
    create_decl (curr_scope, r, decl_spec, const_expr, NULL);
    type = ((struct decl *) r->attr)->decl_spec.type;
    if (const_expr->code != N_IGNORE) {
      struct expr *cexpr;
      
      check (const_expr, r); cexpr = const_expr->attr;
      if (cexpr != NULL) {
	if (type->type_qual.atomic_p)
	  print_error (const_expr->pos, "bit field with _Atomic\n");
	if (! cexpr->const_p) {
	  print_error (const_expr->pos, "bit field is not a constant expr\n");
	} else if (! integer_type_p (type) && (type->mode != TM_BASIC || type->u.basic_type != T_BOOL)) {
	  print_error (const_expr->pos,
		       "bit field type should be _Bool, a signed integer, or an unsigned integer type\n");
	} else if (! integer_type_p (cexpr->type)
		   && (cexpr->type->mode != TM_BASIC || cexpr->type->u.basic_type != TP_BOOL)) {
	  print_error (const_expr->pos, "bit field width is not of an integer type\n");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  print_error (const_expr->pos, "bit field width is negative\n");
	} else if (cexpr->u.i_val == 0  && declarator->code == N_DECL) {
	  print_error (const_expr->pos, "zero bit field width for %s\n", DLIST_HEAD (node_t, declarator->ops)->u.s);
	} else if ((! signed_integer_type_p (cexpr->type) && cexpr->u.u_val > int_bit_size (cexpr->type))
		   || (signed_integer_type_p (cexpr->type) && cexpr->u.i_val > int_bit_size (cexpr->type))) {
	  print_error (const_expr->pos, "bit field width exceeds its type\n");
	}
      }
    }
    if (declarator->code == N_IGNORE) {
      print_error (r->pos, "no declarator in struct or union declaration\n");
    } else {
      node_t id = DLIST_HEAD (node_t, declarator->ops);

      if (type->mode == TM_FUNC) {
	print_error (id->pos, "field %s is declared as a function\n", id->u.s);
      } else if (type->incomplete_p) {
	/* el_type is checked on completness in N_ARR */
	if (type->mode != TM_ARR || type->u.arr_type->size->code != N_IGNORE)
	  print_error (id->pos, "field %s has incomplete type\n", id->u.s);
      }
    }
    break;
  }
  case N_INIT: {
    node_t des_list = DLIST_HEAD (node_t, r->ops), initializer = DLIST_NEXT (node_t, des_list);
    check (des_list, r); check (initializer, r);
    break;
  }
  case N_FUNC_DEF: {
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t declarations = DLIST_NEXT (node_t, declarator);
    node_t block = DLIST_NEXT (node_t, declarations);
    struct decl_spec decl_spec = check_decl_spec (specs, r);
    node_t p, next_p, param_list, param_id, param_declarator, func;
    symbol_t sym;
    
    create_node_scope (block); func_block_scope = curr_scope;
    curr_func_def = r; curr_switch = curr_loop = curr_loop_switch = NULL;
    create_decl (NULL, r, decl_spec, NULL, NULL);
    curr_scope = func_block_scope;
    check (declarations, r);
    /* Process parameter identifier list:  */
    assert (declarator->code == N_DECL);
    func = DLIST_HEAD (node_t, DLIST_EL (node_t, declarator->ops, 1)->ops);
    assert (func != NULL && func->code == N_FUNC);
    param_list = DLIST_HEAD (node_t, func->ops);
    for (p = DLIST_HEAD (node_t, param_list->ops); p != NULL; p = next_p) {
      next_p = DLIST_NEXT (node_t, p);
      if (p->code != N_ID)
	break;
      DLIST_REMOVE (node_t, param_list->ops, p);
      if (! symbol_find (S_REGULAR, p, curr_scope, &sym)) {
	print_error (p->pos, "parameter %s has no type\n", p->u.s);
      } else {
	node_t decl = sym.def_node;
	struct decl_spec decl_spec;
	
	assert (decl->code == N_SPEC_DECL);
	DLIST_REMOVE (node_t, declarations->ops, decl);
	DLIST_APPEND (node_t, param_list->ops, decl);
	param_declarator = DLIST_EL (node_t, decl->ops, 1);
	assert (param_declarator->code == N_DECL);
	param_id = DLIST_HEAD (node_t, param_declarator->ops);
	if (DLIST_NEXT (node_t, param_declarator)->code != N_IGNORE) {
	  print_error (p->pos, "initialized parameter %s\n", param_id->u.s);
	}
	decl_spec = ((struct decl *) decl->attr)->decl_spec;
	if (decl_spec.typedef_p || decl_spec.extern_p || decl_spec.static_p
	    || decl_spec.auto_p || decl_spec.thread_local_p) {
	  print_error (param_id->pos, "storage specifier in a function parameter %s\n", param_id->u.s);
	}
      }
    }
    /* Process the rest declarations: */
    for (p = DLIST_HEAD (node_t, declarations->ops); p != NULL; p = DLIST_NEXT (node_t, p)) {
      if (p->code == N_ST_ASSERT)
	continue;
      assert (p->code == N_SPEC_DECL);
      param_declarator = DLIST_EL (node_t, p->ops, 1);
      assert (param_declarator->code == N_DECL);
      param_id = DLIST_HEAD (node_t, param_declarator->ops);
      assert (param_id->code == N_ID);
      print_error (param_id->pos, "declaration for parameter %s but no such parameter\n", param_id->u.s);
    }
    check (block, r);
    /* Process all gotos: */
    for (size_t i = 0; i < VARR_LENGTH (node_t, gotos); i++) {
      symbol_t sym;
      node_t n = VARR_GET (node_t, gotos, i);
      node_t id = DLIST_NEXT (node_t, DLIST_HEAD (node_t, n->ops));

      if (! symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	print_error (id->pos, "undefined label %s\n", id->u.s);
      } else {
	n->attr = sym.def_node;
      }
    }
    VARR_TRUNC (node_t, gotos, 0);
    assert (curr_scope == NULL); /* set up in the block */
    func_block_scope = NULL;
    break;
  }
  case N_TYPE: {
    struct type *type;
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t abstract_declarator = DLIST_NEXT (node_t, specs);
    struct decl_spec decl_spec = check_decl_spec (specs, r); /* only spec_qual_list here */
    
    type = check_declarator (abstract_declarator, FALSE);
    assert (DLIST_HEAD (node_t, abstract_declarator->ops)->code == N_IGNORE);
    decl_spec.type = append_type (type, decl_spec.type);
    r->attr = reg_malloc (sizeof (struct decl_spec));
    *((struct decl_spec *) r->attr) = decl_spec;
    check_type (((struct decl_spec *) r->attr)->type, 0, FALSE);
    check_decl_align (r->attr);
    break;
  }
  case N_BLOCK: {
    if (curr_scope != r)
      create_node_scope (r); /* it happens if it is the top func block */
    check (DLIST_HEAD (node_t, r->ops), r);
    curr_scope = ((struct node_scope *) r->attr)->scope;
    break;
  }
  case N_IF: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    node_t if_stmt = DLIST_NEXT (node_t, expr);
    node_t else_stmt = DLIST_NEXT (node_t, if_stmt);
 
    check_labels (labels, r); check (expr, r); e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      print_error (expr->pos, "if-expr should be of a scalar type\n");
    }
    check (if_stmt, r); check (else_stmt, r);
    break;
  }
  case N_SWITCH: {
    node_t saved_switch = curr_switch;
    node_t saved_loop_switch = curr_loop_switch;
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    node_t stmt = DLIST_NEXT (node_t, expr);
    struct type t, *type;
    struct switch_attr *switch_attr;
    case_t el;
    
    check_labels (labels, r); check (expr, r); type = ((struct expr *) expr->attr)->type;
    if (! integer_type_p (type)) {
      init_type (&t); t.mode = TM_BASIC; t.u.basic_type = TP_INT;
      print_error (expr->pos, "switch-expr is of non-integer type\n");
    } else {
      t = integer_promotion (type);
    }
    curr_switch = curr_loop_switch = r;
    switch_attr = curr_switch->attr = reg_malloc (sizeof (struct switch_attr));
    switch_attr->type = t;
    DLIST_INIT (case_t, ((struct switch_attr *) curr_switch->attr)->case_labels);
    check (stmt, r);
    for (case_t c = DLIST_HEAD (case_t, switch_attr->case_labels); c != NULL; c = DLIST_NEXT (case_t, c)) {
      if (c->case_node->code == N_DEFAULT)
	continue;
      if (HTAB_DO (case_t, case_tab, c, HTAB_FIND, el)) {
	print_error (c->case_node->pos, "duplicate case value\n");
	continue;
      }
      HTAB_DO (case_t, case_tab, c, HTAB_INSERT, el);
    }
    HTAB_CLEAR (case_t, case_tab);
    curr_switch = saved_switch; curr_loop_switch = saved_loop_switch;
    break;
  }
  case N_DO:
  case N_WHILE: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    node_t stmt = DLIST_NEXT (node_t, expr);
    node_t saved_loop = curr_loop;
    node_t saved_loop_switch = curr_loop_switch;

    check_labels (labels, r); check (expr, r); e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      print_error (expr->pos, "while-expr should be of a scalar type\n");
    }
    curr_loop = curr_loop_switch = r; check (stmt, r); curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
    break;
  }
  case N_FOR: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t init = DLIST_NEXT (node_t, labels);
    node_t cond = DLIST_NEXT (node_t, init);
    node_t iter = DLIST_NEXT (node_t, cond);
    node_t stmt = DLIST_NEXT (node_t, iter);
    struct decl *decl;
    node_t saved_loop = curr_loop;
    node_t saved_loop_switch = curr_loop_switch;
    
    check_labels (labels, r);
    create_node_scope (r); curr_loop = curr_loop_switch = r; check (init, r);
    if (init->code == N_LIST) {
      for (node_t spec_decl = DLIST_HEAD (node_t, init->ops);
	   spec_decl != NULL;
	   spec_decl = DLIST_NEXT (node_t, spec_decl)) {
	assert (spec_decl->code == N_SPEC_DECL);
	decl = spec_decl->attr;
	if (decl->decl_spec.typedef_p || decl->decl_spec.extern_p
	    || decl->decl_spec.static_p || decl->decl_spec.thread_local_p) {
	  print_error (spec_decl->pos, "wrong storage specifier of for-loop initial declaration\n");
	  break;
	}
      }
    }
    check (cond, r); // checking, promotion ???
    check (iter, r);
    check (stmt, r);
    curr_scope = ((struct node_scope *) r->attr)->scope;
    curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
    break;
  }
  case N_GOTO: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t id = DLIST_NEXT (node_t, labels);
    
    check_labels (labels, r);
    VARR_PUSH (node_t, gotos, r);
    break;
  }
  case N_CONTINUE:
  case N_BREAK: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    
    if (r->code == N_BREAK && curr_loop_switch == NULL) {
      print_error (r->pos, "break statement not within loop or switch\n");
    } else if (r->code == N_CONTINUE && curr_loop == NULL) {
      print_error (r->pos, "continue statement not within a loop\n");
    }
    check_labels (labels, r);
    break;
  }
  case N_RETURN: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    struct decl *decl = curr_func_def->attr;
    struct type *ret_type, *type = decl->decl_spec.type;

    assert (type->mode == TM_FUNC);
    check_labels (labels, r); check (expr, r);
    ret_type = type->u.func_type->ret_type;
    if (expr->code != N_IGNORE && ret_type->mode == TM_BASIC && ret_type->u.basic_type == TP_VOID) {
      print_error (r->pos, "return with a value in function returning void\n");
    } else if (expr->code == N_IGNORE && (ret_type->mode != TM_BASIC || ret_type->u.basic_type != TP_VOID)) {
      print_error (r->pos, "return with no value in function returning non-void\n");
    } else if (expr->code != N_IGNORE) {
      check_assignment_types (ret_type, ((struct expr *) expr->attr)->type, r);
    }
    break;
  }
  case N_EXPR: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    
    check_labels (labels, r); check (expr, r);
    break;
  }
  default:
    abort ();
  }
  if (e != NULL && context && context->code != N_ALIGNOF
      && context->code != N_SIZEOF && context->code != N_ADDR) {
    e->type = adjust_type (e->type);
  }
  return TRUE;
}

static void check_init (void) {
  n_i1_node = new_i_node (1, no_pos); check (n_i1_node, NULL);
  curr_scope = func_block_scope = NULL;
  VARR_CREATE (node_t, gotos, 0);
  symbol_init ();
  in_params_p = FALSE;
  HTAB_CREATE (case_t, case_tab, 100, case_hash, case_eq);
}

static void check_finish (void) {
  VARR_DESTROY (node_t, gotos);
  symbol_finish ();
  HTAB_DESTROY (case_t, case_tab);
}

/* ---------------------------- Checker Finish -------------------------------- */



static const char *get_node_name (node_code_t code) {
#define C(n) case N_##n: return #n;
  switch (code) {
    C (IGNORE) C (L) C (LL) C (UL) C (ULL) C (F) C (D) C (LD) C (CH) C (STR) C (ID) C (COMMA) C (ANDAND)
      C (OROR) C (EQ) C (NE) C (LT) C (LE) C (GT) C (GE) C (ASSIGN) C (BITWISE_NOT) C (NOT) C (AND) C (AND_ASSIGN)
      C (OR) C (OR_ASSIGN) C (XOR) C (XOR_ASSIGN) C (LSH) C (LSH_ASSIGN) C (RSH) C (RSH_ASSIGN)
      C (ADD) C (ADD_ASSIGN) C (SUB) C (SUB_ASSIGN) C (MUL) C (MUL_ASSIGN) C (DIV) C (DIV_ASSIGN)
      C (MOD) C (MOD_ASSIGN) C (IND) C (FIELD) C (ADDR) C (DEREF) C (DEREF_FIELD) C (COND) C (INC) C (DEC)
      C (POST_INC) C (POST_DEC) C (ALIGNOF) C (SIZEOF) C (EXPR_SIZEOF) C (CAST) C (COMPOUND_LITERAL)
      C (CALL) C (GENERIC) C (GENERIC_ASSOC) C (IF) C (SWITCH) C (WHILE) C (DO) C (FOR) C (GOTO) C (CONTINUE)
      C (BREAK) C (RETURN) C (EXPR) C (BLOCK) C (CASE) C (DEFAULT) C (LABEL) C (LIST) C (SPEC_DECL) C (SHARE)
      C (TYPEDEF) C (EXTERN) C (STATIC) C (AUTO) C (REGISTER) C (THREAD_LOCAL) C (DECL) C (VOID) C (CHAR)
      C (SHORT) C (INT) C (LONG) C (FLOAT) C (DOUBLE) C (SIGNED) C (UNSIGNED) C (BOOL) C (COMPLEX) C (STRUCT)
      C (UNION) C (ENUM) C (ENUM_CONST) C (MEMBER) C (CONST) C (RESTRICT) C (VOLATILE) C (ATOMIC) C (INLINE)
      C (NO_RETURN) C (ALIGNAS) C (FUNC) C (STAR) C (POINTER) C (DOTS) C (ARR) C (INIT) C (FIELD_ID) C (TYPE)
      C (ST_ASSERT) C (FUNC_DEF)
  default:
    abort ();
  }
#undef C
}

static void print_char (FILE *f, int ch) {
  assert (ch >= 0);
  if (ch == '"' || ch == '\"'  || ch == '\\')
    fprintf (f, "\\");
  if (isprint (ch))
    fprintf(f, "%c", ch);
  else
    fprintf(f, "\\%o", ch);
}

static void print_chars (FILE *f, const char *str) {
  while (*str != 0)
    print_char (f, *str++);
}

static void pr_node (FILE *f, node_t n, int indent);

static void pr_ops (FILE *f, node_t n, int indent) {
  int i;
  node_t op;
  
  for (i = 0; (op = get_op (n, i)) != NULL; i++)
    pr_node (f, op, indent + 2);
}

static void pr_node (FILE *f, node_t n, int indent) {
  int i;
  
  fprintf (f, "%6lu: ", n->uid);
  for (i = 0; i < indent; i++)
    fprintf (f, " ");
  if (n == &err_node) {
    fprintf (f, "<error>\n");
    return;
  }
  fprintf (f, "%s", get_node_name (n->code));
  switch (n->code) {
  case N_IGNORE: fprintf (f, "\n"); break;
  case N_I: fprintf (f, " %lld\n", (long long) n->u.l); break;
  case N_L: fprintf (f, " %lldl\n", (long long) n->u.l); break;
  case N_LL: fprintf (f, " %lldll\n", (long long) n->u.ll); break;
  case N_U: fprintf (f, " %lluu\n", (unsigned long long) n->u.ul); break;
  case N_UL: fprintf (f, " %lluul\n", (unsigned long long) n->u.ul); break;
  case N_ULL: fprintf (f, " %lluull\n", (unsigned long long) n->u.ull); break;
  case N_F: fprintf (f, " %.*g\n", FLT_DECIMAL_DIG, (double) n->u.f); break;
  case N_D: fprintf (f, " %.*g\n", DBL_DECIMAL_DIG, (double) n->u.d); break;
  case N_LD: fprintf (f, " %.*Lg\n", LDBL_DECIMAL_DIG, (double) n->u.ld); break;
  case N_CH: fprintf (f, " '"); print_char (f, n->u.ch); fprintf (f, "'\n"); break;
  case N_STR: fprintf (f, " \""); print_chars (f, n->u.s); fprintf (f, "\"\n"); break;
  case N_ID: fprintf (f, " %s\n", n->u.s); break;
  case N_COMMA: case N_ANDAND: case N_OROR: case N_EQ: case N_NE: case N_LT: case N_LE: case N_GT: case N_GE:
  case N_ASSIGN: case N_BITWISE_NOT: case N_NOT: case N_AND: case N_AND_ASSIGN: case N_OR: case N_OR_ASSIGN:
  case N_XOR: case N_XOR_ASSIGN: case N_LSH: case N_LSH_ASSIGN: case N_RSH: case N_RSH_ASSIGN: case N_ADD:
  case N_ADD_ASSIGN: case N_SUB: case N_SUB_ASSIGN: case N_MUL: case N_MUL_ASSIGN: case N_DIV:
  case N_DIV_ASSIGN: case N_MOD: case N_MOD_ASSIGN: case N_IND: case N_FIELD: case N_ADDR: case N_DEREF:
  case N_DEREF_FIELD: case N_COND: case N_INC: case N_DEC: case N_POST_INC: case N_POST_DEC: case N_ALIGNOF:
  case N_SIZEOF: case N_EXPR_SIZEOF: case N_CAST: case N_COMPOUND_LITERAL: case N_CALL: case N_GENERIC:
  case N_GENERIC_ASSOC: case N_IF: case N_SWITCH: case N_WHILE: case N_DO: case N_FOR: case N_GOTO:
  case N_CONTINUE: case N_BREAK: case N_RETURN: case N_EXPR: case N_BLOCK: case N_CASE: case N_DEFAULT:
  case N_LABEL: case N_LIST: case N_SPEC_DECL: case N_SHARE: case N_TYPEDEF: case N_EXTERN: case N_STATIC:
  case N_AUTO: case N_REGISTER: case N_THREAD_LOCAL: case N_DECL: case N_VOID: case N_CHAR: case N_SHORT:
  case N_INT: case N_LONG: case N_FLOAT: case N_DOUBLE: case N_SIGNED: case N_UNSIGNED: case N_BOOL:
  case N_COMPLEX: case N_STRUCT: case N_UNION: case N_ENUM: case N_ENUM_CONST: case N_MEMBER:
  case N_CONST: case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: case N_INLINE: case N_NO_RETURN:
  case N_ALIGNAS: case N_FUNC: case N_STAR: case N_POINTER: case N_DOTS: case N_ARR:
  case N_INIT: case N_FIELD_ID: case N_TYPE: case N_ST_ASSERT: case N_FUNC_DEF:
    fprintf (f, "\n"); pr_ops (f, n, indent);
    break;
  default:
    abort ();
  }
}

#ifdef TEST_MIR_C
#include <sys/time.h>

static double
real_usec_time(void) {
  struct timeval  tv;

  gettimeofday(&tv, NULL);
  return tv.tv_usec + tv.tv_sec * 1000000.0;
}

static size_t curr_char;
static const char *code;

static int t_getc (void) {
  int c = code[curr_char];

  if (c == 0) c = EOF; else curr_char++;
  return c;
}

static void t_ungetc (int c) {
  if (c == EOF) {
    assert (code[curr_char] == 0);
  } else {
    assert (curr_char != 0 && code [curr_char - 1] == c);
    curr_char--;
  }
}

int main (int argc, const char *argv[]) {
  double start_time = real_usec_time ();
  node_t r;
  VARR (char) *input;
  int c;
  
  VARR_CREATE (char, input, 100);
  if (argc == 3 && strcmp (argv[1], "-c") == 0) {
    code = argv[2];
  } else if (argc == 2) {
    FILE *f;
    
    if (strcmp (argv[1], "-i") == 0) {
      f = stdin;
    } else if ((f = fopen (argv[1], "r")) == NULL) {
      print_error (no_pos, "can not open %s -- goodbye\n", argv[1]);
      exit (1);
    }
    while ((c = getc (f)) != EOF)
      VARR_PUSH (char, input, c);
    VARR_PUSH (char, input, 0);
    code = VARR_ADDR (char, input);
    if (strcmp (argv[1], "-i") != 0)
      fclose (f);
  } else {
    code =
"  static const int SieveSize = 819000;\n"
"  int sieve (void) {\n"
"  int i, k, prime, count, iter;\n"
"  char flags[SieveSize];\n"
"\n"
"  for (iter = 0; iter < 1000; iter++) {\n"
"    count = 0;\n"
"    for (i = 0; i < SieveSize; i++)\n"
"      flags[i] = 1;\n"
"    for (i = 0; i < SieveSize; i++)\n"
"      if (flags[i]) {\n"
"	    prime = i + i + 3;\n"
"	    for (k = i + prime; k < SieveSize; k += prime)\n"
"	      flags[k] = 0;\n"
"	    count++;\n"
"      }\n"
"  }\n"
"  return count;\n"
"}\n"
"\n"
"void main (void) {\n"
"  printf (\"%d\\n\", sieve ());\n"
"}\n";
  }
  curr_char = 0; c_getc = t_getc; c_ungetc = t_ungetc;
  parse_init ();
  check_init ();
  fprintf (stderr, "parser_init end -- %.0f usec\n", real_usec_time () - start_time);
  r = parse ();
  fprintf (stderr, "parser end -- %.0f usec\n", real_usec_time () - start_time);
  if (r != NULL) {
    fprintf (stderr, "parse - OK\n");
    pr_node (stderr, r, 0);
    if (check (r, NULL)) {
      fprintf (stderr, "check - OK\n");
    }
  }
  VARR_DESTROY (char, input);
  parse_finish ();
  check_finish ();
  fprintf (stderr, "parser_finish end -- %.0f usec\n", real_usec_time () - start_time);
  return 0;
}
#endif
