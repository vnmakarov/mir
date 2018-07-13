/* expr extensions */

#include <assert.h>
#include <string.h>
#include <ctype.h>
#include <float.h>
#include <stdlib.h>
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
  N_BLOCK, N_CASE, N_DEFAULT, N_LABEL, N_LIST, N_SPEC_DECL,
  N_TYPEDEF, N_EXTERN, N_STATIC, N_AUTO, N_REGISTER, N_THREAD_LOCAL, N_DECL,
  N_VOID, N_CHAR, N_SHORT, N_INT, N_LONG, N_FLOAT, N_DOUBLE, N_SIGNED, N_UNSIGNED,
  N_BOOL, N_COMPLEX, N_STRUCT, N_UNION, N_ENUM, N_ENUM_CONST, N_MEMBER,
  N_CONST, N_RESTRICT, N_VOLATILE, N_ATOMIC, N_INLINE, N_NO_RETURN, N_ALIGNAS,
  N_FUNC, N_STAR, N_POINTER, N_DOTS, N_ARR, N_INIT, N_FIELD_ID, N_TYPE, N_ST_ASSERT, N_FUNC_DEF
} node_code_t;

typedef struct node *node_t;

DEF_DLIST_LINK (node_t);
DEF_DLIST_TYPE (node_t);

struct node {
  node_code_t code;
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

typedef struct pos {
  int lno, ln_pos;
} pos_t;

typedef struct token {
  token_code_t code;
  pos_t pos;
  node_code_t node_code;
  node_t node;
} token_t;

static void op_append (node_t n, node_t op) {
  DLIST_APPEND (node_t, n->ops, op);
}

static node_t new_node (node_code_t node_code) {
  node_t n = reg_malloc (sizeof (struct node));

  n->code = node_code;
  DLIST_INIT (node_t, n->ops);
  n->attr = NULL;
  return n;
}

static node_t new_node1 (node_code_t node_code, node_t op1) {
  node_t r = new_node (node_code);
  op_append (r, op1); return r;
}

static node_t new_node2 (node_code_t node_code, node_t op1, node_t op2) {
  node_t r = new_node1 (node_code, op1);
  op_append (r, op2); return r;
}

static node_t new_node3 (node_code_t node_code, node_t op1, node_t op2, node_t op3) {
  node_t r = new_node2 (node_code, op1, op2);
  op_append (r, op3); return r;
}

static node_t new_node4 (node_code_t node_code, node_t op1, node_t op2, node_t op3, node_t op4) {
  node_t r = new_node3 (node_code, op1, op2, op3);
  op_append (r, op4); return r;
}

static node_t new_const_node (node_code_t node_code) {
  node_t n = reg_malloc (sizeof (struct node));

  n->code = node_code;
  return n;
}

static node_t new_str_node (node_code_t node_code, const char *s) {
  node_t n = new_const_node (node_code); n->u.s = s; return n;
}

static node_t new_ch_node (int ch) { node_t n = new_const_node (N_CH); n->u.ch = ch; return n; }
static node_t new_f_node (float f) { node_t n = new_const_node (N_F); n->u.f = f; return n; }
static node_t new_d_node (double d) { node_t n = new_const_node (N_D); n->u.d = d; return n; }
static node_t new_ld_node (long double ld) { node_t n = new_const_node (N_LD); n->u.ld = ld; return n; }
static node_t new_i_node (long l) { node_t n = new_const_node (N_I); n->u.l = l; return n; }
static node_t new_l_node (long l) { node_t n = new_const_node (N_L); n->u.l = l; return n; }
static node_t new_ll_node (long long ll) { node_t n = new_const_node (N_LL); n->u.ll = ll; return n; }
static node_t new_u_node (unsigned long ul) { node_t n = new_const_node (N_U); n->u.ul = ul; return n; }
static node_t new_ul_node (unsigned long ul) { node_t n = new_const_node (N_UL); n->u.ul = ul; return n; }
static node_t new_ull_node (unsigned long long ull) { node_t n = new_const_node (N_ULL); n->u.ull = ull; return n; }

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

static int read_str_code (int curr_c, int *newln_p, int *wrong_escape_p) {
  int ch, i, c;

  /* `current_position' corresponds position right after `input_char'
     here. */
  if (curr_c == EOF || curr_c == '\n') {
    curr_pos.ln_pos--; c_ungetc (curr_c); return (-1);
  }
  *newln_p = *wrong_escape_p = FALSE;
  if (curr_c == '\\') {
    curr_c = c_getc (); curr_pos.ln_pos++;
    switch (curr_c) {
    case 'a': curr_c = '\a'; break;
    case 'b': curr_c = '\b'; break;
    case 'n': curr_c = '\n'; break;
    case 'f': curr_c = '\f'; break;
    case 'r': curr_c = '\r'; break;
    case 't': curr_c = '\t'; break;
    case 'v': curr_c = '\v'; break;
    case '\\': case '\'': case '\?': case '\"': break;
    case '\n': curr_pos.ln_pos = 1; curr_pos.lno++; *newln_p = TRUE; break;
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': {
      ch = curr_c - '0'; curr_c = c_getc ();
      if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9')
	c_ungetc (curr_c);
      else {
	 ch = (ch * 8 + curr_c - '0'); curr_pos.ln_pos++; curr_c = c_getc ();
	 if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9') {
	   c_ungetc (curr_c);
	 } else {
	   ch = (ch * 8 + curr_c - '0'); curr_pos.ln_pos++;
	 }
      }
      curr_c = ch;
      break;
    }
    case 'x': case 'X': {
      ch = 0; curr_c = c_getc ();
      for (ch = i = 0; isxdigit (curr_c); i++) {
	c = isdigit (curr_c) ? curr_c - '0' : islower (curr_c) ? curr_c - 'a' + 10 : curr_c - 'A' + 10;
	ch = (ch << 4) | c; curr_c = c_getc (); curr_pos.ln_pos++;
      }
      c_ungetc (curr_c); curr_c = ch; *wrong_escape_p = i == 0;
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
    curr_c = c_getc ();
    switch (start_c = curr_c) {
    case ' ': case '\f':
      curr_pos.ln_pos++; break;
    case '\t':
      curr_pos.ln_pos = ((curr_pos.ln_pos - 1) / TAB_STOP + 1)* TAB_STOP + 1; break;
    case '\n':
      curr_pos.ln_pos = 1; curr_pos.lno++; break;
    case '\r':
      curr_pos.ln_pos++; break;
    case '~':
      setup_curr_token (curr_pos, curr_c, N_BITWISE_NOT); curr_pos.ln_pos++; return;
    case '+': case '-':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == start_c) {
	setup_curr_token (pos, T_INCDEC, start_c == '+' ? N_INC : N_DEC); curr_pos.ln_pos++;
      } else if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, start_c == '+' ? N_ADD_ASSIGN : N_SUB_ASSIGN); curr_pos.ln_pos++;
      } else if (start_c == '-' && curr_c == '>') {
	setup_curr_token (pos, T_ARROW, N_DEREF_FIELD); curr_pos.ln_pos++;
      } else if (isdigit (curr_c)) {
	c_ungetc (start_c); c_ungetc (curr_c); curr_pos.ln_pos--;
	goto number;
      } else if (curr_c == '.') {
	curr_c = c_getc ();
	if (isdigit (curr_c)){
	  c_ungetc (start_c); c_ungetc ('.'); c_ungetc (curr_c); curr_pos.ln_pos--;
	  goto number;
	} else {
	  c_ungetc ('.'); c_ungetc (curr_c); setup_curr_token (pos, T_ADDOP, start_c == '+' ? N_ADD : N_SUB);
	}
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, T_ADDOP, start_c == '+' ? N_ADD : N_SUB);
      }
      return;
    case '=':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_EQNE, N_EQ); curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, '=', N_ASSIGN);
      }
      return;
    case '<': case '>':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '<') {
	curr_pos.ln_pos++; curr_c = c_getc ();
	if (curr_c == '=') {
	  setup_curr_token (pos, T_ASSIGN, start_c == '<' ? N_LSH_ASSIGN : N_RSH_ASSIGN); curr_pos.ln_pos++;
	} else {
	  c_ungetc (curr_c); setup_curr_token (pos, T_SH, start_c == '<' ? N_LSH : N_RSH);
	}
      } else if (curr_c == '=') {
	setup_curr_token (pos, T_CMP, start_c == '<' ? N_LE : N_GE); curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, T_CMP, start_c == '<' ? N_LT : N_GT);
      }
      return;
    case '*':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_MUL_ASSIGN); curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, '*', N_MUL);
      }
      return;
    case '/':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_MUL_ASSIGN); curr_pos.ln_pos++;
      } else if (curr_c == '/') { /* comment // */
	curr_pos.ln_pos++;
	while ((curr_c = c_getc ()) != '\n' && curr_c != EOF)
	  curr_pos.ln_pos++;
	curr_pos.ln_pos = 1; curr_pos.lno++; break;      
      } else if (curr_c == '*') { /* usual C comment */
	curr_pos.ln_pos++;
	for (;;) {
	  if ((curr_c = c_getc ()) == EOF)
	    error_func (C_unfinished_comment, "unfinished comment");
	  curr_pos.ln_pos++;
	  if (curr_c == '*') {
	    if ((curr_c = c_getc ()) == '/') {
	      curr_pos.ln_pos++; break;
	    } else {
	      c_ungetc (curr_c);
	    }
	  }
	}
	break;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, '*', N_MUL);
      }
      return;
    case '%':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, N_MOD_ASSIGN); curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, T_DIVOP, N_MOD);
      }
      return;
    case '&': case '|':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, T_ASSIGN, start_c == '&' ? N_AND_ASSIGN : N_OR_ASSIGN); curr_pos.ln_pos++;
      } else if (curr_c == start_c) {
	setup_curr_token (pos, start_c == '&' ? T_ANDAND : T_OROR, start_c == '&' ? N_ANDAND : N_OROR);
	curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, start_c, start_c == '&' ? N_AND : N_OR);
      }
      return;
    case '^': case '!':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '=') {
	setup_curr_token (pos, start_c == '^' ? T_ASSIGN : T_EQNE, start_c == '^' ? N_XOR_ASSIGN : N_NE);
	curr_pos.ln_pos++;
      } else {
	c_ungetc (curr_c); setup_curr_token (pos, start_c == '^' ? '^' : T_UNOP, start_c == '^' ? N_XOR : N_NOT);
      }
      return;
    case ';': case '?': case ':': case '(': case ')': case '{': case '}': case ']': case EOF:
      curr_pos.ln_pos++; setup_curr_token (curr_pos, curr_c, N_IGNORE); return;
    case ',':
      curr_pos.ln_pos++; setup_curr_token (curr_pos, ',', N_COMMA); return;
    case '[':
      curr_pos.ln_pos++; setup_curr_token (curr_pos, '[', N_IND); return;
    case '.':
      pos = curr_pos; curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c == '.') {
	curr_pos.ln_pos++; curr_c = c_getc ();
	if (curr_c == '.') {
	  setup_curr_token (pos, T_DOTS, N_IGNORE); curr_pos.ln_pos++;
	} else {
	  c_ungetc (curr_c); c_ungetc ('.'); curr_pos.ln_pos--; setup_curr_token (pos, '.', N_FIELD);
	}
	return;
      } else if (! isdigit (curr_c)) {
	c_ungetc (curr_c); setup_curr_token (pos, '.', N_FIELD);
	return;
      }
      c_ungetc (curr_c); curr_c = '.'; curr_pos.ln_pos--;
    number:
      /* Fall through: */
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': {
      int base = 10, err_p = FALSE, float_p = FALSE, double_p = FALSE, long_double_p = FALSE;
      int uns_p = TRUE, long_p = FALSE, long_long_p = FALSE, dec_p = FALSE, hex_p = FALSE, hex_char_p;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0);
      if (curr_c == '+' || curr_c == '-') {
	VARR_PUSH (char, symbol_text, curr_c); curr_pos.ln_pos++; curr_c = c_getc ();
      }
      if (curr_c == '.' && VARR_LENGTH (char, symbol_text) == 0) {
	VARR_PUSH (char, symbol_text, '0');
      }
      if (curr_c == '0') {
	curr_c = c_getc (); curr_pos.ln_pos++;
	if (curr_c != 'x' && curr_c != 'X') {
	base = 8; c_ungetc (curr_c); curr_pos.ln_pos--; curr_c = '0';
	} else {
	  VARR_PUSH (char, symbol_text, '0'); VARR_PUSH (char, symbol_text, 'x');
	  curr_c = c_getc (); curr_pos.ln_pos++; base = 16;
	}
      }
      for (;;) {
	VARR_PUSH (char, symbol_text, curr_c);
	curr_c = c_getc (); curr_pos.ln_pos++;
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
	  VARR_PUSH (char, symbol_text, curr_c); curr_c = c_getc (); curr_pos.ln_pos++;
	} while (isdigit (curr_c));
      }
      if ((base != 16 && (curr_c == 'e' || curr_c == 'E'))
	  || (base == 16 && (curr_c == 'p' || curr_c == 'P'))) {
	double_p = TRUE; curr_c = c_getc (); curr_pos.ln_pos++;
	if (curr_c != '+' && curr_c != '-' && ! isdigit (curr_c)) {
	  error_func (C_absent_exponent, "absent exponent"); err_p = TRUE;
	} else {
	  VARR_PUSH (char, symbol_text, base == 16 ? 'p' : 'e');
	  if (curr_c == '+' || curr_c == '-') {
	    VARR_PUSH (char, symbol_text, curr_c); curr_c = c_getc (); curr_pos.ln_pos++;
	    if (! isdigit (curr_c)) {
	      error_func (C_absent_exponent, "absent exponent"); err_p = TRUE;
	    }
	  }
	  if (! err_p) {
	    do {
	      VARR_PUSH (char, symbol_text, curr_c); curr_c = c_getc (); curr_pos.ln_pos++;
	    } while (isdigit (curr_c));
	  }
	}
      } else if (! double_p && (curr_c == 'l' || curr_c == 'L')) {
	long_p = TRUE; curr_c = c_getc (); curr_pos.ln_pos++;
      }
      if (double_p) {
	if (curr_c == 'f' || curr_c == 'F') {
	  double_p = FALSE; float_p = TRUE; curr_c = c_getc (); curr_pos.ln_pos++;
	} else if (curr_c == 'l' || curr_c == 'L') {
	  double_p = FALSE; long_double_p = TRUE; curr_c = c_getc (); curr_pos.ln_pos++;
	}
      } else {
	int c2 = c_getc (), c3 = c_getc ();
	
	if ((curr_c == 'u' || curr_c == 'U') && (c2 == 'l' || c2 == 'L')  && (c3 == 'l' || c3 == 'L')
	    || (curr_c == 'l' || curr_c == 'L') && (c2 == 'l' || c2 == 'L')  && (c3 == 'u' || c3 == 'u')) {
	  uns_p = long_long_p = TRUE; curr_pos.ln_pos += 3; curr_c = c_getc ();
	} else if ((curr_c == 'u' || curr_c == 'U') && (c2 == 'l' || c2 == 'L')
		   || (curr_c == 'l' || curr_c == 'L') && (c2 == 'u' || c2 == 'u')) {
	  uns_p = long_p = TRUE; curr_pos.ln_pos += 2; curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L') && (c2 == 'l' || c2 == 'L')) {
	  long_p = TRUE; curr_pos.ln_pos += 2; curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L')) {
	  long_p = TRUE; c_ungetc (c3); curr_c = c2; curr_pos.ln_pos++;
	} else if ((curr_c == 'u' || curr_c == 'U')) {
	  long_p = TRUE; c_ungetc (c3); curr_c = c2; curr_pos.ln_pos++;
	} else {
	  c_ungetc (c3); c_ungetc (c2);
	}
      }
      VARR_PUSH (char, symbol_text, '\0');
      c_ungetc (curr_c); curr_pos.ln_pos--;
      if (err_p)
	return;
      errno = 0;
      if (float_p) {
	float f = strtof (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_f_node (f));
      } else if (double_p) {
	double d = strtod (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_d_node (d));
      } else if (long_double_p) {
	long double ld = strtod (VARR_ADDR (char, symbol_text), NULL);
	setup_curr_node_token (pos, T_CONSTANT, new_ld_node (ld));
      } else if (base == 8 && dec_p) {
	error_func (C_wrong_octal_int, "wrong octal integer"); err_p = TRUE;
      } else if (uns_p) {
	if (long_long_p) {
	  unsigned long long ull = strtoul (VARR_ADDR (char, symbol_text), NULL, base);
	  setup_curr_node_token (pos, T_CONSTANT, new_ull_node (ull));
	} else {
	  unsigned long ul = strtoul (VARR_ADDR (char, symbol_text), NULL, base);
	  setup_curr_node_token (pos, T_CONSTANT, new_ul_node (ul));  /* ??? unsigned int */
	}
      } else if (long_long_p) {
	long long ll = strtoll (VARR_ADDR (char, symbol_text), NULL, base);
	setup_curr_node_token (pos, T_CONSTANT, new_ll_node (ll));
      } else {
	long l = strtol (VARR_ADDR (char, symbol_text), NULL, base);
	setup_curr_node_token (pos, T_CONSTANT, new_l_node (l)); /* ??? int */
      }
      if (errno) {
	error_func (C_out_of_range_number, "number is out of range"); err_p = TRUE;
      }
      return;
    }
    case '\'': { /* ??? unicode and wchar */
      int ch, newln_p, wrong_escape_p, err_p = FALSE;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0); curr_pos.ln_pos++; curr_c = c_getc ();
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
      curr_pos.ln_pos++; curr_c = c_getc ();
      if (curr_c != '\'') {
	curr_pos.ln_pos--; c_ungetc (curr_c);
	error_func (C_invalid_char_constant, "more one character in char"); err_p = TRUE;
      }
      setup_curr_node_token (pos, T_CONSTANT, new_ch_node (ch));
      return;
    }
    case '\"': { /* ??? unicode and wchar */
      int ch, newln_p, wrong_escape_p, err_p = FALSE;
      str_t str;
      
      pos = curr_pos; VARR_TRUNC (char, symbol_text, 0); curr_pos.ln_pos++;
      for (;;) {
	curr_c = c_getc (); curr_pos.ln_pos++;
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
      setup_curr_node_token (pos, T_STR, new_str_node (N_STR, str.s));
      return;
    }
    default:
      if (isalpha (curr_c) || curr_c == '_' ) {
	str_t str;
	
	pos = curr_pos;
	do {
	  curr_pos.ln_pos++; VARR_PUSH (char, symbol_text, curr_c); curr_c = c_getc ();
	} while (isalnum (curr_c) || curr_c == '_');
	c_ungetc (curr_c);
	VARR_PUSH (char, symbol_text, '\0');
	str = str_add (VARR_ADDR (char, symbol_text), T_STR, 0, FALSE);
	if (str.key != T_STR) {
	  setup_curr_token (pos, str.key, N_IGNORE);
	} else {
	  setup_curr_node_token (pos, T_ID, new_str_node (N_ID, str.s));
	}
	return;
      } else {
	error_chars_num++;
	if (error_chars_num == 1)
	  error_func (C_invalid_char, "invalid input character");
	curr_pos.ln_pos++;
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

static void syntax_error (int expected_token_code) {
  static int context_len = 30;
  char buf[context_len + 1];
  int i, c;
  
  fprintf (stderr, "syntax error on %s", get_token_name (curr_token.code));
  fprintf (stderr, " (expected %s):", get_token_name (expected_token_code));
  for (i = 0; (c = c_getc ()) != EOF && i < context_len; i++)
    buf[i] = c;
  buf[i] = 0;
  fprintf (stderr, " %s\n", buf);
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

#define P(f) do { if ((r = (f) (no_err_p)) == NULL) return NULL; } while (0)
#define PT(t) do {                              \
  if (! M(t)) {					\
    if (record_level == 0) syntax_error (t);	\
    return NULL;				\
  }						\
} while (0)

#define PTN(t) do {                             \
  if (! MN(t, r)) {				\
    if (record_level == 0) syntax_error (t);	\
    return NULL;				\
  }						\
} while (0)

#define PE(f, l) do {if ((r = (f) (no_err_p)) == NULL) goto l; } while (0)
#define PTE(t, l) do {if (! M(t)) goto l; } while (0)

typedef node_t (*nonterm_func_t) (int);

#define D(f) static node_t f (int no_err_p)

static int C (int c) { return curr_token.code == c; }

static int match (int c, node_code_t *node_code, node_t *node) {
  if (curr_token.code != c)
    return FALSE;
  if (node_code != NULL)
    *node_code = curr_token.node_code;
  if (node != NULL)
    *node = curr_token.node;
  read_token ();
  return TRUE;
}

#define M(c) match (c, NULL, NULL)
#define MC(c, code) match (c, &(code), NULL)
#define MN(c, node) match (c, NULL, &(node))

static node_t try (nonterm_func_t f) {
  node_t r = &err_node;
  size_t mark;
  
  mark = record_start ();
  r = (f) (TRUE);
  record_stop (mark, r == NULL);
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
  node_t r, n, op, gn;

  if (MN (T_ID, r) || MN (T_CONSTANT, r) || MN (T_STR, r)) {
    return r;
  } else if (M ('(')) {
    P (expr);
    if (M (')')) return r;
  } else if (M (T_GENERIC)) {
    PT ('('); P (assign_expr); PT (',');
    n = new_node1 (N_GENERIC, r);
    for (;;) { /* generic-assoc-list , generic-association */
      if (M (T_DEFAULT)) {
	op = new_node (N_IGNORE);
      } else {
	P (type_name); op = r;
      }
      PT (':'); P (assign_expr);
      gn = new_node2 (N_GENERIC_ASSOC, op, r); r = gn;
      op_append (n, r);
      if (! M (','))
	break;
    }
    PT ('(');
    return n;
  }
  return NULL;
}

D (post_expr) {
  node_t r, n, op, list;
  node_code_t code;

  P (primary_expr);
  for (;;) {
    if (MC (T_INCDEC, code)) {
      code = code == N_INC ? N_POST_INC : N_POST_DEC;
      n = new_node (code); op = r; r = NULL;
    } else if (MC ('.', code) || MC (T_ARROW, code)) {
      op = r;
      if (! MN (T_ID, r))
	return NULL;
    } else if (MC ('[', code)) {
      op = r; P (expr); PT (']');
    } else if (M ('(')) {
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
    n = new_node1 (code, op);
    if (r != NULL)
      op_append (n, r);
    r = n;
  }
  return r;
}

D (unary_expr) {
  node_t r, n, t;
  node_code_t code;

  if (TRY (par_type_name) != NULL) {
    t = r;
    if (! M ('{')) {
      P (unary_expr); n = new_node2 (N_CAST, t, r);
    } else {
      P (initializer_list);
      if (! M ('}')) return NULL;
      n = new_node2 (N_COMPOUND_LITERAL, t, r);
    }
    return n;
  } else if (M (T_SIZEOF) && TRY (par_type_name) != NULL) {
    n = new_node1 (N_SIZEOF, r); return n;
  } else if (M (T_SIZEOF)) {
    code = N_EXPR_SIZEOF;
  } else if (M (T_ALIGNOF)) {
    P (par_type_name); n = new_node1 (N_ALIGNOF, r); return n;
  } else if (! MC (T_INCDEC, code) && ! MC (T_UNOP, code) && ! MC (T_ADDOP, code)
	     && ! MC ('*', code)  && ! MC ('&', code)) {
    P (post_expr); return r;
  } else if (code == N_AND) {
    code = N_ADDR;
  } else if (code == N_MUL) {
    code = N_DEREF;
  }
  P (unary_expr); n = new_node1 (code, r); return n;
}

static node_t left_op (int no_err_p, int token, int token2, nonterm_func_t f) {
  node_t r, n;
  node_code_t code;

  P (f);
  while (MC (token, code) || (token2 >= 0 && MC (token2, code))) {
    n = new_node1 (code, r);
    P (f); op_append (n, r); r = n;
  }
  return r;
}

static node_t right_op (int no_err_p, int token, int token2, nonterm_func_t left, nonterm_func_t right) {
  node_t r, n;
  node_code_t code;

  P (left);
  if (MC (token, code) || (token2 >= 0 && MC (token2, code))) {
    n = new_node1 (code, r); P (right); op_append (n, r); r = n;
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
  node_t r, n;
  
  P (lor_expr);
  if (! M ('?')) return r;
  n = new_node1 (N_COND, r);
  P (expr); op_append (n, r);
  if (! M (':')) return NULL;
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
  node_t op, list, decl, spec, r = &err_node;
  
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
	op_append (list, new_node3 (N_SPEC_DECL, spec, decl, r));
	if ( ! M (','))
	  break;
      }
    }
    r = list; PT (';');
  }
  return r;
}

D (declaration_specs) {
  node_t list, r = &err_node;
  int first_p;
  
  list = new_node (N_LIST);
  for (first_p = TRUE;; first_p = FALSE) {
    if (C (T_ALIGNAS)) {
      P (align_spec);
    } else if ((r = TRY (sc_spec)) != NULL) {
    } else if ((r = TRY (type_qual)) != NULL) {
    } else if ((r = TRY (func_spec)) != NULL) {
    } else if (first_p) {
      P (type_spec);
    } else if ((r = TRY (type_spec)) != NULL) {
    } else break;
    op_append (list, r);
  }
  return list;
}

D (sc_spec) {
  node_t r = &err_node;
  
  if (M (T_TYPEDEF)) {
    r = new_node (N_TYPEDEF);
  } else if (M (T_EXTERN)) {
    r = new_node (N_EXTERN);
  } else if (M (T_STATIC)) {
    r = new_node (N_STATIC);
  } else if (M (T_AUTO)) {
    r = new_node (N_AUTO);
  } else if (M (T_REGISTER)) {
    r = new_node (N_REGISTER);
  } else {
    PT (T_THREAD_LOCAL); r = new_node (N_THREAD_LOCAL);
  }
  return r;
}

D (type_spec) {
  node_t op1, op2, op3, op4, r = &err_node;
  int struct_p, id_p = FALSE;
  
  if (M (T_VOID)) {
    r = new_node (N_VOID);
  } else if (M (T_CHAR)) {
    r = new_node (N_CHAR);
  } else if (M (T_SHORT)) {
    r = new_node (N_SHORT);
  } else if (M (T_INT)) {
    r = new_node (N_INT);
  } else if (M (T_LONG)) {
    r = new_node (N_LONG);
  } else if (M (T_FLOAT)) {
    r = new_node (N_FLOAT);
  } else if (M (T_DOUBLE)) {
    r = new_node (N_DOUBLE);
  } else if (M (T_SIGNED)) {
    r = new_node (N_SIGNED);
  } else if (M (T_UNSIGNED)) {
    r = new_node (N_UNSIGNED);
  } else if (M (T_BOOL)) {
    r = new_node (N_BOOL);
  } else if (M (T_COMPLEX)) {
    r = new_node (N_COMPLEX);
  } else if (M (T_ATOMIC)) { /* atomic-type-specifier */
    PT ('('); P (type_name); PT (')');
    fprintf (stderr, "Atomic types are not supported\n");
  } else if ((struct_p = M (T_STRUCT)) || M (T_UNION)) { /* struct-or-union-specifier, struct-or-union */
    if (! MN (T_ID, op1)) {
      op1 = new_node (N_IGNORE);
    } else {
      id_p = TRUE;
    }
    if (M ('{')) {
      P (struct_declaration_list); PT ('}');
    } else if (! id_p) {
      return NULL;
    } else {
      r = new_node (N_IGNORE);
    }
    r = new_node2 (struct_p ? N_STRUCT : N_UNION, op1, r);
  } else if (M (T_ENUM)) { /* enum-specifier */
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
      return NULL;
    } else {
      op2 = new_node (N_IGNORE);
    }
    r = new_node2 (N_ENUM, op1, op2);
  } else {
    P (typedef_name);
  }
  return r;
}

D (struct_declaration_list) {
  node_t r, res = &err_node;
  
  res = new_node (N_LIST);
  for (;;) {
    P (struct_declaration);
    if (r->code != N_LIST) {
      op_append (res, r);
    } else {
      for (r = DLIST_HEAD (node_t, r->ops); r != NULL; r = DLIST_NEXT (node_t, r))
	op_append (res, r);
    }
    if (C ('}')) break;
  }
  return res;
}

D (struct_declaration) {
  node_t list, spec, op, r = &err_node;
  
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
	op = new_node3 (N_MEMBER, spec, op, r); op_append (list, op);
	if (! M (','))
	  break;
      }
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
    } else if ((op = TRY (type_spec)) != NULL) {
    } else if (first_p) {
      return NULL;
    } else {
      break;
    }
    op_append (list, op);
  }
  return list;
}

D (type_qual) {
  node_t r = &err_node;
  
  if (M (T_CONST)) {
    r = new_node (N_CONST);
  } else if (M (T_RESTRICT)) {
    r = new_node (N_RESTRICT);
  } else if (M (T_VOLATILE)) {
    r = new_node (N_VOLATILE);
  } else {
    PT (T_ATOMIC); r = new_node (N_ATOMIC);
  }
  return r;
}

D (func_spec) {
  node_t r = &err_node;
  
  if (M (T_INLINE)) {
    r = new_node (N_INLINE);
  } else {
    PT (T_NO_RETURN); r = new_node (N_NO_RETURN);
  }
  return r;
}

D (align_spec) {
  node_t r = &err_node;
  
  PT (T_ALIGNAS); PT ('(');
  if ((r = TRY (type_name)) != NULL) {
  } else {
    P (const_expr);
  }
  PT (')'); r = new_node1 (N_ALIGNAS, r);
  return r;
}

D (declarator) {
  node_t list, p = NULL, r = &err_node;
  
  if (C ('*')) {
    P (pointer); p = r;
  }
  P (direct_declarator);
  if (p != NULL) {
    list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, p->ops));
    assert (list->code == N_LIST);
    for (p = DLIST_HEAD (node_t, p->ops); p != NULL; p = DLIST_NEXT (node_t, p))
      op_append (list, p);
  }
  return r;
}

D (direct_declarator) {
  node_t list, tql, ae, res, r = &err_node;
  
  if (MN (T_ID, r)) {
    res = new_node2 (N_DECL, r, new_node (N_LIST));
  } else if (M ('(')) {
    P (declarator); res = r; PT (')');
  } else {
    return NULL;
  }
  list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, res->ops));
  assert (list->code == N_LIST);
  for (;;) {
    if (M ('(')) {
      if ((r = TRY (id_list)) != NULL) {
      } else {
	P (param_type_list);
      }
      PT (')'); op_append (list, new_node1 (N_FUNC, r));
    } else if (M ('[')) {
      int static_p = FALSE;
      
      if (M (T_STATIC)) {
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
      } else if (M ('*')) {
	ae = new_node (N_STAR);
      } else if (! C (']')) {
	P (assign_expr); ae = r;
      } else {
	ae = new_node (N_IGNORE);
      }
      PT (']'); op_append (list, new_node3 (N_ARR, static_p ? new_node (N_STATIC) : new_node (N_IGNORE), tql, ae));
    } else break;
  }
  return res;
}

D (pointer) {
  node_t op, r = &err_node;
  
  PT ('*');
  if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
    P (type_qual_list);
  } else {
    r = new_node (N_LIST);
  }
  op = new_node1 (N_POINTER, r);
  if (C ('*')) {
    P (pointer);
  } else {
    r = new_node (N_LIST); 
  }
  op_append (r, op);
  return r;
}

D (type_qual_list) {
  node_t list, r = &err_node;
  
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
  
  list = new_node (N_LIST);
  for (;;) { /* parameter-list, parameter-declaration */
    P (declaration_specs); op1 = r;
    if ((op2 = TRY (declarator)) != NULL) {
      r = new_node3 (N_SPEC_DECL, op1, op2, new_node (N_IGNORE));
    } else if (! C (',') && ! C (')')) {
      P (abstract_declarator);
      r = new_node2 (N_TYPE, op1, r);
    } else {
      r = new_node2 (N_TYPE, op1, new_node (N_IGNORE));
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
    PT (T_DOTS); op_append (list, new_node (N_DOTS));
  }
  return list;
}
 
D (id_list) {
  node_t list, r = &err_node;
  
  list = new_node (N_LIST);
  for (;;) {
    PTN (T_ID); op_append (list, r);
    if (! M (','))
      break;
  }
  return list;
}

D (abstract_declarator) {
  node_t list, p = NULL, r = &err_node;
  
  if (C ('*')) {
    P (pointer); p = r;
  }
  P (direct_abstract_declarator);
  if (p != NULL) {
    list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, p->ops));
    assert (list->code == N_LIST);
    for (p = DLIST_HEAD (node_t, p->ops); p != NULL; p = DLIST_NEXT (node_t, p))
      op_append (list, p);
  }
  return r;
}

D (par_abstract_declarator) {
  node_t r = &err_node;
  
  PT ('('); P (abstract_declarator); PT (')');
  return r;
}

D (direct_abstract_declarator) {
  node_t res, list, tql, ae, r = &err_node;
  
  if ((res = TRY (par_abstract_declarator)) != NULL) {
    if (! C ('(') && ! C ('['))
      return res;
  } else {
    res = new_node2 (N_DECL, new_node (N_IGNORE), new_node (N_LIST));
  }
  list = DLIST_NEXT (node_t, DLIST_HEAD (node_t, res->ops));
  assert (list->code == N_LIST);
  for (;;) {
    if (M ('(')) {
      P (param_type_list); PT (')'); op_append (list, new_node1 (N_FUNC, r));
    } else {
      PT ('[');
      if (M ('*')) {
	r = new_node3 (N_ARR, new_node (N_IGNORE), new_node (N_IGNORE), new_node (N_STAR));
      } else {
	int static_p = FALSE;
	
	if (M (T_STATIC)) {
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
	r = new_node3 (N_ARR, static_p ? new_node (N_STATIC) : new_node (N_IGNORE), tql, ae);
      }
      PT (']'); op_append (list, r);
    }
    if (! C ('(') && ! C ('['))
      break;
  }
  return res;
}

D (typedef_name) {
  node_t scope, r = &err_node;
  
  PTN (T_ID);
  for (scope = curr_scope; scope != NULL; scope = scope->u.scope)
    if (tpname_find (r, scope, NULL))
      return r;
  return NULL;
}

D (initializer) {
  node_t r = &err_node;
  
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
  node_t list, list2, r = &err_node;
  int first_p;
  
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
    if (!first_p) {
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
  node_t op, r = &err_node;

  P (spec_qual_list); op = r;
  if (! C (')') && ! C (':')) {
    P (abstract_declarator);
  } else {
    r = new_node (N_IGNORE);
  }
  return new_node2 (N_TYPE, op, r);
}

D (st_assert) {
  node_t op1, r = &err_node;
  
  PT (T_STATIC_ASSERT); PT ('('); P (const_expr); op1 = r; PT (','); PTN (T_STR); PT (')');  PT (';');
  r = new_node2 (N_ST_ASSERT, op1, r);
  return r;
}

/* Statements: */
D (compound_stmt);

D (label) {
  node_t r = &err_node;
  
  if (M (T_CASE)) {
    P (expr); r = new_node1 (N_CASE, r);
  } else if (M (T_DEFAULT)) {
    r = new_node (N_DEFAULT);
  } else {
    PTN (T_ID); r = new_node1 (N_LABEL, r);
  }
  PT (':');
  return r;
}
 
D (stmt) {
  node_t l, n, op1, op2, op3, r = &err_node;
  
  l = new_node (N_LIST);
  while ((op1 = TRY (label)) != NULL) {
    op_append (l, op1);
  }
  if (C ('{')) {
    P (compound_stmt);
  } else if (M (T_IF)) { /* selection-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt); op2 = r;
    if (! M (T_ELSE)) {
      r = new_node (N_IGNORE);
    } else {
      P (stmt);
    }
    n = new_node4 (N_IF, l, op1, op2, r); r = n;
  } else if (M (T_SWITCH)) { /* selection-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt);
    n = new_node3 (N_SWITCH, l, op1, r); r = n;
  } else if (M (T_WHILE)) {  /* iteration-statement */
    PT ('('); P (expr); op1 = r; PT (')'); P (stmt);
    n = new_node3 (N_WHILE, l, op1, r); r = n;
  } else if (M (T_DO)) {  /* iteration-statement */
    P (stmt); op1 = r; PT (T_WHILE); PT ('('); P (expr); PT (')'); PT (';');
    n = new_node3 (N_DO, l, op1, r); r = n;
  } else if (M (T_FOR)) {  /* iteration-statement */
    PT ('(');
    if ((r = TRY (declaration)) != NULL) {
      op1 = r;
    } else if (! C (';')) {
      P (expr); op1 = r; PT (';');
    } else {
      op1 = new_node (N_IGNORE);
    }
    if (C (';')) {
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
    n = new_node4 (N_FOR, l, op1, op2, op3); op_append (n, r); r = n;
  } else if (M (T_GOTO)) {  /* jump-statement */
    PTN (T_ID); PT (';'); n = new_node2 (N_GOTO, l, r); r = n;
  } else if (M (T_CONTINUE)) {  /* continue-statement */
    PT (';'); n = new_node1 (N_CONTINUE, l);
  } else if (M (T_BREAK)) {  /* break-statement */
    PT (';'); n = new_node1 (N_BREAK, l);
  } else if (M (T_RETURN)) {  /* return-statement */
    if (M (';')) {
      r = new_node (N_IGNORE);
    } else {
      P (expr); PT (';');
    }
    n = new_node2 (N_RETURN, l, r); r = n;
  } else { /* expression-statement */
    if (C (';')) {
      r = new_node (N_IGNORE);
    } else {
      P (expr);
    }
    PT (';'); n = new_node2 (N_EXPR, l, r); r = n;
  }
  return r;
}
 
static void error_recovery (int par_lev) {
  if (prev_token.code == ';' || prev_token.code == '}')
    return;
  for (;;) {
    if (curr_token.code == EOF || (par_lev == 0 && curr_token.code == ';'))
      break;
    if (curr_token.code == '{') {
      par_lev++;
    } else if (curr_token.code == '}') {
      if (par_lev == 0)
	return;
      if (--par_lev == 0)
	break;
    }
    read_token ();
  }
  read_token ();
}

D (compound_stmt) {
  node_t n, r = &err_node;
  
  PTE ('{', err0);
  n = new_node (N_BLOCK); n->u.scope = curr_scope; curr_scope = n;
  while (! C ('}') && ! C (EOF)) { /* block-item-list, block_item */
    if ((r = TRY (declaration)) != NULL) {
    } else {
      PE (stmt, err1);
    }
    op_append (n, r);
    continue;
  err1: error_recovery (1);
  }
  if (! C (EOF))
    PT ('}');
  return n;
 err0:  error_recovery (0);
  return r;
}
 
D (transl_unit) {
  node_t list, ds, d, dl, r = &err_node;

  curr_token.code = ';'; /* for error recovery */
  read_token ();
  list = new_node (N_LIST);
  while (! C (EOF)) { /* external-declaration */
    if ((r  = TRY (declaration)) != NULL) {
    } else {
      PE (declaration_specs, err); ds = r; PE (declarator, err); d = r;
      dl = new_node (N_LIST);
      while (! C ('{')) { /* declaration-list */
	PE (declaration, err); op_append (dl, r);
      }
      P (compound_stmt); r = new_node4 (N_FUNC_DEF, ds, d, dl, r);
    }
    op_append (list, r);
    continue;
  err: error_recovery (0);
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
  curr_scope = new_node (N_BLOCK);
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
#undef PTN
#undef PE
#undef PTE
#undef D
#undef M
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
     | N_ALIGNOF (type_name) | N_SIZEOF (type_name) | N_EXPR_SIZEOF (expr) | N_CAST (type_name, expr)
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
    | N_FOR(N_LIST:(label)*,(declaration | expr)?, expr?, expr?, stmt)
    | N_GOTO(N_LIST:(label)*, N_ID) | (N_CONTINUE|N_BREAK) (N_LIST:(label)*)
    | N_RETURN(N_LIST:(label)*, expr?) | N_EXPR(N_LIST:(label)*, expr)
compound_stmt: BLOCK((declaration | stmt)*)
declaration: N_LIST: N_SPEC_DECL(declaration_specs, declarator?, initializer?)+ | st_assert
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
type_name: N_TYPE(spec_qual_list, abstract_declarator?)
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
  node_t def_node;
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

static void symbol_insert (enum symbol_mode mode, node_t id, node_t scope, node_t def_node) {
  symbol_t el, symbol;
  
  symbol.mode = mode; symbol.id = id; symbol.scope = scope; symbol.def_node = def_node;
  HTAB_DO (symbol_t, symbol_tab, symbol, HTAB_INSERT, el);
}

static void symbol_finish (void) {
  HTAB_DESTROY (symbol_t, symbol_tab);
}

DEF_VARR (node_t);
static VARR (node_t) *gotos;

static node_t func_block_scope;

enum basic_type {
  TP_UNDEF, TP_VOID,
  /* Integer types: the first should be BOOL and the last should be
     ULONG_LONG.  The order is important -- do not change it.  */
  TP_BOOL, TP_CHAR, TP_SCHAR, TP_UCHAR, TP_SHORT, TP_USHORT, TP_INT, TP_UINT,
  TP_LONG, TP_ULONG, TP_LONG_LONG, TP_ULONG_LONG,
  TP_FLOAT, TP_DOUBLE, TP_LONG_DOUBLE, TP_FLOAT_COMPLEX, TP_DOUBLE_COMPLEX, TP_LONG_DOUBLE_COMPLEX, 
};

enum basic_type get_int_basic_type (size_t s) {
  return (s == sizeof (mir_int) ? TP_INT
	  : s == sizeof (mir_short) ? TP_SHORT
	  : s == sizeof (mir_long) ? TP_LONG
	  : s == sizeof (mir_schar) ? TP_SCHAR : TP_LONG_LONG);
}

struct type_qual {
  int const_p : 1, restrict_p : 1, volatile_p : 1, atomic_p : 1; /* Type qualifiers */
};

static const struct type_qual zero_type_qual = {0, 0, 0, 0};

struct arr_type {
  int static_p : 1;
  struct type *el_type;
  struct type_qual ind_type_qual;
  node_t size;
};

struct func_type {
  int dot_p : 1;
  struct type *ret_type;
  node_t param_list;
};

enum type_mode {
  TM_BASIC, TM_ENUM, TM_PTR, TM_STRUCT, TM_UNION, TM_ARR, TM_FUNC,
};

struct type {
  struct type_qual type_qual;
  node_t typedef_id; /* non-null if the original is a typedef name */
  int incomplete_p : 1;
  enum type_mode mode;
  union {
    enum basic_type basic_type;
    node_t tag_type; /* struct/union/enum */
    struct type *ptr_type;
    struct arr_type *arr_type;
    struct func_type *func_type;
  } u;
};

static int type_qual_eq_p (const struct type_qual *tq1, const struct type_qual *tq2) {
  return (tq1->const_p == tq2->const_p && tq1->restrict_p == tq2->restrict_p
	  && tq1->volatile_p == tq2->volatile_p && tq1->atomic_p == tq2->atomic_p);
}

static void clear_type_qual (struct type_qual *tq) {
  tq->const_p = tq->restrict_p = tq->volatile_p = tq->atomic_p = FALSE;
}

static void set_type_qual (node_t r, struct type_qual *tq) {
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    switch (n->code) {
      /* Type qualifiers: */
    case N_CONST: tq->const_p = TRUE; break;
    case N_RESTRICT: tq->restrict_p = TRUE; break;
    case N_VOLATILE: tq->volatile_p = TRUE; break;
    case N_ATOMIC: tq->atomic_p = TRUE; break;
    }
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
  type->typedef_id = NULL; type->incomplete_p = FALSE;
}

static int standard_integer_type_p (struct type *type) {
  return type->mode == TM_BASIC && type->u.basic_type >= TP_BOOL && type->u.basic_type <= TP_ULONG_LONG;
}

static int integer_type_p (struct type *type) {
  return standard_integer_type_p (type) || type->mode == TM_ENUM;
}

static int int_bit_size (struct type *type) {
  return 32; // ???
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
  if (floating_type_p (type1) || floating_type_p (type2)) {
    res.mode = TM_BASIC;
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

static int incomplete_type_p (struct type *type) {
  return FALSE; // ???
}

static struct type *create_type (struct type *copy) {
  struct type *res = reg_malloc (sizeof (struct type));

  if (copy == NULL)
    init_type (res);
  else
    *res = *copy;
  return res;
}

static int type_align (node_t type) {
  return 4; //  ???
}

struct decl_spec {
  int typedef_p : 1, extern_p : 1, static_p : 1, auto_p : 1, register_p : 1, thread_local_p : 1;
  int inline_p : 1, no_return_p : 1; /* func specifiers  */
  int align; // negative value means undefined
  node_code_t linkage; // N_IGNORE - none, N_STATIC - internal, N_EXTERN - external
  node_t align_spec;
  struct type *type;
};

struct enum_value {
  mir_int val;
};

struct expr {
  int const_p : 1;
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

static int void_ptr_p (struct type *type) {
  return type->mode == TM_PTR && type->u.ptr_type->mode == TM_BASIC && type->u.ptr_type->u.basic_type == TP_VOID;
}

static int null_const_p (struct expr *expr, struct type *type) {
  return  void_ptr_p (type) && expr->const_p && expr->u.u_val == 0 && type_qual_eq_p (&type->type_qual, &zero_type_qual);
}

static void convert_value (struct expr *e, struct type *t) {
}

static void create_node_scope (node_t node) {
  struct node_scope *ns = reg_malloc (sizeof (struct node_scope));
  
  node->attr = ns; ns->scope = curr_scope; curr_scope = node;
}

static void check_type_qual (const struct type *type) {
  if (type->type_qual.restrict_p && type->mode != TM_PTR)
    fprintf (stderr, "restrict requires a pointer\n");
  if (type->type_qual.atomic_p) {
    if (type->mode == TM_ARR)
      fprintf (stderr, "_Atomic qualifying array\n");
    else if (type->mode == TM_FUNC)
      fprintf (stderr, "_Atomic qualifying function\n");
  }
}

static void check_type_duplication (struct type *type, const char *name, int size, int sign) {
  if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
    fprintf (stderr, "%s with another type\n", name);
  else if (type->mode != TM_BASIC && size != 0)
    fprintf (stderr, "size with non-numeric type\n");
  else if (type->mode != TM_BASIC && sign != 0)
    fprintf (stderr, "sign attribute with non-integer type\n");
}

static node_t process_tag (node_t r, node_t id, node_t decl_list) {
  symbol_t sym;
  
  if (id->code != N_ID)
    return r;
  if (! symbol_find (S_TAG, id, curr_scope, &sym)) {
    symbol_insert (S_TAG, id, curr_scope, r);
  } else if (sym.def_node->code != r->code) {
    fprintf (stderr, "kind of tag %s is unmatched with previous declaration\n", id->u.s);
  } else if (DLIST_NEXT (node_t, DLIST_HEAD (node_t, sym.def_node->ops))->code != N_IGNORE
	     && decl_list->code != N_IGNORE) {
    fprintf (stderr, "tag %s redeclaration\n", id->u.s);
  } else if (decl_list->code != N_IGNORE) {
    symbol_insert (S_TAG, id, curr_scope, r);
  } else {
    r = sym.def_node;
  }
  return r;
}

static int compatible_types_p (struct type *type1, struct type *type2, int ignore_quals_p) {
  if (type1->mode != type2->mode) return FALSE;
  if (type1->mode == TM_PTR) {
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
  }
  return TRUE; // ???
}

static int assignment_compatible_types_p (struct type *type1, struct type *type2) {
  return TRUE; // ???
}

static node_t find_def (enum symbol_mode mode, node_t id, node_t scope) {
  symbol_t sym;

  while (scope != NULL)
    if (! symbol_find (mode, id, scope, &sym)) {
      scope = ((struct node_scope *) scope->attr)->scope;
    } else {
      return sym.def_node;
    }
  return NULL;
}

static void def_symbol (enum symbol_mode mode, node_t id, node_t scope,
			node_t def_node, node_code_t linkage) {
  symbol_t sym;
  struct decl_spec tab_decl_spec, decl_spec = ((struct decl *) def_node->attr)->decl_spec;
  
  if (id->code == N_IGNORE)
    return;
  assert (id->code == N_ID);
  assert (scope->code == N_BLOCK || scope->code == N_STRUCT || scope->code == N_UNION || scope->code == N_FUNC);
  if (scope != NULL && decl_spec.thread_local_p && ! decl_spec.static_p && ! decl_spec.extern_p)
    fprintf (stderr, "auto %s is declared as thread local\n", id->u.s);
  if (! symbol_find (mode, id, scope, &sym)) {
    symbol_insert (mode, id, scope, def_node);
    return;
  }
  tab_decl_spec = ((struct decl *) sym.def_node->attr)->decl_spec;
  if (linkage == N_IGNORE) {
    if (! decl_spec.typedef_p || ! tab_decl_spec.typedef_p
	|| decl_spec.type != tab_decl_spec.type)
    fprintf (stderr, "repeated declaration %s\n", id->u.s);
  } else if (! compatible_types_p (decl_spec.type, tab_decl_spec.type, FALSE)) {
    fprintf (stderr, "incompatible types of %s declarations\n", id->u.s);
  }
  if (tab_decl_spec.thread_local_p != decl_spec.thread_local_p) {
    fprintf (stderr, "thread local and non-thread local declarations of %s\n", id->u.s);
  }
}

static int incomplete_array_permitted_p; // ???
static int in_params_p;

static int check (node_t node);

static struct decl_spec check_decl_spec (node_t r, node_t decl) {
  int n_sc = 0, sign = 0, size = 0;
  struct decl_spec *res;
  struct type *type;
  
  if (r->attr != NULL)
    return *(struct decl_spec *) r->attr;
  r->attr = res = reg_malloc (sizeof (struct decl_spec));
  res->typedef_p = res->extern_p = res->static_p = res->auto_p = res->register_p = res->thread_local_p = FALSE;
  res->inline_p = res->no_return_p = FALSE; res->align = -1;
  res->type = type = create_type (NULL);
  type->mode = TM_BASIC; type->u.basic_type = TP_UNDEF;
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    if (n->code == N_SIGNED || n->code == N_UNSIGNED) {
      if (sign != 0) fprintf (stderr, "more than one sign qualifier\n");
      else sign = n->code == N_SIGNED ? 1 : -1;
    } else if (n->code == N_SHORT) {
      if (size != 0) fprintf (stderr, "more than one type\n");
      else size = 1;
    } else if (n->code == N_LONG) {
      if (size == 2) size = 3;
      else if (size == 3) fprintf (stderr, "more than two long\n");
      else if (size == 1) fprintf (stderr, "short with long\n");
      else size = 2;
    } else if (n->code == N_COMPLEX) {
      fprintf (stderr, "complex numbers are not supported\n");
    }
  set_type_qual (r, &type->type_qual);
  for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
    switch (n->code) {
      /* Type qualifiers are already processed. */
    case N_CONST: case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: break;
      /* Func specifiers: */
    case N_INLINE:
      if (decl->code != N_FUNC_DEF)
	fprintf (stderr, "non-function declaration with inline\n");
      else
	res->inline_p = TRUE;
      break;
    case N_NO_RETURN:
      if (decl->code != N_FUNC_DEF)
	fprintf (stderr, "non-function declaration with no-return\n");
      else
	res->no_return_p = TRUE;
      break;
      /* Storage specifiers: */
    case N_TYPEDEF:
    case N_AUTO:
    case N_REGISTER:
      if (n_sc != 0) fprintf (stderr, "more than one storage specifier\n");
      else if (n->code == N_TYPEDEF) res->typedef_p = TRUE;
      else if (n->code == N_AUTO) res->auto_p = TRUE;
      else res->register_p = TRUE;
      n_sc++;
      break;
    case N_EXTERN:
    case N_STATIC:
      if (n_sc != 0 && (n_sc != 1 || !res->thread_local_p)) fprintf (stderr, "more than one storage specifier\n");
      else if (n->code == N_EXTERN) res->extern_p = TRUE;
      else res->static_p = TRUE;
      n_sc++;
      break;
    case N_THREAD_LOCAL:
      if (n_sc != 0 && (n_sc != 1 || (!res->extern_p && !res->static_p))) fprintf (stderr, "more than one storage specifier\n");
      else res->thread_local_p = TRUE;
      n_sc++;
      break;
    case N_VOID:
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) fprintf (stderr, "void with another type\n");
      else if (sign != 0) fprintf (stderr, "void with sign qualifier\n");
      else if (size != 0) fprintf (stderr, "void with short or long\n");
      else type->u.basic_type = TP_VOID;
      break;
    case N_UNSIGNED:
    case N_SIGNED:
    case N_COMPLEX:
    case N_SHORT:
    case N_LONG:
      break;
    case N_CHAR:
    case N_INT:
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) {
	fprintf (stderr, "char or int with another type\n");
      } else if (n->code == N_CHAR) {
	if (size != 0) fprintf (stderr, "char with short or long\n");
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
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) fprintf (stderr, "_Bool with another type\n");
      else if (sign != 0) fprintf (stderr, "_Bool with sign qualifier\n");
      else if (size != 0) fprintf (stderr, "_Bool with short or long\n");
      type->u.basic_type = TP_BOOL;
      break;
    case N_FLOAT:
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) fprintf (stderr, "float with another type\n");
      else if (sign != 0) fprintf (stderr, "float with sign qualifier\n");
      else if (size != 0) fprintf (stderr, "float with short or long\n");
      else type->u.basic_type = TP_FLOAT;
      break;
    case N_DOUBLE:
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) fprintf (stderr, "double with another type\n");
      else if (sign != 0) fprintf (stderr, "double with sign qualifier\n");
      else if (size == 0)
	type->u.basic_type = TP_DOUBLE;
      else if (size == 2)
	type->u.basic_type = TP_LONG_DOUBLE;
      else fprintf (stderr, "double with short\n");
      break;
    case N_ID: {
      node_t def = find_def (S_REGULAR, r, curr_scope);
      struct decl *decl;
      
      assert (def == NULL && def->code == N_SPEC_DECL);
      decl = def->attr;
      assert (decl->decl_spec.typedef_p);
      type = decl->decl_spec.type;
      break;
    }
    case N_STRUCT:
    case N_UNION: {
      node_t res, id = DLIST_HEAD (node_t, r->ops);
      node_t decl_list = DLIST_NEXT (node_t, id);

      res = process_tag (n, id, decl_list); create_node_scope (n);
      check_type_duplication (type, n->code == N_STRUCT ? "struct" : "union", size, sign);
      type->mode = n->code == N_STRUCT ? TM_STRUCT : TM_UNION; type->u.tag_type = res;
      check (decl_list);
      curr_scope = ((struct node_scope *) n->attr)->scope;
      break;
    }
    case N_ENUM: {
      node_t res, id = DLIST_HEAD (node_t, r->ops);
      node_t enum_list = DLIST_NEXT (node_t, id);
      
      res = process_tag (n, id, enum_list); check_type_duplication (type, "enum", size, sign);
      type->mode = TM_ENUM; type->u.tag_type = res;
      if (enum_list->code == N_IGNORE) {
	fprintf (stderr, "enum storage size is unknown\n");
      } else {
	for (node_t en = DLIST_HEAD (node_t, enum_list->ops); en != NULL; en = DLIST_NEXT (node_t, en)) { // ??? id
	  node_t id, const_expr;
	  
	  assert (en->code == N_ENUM_CONST);
	  id = DLIST_HEAD (node_t, en->ops); const_expr = DLIST_NEXT (node_t, id);
	  check (const_expr);
	  if (const_expr->code != N_IGNORE) {
	    struct expr *cexpr = const_expr->attr;
	    struct enum_value *enum_value;
	    mir_int val = 0;
	    
	    if (! cexpr->const_p)
	      fprintf (stderr, "non-constant value in enum const expression\n");
	    else if (! integer_type_p (cexpr->type))
	      fprintf (stderr, "enum const expression is not of an integer type\n");
	    else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val <= MIR_INT_MAX)
		     || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val <= MIR_INT_MAX))
	      fprintf (stderr, "enum const expression is not represenetd by int\n");
	    else
	      val = cexpr->u.i_val;
	    en->attr = enum_value = reg_malloc (sizeof (struct enum_value));
	    enum_value->val = val;
	  }
	}
      }
      break;
    }
    case N_ALIGNAS: {
      node_t el;
      
      if (decl->code == N_FUNC_DEF) {
	fprintf (stderr, "_Alignas for function\n");
      } else if (decl->code == N_MEMBER && (el = DLIST_EL (node_t, decl->ops, 3)) != NULL
		 && el->code != N_IGNORE) {
	fprintf (stderr, "_Alignas for a bit-field\n");
      } else if (decl->code == N_SPEC_DECL && in_params_p) {
	fprintf (stderr, "_Alignas for a function parameter\n");
      } else {
	node_t op = DLIST_HEAD (node_t, r->ops);

	check (op);
	if (op->code == N_TYPE) {
	  res->align = type_align (op);
	} else {
	  struct expr *cexpr = op->attr;

	  if (! cexpr->const_p) {
	    fprintf (stderr, "non-constant value in _Alignas\n");
	  } else if (! integer_type_p (cexpr->type)) {
	    fprintf (stderr, "constant value in _Alignas is not of an integer type\n");
	  } else if (! signed_integer_type_p (cexpr->type) || ! supported_alignment_p (cexpr->u.i_val)) {
	    fprintf (stderr, "constant value in _Alignas specifies unspported alignment\n");
	  } else {
	    if (res->align < cexpr->u.i_val)
	      res->align = cexpr->u.i_val; /* use the strictest alignment */
	  }
	}
      }
      break;
    }
    default:
      abort ();
    }
  check_type_qual (type);
  if (res->align >= 0 && res->typedef_p)
    fprintf (stderr, "_Alignas in typedef\n");
  else if (res->align >= 0 && res->register_p)
    fprintf (stderr, "_Alignas with register\n");
  return *res;
}

static struct type *append_type (struct type *head, struct type *el) {
  if (head == NULL)
    return el;
  for (struct type *tp = head;;) {
    struct type **holder;
    
    if (tp->mode == TM_PTR) {
      holder = &tp->u.ptr_type;
    } else if (tp->mode == TM_ARR) {
      holder = &tp->u.arr_type->el_type;
    } else {
      assert (tp->mode == TM_FUNC);
      holder = &tp->u.func_type->ret_type;
    }
    tp = *holder;
    if (tp == NULL) {
      *holder = el;
      return head;
    }
  }
}

static struct type *check_declarator (node_t r, int func_def_p) {
  struct type *res = NULL;
  struct type *type = create_type (NULL);
  
  assert (r->code == N_DECL || r->code == N_MEMBER || r->code == N_FUNC_DEF);
  for (node_t n = DLIST_HEAD (node_t, r->ops); (n = DLIST_NEXT (node_t, n)) != NULL;) {
    switch (n->code) {
    case N_POINTER: {
      node_t type_qual = DLIST_HEAD (node_t, r->ops);
      
      type->mode = TM_PTR; type->u.ptr_type = NULL;
      set_type_qual (type_qual, &type->type_qual); check_type_qual (type);
      break;
    }
    case N_ARR: {
      struct arr_type *arr_type;
      node_t static_node = DLIST_HEAD (node_t, r->ops);
      node_t type_qual = DLIST_NEXT (node_t, static_node);
      node_t size = DLIST_NEXT (node_t, type_qual);
      
      type->mode = TM_ARR;
      type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
      set_type_qual (type_qual, &arr_type->ind_type_qual);
      check (size);
      arr_type->size = size;
      arr_type->static_p = static_node->code == N_STATIC; arr_type->el_type = NULL;
      break;
    }
    case N_FUNC: {
      struct func_type *func_type;
      node_t param_list = DLIST_HEAD (node_t, n->ops);
      node_t last = DLIST_TAIL (node_t, param_list->ops);
      int saved_in_params_p = in_params_p;
      
      n->attr = type;
      type->mode = TM_FUNC;
      type->u.func_type = func_type = reg_malloc (sizeof (struct func_type));
      func_type->ret_type = NULL;
      if ((func_type->dot_p = last != NULL && last->code == N_DOTS))
	DLIST_REMOVE (node_t, param_list->ops, last);
      create_node_scope (n);
      func_type->param_list = param_list;
      in_params_p = TRUE;
      for (node_t p = DLIST_HEAD (node_t, param_list->ops); p != NULL; p = DLIST_NEXT (node_t, p)) {
	struct decl_spec *decl_spec_ptr;
      	struct type *type;
	
	if (p->code != N_ID) {
	  check (p);
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
	    type->u.ptr_type = arr_type->el_type;
	    type->type_qual = arr_type->ind_type_qual;
	  } else if (type->mode == TM_FUNC) {
	    struct type *par_type = create_type (NULL);
	    
	    par_type->mode = TM_PTR; par_type->u.ptr_type = decl_spec_ptr->type;
	  }
	} else if (! func_def_p) {
	  fprintf (stderr, "parameters identifier list can be only in function definition\n");
	  break;
	} else { // adjustment???
	  struct decl_spec decl_spec;
	  struct decl *decl = reg_malloc (sizeof (struct decl));
	  
	  /* Use N_IGNORE as def_node as we never read it: */
	  def_symbol (S_REGULAR, p, curr_scope, N_IGNORE, N_IGNORE);
	  decl->decl_spec = decl_spec;
	}
      }
      in_params_p = saved_in_params_p;
      curr_scope = ((struct node_scope *) n->attr)->scope;
      break;
    }
    default:
      abort ();
    }
    if (res == NULL)
      r->attr = res = type;
    else
      append_type (res, type);
  }
  return type;
}

static node_t curr_switch;

static void check_labels (node_t labels, node_t target) {
  for (node_t l = DLIST_HEAD (node_t, labels->ops); l != NULL; l = DLIST_NEXT (node_t, l)) {
    if (l->code == N_LABEL) {
      symbol_t sym;
      node_t id = DLIST_HEAD (node_t, labels->ops);
      
      if (symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	fprintf (stderr, "label %s redeclaration\n", id->u.s);
      } else {
	symbol_insert (S_LABEL, id, func_block_scope, target);
      }
    } else if (curr_switch == NULL) {
      fprintf (stderr, "%s not witin a switch-stmt\n", l->code == N_CASE ? "case label" : "default label");
    } else {
      struct switch_attr *switch_attr = curr_switch->attr;
      struct type *type = &switch_attr->type;
      node_t case_expr = l->code == N_CASE ? DLIST_HEAD (node_t, labels->ops) : NULL;
      case_t case_attr, tail = DLIST_TAIL (case_t, switch_attr->case_labels);
      int ok_p = FALSE, default_p = tail != NULL && tail->case_node->code == N_DEFAULT;
      struct expr *expr;
      
      if (case_expr == NULL) {
	if (default_p) {
	  fprintf (stderr, "multiple default labels in one switch\n");
	} else {
	  ok_p = TRUE;
	}
      } else {
	check (case_expr);
	expr = case_expr->attr;
	if (! expr->const_p) {
	  fprintf (stderr, "case-expr is not a constant expression\n");
	} else if (! integer_type_p (expr->type)) {
	  fprintf (stderr, "case-expr is not an integer type expression\n");
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
  node_t def = find_def (S_REGULAR, id, scope);
  
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

    if (decl_list == N_IGNORE)
      type->incomplete_p = TRUE;
    break;
  }
  case TM_ARR: {
    struct arr_type *arr_type = type->u.arr_type;
    struct type *el_type = arr_type->el_type;

    if (arr_type->size->code == N_IGNORE) {
      type->incomplete_p = TRUE;
    } else if (arr_type->size->code == N_STAR) {
      fprintf (stderr, "variable size arrays are not supported\n");
    } else {
      struct expr *cexpr = arr_type->size->attr;
      
      if (! integer_type_p (cexpr->type)) {
	fprintf (stderr, "non-integer array size type\n");
      } else if (! cexpr->const_p) {
	fprintf (stderr, "variable size arrays are not supported\n");
      } else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val <= 0)
		 || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val == 0)) {
	fprintf (stderr, "array size should be positive\n");
      }
    }
    check_type (arr_type->el_type, level + 1, FALSE);
    if (arr_type->el_type->incomplete_p) {
      fprintf (stderr, "incomplete array element type\n");
      type->incomplete_p = TRUE;
    }
    if (el_type->mode == TM_FUNC) {
      fprintf (stderr, "array of functions\n");
    } else if (! in_params_p || level != 0) {
      if (arr_type->static_p)
	fprintf (stderr, "static should be only in parameter outermost\n");
      else if (! type_qual_eq_p (&arr_type->ind_type_qual, &zero_type_qual))
	fprintf (stderr, "type qualifiers should be only in parameter outermost array\n");
    }
    break;
  }
  case TM_FUNC: {
    struct decl_spec decl_spec;
    struct func_type *func_type = type->u.func_type;
    struct type *ret_type = func_type->ret_type;
    node_t param_list = func_type->param_list;
    
    check_type (ret_type, level + 1, FALSE);
    if (ret_type->mode == TM_FUNC) {
      fprintf (stderr, "function returning a function\n");
    } else if (ret_type->mode == TM_FUNC) {
      fprintf (stderr, "function returning an array\n");
    }
    for (node_t p = DLIST_HEAD (node_t, param_list->ops); p != NULL; p = DLIST_NEXT (node_t, p)) {
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
      if (p != NULL) {
      } else if (decl_spec.typedef_p || decl_spec.extern_p || decl_spec.static_p
		 || decl_spec.auto_p || decl_spec.thread_local_p) {
	fprintf (stderr, "storage specifier in a function parameter\n");
      } else if (func_def_p) {
	if (p->code == N_TYPE)
	  fprintf (stderr, "parameter type without a name in function definition\n");
	else if (decl_spec.type->incomplete_p)
	  fprintf (stderr, "incomplete parameter type in function definition\n");
      }
    }
    break; // ???
  }
  default:
    break;
  }
}


static void check_initializer (struct type *type, node_t initializer, int const_only_p, int top_p) {
  struct expr *cexpr;
  node_t des_list, curr_des, init, last_member, value, declarator;
  mir_long_long last_index, size_val;
  symbol_t sym;
  
  if (initializer->code != N_LIST) {
  scalar:
    if (! (cexpr = initializer->attr)->const_p && const_only_p) {
      fprintf (stderr, "initializer of static or thread local obejct should be a constant expression\n");
      return;
    }
    if (! assignment_compatible_types_p (cexpr->type, type)) {
      fprintf (stderr, "incompatible assignment types\n");
      return;
    }
    return;
  }
  init = DLIST_HEAD (node_t, initializer->ops);
  assert (init->code == N_INIT);
  des_list = DLIST_HEAD (node_t, init->ops);
  assert (des_list->code == N_LIST);
  if (type->mode != TM_ARR && type->mode != TM_STRUCT  && type->mode != TM_UNION) {
    if (DLIST_NEXT (node_t, init) != NULL) {
      fprintf (stderr, "excess elements in scalar initializer\n");
      return;
    }
    if (DLIST_HEAD (node_t, des_list->ops) != NULL) {
      fprintf (stderr, "designator in scalar initializer\n");
      return;
    }
    initializer = DLIST_NEXT (node_t, des_list);;
    if (! top_p) {
      fprintf (stderr, "braces around scalar initializer\n");
      return;
    }
    goto scalar;
  }
  last_member = NULL; size_val = -1;
  if (type->mode == TM_ARR) {
    node_t size_node = type->u.arr_type->size;
    struct expr *sexpr = size_node->attr;
    
    size_val = size_node->code != N_IGNORE && sexpr->const_p && integer_type_p (sexpr->type) ? sexpr->u.i_val : -1;
  }
  last_index = -1; last_member = NULL;
  for (; init != NULL; init = DLIST_NEXT (node_t, init)) {
    assert (init->code == N_INIT);
    des_list = DLIST_HEAD (node_t, init->ops);
    value = DLIST_NEXT (node_t, des_list);
    if (! ((struct expr *) value->attr)->const_p && const_only_p) {
      fprintf (stderr, "initializer of static or thread local obejct should be a constant expression\n");
      continue;
    }
    if ((curr_des = DLIST_HEAD (node_t, des_list->ops)) == NULL) {
      if (type->mode == TM_ARR) {
	check_initializer (type->u.arr_type->el_type, value, const_only_p, FALSE);
	last_index++;
      } else if (type->mode == TM_STRUCT || type->mode == TM_UNION) {
	if (last_member != NULL) {
	  last_member = DLIST_NEXT (node_t, last_member);
	} else {
	  node_t declaration_list = DLIST_EL (node_t, type->u.tag_type->ops, 1);

	  assert (declaration_list != NULL && declaration_list->code == N_LIST);
	  last_member = DLIST_HEAD (node_t, declaration_list->ops);
	}
	while (last_member != NULL && last_member->code != N_MEMBER)
	  last_member = DLIST_NEXT (node_t, last_member);
	if (last_member == NULL) {
	  fprintf (stderr, "excess elements in struct/union initializer");
	} else {
	  declarator = DLIST_EL (node_t, last_member->ops, 1);
	  check_initializer ((struct type *) declarator->attr, value, const_only_p, FALSE);
	}
      }
    } else {
      for (; curr_des != NULL; curr_des = DLIST_NEXT (node_t, curr_des)) {
	if (curr_des->code == N_FIELD_ID) {
	  node_t id = DLIST_HEAD (node_t, curr_des->ops);
	  
	  if (type->mode != TM_STRUCT && type->mode != TM_UNION) {
	    fprintf (stderr, "field name not in struct or union initializer\n");
	  } else if (! symbol_find (S_REGULAR, id, type->u.tag_type, &sym)) {
	    fprintf (stderr, "unknown field %s in initializer\n", id->u.s);
	  } else {
	    last_member = sym.def_node;
	    assert (last_member->code == N_MEMBER);
	    declarator = DLIST_EL (node_t, last_member->ops, 1);
	    check_initializer ((struct type *) declarator->attr, value, const_only_p, FALSE);
	  }
	} else if (type->mode != TM_ARR) {
	  fprintf (stderr, "array index in initializer for non-array\n");
	} else if (! (cexpr = curr_des->attr)->const_p) {
	  fprintf (stderr, "nonconstant array index in initializer\n");
	} else if (integer_type_p (cexpr->type)) {
	  fprintf (stderr, "array index in initializer not of integer type\n");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  fprintf (stderr, "negative array index in initializer\n");
	} else if (size_val >= 0 && (! signed_integer_type_p (cexpr->type) || size_val <= cexpr->u.i_val)) {
	  fprintf (stderr, "array index in initializer exceeds array bounds\n");
	} else {
	  check_initializer (type->u.arr_type->el_type, value, const_only_p, FALSE);
	  last_index = cexpr->u.i_val;
	}
      }
    }
  }
}

static void create_decl (node_t scope, node_t decl_node, struct decl_spec decl_spec,
			 node_t width, node_t initializer) {
  int func_def_p, func_p;
  node_t id, list, declarator, def;
  struct type *type;
  struct decl *decl = reg_malloc (sizeof (struct decl));
  
  assert (decl_node->code == N_MEMBER || decl_node->code == N_SPEC_DECL || decl_node->code == N_FUNC_DEF);
  func_def_p = decl_node->code == N_FUNC_DEF;
  declarator = DLIST_EL (node_t, decl_node->ops, 1);
  assert (declarator->code == N_DECL);
  type = check_declarator (declarator, func_def_p);
  append_type (type, decl_spec.type);
  decl_spec.type = type;
  check_type (type, 0, func_def_p);
  id = DLIST_HEAD (node_t, declarator->ops);
  list = DLIST_NEXT (node_t, id);
  func_p = DLIST_HEAD (node_t, list->ops)->code == N_FUNC;
  decl_spec.linkage = get_id_linkage (func_p, id, scope, decl_spec);
  decl->decl_spec = decl_spec;
  decl_node->attr = decl;
  if (scope == NULL)
    def_symbol (S_REGULAR, id, NULL, decl_node, decl_spec.linkage);
  else {
    def_symbol (S_REGULAR, id, scope, decl_node, decl_spec.linkage);
    if (decl_spec.linkage == N_EXTERN)
      def_symbol (S_REGULAR, id, NULL, decl_node, N_EXTERN);
  }
  if (func_p && decl_spec.thread_local_p) {
    fprintf (stderr, "thread local function declaration");
    if (id->code != N_IGNORE)
      fprintf (stderr, " of %s", id->u.s);
    fprintf (stderr, "\n");
  }
  if (initializer == NULL)
    return;
  if (type->incomplete_p && (type->mode != TM_ARR || type->u.arr_type->el_type->incomplete_p)) {
    fprintf (stderr, "initialization of incomplete type variable\n");
    return;
  }
  if (decl_spec.linkage != N_IGNORE && scope != NULL) {
    fprintf (stderr, "initialization for block scope identifier with external or internal linkage\n");
    return;
  }
  check (initializer);
  check_initializer (type, initializer, decl_spec.static_p || decl_spec.thread_local_p, TRUE);
}

static void process_unop (node_t r, node_t *op, struct expr **e, struct type **t) {
  *op = DLIST_HEAD (node_t, r->ops); check (*op);
  *e = (*op)->attr; *t = (*e)->type;
}

static void process_bin_ops (node_t r, node_t *op1, node_t *op2, struct expr **e1, struct expr **e2,
			     struct type **t1, struct type **t2) {
  *op1 = DLIST_HEAD (node_t, r->ops); *op2 = DLIST_NEXT (node_t, *op1);
  check (*op1); check (*op2);
  *e1 = (*op1)->attr; *e2 = (*op2)->attr;
  *t1 = (*e1)->type; *t2 = (*e2)->type;
}

static void process_type_bin_ops (node_t r, node_t *op1, node_t *op2, struct expr **e2, struct type **t2) {
  *op1 = DLIST_HEAD (node_t, r->ops); *op2 = DLIST_NEXT (node_t, *op1);
  check (*op1); check (*op2);
  *e2 = (*op2)->attr; *t2 = (*e2)->type;
}

static struct expr *create_expr (node_t r) {
  struct expr *e = reg_malloc (sizeof (struct expr));
  
  e->type = create_type (NULL);
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
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! integer_type_p (t1) || ! integer_type_p (t2)) {
      fprintf (stderr, "bitwise operation operands should be of an integer type\n");
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
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! integer_type_p (t1) || ! integer_type_p (t2)) {
      fprintf (stderr, "shift operands should be of an integer type\n");
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
  case N_ADD: case N_SUB: {
    mir_size_t size;
    int add_p = r->code == N_ADD || r->code == N_INC || r->code == N_POST_INC;
    
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
	fprintf (stderr, "invalid operand types of +\n");
      } else if (t1->u.ptr_type->incomplete_p) {
	fprintf (stderr, "pointer to incomplete type as an operand of +\n");
      } else {
	*e->type = *t1;
	if (e1->const_p && e2->const_p) {
	  size = 1; // ???
	  e->const_p = TRUE;
	  e->u.u_val = (signed_integer_type_p (t2)
			? e1->u.u_val + e2->u.i_val * size : e1->u.u_val + e2->u.u_val * size);
	}
      }
    } else if (t1->mode == TM_PTR && integer_type_p (t2)) {
      if (t1->u.ptr_type->incomplete_p) {
	fprintf (stderr, "pointer to incomplete type as an operand of -\n");
      } else {
	*e->type = *t1;
	if (e1->const_p && e2->const_p) {
	  size = 1; // ???
	  e->const_p = TRUE;
	  e->u.u_val = (signed_integer_type_p (t2)
			? e1->u.u_val - e2->u.i_val * size : e1->u.u_val - e2->u.u_val * size);
	}
      }
    } else if (t1->mode == TM_PTR && t2->mode == TM_PTR && compatible_types_p (t1, t2, TRUE)) {
      if (t1->u.ptr_type->incomplete_p && t2->u.ptr_type->incomplete_p) {
	fprintf (stderr, "pointer to incomplete type as an operand of -\n");
      } else if (t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p) {
	fprintf (stderr, "pointer to atomic type as an operand of -\n");
      } else {
	e->type->mode = TM_BASIC;
	e->type->u.basic_type = get_int_basic_type (sizeof (mir_ptrdiff_t));
	if (e1->const_p && e2->const_p) {
	  size = 1; // ???
	  e->const_p = TRUE;
	  e->u.i_val = (e1->u.u_val > e2->u.u_val
			? (mir_ptrdiff_t) ((e1->u.u_val - e2->u.u_val) / size)
			: -(mir_ptrdiff_t) ((e2->u.u_val - e1->u.u_val) / size));
	}
      }
    } else {
      fprintf (stderr, "invalid operand types of -\n");
    }
    break;
  }
  case N_MUL: case N_DIV: case N_MOD:
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_MOD && (! integer_type_p (t1) || ! integer_type_p (t2))) {
      fprintf (stderr, "invalid operand types of %%\n");
    } else if (r->code != N_MOD && (! arithmetic_type_p (t1) || ! arithmetic_type_p (t2))) {
      fprintf (stderr, "invalid operand types of %s\n", r->code == N_MUL ? "*" : "/");
    } else {
      t = arithmetic_conversion (t1, t2); e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	convert_value (e1, &t); convert_value (e2, &t);
	if (r->code != N_MOD && floating_type_p (&t))
	  e->u.d_val = (r->code == N_MUL ? e1->u.d_val * e2->u.d_val : e1->u.d_val / e2->u.d_val);
	else if (signed_integer_type_p (&t))
	  e->u.i_val = (r->code == N_MUL ? e1->u.i_val * e2->u.i_val : r->code == N_DIV ? e1->u.i_val / e2->u.i_val : e1->u.i_val % e2->u.i_val);
	else
	  e->u.u_val = (r->code == N_MUL ? e1->u.u_val * e2->u.u_val : r->code == N_DIV ? e1->u.u_val / e2->u.u_val : e1->u.u_val % e2->u.u_val);
      }
    }
    break;
  default:
    assert (FALSE);
  }
}

static void check_assignment_types (struct type *left, struct type *right, int assign_p) {
  if (arithmetic_type_p (left)) {
    if (! arithmetic_type_p (right)
	&& (left->mode != TM_BASIC || left->u.basic_type != TP_BOOL || right->mode != TM_PTR)) {
      fprintf (stderr, (assign_p
			? "incompatible types in assignment to an arithemtic type lvalue\n"
			: "incompatible return-expr type in function returning an arithemtic value\n"));
    }
  } else if (left->mode == TM_STRUCT || left->mode == TM_UNION) {
    if ((right->mode != TM_STRUCT && right->mode != TM_UNION)
	|| ! compatible_types_p (left, right, TRUE)) {
      fprintf (stderr, (assign_p
			? "incompatible types in assignment to struct/union\n"
			: "incompatible return-expr type in function returning a struct/union\n"));
    }
  } else if (left->mode == TM_PTR) {
    if (right->mode != TM_PTR
	|| (! compatible_types_p (left->u.ptr_type, right->u.ptr_type, TRUE) && ! void_ptr_p (right))) {
      fprintf (stderr, (assign_p
			? "incompatible types in assignment to a pointer\n"
			: "incompatible return-expr type in function returning a pointer\n"));
    } else if (right->u.ptr_type->type_qual.atomic_p) {
      fprintf (stderr, (assign_p
			? "assignment of pointer to an atomic type\n"
			: "returning a pointer to an atomic type\n"));
    } else if (! type_qual_subset_p (&right->type_qual, &left->type_qual)) {
      fprintf (stderr, (assign_p
			? "assignment discards a type qualifier from a pointer\n"
			: "return discards a type qualifier from a pointer\n"));
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

static int check (node_t r) {
  node_t op1, op2;
  struct expr *e, *e1, *e2;
  struct type t, *t1, *t2;
  
  switch (r->code) {
  case N_IGNORE: case N_STAR: case N_FIELD_ID:
    break; /* do nothing */
  case N_LIST: {
    for (node_t n = DLIST_HEAD (node_t, r->ops); n != NULL; n = DLIST_NEXT (node_t, n))
      check (n);
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
    e->type->mode = TM_ARR;
    e->type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
    clear_type_qual (&arr_type->ind_type_qual); arr_type->static_p = FALSE;
    arr_type->el_type = create_type (NULL);
    arr_type->el_type->mode = TM_BASIC; arr_type->el_type->u.basic_type = TP_CHAR;
    break;
  }
  case N_ID:
    op1 = find_def (S_REGULAR, r, curr_scope); e = create_expr (r);
    if (op1 == NULL) {
      fprintf (stderr, "undeclared identifier %s\n", r->u.s);
    } else if (op1->code == N_SPEC_DECL) {
      struct decl *decl = op1->attr;
      
      if (decl->decl_spec.typedef_p) {
	fprintf (stderr, "typedef name %s as an operand\n", op1->u.s);
      }
      *e->type = *decl->decl_spec.type;
      if (decl->decl_spec.type->mode == TM_FUNC) {
	e->type->mode = TM_PTR; e->type->u.ptr_type = create_type (decl->decl_spec.type);
      } else {
	/* still keeping an array for the assignment check */
	e->lvalue_node = op1;
      }
    } else if (op1->code == N_FUNC_DEF) {
      struct decl *decl = op1->attr;

      assert (decl->decl_spec.type->mode == TM_FUNC);
      e->type->mode = TM_PTR; e->type->u.ptr_type = create_type (decl->decl_spec.type);
    }
    break;
  case N_COMMA:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); e = create_expr (r);
    *e->type = *e2->type;
    break;
  case N_ANDAND: case N_OROR:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1) || ! scalar_type_p (t2)) {
      fprintf (stderr, "invalid operand types of %s\n", r->code == N_ANDAND ? "&&" : "||");
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
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode == TM_PTR && t2->mode == TM_PTR) {
      if (! compatible_types_p (t1, t2, TRUE)
	  && ((r->code != N_EQ && r->code != N_NE)
	      || (! void_ptr_p (t1) && ! void_ptr_p (t2)
		  && ! null_const_p (e1, t1) && ! null_const_p (e2, t2)))) {
	fprintf (stderr, "incompatible pointer types in comparisons\n");
      } else if ((t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p)
		 && ((r->code != N_EQ && r->code != N_NE)
		     || ! null_const_p (e1, t1) && ! null_const_p (e2, t2))) {
	fprintf (stderr, "pointer to atomic type as a comparison operand\n");
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
      fprintf (stderr, "invalid types of comparison operands\n");
    }
    break;
  case N_BITWISE_NOT:
  case N_NOT:
    process_unop (r, &op1, &e1, &t1); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_BITWISE_NOT && ! integer_type_p (t1)) {
      fprintf (stderr, "bitwise-not operand should be of an integer type\n");
    } else if (r->code == N_NOT && ! scalar_type_p (t1)) {
      fprintf (stderr, "not operand should be of a scalar type\n");
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
    
    process_unop (r, &op1, &e1, &t1); saved_expr = *e1;
    get_one_node (&op2, &e2, &t2);
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    *e1 = saved_expr; t1 = e1->type;
    goto assign;
    break;
  }
  case N_ADD: case N_SUB:
    if (DLIST_NEXT (node_t, DLIST_HEAD (node_t, r->ops)) == NULL) { /* unary */
      process_unop (r, &op1, &e1, &t1); e = create_expr (r);
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      if (! arithmetic_type_p (t1)) {
	fprintf (stderr, "unary + or - operand should be of an arithmentic type\n");
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
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2);
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    break;
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN:
  case N_LSH_ASSIGN: case N_RSH_ASSIGN:
  case N_ADD_ASSIGN: case N_SUB_ASSIGN: case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN: {
    struct expr saved_expr;
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); saved_expr = *e1;
    check_assign_op (r, op1, op2, e1, e2, t1, t2);
    *e1 = saved_expr; t1 = e1->type;
    goto assign;
    break;
  }
  case N_ASSIGN:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); e = create_expr (r);
  assign:
    if (! e1->lvalue_node) {
      fprintf (stderr, "lvalue required as left operand of assignment\n");
    }
    check_assignment_types (t1, t2, TRUE);
    *e->type = *t1;
    break;
  case N_IND:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2); e = create_expr (r);
    e->lvalue_node = r; e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR && t1->mode != TM_ARR) {
      fprintf (stderr, "subscripted value is neither array nor pointer\n");
    } else if (t1->mode == TM_PTR) {
      *e->type = *t1->u.ptr_type;
      if (t1->u.ptr_type->incomplete_p) {
	fprintf (stderr, "pointer to incomplete type in array subscription\n");
      }
    } else {
      *e->type = *t1->u.arr_type->el_type;
      e->type->type_qual = t1->u.arr_type->ind_type_qual;
      if (e->type->incomplete_p) {
	fprintf (stderr, "array type has incomplete element type\n");
      }
    }
    if (! integer_type_p (t2)) {
      fprintf (stderr, "array subscript is not an integer\n");
    }
    break;
  case N_ADDR:
    process_unop (r, &op1, &e1, &t1); e = create_expr (r);
    if (op1->code == N_DEREF) {
      node_t deref_op = DLIST_HEAD (node_t, op1->ops);
      
      *e->type = *((struct expr *) deref_op->attr)->type;
      break;
    } else if (! e1->lvalue_node) {
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      fprintf (stderr, "lvalue required as unary & operand\n");
      break;
    }
    if (op1->code == N_IND) {
      t2 = create_type (t1);
    } else if (op1->code == N_ID) {
      node_t decl_node = e1->lvalue_node;
      struct decl *decl = decl_node->attr;

      if (decl->decl_spec.register_p) {
	fprintf (stderr, "address of register variable %s requested\n", op1->u.s);
      }
      t2 = create_type (decl->decl_spec.type);
    } else if (e1->lvalue_node->code == N_MEMBER) {
      node_t declarator = DLIST_EL (node_t, e1->lvalue_node->ops, 1);
      node_t width = DLIST_NEXT (node_t, declarator);
      struct decl *decl = declarator->attr;
      
      assert (declarator->code == N_DECL);
      if (width->code != N_IGNORE) {
	fprintf (stderr, "cannot take address of bit-field %s\n", DLIST_HEAD (node_t, declarator->ops)->u.s);
      }
      t2 = create_type (decl->decl_spec.type);
    }
    e->type->u.ptr_type = t2;
    break;
  case N_DEREF:
    process_unop (r, &op1, &e1, &t1); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR) {
      fprintf (stderr, "invalid type argument of unary *\n");
    } else {
      *e->type = *t1->u.ptr_type;
    }
    break;
  case N_FIELD: case N_DEREF_FIELD: {
    symbol_t sym;
    struct decl *decl;
    
    process_unop (r, &op1, &e1, &t1); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    op2 = DLIST_NEXT (node_t, op1);
    assert (op2->code == N_ID);
    if (r->code == N_DEREF_FIELD && t1->mode == TM_PTR) {
      t1 = t1->u.ptr_type;
    }
    if (t1->mode != TM_STRUCT && t1->mode != TM_UNION) {
      fprintf (stderr, "request for member %s in something not a structure or union\n", op2->u.s);
    } else if (! symbol_find (S_REGULAR, op2, t1->u.tag_type, &sym)) {
      fprintf (stderr, "%s has no member %s\n", t1->mode == TM_STRUCT ? "struct" : "union", op2->u.s);
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
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2);
    op3 = DLIST_NEXT (node_t, op2); check (op3);
    e3 = op3->attr; t3 = e3->type; e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1)) {
      fprintf (stderr, "condition should be of a scalar type\n");
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
    } else if (t3->mode != TM_PTR || t3->mode != TM_PTR) {
      fprintf (stderr, "incompatible types in true and false parts of cond-expression\n");
      break;
    } else if (compatible_types_p (t2, t3, TRUE)) {
      t = composite_type (t2->u.ptr_type, t3->u.ptr_type);
      e->type->mode = TM_PTR; e->type->u.ptr_type = create_type (&t);
      e->type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual, &t3->u.ptr_type->type_qual);
      if ((t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p)
	  && ! null_const_p (e2, t2) && ! null_const_p (e3, t3)) {
	fprintf (stderr, "pointer to atomic type in true or false parts of cond-expression\n");
      }
    } else if ((first_p = void_ptr_p (t2)) || void_ptr_p (t3)) {
      e->type->mode = TM_PTR; e->type->u.ptr_type = create_type (NULL);
      if (first_p && null_const_p (e2, t2)) {
	e->type->u.ptr_type = e2->type->u.ptr_type;
      } else if (null_const_p (e3, t3)) {
	e->type->u.ptr_type = e3->type->u.ptr_type;
      } else {
	if (t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p) {
	  fprintf (stderr, "pointer to atomic type in true or false parts of cond-expression\n");
	}
	e->type->u.ptr_type->mode = TM_BASIC; e->type->u.ptr_type->u.basic_type = TP_VOID;
      }
      e->type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual, &t3->u.ptr_type->type_qual);
    } else {
      fprintf (stderr, "incompatible pointer types in true and false parts of cond-expression\n");
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

    op1 = DLIST_HEAD (node_t, r->ops); check (op1);
    e = create_expr (r);
    assert (op1->code == N_TYPE);
    decl_spec = op1->attr; e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (decl_spec->type->incomplete_p) {
      fprintf (stderr, "%s of incomplete type requested\n", r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else if (decl_spec->type->mode == TM_FUNC) {
      fprintf (stderr, "%s of function type requested\n", r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else {
      e->const_p = TRUE;
      e->u.i_val = 1; // ???
    }
    break;
  }
  case N_EXPR_SIZEOF:
    process_unop (r, &op1, &e1, &t1); e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (e->type->incomplete_p) {
      fprintf (stderr, "sizeof of incomplete type requested\n");
    } else if (e->type->mode == TM_FUNC) {
      fprintf (stderr, "sizeof of function type requested\n");
    } else {
      e->const_p = TRUE;
      e->u.i_val = 1; // ???
    }
    break;
  case N_CAST: {
    struct decl_spec *decl_spec;
    int void_p;
    
    process_type_bin_ops (r, &op1, &op2, &e2, &t2); e = create_expr (r);
    assert (op1->code == N_TYPE);
    decl_spec = op1->attr;
    *e->type = *decl_spec->type;
    void_p = decl_spec->type->mode == TM_BASIC && decl_spec->type->u.basic_type == TP_VOID;
    if (! void_p && ! scalar_type_p (decl_spec->type)) {
      fprintf (stderr, "conversion to non-scalar type requested\n");
    } else if (! scalar_type_p (t2)) {
      fprintf (stderr, "conversion of non-scalar value requested\n");
    } else if (t2->mode == TM_PTR && floating_type_p (decl_spec->type)) {
      fprintf (stderr, "conversion of a pointer to floating value requested\n");
    } else if (decl_spec->type->mode == TM_PTR && floating_type_p (t2)) {
      fprintf (stderr, "conversion of floating point value to a pointer requested\n");
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
  case N_COMPOUND_LITERAL:
  case N_CALL:
  case N_GENERIC: case N_GENERIC_ASSOC:
    break; // ???
  case N_SPEC_DECL: {
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t initializer = DLIST_NEXT (node_t, declarator);
    struct decl_spec decl_spec = check_decl_spec (specs, r);
    
    if (declarator->code != N_IGNORE) {
      create_decl (curr_scope, r, decl_spec, NULL, initializer);
    } else if ((decl_spec.type->mode == N_STRUCT || decl_spec.type->mode == N_UNION)
	       && DLIST_HEAD (node_t, decl_spec.type->u.tag_type->ops)->code != N_ID) {
      fprintf (stderr, "unnamed struct/union with no instances\n");
    } else if (decl_spec.type->mode != N_ENUM) {
      fprintf (stderr, "useless declaration\n");
    }
    /* We have at least one enum constant according to the syntax. */
    break;
  }
  case N_ST_ASSERT: { // ???
    break;
  }
  case N_MEMBER: {
    struct type *type;
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t const_expr = DLIST_NEXT (node_t, declarator);
    struct decl_spec decl_spec = check_decl_spec (specs, r);
    
    create_decl (curr_scope, r, decl_spec, const_expr, NULL);
    type = ((struct decl *) declarator->attr)->decl_spec.type;
    if (const_expr->code != N_IGNORE) {
      struct expr *cexpr;
      
      check (const_expr); cexpr = const_expr->attr;
      if (cexpr != NULL) {
	if (type->type_qual.atomic_p)
	  fprintf (stderr, "bit field with _Atomic\n");
	if (! cexpr->const_p) {
	  fprintf (stderr, "bit field is not a constant expr\n");
	} else if (! integer_type_p (type) && (type->mode != TM_BASIC || type->u.basic_type != T_BOOL)) {
	  fprintf (stderr, "bit field type should be _Bool, a signed integer, or an unsigned integer type\n");
	} else if (! integer_type_p (cexpr->type)
		   && (cexpr->type->mode != TM_BASIC || cexpr->type->u.basic_type != TP_BOOL)) {
	  fprintf (stderr, "bit field width is not of an integer type\n");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  fprintf (stderr, "bit field width is negative\n");
	} else if (cexpr->u.i_val == 0  && declarator->code == N_DECL) {
	  fprintf (stderr, "zero bit field width for %s\n", DLIST_HEAD (node_t, declarator->ops)->u.s);
	} else if ((! signed_integer_type_p (cexpr->type) && cexpr->u.u_val > int_bit_size (cexpr->type))
		   || (signed_integer_type_p (cexpr->type) && cexpr->u.i_val > int_bit_size (cexpr->type))) {
	  fprintf (stderr, "bit field width exceeds its type\n");
	}
      }
    }
    if (declarator->code == N_IGNORE) {
      fprintf (stderr, "no declarator in struct or union declaration\n");
    } else {
      node_t id = DLIST_HEAD (node_t, declarator->ops);

      if (type->mode == TM_FUNC) {
	fprintf (stderr, "field %s is declared as a function\n", id->u.s);
      } else if (incomplete_type_p (type)) {
	// el_type is checked on completness in N_ARR
	if (! incomplete_array_permitted_p || type->mode != TM_ARR
	    || type->u.arr_type->size->code != N_IGNORE)
	  fprintf (stderr, "field %s has incomplete type\n", id->u.s);
      }
    }
    break;
  }
  case N_INIT: {
    node_t des_list = DLIST_HEAD (node_t, r->ops), initializer = DLIST_NEXT (node_t, des_list);
    check (des_list); check (initializer);
  }
  case N_FUNC_DEF: {
    node_t func;
    node_t specs = DLIST_HEAD (node_t, r->ops);
    node_t declarator = DLIST_NEXT (node_t, specs);
    node_t declarations = DLIST_NEXT (node_t, declarator);
    node_t block = DLIST_NEXT (node_t, declarations);
    struct decl_spec decl_spec = check_decl_spec (specs, r);

    create_node_scope (block); func_block_scope = curr_scope;
    curr_func_def = r; curr_switch = curr_loop = curr_loop_switch = NULL;  
    create_decl (NULL, r, decl_spec, NULL, NULL);
    check (block);
    for (size_t i = 0; i < VARR_LENGTH (node_t, gotos); i++) {
      symbol_t sym;
      node_t n = VARR_GET (node_t, gotos, i);
      node_t id = DLIST_NEXT (node_t, DLIST_HEAD (node_t, n->ops));

      if (! symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	fprintf (stderr, "undefined label %s\n", id->u.s);
      } else {
	n->attr = sym.def_node;
      }
    }
    VARR_TRUNC (node_t, gotos, 0);
    curr_scope = ((struct node_scope *) r->attr)->scope; func_block_scope = NULL;
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
    check_type (r->attr, 0, FALSE);
    break;
  }
  case N_BLOCK: {
    create_node_scope (r);
    check (DLIST_HEAD (node_t, r->ops));
    curr_scope = ((struct node_scope *) r->attr)->scope;
    break;
  }
  case N_IF: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    node_t if_stmt = DLIST_NEXT (node_t, expr);
    node_t else_stmt = DLIST_NEXT (node_t, if_stmt);
 
    check_labels (labels, r); check (expr); e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      fprintf (stderr, "if-expr should be of a scalar type\n");
    }
    check (if_stmt); check (else_stmt);
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
    
    check_labels (labels, r); check (expr); type = ((struct expr *) expr->attr)->type;
    if (! integer_type_p (type)) {
      init_type (&t); t.mode = TM_BASIC; t.u.basic_type = TP_INT;
      fprintf (stderr, "switch-expr is of non-integer type\n");
    } else {
      t = integer_promotion (type);
    }
    curr_switch = curr_loop_switch = r;
    switch_attr = curr_switch->attr = reg_malloc (sizeof (struct switch_attr));
    switch_attr->type = t;
    DLIST_INIT (case_t, ((struct switch_attr *) curr_switch->attr)->case_labels);
    check (stmt);
    for (case_t c = DLIST_HEAD (case_t, switch_attr->case_labels); c != NULL; c = DLIST_NEXT (case_t, c)) {
      if (HTAB_DO (case_t, case_tab, c, HTAB_FIND, el)) {
	fprintf (stderr, "duplicate case value\n");
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

    check_labels (labels, r); check (expr); e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      fprintf (stderr, "while-expr should be of a scalar type\n");
    }
    curr_loop = curr_loop_switch = r; check (stmt); curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
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
    create_node_scope (r); curr_loop = curr_loop_switch = r; check (init);
    if (init->code != N_LIST) {
      for (node_t spec_decl = DLIST_HEAD (node_t, init->ops);
	   spec_decl != NULL;
	   spec_decl = DLIST_NEXT (node_t, spec_decl)) {
	assert (spec_decl->code == N_SPEC_DECL);
	decl = spec_decl->attr;
	if (decl->decl_spec.typedef_p || decl->decl_spec.extern_p
	    || decl->decl_spec.static_p || decl->decl_spec.thread_local_p) {
	  fprintf (stderr, "wrong storage specifier of for-loop initial declaration\n");
	  break;
	}
      }
    }
    check (cond); check (iter);
    check (stmt);
    curr_scope = ((struct node_scope *) r->attr)->scope;
    curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
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
      fprintf (stderr, "break statement not within loop or switch\n");
    } else if (r->code == N_CONTINUE && curr_loop == NULL) {
      fprintf (stderr, "continue statement not within a loop\n");
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
    check_labels (labels, r); check (expr);
    ret_type = type->u.func_type->ret_type;
    if (expr->code != N_IGNORE && ret_type->mode == TM_BASIC && ret_type->u.basic_type == TP_VOID) {
      fprintf (stderr, "return with a value in function returning void\n");
    } else if (expr->code == N_IGNORE && (ret_type->mode != TM_BASIC || ret_type->u.basic_type != TP_VOID)) {
      fprintf (stderr, "return with no value in function returning non-void\n");
    } else if (expr->code != N_IGNORE) {
      check_assignment_types (ret_type, ((struct expr *) expr->attr)->type, FALSE);
    }
    break;
  }
  case N_EXPR: {
    node_t labels = DLIST_HEAD (node_t, r->ops);
    node_t expr = DLIST_NEXT (node_t, labels);
    
    check_labels (labels, r); check (expr);
    break;
  }
  default:
    abort ();
  }
  return TRUE;
}

static void check_init (void) {
  n_i1_node = new_i_node (1);
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
      C (MOD) C (MOD_ASSIGN) C (IND) C (FIELD) C (DEREF) C (DEREF_FIELD) C (COND) C (INC) C (DEC)
      C (POST_INC) C (POST_DEC) C (ALIGNOF) C (SIZEOF) C (EXPR_SIZEOF) C (CAST) C (COMPOUND_LITERAL)
      C (CALL) C (GENERIC) C (GENERIC_ASSOC) C (IF) C (SWITCH) C (WHILE) C (DO) C (FOR) C (GOTO) C (CONTINUE)
      C (BREAK) C (RETURN) C (EXPR) C (BLOCK) C (CASE) C (DEFAULT) C (LABEL) C (LIST) C (SPEC_DECL) C (TYPEDEF)
      C (EXTERN) C (STATIC) C (AUTO) C (REGISTER) C (THREAD_LOCAL) C (DECL) C (VOID) C (CHAR) C (SHORT) C (INT)
      C (LONG) C (FLOAT) C (DOUBLE) C (SIGNED) C (UNSIGNED) C (BOOL) C (COMPLEX) C (STRUCT)
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
  
  for (i = 0; i < indent; i++)
    fprintf (f, " ");
  if (n == &err_node) {
    fprintf (f, "<error>\n");
    return;
  }
  fprintf (f, "%s\n", get_node_name (n->code));
  switch (n->code) {
  case N_IGNORE: break;
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
  case N_LABEL: case N_LIST: case N_SPEC_DECL: case N_TYPEDEF: case N_EXTERN: case N_STATIC: case N_AUTO:
  case N_REGISTER: case N_THREAD_LOCAL: case N_DECL: case N_VOID: case N_CHAR: case N_SHORT: case N_INT:
  case N_LONG: case N_FLOAT: case N_DOUBLE: case N_SIGNED: case N_UNSIGNED: case N_BOOL: case N_COMPLEX:
  case N_STRUCT: case N_UNION: case N_ENUM: case N_ENUM_CONST: case N_MEMBER:
  case N_CONST: case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: case N_INLINE: case N_NO_RETURN:
  case N_ALIGNAS: case N_FUNC: case N_STAR: case N_POINTER: case N_DOTS: case N_ARR:
  case N_INIT: case N_FIELD_ID: case N_TYPE: case N_ST_ASSERT: case N_FUNC_DEF:
    pr_ops (f, n, indent);
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
  } else if (argc == 2 && strcmp (argv[1], "-i") == 0) {
    while ((c = getc (stdin)) != EOF)
      VARR_PUSH (char, input, c);
    VARR_PUSH (char, input, 0);
    code = VARR_ADDR (char, input);
  } else {
    code = "\n\
  static const int SieveSize = 819000;\n	\
  int sieve (void) {\n				\
  int i, k, prime, count, iter;\n		\
  char flags[SieveSize];\n			\
\n						\
  for (iter = 0; iter < 1000; iter++) {\n	\
    count = 0;\n				\
    for (i = 0; i < SieveSize; i++)\n		\
      flags[i] = 1;\n				\
    for (i = 0; i < SieveSize; i++)\n		\
      if (flags[i]) {\n				\
	    prime = i + i + 3;\n				\
	    for (k = i + prime; k < SieveSize; k += prime)\n	\
	      flags[k] = 0;\n					\
	    count++;\n						\
      }\n							\
  }\n								\
  return count;\n						\
}\n								\
\n								\
void main (void) {\n						\
  printf (\"%d\\n\", sieve ());\n				\
}\n								\
";
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
    if (check (r)) {
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
