/* expr extensions */

#include <assert.h>
#include <string.h>
#include <ctype.h>
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

enum str_flag { FLAG_EXT = 1, FLAG_C89, FLAG_EXT89 };

typedef struct {
  const char *s;
  size_t key, flags;
} str_t;

DEF_VARR (str_t);
static VARR (str_t) *strs;

DEF_HTAB (str_t);
static HTAB (str_t) *str_tab;
static HTAB (str_t) *str_key_tab;

static int str_eq (str_t str1, str_t str2) { return strcmp (str1.s, str2.s) == 0; }
static htab_hash_t str_hash (str_t str) { return mum_hash (str.s, strlen (str.s), 0x42); }
static int str_key_eq (str_t str1, str_t str2) { return str1.key == str2.key; }
static htab_hash_t str_key_hash (str_t str) { return mum_hash64 (str.key, 0x24); }


static void str_init (void) {
  str_t string;
  
  VARR_CREATE (str_t, strs, 0);
  HTAB_CREATE (str_t, str_tab, 1000, str_hash, str_eq);
  HTAB_CREATE (str_t, str_key_tab, 200, str_key_hash, str_key_eq);
}

static str_t str_add (const char *s, size_t key, size_t flags, int key_p) {
  char *heap_s;
  str_t el, str;
  
  str.s = s;
  if (HTAB_DO (str_t, str_tab, str, HTAB_FIND, el))
    return el;
  if ((heap_s = malloc (strlen (s) + 1)) == NULL)
    error ("no memory");
  strcpy (heap_s, s); str.s = heap_s; str.key = key; str.flags = flags;
  VARR_PUSH (str_t, strs, str);
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
  size_t i;
  
  for (i = 1; i < VARR_LENGTH (str_t, strs); i++)
    free ((char *) VARR_ADDR (str_t, strs)[i].s);
  VARR_DESTROY (str_t, strs);
  HTAB_DESTROY (str_t, str_tab);
  HTAB_DESTROY (str_t, str_key_tab);
}


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
  N_IGNORE, N_L, N_LL, N_UL, N_ULL, N_F, N_D, N_LD, N_CH, N_STR, N_ID,
  N_COMMA, N_ANDAND, N_OROR, N_EQ, N_NE, N_LT, N_LE, N_GT, N_GE, N_ASSIGN,
  N_BITWISE_NOT, N_NOT, N_AND, N_AND_ASSIGN, N_OR, N_OR_ASSIGN, N_XOR, N_XOR_ASSIGN,
  N_LSH, N_LSH_ASSIGN, N_RSH, N_RSH_ASSIGN, N_ADD, N_ADD_ASSIGN, N_SUB, N_SUB_ASSIGN,
  N_MUL, N_MUL_ASSIGN, N_DIV, N_DIV_ASSIGN, N_MOD, N_MOD_ASSIGN,
  N_IND, N_FIELD, N_DEREF, N_DEREF_FIELD, N_COND, N_INC, N_DEC, N_POST_INC, N_POST_DEC,
  N_ALIGNOF, N_SIZEOF, N_EXPR_SIZEOF, N_CAST, N_COMPOUND_LITERAL, N_CALL,
  N_GENERIC, N_GENERIC_ASSOC
} node_code_t;

typedef struct node *node_t;
typedef struct node *all_node_list_elem_t;

DEF_DLIST_LINK (all_node_list_elem_t);
DEF_DLIST_LINK (node_t);
DEF_DLIST_TYPE (node_t);

struct node {
  node_code_t code;
  DLIST_LINK (all_node_list_elem_t) all_node_list_elem_link;
  DLIST_LINK (node_t) op_link;
  union {
    DLIST (node_t) ops;
    const char *s;
    char ch;
    long l;
    long long ll;
    unsigned long ul;
    unsigned long long ull;
    float f;
    double d;
    long double ld;
  } u;
};

DEF_DLIST (all_node_list_elem_t, all_node_list_elem_link);
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

static DLIST (all_node_list_elem_t) all_nodes;

static void remove_all_nodes (void) {
  node_t n, next_n;

  for (n = DLIST_HEAD (all_node_list_elem_t, all_nodes); n != NULL; n = next_n) {
    next_n = DLIST_NEXT (all_node_list_elem_t, n);
    free (n);
  }
}

static node_t new_node (node_code_t node_code) {
  node_t n = malloc (sizeof (struct node));

  if (n == NULL) error ("no memory");
  n->code = node_code;
  DLIST_INIT (node_t, n->u.ops);
  DLIST_APPEND (all_node_list_elem_t, all_nodes, n);
  return n;
}

static node_t new_const_node (node_code_t node_code) {
  node_t n = malloc (sizeof (struct node));

  if (n == NULL) error ("no memory");
  n->code = node_code;
  DLIST_APPEND (all_node_list_elem_t, all_nodes, n);
  return n;
}

static node_t new_str_node (node_code_t node_code, const char *s) {
  node_t n = new_const_node (node_code); n->u.s = s; return n;
}

static node_t new_ch_node (int ch) { node_t n = new_const_node (N_CH); n->u.ch = ch; return n; }
static node_t new_f_node (float f) { node_t n = new_const_node (N_F); n->u.f = f; return n; }
static node_t new_d_node (double d) { node_t n = new_const_node (N_D); n->u.d = d; return n; }
static node_t new_ld_node (long double ld) { node_t n = new_const_node (N_LD); n->u.ld = ld; return n; }
static node_t new_l_node (long l) { node_t n = new_const_node (N_L); n->u.l = l; return n; }
static node_t new_ll_node (long long ll) { node_t n = new_const_node (N_LL); n->u.ll = ll; return n; }
static node_t new_ul_node (unsigned long ul) { node_t n = new_const_node (N_UL); n->u.ul = ul; return n; }
static node_t new_ull_node (unsigned long long ull) { node_t n = new_const_node (N_ULL); n->u.ull = ull; return n; }

static void op_append (node_t n, node_t op) {
  DLIST_APPEND (node_t, n->u.ops, op);
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

#define P(f) do { if ((r = (f) (no_err_p)) == NULL) return NULL; } while (0)
#define PT(t) do {                              \
  if (! M(t)) {					\
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

static int try (nonterm_func_t f) {
  node_t r = &err_node;
  size_t mark;
  
  mark = record_start ();
  r = (f) (TRUE);
  record_stop (mark, r == NULL);
  return r != NULL;
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
    n = new_node (N_GENERIC); op_append (n, r);
    for (;;) { /* generic-assoc-list , generic-association */
      op = NULL;
      if (M (T_DEFAULT)) {
	P (type_name); op = r;
      }
      PT (':'); P (assign_expr);
      if (op != NULL) {
	gn = new_node (N_GENERIC_ASSOC);
	op_append (gn, op); op_append (gn, r); r = gn;
      }
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
  node_t r, n, op;
  node_code_t code;

  P (primary_expr);
  for (;;) {
    if (MC (T_INCDEC, code)) {
      code = code == N_INC ? N_POST_INC : N_POST_DEC;
      n = new_node (code); op = r; r = &err_node;
    } else if (MC ('.', code) || MC (T_ARROW, code)) {
      op = r;
      if (! MN (T_ID, r))
	return NULL;
    } else if (MC ('[', code)) {
      op = r; P (expr); PT (']');
    } else if (M ('(')) {
      op = r; r = NULL; code = N_CALL;
      if (! C (')')) {
	P (expr); /* expr list */
      }
      PT (')');
    } else break;
    n = new_node (code); op_append (n, op);
    if (r != NULL)
      op_append (n, r);
    r = n;
  }
  return r;
}

D (unary_expr) {
  node_t r, n, t;
  node_code_t code;

  if (TRY (par_type_name)) {
    code = N_CAST;
    if (M ('{')) {
      t = r; P (initializer_list);
      if (! M ('}')) return NULL;
      n = new_node (N_COMPOUND_LITERAL); op_append (n, t); op_append (n, r); return n;
    }
  } else if (M (T_SIZEOF) && TRY (par_type_name)) {
    n = new_node (N_SIZEOF); op_append (n, r); return n;
  } else if (M (T_SIZEOF)) {
    code = N_EXPR_SIZEOF;
  } else if (M (T_ALIGNOF)) {
    P (par_type_name); n = new_node (N_ALIGNOF); op_append (n, r); return n;
  } else if (! MC (T_INCDEC, code) && ! MC (T_UNOP, code) && ! MC (T_ADDOP, code) && ! MC ('*', code)) {
    P (post_expr); return r;
  } else if (code == N_MUL) {
    code = N_DEREF;
  }
  P (unary_expr); n = new_node (code); op_append (n, r);
  return n;
}

static node_t left_op (int no_err_p, int token, int token2, nonterm_func_t f) {
  node_t r, n;
  node_code_t code;

  P (f);
  while (MC (token, code) || (token2 >= 0 && MC (token2, code))) {
    n = new_node (code); op_append (n, r);
    P (f); op_append (n, r); r = n;
  }
  return r;
}

static node_t right_op (int no_err_p, int token, int token2, nonterm_func_t left, nonterm_func_t right) {
  node_t r, n;
  node_code_t code;

  P (left);
  if (MC (token, code) || (token2 >= 0 && MC (token2, code))) {
    n = new_node (code); op_append (n, r); P (right); op_append (n, r); r = n;
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
  n = new_node (N_COND); op_append (n, r);
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
  node_t r = &err_node;
  
  if (C (T_STATIC_ASSERT)) {
    P (st_assert);
  } else {
    P (declaration_specs);
    if (! C (';')) { /* init-declarator-list */
      for (;;) { /* init-declarator */
	P (declarator);
	if (M ('=')) {
	  P (initializer);
	}
	if ( ! M (','))
	  break;
      }
    }
    PT (';');
  }
  return r;
}

D (declaration_specs) {
  node_t r = &err_node;
  int first_p;
  
  for (first_p = TRUE;; first_p = FALSE) {
    if (C (T_ALIGNAS)) {
      P (align_spec);
    } else if (TRY (sc_spec)) {
    } else if (TRY (type_qual)) {
    } else if (TRY (func_spec)) {
    } else if (first_p) {
      P (type_spec);
    } else if (TRY (type_spec)) {
    } else break;
  }
  return r;
}

D (sc_spec) {
  node_t r = &err_node;
  
  if (M (T_TYPEDEF)) {
  } else if (M (T_EXTERN)) {
  } else if (M (T_STATIC)) {
  } else if (M (T_AUTO)) {
  } else if (M (T_REGISTER)) {
  } else {
    PT (T_THREAD_LOCAL);
  }
  return r;
}

D (type_spec) {
  node_t r = &err_node;
  int id_p = FALSE;
  
  if (M (T_VOID)) {
  } else if (M (T_CHAR)) {
  } else if (M (T_SHORT)) {
  } else if (M (T_INT)) {
  } else if (M (T_LONG)) {
  } else if (M (T_FLOAT)) {
  } else if (M (T_DOUBLE)) {
  } else if (M (T_SIGNED)) {
  } else if (M (T_UNSIGNED)) {
  } else if (M (T_BOOL)) {
  } else if (M (T_COMPLEX)) {
  } else if (M (T_ATOMIC)) { /* atomic-type-specifier */
    PT ('('); P (type_name); PT (')');
  } else if (M (T_STRUCT) || M (T_UNION)) { /* struct-or-union-specifier, struct-or-union */
    if (M (T_ID)) {
      id_p = TRUE;
    }
    if (M ('{')) {
      P (struct_declaration_list); PT ('}');
    } else if (! id_p)
      return NULL;
  } else if (M (T_ENUM)) { /* enum-specifier */
    if (M (T_ID)) {
      id_p = TRUE;
    }
    if (M ('{')) { /* enumerator-list */
      for (;;) { /* enumerator */
	PT (T_ID); /* enumeration-constant */
	if (M ('=')) {
	  P (const_expr);
	}
	if (! M (','))
	  break;
      }
      PT ('}');
    } else if (! id_p)
      return NULL;
  } else {
    P (typedef_name);
  }
  return r;
}

D (struct_declaration_list) {
  node_t r = &err_node;
  
  for (;;) {
    P (struct_declaration);
    if (C ('}')) break;
  }
  return r;
}

D (struct_declaration) {
  node_t r = &err_node;
  
  if (C (T_STATIC_ASSERT)) {
    P (st_assert);
  } else {
    P (spec_qual_list);
    if (! M (';')) { /* struct-declarator-list */
      for (;;) { /* struct-declarator */
	if (! C (':')) {
	  P (declarator);
	}
	if (M (':')) {
	  P (const_expr);
	}
	if (! M (','))
	  break;
      }
    }
  }
  return r;
}

D (spec_qual_list) {
  node_t r = &err_node;
  int first_p;
  
  for (first_p = TRUE;; first_p = FALSE) {
    if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
      P (type_qual);
    } else if (TRY (type_spec)) {
    } else if (first_p) {
      return NULL;
    } else {
      break;
    }
  }
  return r;
}

D (type_qual) {
  node_t r = &err_node;
  
  if (M (T_CONST)) {
  } else if (M (T_RESTRICT)) {
  } else if (M (T_VOLATILE)) {
  } else {
    PT (T_ATOMIC);
  }
  return r;
}

D (func_spec) {
  node_t r = &err_node;
  
  if (M (T_INLINE)) {
  } else {
    PT (T_NO_RETURN);
  }
  return r;
}

D (align_spec) {
  node_t r = &err_node;
  
  PT (T_ALIGNAS); PT ('(');
  if (TRY (type_name)) {
  } else {
    P (const_expr);
  }
  PT (')');
  return r;
}

D (declarator) {
  node_t r = &err_node;
  
  if (C ('*')) {
    P (pointer);
  }
  P (direct_declarator);
  return r;
}

D (direct_declarator) {
  node_t r = &err_node;
  
  if (M (T_ID)) {
  } else if (M ('(')) {
    P (declarator); PT (')');
  }
  for (;;) {
    if (M ('(')) {
      if (TRY (id_list)) {
      } else {
	P (param_type_list);
      }
      PT (')');
    } else if (M ('[')) {
      int static_p = FALSE;
      
      if (M (T_STATIC)) {
	static_p = TRUE;
      }
      if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
	P (type_qual_list);
	if (! static_p && M (T_STATIC)) {
	  static_p = TRUE;
	}	
      }
      if (static_p) {
	P (assign_expr);
      } else if (M ('*')) {
      } else if (! C (']')) {
	P (assign_expr);
      }
      PT (']');
    } else break;
  }
  return r;
}

D (pointer) {
  node_t r = &err_node;
  
  PT ('*');
  if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
    P (type_qual_list);
  }
  if (C ('*')) {
    P (pointer);
  }
  return r;
}

D (type_qual_list) {
  node_t r = &err_node;
  
  for (;;) {
    P (type_qual);
    if (! C (T_CONST) && ! C (T_RESTRICT) && ! C (T_VOLATILE) && ! C (T_ATOMIC))
      break;
  }
  return r;
}

D (param_type_list) {
  node_t r = &err_node;
  int comma_p;
  
  for (;;) { /* parameter-list, parameter-declaration */
    P (declaration_specs);
    if (TRY (declarator)) {
    } else if (! C (',') && ! C (')')) {
      P (abstract_declarator);
    }
    comma_p = FALSE;
    if (! M (','))
      break;
    comma_p = TRUE;
    if (C (T_DOTS))
      break;
  }
  if (comma_p) {
    PT (T_DOTS);
  }
  return r;
}
 
D (id_list) {
  node_t r = &err_node;
  
  for (;;) {
    PT (T_ID);
    if (! M (','))
      break;
  }
  return r;
}

D (abstract_declarator) {
  node_t r = &err_node;
  
  if (C ('*')) {
    P (pointer);
  }
  P (direct_abstract_declarator);
  return r;
}

D (direct_abstract_declarator) {
  node_t r = &err_node;
  
  if (TRY (abstract_declarator)) {
    if (! C ('(') && ! C ('['))
      return r;
  }
  for (;;) {
    if (M ('(')) {
      P (param_type_list); PT (')');
    } else {
      PT ('[');
      if (M ('*')) {
      } else {
	int static_p = FALSE;
	
	if (M (T_STATIC)) {
	  static_p = TRUE;
	}
	if (C (T_CONST) || C (T_RESTRICT) || C (T_VOLATILE) || C (T_ATOMIC)) {
	  P (type_qual_list);
	  if (! static_p && M (T_STATIC)) {
	    static_p = TRUE;
	  }
	}
	if (! C (']')) {
	  P (assign_expr);
	}
      }
      PT (']');
    }
    if (! C ('(') && ! C ('['))
      break;
  }
  return r;
}

D (typedef_name) {
  node_t r = &err_node;
  
  PT (T_ID);
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
  node_t r = &err_node;
  int first_p;
  
  for (;;) { /* designation */
    for (first_p = TRUE;; first_p = FALSE) {  /* designator-list, designator */
      if (M ('[')) {
	P (const_expr); PT (']');
      }	else if (M ('.')) {
	PT (T_ID);
      } else break;
    }
    if (!first_p) {
      PT ('=');
    }
    P (initializer);
    if (! M (','))
      break;
  }
  return r;
}

D (type_name) {
  node_t r = &err_node;

  P (spec_qual_list);
  if (! C (')') && ! C (':')) {
    P (abstract_declarator);
  }
  return r;
}

D (st_assert) {
  node_t r = &err_node;
  
  PT (T_STATIC_ASSERT); PT ('('); P (const_expr); PT (','); PT (')');  PT (';');
  return r;
}

/* Statements: */
D (compound_stmt);

D (label) {
  node_t r = &err_node;
  
  for (;;) {
    if (M (T_CASE)) {
    } else if (M (T_DEFAULT)) {
    } else {
      PT (T_ID); PT (':');
    }
  }
  return r;
}
 
D (stmt) {
  node_t r = &err_node;
  
  while (TRY (label)) {
  }
  if (C ('{')) {
    P (compound_stmt);
  } else if (M (T_IF)) { /* selection-statement */
    PT ('('); P (expr); PT (')'); P (stmt);
    if (M (T_ELSE)) {
      P (stmt);
    }
  } else if (M (T_SWITCH)) { /* selection-statement */
    PT ('('); P (expr); PT (')'); P (stmt);
  } else if (M (T_WHILE)) {  /* iteration-statement */
    PT ('('); P (expr); PT (')'); P (stmt);
  } else if (M (T_DO)) {  /* iteration-statement */
    P (stmt); PT (T_WHILE); PT ('('); P (expr); PT (')'); PT (';');
  } else if (M (T_FOR)) {  /* iteration-statement */
    PT ('(');
    if (TRY (declaration)) {
    } else if (! C (';')) {
      P (expr); PT (';');
    }
    if (! C (';')) {
      P (expr); PT (';');
    }
    if (! C (')')) {
      P (expr);
    }
    PT (')'); P (stmt);
  } else if (M (T_GOTO)) {  /* jump-statement */
    PT (T_ID); PT (';');
  } else if (M (T_CONTINUE)) {  /* jump-statement */
    PT (';');
  } else if (M (T_BREAK)) {  /* jump-statement */
    PT (';');
  } else if (M (T_RETURN)) {  /* jump-statement */
    if (! M (';')) {
      P (expr); PT (';');
    }
  } else { /* expression-statement */
    if (! C (';')) {
      P (expr);
    }
    PT (';');
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
  node_t r = &err_node;
  
  PTE ('{', err0);
  while (! C ('}')) { /* block-item-list, block_item */
    if (TRY (declaration)) {
    } else {
      PE (stmt, err1);
    }
    continue;
  err1: error_recovery (1);
  }
  PT ('}');
  return r;
 err0:  error_recovery (0);
  return r;
}
 
D (transl_unit) {
  node_t r = &err_node;

  curr_token.code = ';'; /* for error recovery */
  read_token ();
  while (! C (EOF)) { /* external-declaration */
    if (TRY (declaration)) {
    } else {
      PE (declaration_specs, err); PE (declarator, err);
      while (! C ('{')) { /* declaration-list */
	PE (declaration, err);
      }
      P (compound_stmt);
    }
    continue;
  err: error_recovery (0);
  }
  return r;
}

static void fatal_error (C_error_code_t code, const char *message) {
  fprintf (stderr, "%s\n", message); exit (1);
}

static void kw_add (const char *name, token_code_t tc, size_t flags) { str_add (name, tc, flags, TRUE); }

static void parse_init (void) {
  error_func = fatal_error;
  record_level = 0;
  VARR_CREATE (char, symbol_text, 100);
  VARR_CREATE (token_t, buffered_tokens, 32);
  VARR_CREATE (token_t, recorded_tokens, 32);
  DLIST_INIT (all_node_list_elem_t, all_nodes);
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
}

static node_t parse (void) {
  return transl_unit (FALSE);
}

static void parse_finish (void) {
  VARR_DESTROY (char, symbol_text);
  VARR_DESTROY (token_t, buffered_tokens);
  VARR_DESTROY (token_t, recorded_tokens);
  remove_all_nodes ();
  str_finish ();
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

int main (void) {
  double start_time = real_usec_time ();
  node_t r;
  
  code = "\n\
  static const while int SieveSize = 819000;\n\
  int sieve (void) {\n\
  int i, k, prime, count, iter;\n\
  for;char flags[SieveSize];\n\
\n\
  for (iter = 0; iter < 1000; iter++) {\n\
    count = 0;\n\
    for (i = 0; i < SieveSize; i++)\n\
      flags[i] = 1;\n\
    for (i = 0; i < SieveSize; i++)\n\
      if (flags[i]) {\n\
	    prime = i + i + 3;\n\
	    for (k = i + prime; k < SieveSize; k += prime)\n\
	      flags[k] = 0;\n\
	    count++;\n\
      }\n\
  }\n\
  return count;\n\
}\n\
\n\
void main (void) {\n\
  printf (\"%d\\n\", sieve ());\n\
}\n\
";
  curr_char = 0; c_getc = t_getc; c_ungetc = t_ungetc;
  parse_init ();
  fprintf (stderr, "parser_init end -- %.0f usec\n", real_usec_time () - start_time);
  r = parse ();
  fprintf (stderr, "parser end -- %.0f usec\n", real_usec_time () - start_time);
  if (r != NULL)
    fprintf (stderr, "OK\n");
  parse_finish ();
  fprintf (stderr, "parser_finish end -- %.0f usec\n", real_usec_time () - start_time);
  return 0;
}
#endif
