/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* C to MIR compiler.  It is a four pass compiler:
   o preprocessor pass generating tokens
   o parsing pass generating AST
   o context pass checking context constraints and augmenting AST
   o generation pass producing MIR

   The compiler implements C11 standard w/o C11 optional features:
   atomic, complex, variable size arrays. */

#include <assert.h>
#include <string.h>
#include <ctype.h>
#include <float.h>
#include <stdlib.h>
#include <stdarg.h>
#include <errno.h>
#include "time.h"

#include "mir.h"

#ifdef __x86_64__
#include "cx86_64.h"
#else
#error "undefined or unsupported generation target for C"
#endif

static int debug_p, verbose_p, asm_p, no_prepro_p, prepro_only_p;
/* Dirs to search include files in "" and in <>.  End mark is NULL. */
static const char **header_dirs, **system_header_dirs;

static const int max_nested_includes = 32;

#define MIR_VARR_ERROR alloc_error
#define MIR_HTAB_ERROR MIR_VARR_ERROR 

#define FALSE 0
#define TRUE 1

typedef enum {
  C_alloc_error, C_unfinished_comment, C_absent_exponent, C_wrong_octal_int, C_out_of_range_number,
  C_invalid_char_constant, C_no_string_end, C_invalid_str_constant, C_invalid_char,
} C_error_code_t;

static void (*error_func) (C_error_code_t code, const char *message);
static void alloc_error (const char *message) { error_func (C_alloc_error, message); }

#include "mir-varr.h"
#include "mir-dlist.h"
#include "mir-hash.h"
#include "mir-htab.h"

typedef struct node *node_t;

/* Some abbreviations: */
#define NL_HEAD(list) DLIST_HEAD (node_t, list)
#define NL_TAIL(list) DLIST_TAIL (node_t, list)
#define NL_LENGTH(list) DLIST_LENGTH (node_t, list)
#define NL_NEXT(el) DLIST_NEXT (node_t, el)
#define NL_REMOVE(list, el) DLIST_REMOVE (node_t, list, el)
#define NL_APPEND(list, el) DLIST_APPEND (node_t, list, el)
#define NL_PREPEND(list, el) DLIST_PREPEND (node_t, list, el)
#define NL_EL(list, n) DLIST_EL (node_t, list, n)

enum basic_type {
  TP_UNDEF, TP_VOID,
  /* Integer types: the first should be BOOL and the last should be
     ULLONG.  The order is important -- do not change it.  */
  TP_BOOL, TP_CHAR, TP_SCHAR, TP_UCHAR, TP_SHORT, TP_USHORT, TP_INT, TP_UINT, TP_LONG, TP_ULONG,
  TP_LLONG, TP_ULLONG,
  TP_FLOAT, TP_DOUBLE, TP_LDOUBLE,
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
  MIR_item_t proto_item;
};

enum type_mode {
  TM_UNDEF, TM_BASIC, TM_ENUM, TM_PTR, TM_STRUCT, TM_UNION, TM_ARR, TM_FUNC,
};

struct type {
  struct type_qual type_qual;
  node_t pos_node; /* set up and used only for checking type correctness */
  unsigned int incomplete_p : 1;
  /* Raw type size (w/o alignment type itself requirement but with
     element alignment requirements), undefined if mir_size_max.  */
  mir_size_t raw_size;
  int align; /* type align, undefined if < 0  */
  enum type_mode mode;
  union {
    enum basic_type basic_type;
    node_t tag_type; /* struct/union/enum */
    struct type *ptr_type;
    struct arr_type *arr_type;
    struct func_type *func_type;
  } u;
};

static mir_size_t raw_type_size (struct type *type) {
  assert (type->raw_size != MIR_SIZE_MAX);
  return type->raw_size;
}

#ifdef __x86_64__
#include "cx86_64-code.c"
#else
#error "undefined or unsupported generation target for C"
#endif

typedef void *void_ptr_t;
DEF_VARR (void_ptr_t);
static VARR (void_ptr_t) *reg_memory;

static void *reg_malloc (size_t s) {
  void *mem = malloc (s);

  if (mem == NULL)
    alloc_error ("no memory");
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

DEF_VARR (node_t);
static VARR (node_t) *call_nodes;

static int char_is_signed_p (void) {
  return MIR_CHAR_MAX == MIR_SCHAR_MAX;
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
static htab_hash_t str_hash (str_t str) { return mir_hash (str.s, strlen (str.s), 0x42); }
static int str_key_eq (str_t str1, str_t str2) { return str1.key == str2.key; }
static htab_hash_t str_key_hash (str_t str) { return mir_hash64 (str.key, 0x24); }

static const char *uniq_str (const char *str);

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
  strcpy (heap_s, s);
  str.s = heap_s; str.key = key; str.flags = flags;
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



/* ------------------------- Parser Start ------------------------------ */

/* Parser is manually written parser with back-tracing to keep original
   grammar close to C11 standard grammar as possible.  It has a
   rudimentary syntax error recovery based on stop symbols ';' and
   '}'.  The input is parse tokens and the output is the following AST
   nodes (the AST root is transl_unit):

expr : N_I | N_L | N_LL | N_U | N_UL | N_ULL | N_F | N_D | N_LD | N_CH | N_STR | N_ID
     | N_ADD (expr) | N_SUB (expr) | N_ADD (expr, expr) | N_SUB (expr, expr)
     | N_MUL (expr, expr) | N_DIV (expr, expr) | N_MOD (expr, expr)
     | N_LSH (expr, expr) | N_RSH (expr, expr)
     | N_NOT (expr) | N_BITWISE_NOT (expr)
     | N_INC (expr) | N_DEC (expr) | N_POST_INC (expr)| N_POST_DEC (expr)
     | N_ALIGNOF (type_name?) | N_SIZEOF (type_name) | N_EXPR_SIZEOF (expr)
     | N_CAST (type_name, expr) | N_COMMA (expr, expr) | N_ANDAND (expr, expr)
     | N_OROR (expr, expr) | N_EQ (expr, expr) | N_NE (expr, expr)
     | N_LT (expr, expr) | N_LE (expr, expr) | N_GT (expr, expr) | N_GE (expr, expr)
     | N_AND (expr, expr) | N_OR (expr, expr) | N_XOR (expr, expr)
     | N_ASSIGN (expr, expr) | N_ADD_ASSIGN (expr, expr) | N_SUB_ASSIGN (expr, expr)
     | N_MUL_ASSIGN (expr, expr) | N_DIV_ASSIGN (expr, expr) | N_MOD_ASSIGN (expr, expr)
     | N_LSH_ASSIGN (expr, expr) | N_RSH_ASSIGN (expr, expr)
     | N_AND_ASSIGN (expr, expr) | N_OR_ASSIGN (expr, expr) | N_XOR_ASSIGN (expr, expr)
     | N_DEREF (expr) | | N_ADDR (expr) | N_IND (expr, expr) | N_FIELD (expr, N_ID)
     | N_DEREF_FIELD (expr, N_ID) | N_COND (expr, expr, expr)
     | N_COMPOUND_LITERAL (type_name, initializer) | N_CALL (expr, N_LIST:(expr)*)
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
type_spec: N_VOID|N_CHAR|N_SHORT|N_INT|N_LONG|N_FLOAT|N_DOUBLE|N_SIGNED|N_UNSIGNED|N_BOOL
         | (N_STRUCT|N_UNION) (N_ID?, struct_declaration_list?)
	 | N_ENUM(N_ID?, N_LIST?: N_ENUM_COST(N_ID, const_expr?)*) | typedef_name
struct_declaration_list: N_LIST: struct_declaration+
struct_declaration: st_assert | N_MEMBER(N_SHARE(spec_qual_list), declarator?, const_expr?)
spec_qual_list: N_LIST:(type_qual|type_spec)*
declarator: the same as direct declarator
direct_declarator: N_DECL(N_ID,
                          N_LIST:(N_POINTER(type_qual_list) | N_FUNC(id_list|parameter_list)
                                            | N_ARR(N_STATIC?, type_qual_list,
                                                    (assign_expr|N_STAR)?))*)
pointer: N_LIST: N_POINTER(type_qual_list)*
type_qual_list : N_LIST: type_qual*
parameter_type_list: N_LIST:(N_SPEC_DECL(declaration_specs, declarator, ignore)
                             | N_TYPE(declaration_specs, abstract_declarator))+ [N_DOTS]
id_list: N_LIST: N_ID*
initializer: assign_expr | initialize_list
initialize_list: N_LIST: N_INIT(N_LIST:(const_expr | N_FIELD_ID (N_ID))* initializer)+
type_name: N_TYPE(spec_qual_list, abstract_declarator)
abstract_declarator: the same as abstract direct declarator
abstract_direct_declarator: N_DECL(ignore,
                                   N_LIST:(N_POINTER(type_qual_list) | N_FUNC(parameter_list)
                                           | N_ARR(N_STATIC?, type_qual_list,
                                                   (assign_expr|N_STAR)?))*)
typedef_name: N_ID
transl_unit: N_MODULE(N_LIST:(declaration
                              | N_FUNC_DEF(declaration_specs, declarator,
                                           N_LIST: declaration*, compound_stmt))*)

Here ? means it can be N_IGNORE, * means 0 or more elements in the list, + means 1 or more.

*/

typedef enum {
  T_NUMBER = 256, T_CH, T_STR, T_ID, T_ASSIGN, T_DIVOP, T_ADDOP, T_SH, T_CMP, T_EQNE, T_ANDAND, T_OROR,
  T_INCDEC, T_ARROW, T_UNOP, T_DOTS, T_BOOL, T_COMPLEX, T_ALIGNOF, T_ALIGNAS, T_ATOMIC, T_GENERIC,
  T_NO_RETURN, T_STATIC_ASSERT, T_THREAD_LOCAL, T_THREAD, T_AUTO, T_BREAK, T_CASE, T_CHAR, T_CONST,
  T_CONTINUE, T_DEFAULT, T_DO, T_DOUBLE, T_ELSE, T_ENUM, T_EXTERN, T_FLOAT, T_FOR, T_GOTO, T_IF,
  T_INLINE, T_INT, T_LONG, T_REGISTER, T_RESTRICT, T_RETURN, T_SHORT, T_SIGNED, T_SIZEOF, T_STATIC,
  T_STRUCT, T_SWITCH, T_TYPEDEF, T_TYPEOF, T_UNION, T_UNSIGNED, T_VOID, T_VOLATILE, T_WHILE,
  T_EOF,
  /* tokens existing in preprocessor only: */
  T_HEADER, /* include header */
  T_NO_MACRO_IDENT, /* ??? */
  T_DBLNO,          /* ## */
  T_PLM, T_RDBLNO,  /* placemarker, ## in replacement list */
  T_EOA, T_EOR,     /* end of argument and macro replacement */
  T_EOP,            /* end of processing */
  T_EOU,            /* end of translation unit */
} token_code_t;

typedef enum {
  N_IGNORE, N_I, N_L, N_LL, N_U, N_UL, N_ULL, N_F, N_D, N_LD, N_CH, N_STR, N_ID, N_COMMA, N_ANDAND,
  N_OROR, N_EQ, N_NE, N_LT, N_LE, N_GT, N_GE, N_ASSIGN, N_BITWISE_NOT, N_NOT, N_AND, N_AND_ASSIGN,
  N_OR, N_OR_ASSIGN, N_XOR, N_XOR_ASSIGN, N_LSH, N_LSH_ASSIGN, N_RSH, N_RSH_ASSIGN, N_ADD,
  N_ADD_ASSIGN, N_SUB, N_SUB_ASSIGN, N_MUL, N_MUL_ASSIGN, N_DIV, N_DIV_ASSIGN, N_MOD, N_MOD_ASSIGN,
  N_IND, N_FIELD, N_ADDR, N_DEREF, N_DEREF_FIELD, N_COND, N_INC, N_DEC, N_POST_INC, N_POST_DEC,
  N_ALIGNOF, N_SIZEOF, N_EXPR_SIZEOF, N_CAST, N_COMPOUND_LITERAL, N_CALL, N_GENERIC,
  N_GENERIC_ASSOC, N_IF, N_SWITCH, N_WHILE, N_DO, N_FOR, N_GOTO, N_CONTINUE, N_BREAK, N_RETURN,
  N_EXPR, N_BLOCK, N_CASE, N_DEFAULT, N_LABEL, N_LIST, N_SPEC_DECL, N_SHARE, N_TYPEDEF, N_EXTERN,
  N_STATIC, N_AUTO, N_REGISTER, N_THREAD_LOCAL, N_DECL, N_VOID, N_CHAR, N_SHORT, N_INT, N_LONG,
  N_FLOAT, N_DOUBLE, N_SIGNED, N_UNSIGNED, N_BOOL, N_STRUCT, N_UNION, N_ENUM,
  N_ENUM_CONST, N_MEMBER, N_CONST, N_RESTRICT, N_VOLATILE, N_ATOMIC, N_INLINE, N_NO_RETURN,
  N_ALIGNAS, N_FUNC, N_STAR, N_POINTER, N_DOTS, N_ARR, N_INIT, N_FIELD_ID, N_TYPE, N_ST_ASSERT,
  N_FUNC_DEF, N_MODULE
} node_code_t;

DEF_DLIST_LINK (node_t);
DEF_DLIST_TYPE (node_t);

typedef struct pos {
  const char *fname;
  int lno, ln_pos;
} pos_t;

static const pos_t no_pos = {NULL, -1, -1};

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
    mir_llong ll;
    mir_ulong ul;
    mir_ullong ull;
    mir_float f;
    mir_double d;
    mir_ldouble ld;
    node_t scope;
  } u;
  void *attr;
};

DEF_DLIST_CODE (node_t, op_link);

static struct node err_node;

typedef struct token {
  token_code_t code : 16;
  int processed_p : 16;
  pos_t pos;
  node_code_t node_code;
  node_t node;
  const char *repr;
} *token_t;

static node_t add_pos (node_t n, pos_t p) {
  if (n->pos.lno < 0)
    n->pos = p;
  return n;
}

static node_t op_append (node_t n, node_t op) {
  NL_APPEND (n->ops, op);
  return add_pos (n, op->pos);
}

static void op_flat_append (node_t n, node_t op) {
  if (op->code != N_LIST) {
    op_append (n, op);
    return;
  }
  for (node_t next_el, el = NL_HEAD (op->ops); el != NULL; el = next_el) {
    next_el = NL_NEXT (el);
    NL_REMOVE (op->ops, el);
    op_append (n, el);
  }
}

static unsigned long curr_uid;

static node_t new_node (node_code_t nc) {
  node_t n = reg_malloc (sizeof (struct node));

  n->code = nc; n->uid = curr_uid++;
  DLIST_INIT (node_t, n->ops);
  n->attr = NULL; n->pos = no_pos;
  return n;
}

static node_t new_pos_node (node_code_t nc, pos_t p) { return add_pos (new_node (nc), p); }
static node_t new_node1 (node_code_t nc, node_t op1) { return op_append (new_node (nc), op1); }
static node_t new_pos_node1 (node_code_t nc, pos_t p, node_t op1) {
  return add_pos (new_node1 (nc, op1), p);
}
static node_t new_node2 (node_code_t nc, node_t op1, node_t op2) {
  return op_append (new_node1 (nc, op1), op2);
}
static node_t new_pos_node2 (node_code_t nc, pos_t p, node_t op1, node_t op2) {
  return add_pos (new_node2 (nc, op1, op2), p);
}
static node_t new_node3 (node_code_t nc, node_t op1, node_t op2, node_t op3) {
  return op_append (new_node2 (nc, op1, op2), op3);
}
static node_t new_pos_node3 (node_code_t nc, pos_t p, node_t op1, node_t op2, node_t op3) {
  return add_pos (new_node3 (nc, op1, op2, op3), p);
}
static node_t new_node4 (node_code_t nc, node_t op1, node_t op2, node_t op3, node_t op4) {
  return op_append (new_node3 (nc, op1, op2, op3), op4);
}
static node_t new_pos_node4 (node_code_t nc, pos_t p,
			     node_t op1, node_t op2, node_t op3, node_t op4) {
  return add_pos (new_node4 (nc, op1, op2, op3, op4), p);
}
static node_t new_ch_node (int ch, pos_t p) {
  node_t n = new_pos_node (N_CH, p);

  n->u.ch = ch;
  return n;
}
static node_t new_i_node (long l, pos_t p) {
  node_t n = new_pos_node (N_I, p);

  n->u.l = l;
  return n;
}
static node_t new_l_node (long l, pos_t p) {
  node_t n = new_pos_node (N_L, p);

  n->u.l = l;
  return n;
}
static node_t new_ll_node (long long ll, pos_t p) {
  node_t n = new_pos_node (N_LL, p);

  n->u.ll = ll;
  return n;
}
static node_t new_u_node (unsigned long ul, pos_t p) {
  node_t n = new_pos_node (N_U, p);

  n->u.ul = ul;
  return n;
}
static node_t new_ul_node (unsigned long ul, pos_t p) {
  node_t n = new_pos_node (N_UL, p);

  n->u.ul = ul;
  return n;
}
static node_t new_ull_node (unsigned long long ull, pos_t p) {
  node_t n = new_pos_node (N_ULL, p);

  n->u.ull = ull;
  return n;
}
static node_t new_f_node (float f, pos_t p) {
  node_t n = new_pos_node (N_F, p);

  n->u.f = f;
  return n;
}
static node_t new_d_node (double d, pos_t p) {
  node_t n = new_pos_node (N_D, p);

  n->u.d = d;
  return n;
}
static node_t new_ld_node (long double ld, pos_t p) {
  node_t n = new_pos_node (N_LD, p);

  n->u.ld = ld;
  return n;
}
static node_t new_str_node (node_code_t nc, const char *s, pos_t p) {
  node_t n = new_pos_node (nc, p);

  n->u.s = s;
  return n;
}

static node_t get_op (node_t n, int nop) {
  n = NL_HEAD (n->ops);
  for (; nop > 0; nop--)
    n = NL_NEXT (n);
  return n;
}

static const char *uniq_str (const char *str) {
  return str_add (str, T_STR, 0, FALSE).s;
}

static token_t new_token (pos_t pos, const char *repr, int token_code, node_code_t node_code) {
  token_t token = reg_malloc (sizeof (struct token));
  
  token->code = token_code; token->processed_p = FALSE;
  token->pos = pos; token->repr = repr;
  token->node_code = node_code; token->node = NULL;
  return token;
}

static token_t new_token_wo_uniq_repr (pos_t pos, const char *repr,
					   int token_code, node_code_t node_code) {
  return new_token (pos, uniq_str (repr), token_code, node_code);
}

static token_t new_node_token (pos_t pos, const char *repr, int token_code, node_t node) {
  token_t token = new_token_wo_uniq_repr (pos, repr,  token_code, N_IGNORE);
  
  token->node = node;
  return token;
}

static void print_pos (FILE *f, pos_t pos, int col_p) {
  if (pos.lno < 0)
    return;
  fprintf (f, "%s:%d", pos.fname, pos.lno);
  if (col_p)
    fprintf (f, ":%d: ", pos.ln_pos);
}

static const char *get_token_name (int token_code) {
  static char buf[30];
  const char *s;
  
  switch (token_code) {
  case T_NUMBER:
    return "number";
  case T_CH:
    return "char constant";
  case T_STR:
    return "string";
  case T_ID:
    return "identifier";
  case T_ASSIGN:
    return "assign op";
  case T_DIVOP:
    return "/ or %";
  case T_ADDOP:
    return "+ or -";
  case T_SH:
    return "shift op";
  case T_CMP:
    return "comparison op";
  case T_EQNE:
    return "equality op";
  case T_ANDAND:
    return "&&";
  case T_OROR:
    return "||";
  case T_INCDEC:
    return "++ or --";
  case T_ARROW:
    return "->";
  case T_UNOP:
    return "unary op";
  case T_DOTS:
    return "...";
  default:
    if ((s = find_str_by_key (token_code)) != NULL) // ???
      return s;
    if (isprint (token_code))
      sprintf (buf, "%c", token_code);
    else
      sprintf (buf, "%d", token_code);
    return buf;
  }
}

static int (*c_getc) (void);
static void (*c_ungetc) (int c);

static unsigned n_errors, n_warnings;

static void error (pos_t pos, const char *format, ...) {
  va_list args;
   
  n_errors++;
  va_start (args, format);
  print_pos (stderr, pos, TRUE);
  vfprintf (stderr, format, args);
  va_end (args);
  fprintf (stderr, "\n");
}

static void warning (pos_t pos, const char *format, ...) {
  va_list args;
   
  n_warnings++;
  va_start (args, format);
  print_pos (stderr, pos, TRUE);
  fprintf (stderr, "warning -- ");
  vfprintf (stderr, format, args);
  va_end (args);
  fprintf (stderr, "\n");
}

#define TAB_STOP 8

DEF_VARR (char);

typedef struct stream {
  FILE *f;                         /* the current file, NULL for top level file */
  const char *fname;               /* NULL only for sting stream */
  VARR (char) *ln;                 /* stream current line in reverse order */
  pos_t pos;                       /* includes file name used for reports */
  fpos_t fpos;                     /* file pos to resume stream */
  int ifs_length_at_stream_start;  /* length of ifs at the stream start */
} *stream_t;

DEF_VARR (stream_t);
static VARR (stream_t) *streams;  /* stack of streams */
static stream_t cs, eof_s;        /* current stream and stream corresponding the last EOF */
  
static void init_streams (void) {
  eof_s = NULL;
  VARR_CREATE (stream_t, streams, 32);
}

static void free_stream (stream_t s) {
  VARR_DESTROY (char, s->ln);
  free (s);
}

static void finish_streams (void) {
  if (eof_s != NULL)
    free_stream (eof_s);
  while (VARR_LENGTH (stream_t, streams) != 0)
    free_stream (VARR_POP (stream_t, streams));
  VARR_DESTROY (stream_t, streams);
}

static stream_t new_stream (FILE *f, const char *fname) {
  stream_t s = malloc (sizeof (struct stream));
  
  VARR_CREATE (char, s->ln, 128);
  s->f = f; s->fname = s->pos.fname = fname;
  s->pos.lno = 1; s->pos.ln_pos = 0; s->ifs_length_at_stream_start = 0;
  return s;
}

static void add_stream (FILE *f, const char *fname) {
  assert (fname != NULL);
  if (cs != NULL && cs->f !=  NULL && cs->f != stdin) {
    fgetpos (cs->f, &cs->fpos);
    fclose (cs->f);
  }
  cs = new_stream (f, fname);
  VARR_PUSH (stream_t, streams, cs);
}

static void change_stream_pos (pos_t pos) {
  cs->pos = pos;
}

static void remove_trigraphs (void) {
  int len = VARR_LENGTH (char, cs->ln);
  char *addr = VARR_ADDR (char, cs->ln);
  int i, start, to, ch;
  
  for (i = to = 0; i < len; i++, to++) {
    addr[to] = addr[i];
    for (start = i; i < len && addr[i] == '?'; i++, to++)
      addr[to] = addr[i];
    if (i >= len)
      break;
    if (i < start + 2) {
      addr[to] = addr[i];
      continue;
    }
    switch (addr[i]) {
    case '=': ch = '#'; break;
    case '(': ch = '['; break;
    case '/': ch = '\\'; break;
    case ')': ch = ']'; break;
    case '\'': ch = '^'; break;
    case '<': ch = '{'; break;
    case '!': ch = '|'; break;
    case '>': ch = '}'; break;
    case '-': ch = '~'; break;
    default: ch = 0; break;
    }
    if (ch == 0)
      continue;
    to -= 2;
    addr[to] = ch;
    len -= 2;
  }
  VARR_TRUNC (char, cs->ln, len);
}
  
static int ln_get (FILE *f) {
  if (f == NULL)
    return c_getc (); /* top level */
  return fgetc (f);
}

static char *reverse (VARR (char)  *v) {
  char *addr = VARR_ADDR (char, v);
  int i, j, temp, last = (int) VARR_LENGTH (char, v) - 1;
  
  if (last >= 0 && addr[last] == '\0')
    last--;
  for (i = last, j = 0; i > j; i--, j++) {
    temp = addr[i]; addr[i] = addr[j]; addr[j] = temp;
  }
  return addr;
}

static int get_line (void) { /* translation phase 1 and 2 */
  int c, eof_p = 0;

  VARR_TRUNC (char, cs->ln, 0);
  for (c = ln_get (cs->f); c != EOF && c != '\n'; c = ln_get (cs->f))
    VARR_PUSH (char, cs->ln, c);
  eof_p = c == EOF;
  if (eof_p) {
    if (VARR_LENGTH (char, cs->ln) == 0)
      return FALSE;
    if (c != '\n')
      error (cs->pos, "no end of line at file end");
  }
  remove_trigraphs ();
  VARR_PUSH (char, cs->ln, '\n');
  reverse (cs->ln);
  return TRUE;
}

static int cs_get (void) {
  if (VARR_LENGTH (char, cs->ln) > 0) {
    cs->pos.ln_pos++;
    return VARR_POP (char, cs->ln);
  }
  if (cs->fname != NULL && get_line ()) {
    assert (VARR_LENGTH (char, cs->ln) > 0);
    cs->pos.ln_pos = 0;
    return VARR_POP (char, cs->ln);
  }
  return EOF;
}
  
static void cs_unget (int c) {
  cs->pos.ln_pos--;
  VARR_PUSH (char, cs->ln, c);
}
  
static void set_string_stream (const char *str, pos_t pos,
			       void (*transform) (const char *, VARR (char) *)) {
  /* read from string str */
  cs = new_stream (NULL, NULL);
  VARR_PUSH (stream_t, streams, cs);
  cs->pos = pos;
  if (transform != NULL) {
    transform (str, cs->ln);
  } else {
    for (; *str != '\0'; str++)
      VARR_PUSH (char, cs->ln, *str);
  }
}

static void remove_string_stream (void) {
  assert (cs->f == NULL && cs->f == NULL);
  free_stream (VARR_POP (stream_t, streams));
  cs = VARR_LAST (stream_t, streams);
}

static VARR (char) *symbol_text, *temp_string;

static int set_string_val (token_t t, VARR (char) *temp) {
  int i, str_len, curr_c, lns_num = 0;
  const char *str;

  assert (t->code == T_STR || t->code == T_CH);
  str = t->repr;
  VARR_TRUNC (char, temp, 0);
  str_len = strlen (str);
  assert (str_len >= 2 && (str[0] == '"' || str[0] == '\'') && str[0] == str[str_len - 1]);
  for (i = 1; i < str_len - 1; i++) {
    curr_c = str[i];
    if (curr_c != '\\') {
      VARR_PUSH (char, temp, curr_c);
      continue;
    }
    curr_c = str[++i];
    switch (curr_c) {
    case 'a':
      curr_c = '\a';
      break;
    case 'b':
      curr_c = '\b';
      break;
    case 'n':
      curr_c = '\n';
      break;
    case 'f':
      curr_c = '\f';
      break;
    case 'r':
      curr_c = '\r';
      break;
    case 't':
      curr_c = '\t';
      break;
    case 'v':
      curr_c = '\v';
      break;
    case '\\': case '\'': case '\?': case '\"':
      break;
    case '\n':
      lns_num++;
      break;
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': {
      unsigned long v = curr_c;

      curr_c = str[++i];
      if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9') {
	i--;
      } else {
	v = v * 8 + curr_c; curr_c = str[++i];
	if (! isdigit (curr_c) || curr_c == '8' || curr_c == '9')
	  i--;
	else
	  v = v * 8 + curr_c;
      }
      curr_c = v;
      break;
    }
    case 'x': case 'X': {
      int first_p = TRUE;
      unsigned long v = 0;
      
      for (i++; ; i++) {
	curr_c = str[i];
	if (! isxdigit (curr_c))
	  break;
	first_p = FALSE; v *= 16;
	v += (isdigit (curr_c) ? curr_c - '0'
	      : islower (curr_c) ? curr_c - 'a' + 10 : curr_c - 'A' + 10);
      }
      if (first_p)
	error (t->pos, "wrong hexadecimal char %c", curr_c);
      else if (v > MIR_UCHAR_MAX)
	error (t->pos, "too big hexadecimal char 0x%x", v);
      curr_c = v;
      i--;
      break;
    }
    default:
      error (t->pos, "wrong escape char 0x%x", curr_c);
      curr_c = 0;
    }
    if (curr_c != 0)
      VARR_PUSH (char, temp, curr_c);
  }
  VARR_PUSH (char, temp, '\0');
  if (t->repr[0] == '"')
    t->node->u.s = uniq_str (VARR_ADDR (char, temp));
  else if (VARR_LENGTH (char, temp) == 1)
    error (t->pos, "empty char constant");
  else
    t->node->u.ch = VARR_GET (char, temp, 0);
  return lns_num;
}

static token_t new_id_token (pos_t pos, const char *id_str) {
  token_t token;
  const char *str = uniq_str (id_str);
  
  token = new_token (pos, str, T_ID, N_IGNORE);
  token->node = new_str_node (N_ID, str, pos);
  return token;
}

DEF_VARR (token_t);
static VARR (token_t) *buffered_tokens;

static token_t get_next_pptoken_1 (int header_p) {
  int start_c, curr_c, nl_p, comment_char;
  pos_t pos;
  
  if (cs->fname != NULL && VARR_LENGTH (token_t, buffered_tokens) != 0) {
    return VARR_POP (token_t, buffered_tokens);
  }
  VARR_TRUNC (char, symbol_text, 0);
  for (;;) {
    curr_c = cs_get ();
    /* Process sequence of white spaces/comments: */
    for (comment_char = -1, nl_p = FALSE;; curr_c = cs_get ()) {
      switch (curr_c) {
      case '\t':
	cs->pos.ln_pos = (cs->pos.ln_pos / TAB_STOP + 1) * TAB_STOP;
	/* fall through */
      case ' ': case '\f': case '\r': case '\v':
	break;
      case '\n':
	cs->pos.lno++; cs->pos.ln_pos = 0;
	if (comment_char < 0) {
	  nl_p = TRUE;
	} else if (comment_char == '/') {
	  comment_char = -1;
	}
	break;
      case '/':
	if (comment_char >= 0)
	  break;
	curr_c = cs_get ();
	if (curr_c == '/' || curr_c == '*') {
	  VARR_PUSH (char, symbol_text, '/');
	  comment_char = curr_c;
	  break;
	}
	cs_unget (curr_c);
	curr_c = '/';
	goto end_ws;
      case '*':
	if (comment_char < 0)
	  goto end_ws;
	if (comment_char != '*')
	  break;
	VARR_PUSH (char, symbol_text, '*');
	curr_c = cs_get ();
	if (curr_c == '/')
	  comment_char = -1;
	break;
      case '\\':
	curr_c = cs_get ();
	if (curr_c == '\n') {
	  cs->pos.lno++; cs->pos.ln_pos = 0;
	  continue;
	}
	cs_unget (curr_c);
	curr_c = '\\';
	/* fall through */
      default:
	if (comment_char < 0)
	  goto end_ws;
	if (curr_c == EOF) {
	  error_func (C_unfinished_comment, "unfinished comment");
	  goto end_ws;
	}
	break;
      }
      VARR_PUSH (char, symbol_text, curr_c);
    }
  end_ws:
    if (VARR_LENGTH (char, symbol_text) != 0) {
      cs_unget (curr_c);
      VARR_PUSH (char, symbol_text, '\0');
      return new_token_wo_uniq_repr (cs->pos, VARR_ADDR (char, symbol_text),
				     nl_p ? '\n' : ' ',  N_IGNORE);
    }
    if (header_p && (curr_c == '<' || curr_c == '\"')) {
      int i, stop;
      
      pos = cs->pos;
      VARR_TRUNC (char, temp_string, 0);
      for (stop = curr_c == '<' ? '>' : '\"';;) {
	VARR_PUSH (char, symbol_text, curr_c);
	curr_c = cs_get ();
	VARR_PUSH (char, temp_string, curr_c);
	if (curr_c == stop || curr_c == '\n' || curr_c == EOF)
	  break;
      }
      if (curr_c == stop) {
	VARR_PUSH (char, symbol_text, curr_c);
	VARR_PUSH (char, symbol_text, '\0');
	VARR_POP (char, temp_string);
	VARR_PUSH (char, temp_string, '\0');
	return new_node_token (pos, VARR_ADDR (char, symbol_text), T_HEADER,
			       new_str_node (N_STR, uniq_str (VARR_ADDR (char, temp_string)), pos));
      } else {
	VARR_PUSH (char, symbol_text, curr_c);
	for (i = 0; i < VARR_LENGTH (char, symbol_text); i++)
	  cs_unget (VARR_GET (char, symbol_text, i));
	curr_c = (stop == '>' ? '<' : '\"');
      }
    }
    switch (start_c = curr_c) {
    case '\\':
      curr_c = cs_get ();
      assert (curr_c != '\n');
      cs_unget (curr_c);
      return new_token (cs->pos, "\\", '\\', N_IGNORE);
    case '~':
      return new_token (cs->pos, "~", T_UNOP, N_BITWISE_NOT);
    case '+': case '-':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == start_c) {
	if (start_c == '+')
	  return new_token (pos, "++", T_INCDEC, N_INC);
	else
	  return new_token (pos, "--", T_INCDEC, N_DEC);
      } else if (curr_c == '=') {
	if (start_c == '+')
	  return new_token (pos, "+=", T_ASSIGN, N_ADD_ASSIGN);
	else
	  return new_token (pos, "-=", T_ASSIGN, N_SUB_ASSIGN);
      } else if (start_c == '-' && curr_c == '>') {
	return new_token (pos, "->", T_ARROW, N_DEREF_FIELD);
      } else if (isdigit (curr_c)) {
	cs_unget (curr_c);
	curr_c = start_c;
	goto number;
      } else if (curr_c == '.') {
	curr_c = cs_get ();
	if (isdigit (curr_c)){
	  cs_unget ('.');
	  cs_unget (curr_c);
	  curr_c = start_c;
	  goto number;
	} else {
	  cs_unget ('.');
	  cs_unget (curr_c);
	  if (start_c == '+')
	    return new_token (pos, "+", T_ADDOP, N_ADD);
	  else
	    return new_token (pos, "-", T_ADDOP, N_SUB);
	}
      } else {
	cs_unget (curr_c);
	if (start_c == '+')
	  return new_token (pos, "+", T_ADDOP, N_ADD);
	else
	  return new_token (pos, "-", T_ADDOP, N_SUB);
      }
      assert (FALSE);
    case '=':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == '=') {
	return new_token (pos, "==", T_EQNE, N_EQ);
      } else {
	cs_unget (curr_c);
	return new_token (pos, "=", '=', N_ASSIGN);
      }
      assert (FALSE);
    case '<': case '>':
      pos = cs->pos; curr_c = cs_get ();
      if (curr_c == start_c) {
	curr_c = cs_get (); 
	if (curr_c == '=') {
	  if (start_c == '<')
	    return new_token (pos, "<<=", T_ASSIGN, N_LSH_ASSIGN);
	  else
	    return new_token (pos, ">>=", T_ASSIGN, N_RSH_ASSIGN);
	} else {
	  cs_unget (curr_c);
	  if (start_c == '<')
	    return new_token (pos, "<<", T_SH, N_LSH);
	  else
	    return new_token (pos, ">>", T_SH, N_RSH);
	}
      } else if (curr_c == '=') {
	if (start_c == '<')
	  return new_token (pos, "<=", T_CMP, N_LE);
	else
	  return new_token (pos, ">=", T_CMP, N_GE);
      } else if (start_c == '<' && curr_c == ':') {
	return new_token (pos, "<:", '[', N_IGNORE);
      } else if (start_c == '<' && curr_c == '%') {
	return new_token (pos, "<%", '{', N_IGNORE);
      } else {
	cs_unget (curr_c);
	if (start_c == '<')
	  return new_token (pos, "<", T_CMP, N_LT);
	else
	  return new_token (pos, ">", T_CMP, N_GT);
      }
      assert (FALSE);
    case '*':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == '=') {
	return new_token (pos, "*=", T_ASSIGN, N_MUL_ASSIGN);
      } else {
	cs_unget (curr_c);
	return new_token (pos, "*", '*', N_MUL);
      }
      assert (FALSE);
    case '/':
      pos = cs->pos;
      curr_c = cs_get ();
      assert (curr_c != '/' && curr_c != '*');
      if (curr_c == '=')
	return new_token (pos, "/=", T_ASSIGN, N_DIV_ASSIGN);
      assert (curr_c != '*' && curr_c != '/'); /* we already processed comments */
      cs_unget (curr_c);
      return new_token (pos, "/", T_DIVOP, N_DIV);
    case '%':
      pos = cs->pos; curr_c = cs_get ();
      if (curr_c == '=') {
	return new_token (pos, "%=", T_ASSIGN, N_MOD_ASSIGN);
      } else if (curr_c == '>') {
	return new_token (pos, "%>", '}', N_IGNORE);
      } else if (curr_c == ':') {
	curr_c = cs_get ();
	if (curr_c != '%') {
	  cs_unget (curr_c);
	  return new_token (pos, "%:", '#', N_IGNORE);
	} else {
	  curr_c = cs_get ();
	  if (curr_c == ':')
	    return new_token (pos, "%:%:", T_DBLNO, N_IGNORE);
	  else {
	    cs_unget ('%');
	    cs_unget (curr_c);
	    return new_token (pos, "%:", '#', N_IGNORE);
	  }
	}
      } else {
	cs_unget (curr_c);
	return new_token (pos, "%", T_DIVOP, N_MOD);
      }
      assert (FALSE);
    case '&': case '|':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == '=') {
	if (start_c == '&')
	  return new_token (pos, "&=", T_ASSIGN, N_AND_ASSIGN);
	else
	  return new_token (pos, "|=", T_ASSIGN, N_OR_ASSIGN);
      } else if (curr_c == start_c) {
	if (start_c == '&')
	  return new_token (pos, "&&", T_ANDAND, N_ANDAND);
	else
	  return new_token (pos, "||", T_OROR, N_OROR);
      } else {
	cs_unget (curr_c);
	if (start_c == '&')
	  return new_token (pos, "&", start_c, N_AND);
	else
	  return new_token (pos, "|", start_c, N_OR);
      }
      assert (FALSE);
    case '^': case '!':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == '=') {
	if (start_c == '^')
	return new_token (pos, "^=", T_ASSIGN, N_XOR_ASSIGN);
	else
	return new_token (pos, "!=",  T_EQNE, N_NE);
      } else {
	cs_unget (curr_c);
	if (start_c == '^')
	  return new_token (pos, "^", '^', N_XOR);
	else
	  return new_token (pos, "!", T_UNOP, N_NOT);

      }
      assert (FALSE);
    case ';':
      return new_token (cs->pos, ";", curr_c, N_IGNORE);
    case '?':
      return new_token (cs->pos, "?", curr_c, N_IGNORE);
    case '(':
      return new_token (cs->pos, "(", curr_c, N_IGNORE);
    case ')':
      return new_token (cs->pos, ")", curr_c, N_IGNORE);
    case '{':
      return new_token (cs->pos, "{", curr_c, N_IGNORE);
    case '}':
      return new_token (cs->pos, "}", curr_c, N_IGNORE);
    case ']':
      return new_token (cs->pos, "]", curr_c, N_IGNORE);
    case EOF: {
      pos_t pos = cs->pos;
      
      if (eof_s != NULL)
	free_stream (eof_s);
      if (cs->f != stdin && cs->f != NULL)
	fclose (cs->f);
      eof_s = VARR_POP (stream_t, streams);
      if (VARR_LENGTH (stream_t, streams) == 0) {
	return new_token (pos, "<EOU>", T_EOU, N_IGNORE);
      }
      cs = VARR_LAST (stream_t, streams);
      if (cs->fname != NULL && VARR_LENGTH (stream_t, streams) > 1) {
	cs->f = fopen (cs->fname, "r");
	fsetpos (cs->f, &cs->fpos);
      }
      return new_token (cs->pos, "<EOF>", T_EOF, N_IGNORE);
    }
    case ':':
      curr_c = cs_get ();
      if (curr_c == '>') {
	return new_token (cs->pos, ":>", ']', N_IGNORE);
      } else {
	cs_unget (curr_c);
	return new_token (cs->pos, ":", ':', N_IGNORE);
      }
    case '#':
      curr_c = cs_get ();
      if (curr_c == '#') {
	return new_token (cs->pos, "##", T_DBLNO, N_IGNORE);
      } else {
	cs_unget (curr_c);
	return new_token (cs->pos, "#", '#', N_IGNORE);
      }
    case ',':
      return new_token (cs->pos, ",", ',', N_COMMA);
    case '[':
      return new_token (cs->pos, "[", '[', N_IND);
    case '.':
      pos = cs->pos;
      curr_c = cs_get ();
      if (curr_c == '.') {
	curr_c = cs_get ();
	if (curr_c == '.') {
	  return new_token (pos, "...", T_DOTS, N_IGNORE);
	} else {
	  cs_unget ('.');
	  cs_unget (curr_c);
	  return new_token (pos, ".", '.', N_FIELD);
	}
      } else if (! isdigit (curr_c)) {
	cs_unget (curr_c);
	return new_token (pos, ".", '.', N_FIELD);
      }
      cs_unget (curr_c);
      curr_c = '.';
    number:
      /* Fall through: */
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9': {
      int base = 10, err_p = FALSE, double_p = FALSE;
      int dec_p = FALSE, hex_p = FALSE;
      int prev_c, hex_char_p;
      
      pos = cs->pos;
      VARR_TRUNC (char, symbol_text, 0);
      if (curr_c == '+' || curr_c == '-') {
	VARR_PUSH (char, symbol_text, curr_c);
	curr_c = cs_get ();
      }
      if (curr_c == '0') {
	curr_c = cs_get ();
	if (curr_c != 'x' && curr_c != 'X') {
	  base = 8;
	  cs_unget (curr_c);
	  curr_c = '0';
	} else {
	  VARR_PUSH (char, symbol_text, '0');
	  VARR_PUSH (char, symbol_text, 'x');
	  curr_c = cs_get ();
	  base = 16;
	}
      }
      for (;;) {
	VARR_PUSH (char, symbol_text, curr_c);
	curr_c = cs_get ();
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
	  VARR_PUSH (char, symbol_text, curr_c);
	  curr_c = cs_get ();
	} while (isdigit (curr_c));
      }
      if ((base != 16 && (curr_c == 'e' || curr_c == 'E'))
	  || (base == 16 && (curr_c == 'p' || curr_c == 'P'))) {
	double_p = TRUE;
	prev_c = curr_c;
	curr_c = cs_get ();
	if (curr_c != '+' && curr_c != '-' && ! isdigit (curr_c)) {
	  error_func (C_absent_exponent, "absent exponent");
	  err_p = TRUE;
	} else {
	  VARR_PUSH (char, symbol_text, prev_c);
	  if (curr_c == '+' || curr_c == '-') {
	    VARR_PUSH (char, symbol_text, curr_c);
	    curr_c = cs_get ();
	    if (! isdigit (curr_c)) {
	      error_func (C_absent_exponent, "absent exponent");
	      err_p = TRUE;
	    }
	  }
	  if (! err_p) {
	    do {
	      VARR_PUSH (char, symbol_text, curr_c);
	      curr_c = cs_get ();
	    } while (isdigit (curr_c));
	  }
	}
      }
      if (double_p) {
	if (curr_c == 'f' || curr_c == 'F') {
	  VARR_PUSH (char, symbol_text, curr_c);
	  curr_c = cs_get ();
	} else if (curr_c == 'l' || curr_c == 'L') {
	  VARR_PUSH (char, symbol_text, curr_c);
	  curr_c = cs_get ();
	}
      } else {
	int c2 = cs_get (), c3 = cs_get ();
	
	if (((curr_c == 'u' || curr_c == 'U')
	     && (c2 == 'l' || c2 == 'L')  && (c3 == 'l' || c3 == 'L'))
	    || ((curr_c == 'l' || curr_c == 'L')
		&& (c2 == 'l' || c2 == 'L')  && (c3 == 'u' || c3 == 'u'))) {
	  VARR_PUSH (char, symbol_text, curr_c);
	  VARR_PUSH (char, symbol_text, c2);
	  VARR_PUSH (char, symbol_text, c3);
	  curr_c = cs_get ();
	} else if (((curr_c == 'u' || curr_c == 'U') && (c2 == 'l' || c2 == 'L'))
		   || ((curr_c == 'l' || curr_c == 'L') && (c2 == 'u' || c2 == 'u'))) {
	  VARR_PUSH (char, symbol_text, curr_c);
	  VARR_PUSH (char, symbol_text, c2);
	  curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L') && (c2 == 'l' || c2 == 'L')) {
	  VARR_PUSH (char, symbol_text, curr_c);
	  VARR_PUSH (char, symbol_text, c2);
	  curr_c = c3;
	} else if ((curr_c == 'l' || curr_c == 'L')) {
	  VARR_PUSH (char, symbol_text, curr_c);
	  cs_unget (c3);
	  curr_c = c2;
	} else if ((curr_c == 'u' || curr_c == 'U')) {
	  VARR_PUSH (char, symbol_text, curr_c);
	  cs_unget (c3);
	  curr_c = c2;
	} else {
	  cs_unget (c3);
	  cs_unget (c2);
	}
      }
      VARR_PUSH (char, symbol_text, '\0');
      cs_unget (curr_c);
      if (! err_p && base == 8 && dec_p) {
	error_func (C_wrong_octal_int, "wrong octal integer");
	err_p = TRUE;
      }
      return new_token_wo_uniq_repr (pos, err_p ? "1" : VARR_ADDR (char, symbol_text),
				     T_NUMBER, N_IGNORE);
    }
    case '\'': case '\"': { /* ??? unicode and wchar */
      token_t t;
      int lns_num, stop = curr_c;
      
      pos = cs->pos;
      VARR_PUSH (char, symbol_text, curr_c);
      for (curr_c = cs_get ();
	   curr_c != stop && curr_c != '\n' && curr_c != EOF;
	   curr_c = cs_get ()) {
	VARR_PUSH (char, symbol_text, curr_c);
	if (curr_c != '\\' )
	  continue;
	curr_c = cs_get ();
	if (curr_c == '\n' || curr_c == EOF)
	  break;
	VARR_PUSH (char, symbol_text, curr_c);
      }
      if (curr_c == stop) {
	if (stop == '\'' && VARR_LENGTH (char, symbol_text) == 1)
	  error (pos, "empty character");
      } else {
	error (pos, "unterminated %s", stop == '"' ? "string" : "char");
      }
      VARR_PUSH (char, symbol_text, curr_c);
      VARR_PUSH (char, symbol_text, '\0');
      t = (stop == '\"' ? new_node_token (pos, VARR_ADDR (char, symbol_text), T_STR,
					  new_str_node (N_STR, NULL, pos))
	   : new_node_token (pos, VARR_ADDR (char, symbol_text), T_CH, new_ch_node (' ', pos)));
      if ((lns_num = set_string_val (t, symbol_text)) !=  0) {
	cs->pos.lno += lns_num; cs->pos.ln_pos = 0;
      }
      return t;
    }
    default:
      if (isalpha (curr_c) || curr_c == '_' ) {
	pos = cs->pos;
	do {
	  VARR_PUSH (char, symbol_text, curr_c);
	  curr_c = cs_get ();
	} while (isalnum (curr_c) || curr_c == '_');
	cs_unget (curr_c);
	VARR_PUSH (char, symbol_text, '\0');
	return new_id_token (pos, VARR_ADDR (char, symbol_text));
      } else {
	VARR_PUSH (char, symbol_text, curr_c);
	VARR_PUSH (char, symbol_text, '\0');
	return new_token_wo_uniq_repr (pos, VARR_ADDR (char, symbol_text), curr_c, N_IGNORE);
      }
    }
  }
}

static token_t get_next_pptoken (void) {
  return get_next_pptoken_1 (FALSE);
}

static token_t get_next_include_pptoken (void) {
  return get_next_pptoken_1 (TRUE);
}

static void unget_next_pptoken (token_t t) {
  VARR_PUSH (token_t, buffered_tokens, t);
}

static const char *stringify (const char *str, VARR (char) *to) {
  VARR_TRUNC (char, to, 0);
  VARR_PUSH (char, to, '"');
  for (; *str != '\0'; str++) {
    if (*str == '\"' || *str == '\\')
      VARR_PUSH (char, to, '\\');
    VARR_PUSH (char, to, *str);
  }
  VARR_PUSH (char, to, '"');
  return VARR_ADDR (char, to);
}

static void destringify (const char *repr, VARR (char) *to) {
  int i, repr_len = strlen (repr);
  
  VARR_TRUNC (char, to,  0);
  if (repr_len == 0)
    return;
  i = repr[0] == '"' ? 1 : 0;
  if (i == 1 && repr_len == 1)
    return;
  if (repr [repr_len - 1] == '"')
    repr_len--;
  for (; i < repr_len; i++)
    if (repr[i] != '\\' || i + 1 >= repr_len || (repr[i + 1] != '\\' && repr[i + 1] != '"'))
      VARR_PUSH (char, to, repr[i]);
}

static token_t token_stringify (token_t t, VARR (token_t) *ts) { // ts - vector, t defines pos. for empty vector
  int i;
  
  if (VARR_LENGTH (token_t, ts) != 0)
    t = VARR_GET (token_t, ts, 0);
  t = new_node_token (t->pos, "", T_STR, new_str_node (N_STR, "", t->pos));
  VARR_TRUNC (char, temp_string, 0);
  for (const char *s = t->repr; *s != 0; s++)
    VARR_PUSH (char, temp_string, *s);
  VARR_PUSH (char, temp_string, '"');
  for (i = 0; i < VARR_LENGTH (token_t, ts); i++)
    if (VARR_GET (token_t, ts, i)->code == ' ') {
      VARR_PUSH (char, temp_string, ' ');
    } else {
      for (const char *s = VARR_GET (token_t, ts, i)->repr; *s != 0; s++) {
	int c = VARR_LENGTH (token_t, ts) == i + 1 ? '\0' : VARR_GET (token_t, ts, i + 1)->repr[0];
	
	/* It is an implementation defined behaviour analogous GCC/Clang: */
	if (*s == '\"' || (*s == '\\' && c != 'a' && c != 'b'
			   && c != 'f' && c != 'n' && c != 'r' && c != 't'))
	  VARR_PUSH (char, temp_string, '\\');
	VARR_PUSH (char, temp_string, *s);
      }
    }
  VARR_PUSH (char, temp_string, '"');
  VARR_PUSH (char, temp_string, '\0');
  t->repr = uniq_str (VARR_ADDR (char, temp_string));
  set_string_val (t, temp_string);
  return t;
}

static token_t pptoken2token (token_t t, int id2kw_p) {
  assert (t->code != T_HEADER && t->code != T_EOA && t->code != T_EOR && t->code != T_EOP
	  && t->code != T_EOF && t->code != T_EOU && t->code != T_PLM && t->code != T_RDBLNO);
  if (t->code == T_ID && id2kw_p) {
    str_t str = str_add (t->repr, T_STR, 0, FALSE);
    
    if (str.key != T_STR) {
      t->code = str.key; t->node_code = N_IGNORE; t->node = NULL;
    }
    return t;
  } else if (t->code == ' ' || t->code == '\n') {
    return NULL;
  } else if (t->code == T_NUMBER) {
    int i, base = 10, float_p = FALSE, double_p = FALSE, ldouble_p = FALSE;
    int uns_p = FALSE, long_p = FALSE, llong_p = FALSE;
    const char *repr = t->repr;
    int last = strlen (repr) - 1;
    
    assert (last >= 0);
    if (repr[0] == '0' && (repr[1] == 'x' || repr[1] == 'X')) {
      repr += 2; base = 16;
    } else if (repr[0] == '0') {
      base = 8;
    }
    for (i = last; i >= 0; i--) {
      if ((repr[i] == 'l' && repr[i - 1] == 'l') || (repr[i] == 'L' && repr[i - 1] == 'L')) {
	i--; llong_p = TRUE;
      } else if (repr[i] == 'l' || repr[i] == 'L') {
	long_p = TRUE;
      } else if (repr[i] == 'u' || repr[i] == 'U') {
	uns_p = TRUE;
      } else if (repr[i] == '.') {
	double_p = TRUE;
      } else if (repr[i] == 'p' || repr[i] == 'P') {
	assert (base == 16);
	double_p = TRUE;
      } else if ((repr[i] == 'e' || repr[i] == 'E') && base != 16) {
	double_p = TRUE;
      }
    }
    if (repr[last] == 'f' || repr[last] == 'f') {
      float_p = TRUE; double_p = FALSE;
    } else if (double_p && long_p) {
      ldouble_p = TRUE; double_p = FALSE;
    }
    errno = 0;
    if (float_p) {
      t->node = new_f_node (strtof (repr, NULL), t->pos);
    } else if (double_p) {
      t->node = new_d_node (strtod (repr, NULL), t->pos);
    } else if (ldouble_p) {
      t->node = new_ld_node (strtold (repr, NULL), t->pos);
    } else if (uns_p) {
      if (llong_p) {
	t->node = new_ull_node (strtoull (repr, NULL, base), t->pos);
      } else if (long_p) {
	t->node = new_ul_node (strtoul (repr, NULL, base), t->pos);
      } else {
	t->node = new_u_node (strtoul (repr, NULL, base), t->pos);
      }
    } else if (llong_p) {
      t->node = new_ll_node (strtoll (repr, NULL, base), t->pos);
    } else if (long_p) {
      t->node = new_l_node (strtol (repr, NULL, base), t->pos);
    } else {
      t->node = new_i_node (strtol (repr, NULL, base), t->pos);
    }
    if (errno) {
      error (t->pos, "number %s is out of range", repr);
    }
  }
  return t;
}

/* --------------------------- Preprocessor -------------------------------- */

/* It is a token based prerpocessor.
   It is input preprocessor tokens and output is (parser) tokens */

static VARR (char) *temp_string;

static void add_to_temp_string (const char *str) {
  size_t i, len;
  
  if ((len = VARR_LENGTH (char, temp_string)) != 0
      && VARR_GET (char, temp_string, len - 1) == '\0') {
    VARR_POP (char, temp_string);
 }
 len = strlen (str);
 for (i = 0; i < len; i++)
   VARR_PUSH (char, temp_string, str[i]);
 VARR_PUSH (char, temp_string, '\0');
}
 
static VARR (token_t) *temp_tokens;

typedef struct macro { /* macro definition: */
  token_t id;                  /* T_ID */
  VARR (token_t) *params;  /* (T_ID)* [N_DOTS], NULL means no params */
  VARR (token_t) *replacement; /* token*, NULL means a standard macro */
  int ignore_p;
} *macro_t;

DEF_HTAB (macro_t);
static HTAB (macro_t) *macro_tab;

static int macro_eq (macro_t macro1, macro_t macro2) {
  return macro1->id->repr == macro2->id->repr;
}

static htab_hash_t macro_hash (macro_t macro) {
  return mir_hash (macro->id->repr, strlen (macro->id->repr), 0x42);
}

DEF_VARR (macro_t);
static VARR (macro_t) *macros;

static macro_t new_macro (token_t id, VARR (token_t) *params, VARR (token_t) *replacement);

static void new_std_macro (const char *id_str) {
  new_macro (new_id_token (no_pos, id_str), NULL, NULL);
}

static void init_macros (void) {
  VARR_CREATE (macro_t, macros, 2048);
  HTAB_CREATE (macro_t, macro_tab, 2048, macro_hash, macro_eq);
  /* Standard macros : */
  new_std_macro ("__DATE__");
  new_std_macro ("__TIME__");
  new_std_macro ("__FILE__");
  new_std_macro ("__LINE__");
}

static macro_t new_macro (token_t id, VARR (token_t) *params, VARR (token_t) *replacement) {
  macro_t tab_m, m = malloc (sizeof (struct macro));
  
  m->id = id; m->params = params; m->replacement = replacement; m->ignore_p = FALSE;
  assert (! HTAB_DO (macro_t, macro_tab, m, HTAB_FIND, tab_m));
  HTAB_DO (macro_t, macro_tab, m, HTAB_INSERT, tab_m);
  VARR_PUSH (macro_t, macros, m);
  return m;
}

static void finish_macros (void) {
  while (VARR_LENGTH (macro_t, macros) != 0) {
    macro_t m = VARR_POP (macro_t, macros);

    if (m->params != NULL)
      VARR_DESTROY (token_t, m->params);
    if (m->replacement != NULL)
      VARR_DESTROY (token_t, m->replacement);
    free (m);
  }
  VARR_DESTROY (macro_t, macros);
  HTAB_DESTROY (macro_t, macro_tab);
}

typedef VARR (token_t) *token_arr_t;

DEF_VARR (token_arr_t);

typedef struct macro_call {
  macro_t macro;
  /* Var array of arguments, each arg is var array of tokens, NULL for args absence: */
  VARR (token_arr_t) *args;
  int repl_pos;    /* position in macro replacement */
  VARR (token_t) *repl_buffer; /* LIST:(token nodes)* */
} *macro_call_t;

static macro_call_t new_macro_call (macro_t m) {
  macro_call_t mc = malloc (sizeof (struct macro_call));

  mc->macro = m; mc->repl_pos = 0; mc->args = NULL;
  VARR_CREATE (token_t, mc->repl_buffer, 64);
  return mc;
}

static void free_macro_call (macro_call_t mc) {
  VARR_DESTROY (token_t, mc->repl_buffer);
  if (mc->args != NULL) {
    while (VARR_LENGTH (token_arr_t, mc->args) != 0) {
      VARR (token_t) *arg = VARR_POP (token_arr_t, mc->args);
      VARR_DESTROY (token_t, arg);
    }
    VARR_DESTROY (token_arr_t, mc->args);
  }
  free (mc);
}

typedef struct ifstate {
  int skip_p, true_p, else_p;  /* ??? flags that we are in a else part and in a false part */
  pos_t if_pos;  /* pos for #if and last #else, #elif */
} *ifstate_t;

DEF_VARR (ifstate_t);
static VARR (ifstate_t) *ifs; /* stack of ifstates */

static ifstate_t new_ifstate (int skip_p, int true_p, int else_p, pos_t if_pos) {
  ifstate_t ifstate = malloc (sizeof (struct ifstate));

  ifstate->skip_p = skip_p; ifstate->true_p = true_p;
  ifstate->else_p = else_p; ifstate->if_pos = if_pos;
  return ifstate;
}

static void pop_ifstate (void) {
  free (VARR_POP (ifstate_t, ifs));
}

static int no_out_p; /* don't output lexs -- put them into buffer */
static int skip_if_part_p;
static const char *varg = "__VA_ARGS__";
static token_t if_id; /* last processed token #if or #elif: used for error messages */
static char date_str[100], time_str[100];

static VARR (token_t) *buffer;

DEF_VARR (macro_call_t);
static VARR (macro_call_t) *macro_call_stack;

static void (*pre_out_token_func) (token_t);

static void pre_init (void) {
  time_t t;
  struct tm *tm;
  
  no_out_p = skip_if_part_p = FALSE;
  t = time (NULL);
  tm = localtime(&t);
  if (tm == NULL) {
    strcpy (date_str, "\"Unknown date\"");
    strcpy (time_str, "\"Unknown time\"");
  } else {
    strftime (date_str, sizeof (date_str), "\"%b %d %Y\"", tm);
    strftime (time_str, sizeof (time_str), "\"%H:%M:%S\"", tm);
  }
  VARR_CREATE (token_t, temp_tokens, 128);
  VARR_CREATE (token_t, buffer, 2048);
  init_macros ();
  VARR_CREATE (ifstate_t, ifs, 512);
  VARR_CREATE (macro_call_t, macro_call_stack, 512);
}

static void pre_finish (void) {
  VARR_DESTROY (token_t, temp_tokens);
  VARR_DESTROY (token_t, buffer);
  finish_macros ();
  while (VARR_LENGTH (ifstate_t, ifs) != 0)
    pop_ifstate ();
  VARR_DESTROY (ifstate_t, ifs);
  while (VARR_LENGTH (macro_call_t, macro_call_stack) != 0)
    free_macro_call (VARR_POP (macro_call_t, macro_call_stack));
  VARR_DESTROY (macro_call_t, macro_call_stack);
}

static void add_include_stream (const char *fname) {
  FILE *f;
  
  assert (fname != NULL);
  if ((f = fopen (fname, "r")) == NULL) {
    fprintf (stderr, "error in opening file %s\n", fname);
    exit (1); // ???
  }
  add_stream (f, fname);
  cs->ifs_length_at_stream_start = VARR_LENGTH (ifstate_t, ifs);
}

static void skip_nl (token_t t, VARR (token_t) *buffer) { /* skip until new line */
  if (t == NULL)
    t = get_next_pptoken ();
  for (; t->code != '\n'; t = get_next_pptoken ()) // ??>
    if (buffer != NULL)
      VARR_PUSH (token_t, buffer, t);
  unget_next_pptoken (t);
}

static int find_param (VARR (token_t) *params, const char *name) {
  size_t len;
  token_t param;
  
  len = VARR_LENGTH (token_t, params);
  if (strcmp (name, varg) == 0 && len != 0 && VARR_LAST (token_t, params)->code == T_DOTS)
    return len - 1;
  for (int i = 0; i < len; i++)  {
    param = VARR_GET (token_t, params, i);
    if (strcmp (param->repr, name) == 0)
      return i;
  }
  return -1;
}

static int params_eq_p (VARR (token_t) *params1, VARR (token_t) *params2) {
  token_t param1, param2;
  
  if (params1 == NULL || params2 == NULL)
    return params1 == params2;
  if (VARR_LENGTH (token_t, params1) != VARR_LENGTH (token_t, params2))
    return FALSE;
  for (int i = 0; i < VARR_LENGTH (token_t, params1); i++)  {
    param1 = VARR_GET (token_t, params1, i);
    param2 = VARR_GET (token_t, params2, i);
    if (strcmp (param1->repr, param2->repr) != 0)
      return FALSE;
  }
  return TRUE;
}

static int replacement_eq_p (VARR (token_t) *r1, VARR (token_t) *r2) {
  token_t el1, el2;
  
  if (VARR_LENGTH (token_t, r1) != VARR_LENGTH (token_t, r2))
    return FALSE;
  for (int i = 0; i < VARR_LENGTH (token_t, r1); i++)  {
    el1 = VARR_GET (token_t, r1, i);
    el2 = VARR_GET (token_t, r2, i);
    
    if (el1->code == ' ' && el2->code == ' ')
      return TRUE;
    if (el1->node_code != el2->node_code)
      return FALSE;
    if (strcmp (el1->repr, el2->repr) != 0)
      return FALSE;
  }
  return TRUE;
}

static void define (void) {
  VARR (token_t) *repl, *params;
  token_t id, t;
  const char *name;
  macro_t m;
  struct  macro macro_struct;
  
  t = get_next_pptoken (); // ???
  if (t->code == ' ')
    t = get_next_pptoken (); // ??
  if (t->code != T_ID) {
    error (t->pos, "no ident after #define: %s", t->repr);
    skip_nl (t, NULL);
    return;
  }
  id = t;
  t = get_next_pptoken ();
  VARR_CREATE (token_t, repl, 64);
  params = NULL;
  if (t->code == '(') {
    VARR_CREATE (token_t, params, 16);
    t = get_next_pptoken (); /* skip '(' */
    if (t->code == ' ')
      t = get_next_pptoken ();
    if (t->code != ')') {
      for (;;) {
	if (t->code == ' ')
	  t = get_next_pptoken ();
	if (t->code == T_ID) {
	  if (find_param (params, t->repr) >= 0)
	    error (t->pos, "repeated macro parameter %s", t->repr);
	  VARR_PUSH (token_t, params, t);
	} else if (t->code == T_DOTS) {
	  VARR_PUSH (token_t, params, t);
	} else {
	  error (t->pos, "macro parameter is expected");
	  break;
	}
	t = get_next_pptoken ();
	if (t->code == ' ')
	  t = get_next_pptoken ();
	if (t->code == ')')
	  break;
	if (VARR_LAST (token_t, params)->code == T_DOTS) {
	  error (t->pos, "... is not the last parameter");
	  break;
	}
	if (t->code == T_DOTS)
	  continue;
	if (t->code != ',') {
	  error (t->pos, "missed ,");
	  continue;
	}
	t = get_next_pptoken ();
      }
    }
    for (;t->code != '\n' && t->code != ')';)
      t = get_next_pptoken ();
    if (t->code == ')')
      t = get_next_pptoken ();
  }
  if (t->code == ' ')
    t = get_next_pptoken ();
  for (; t->code != '\n'; t = get_next_pptoken ()) {
    if (t->code == T_DBLNO)
      t->code = T_RDBLNO;
    VARR_PUSH (token_t, repl, t);
  }
  unget_next_pptoken (t);
  name = id->repr; macro_struct.id = id;
  if (! HTAB_DO (macro_t, macro_tab, &macro_struct, HTAB_FIND, m)) {
    if (strcmp (name, "defined") == 0) {
      error (id->pos, "macro definition of %s", name);
    } else {
      new_macro (id, params, repl);
    }
  } else if (m->replacement == NULL) {
    error (id->pos, "standard macro %s redefinition", name);
  } else if (! params_eq_p (m->params, params) || ! replacement_eq_p (m->replacement, repl)) {
    error (id->pos, "different macro redefinition of %s", name);
  }
}

static void push_back (VARR (token_t) *tokens) {
  for (int i = (int) VARR_LENGTH (token_t, tokens) - 1; i >= 0;  i--)
    unget_next_pptoken (VARR_GET (token_t, tokens, i));
}

static int file_found_p (const char *name) {
  FILE *f;
  
  if ((f = fopen (name, "r")) == NULL)
    return FALSE;
  fclose (f);
  return TRUE;
}

static const char *get_full_name (const char *base, const char *name, int dir_base_p) {
  const char *str, *last;
  size_t len;
  
  VARR_TRUNC (char, temp_string, 0);
  if (base == NULL || *base == '\0') {
    assert (name != NULL && name[0] != '\0');
    return name;
  }
  if (dir_base_p) {
    len = strlen (base);
    assert (len > 0);
    add_to_temp_string (base);
    if (base[len - 1] != '/')
      add_to_temp_string ("/");
  } else if ((last = strrchr (base, '/')) == NULL) {
    add_to_temp_string ("./");
  } else {
    for (str = base; str <= last; str++)
      VARR_PUSH (char, temp_string, *str);
    VARR_PUSH (char, temp_string, '\0');
  }
  add_to_temp_string (name);
  return VARR_ADDR (char, temp_string);
}

static const char *get_include_fname (token_t t) {
  const char *fullname, *name;

  assert (t->code == T_STR || t->code == T_HEADER);
  if ((name = t->node->u.s)[0] != '/') {
    if (t->repr[0] == '"') {
      /* Search relative to the current source dir */
      if (cs->fname != NULL) {
	fullname = get_full_name (cs->fname, name, FALSE);
	if (file_found_p (fullname))
	  return uniq_str (fullname);
      }
      for (size_t i = 0; header_dirs[i] != NULL; i++) {
	fullname = get_full_name (header_dirs[i], name, TRUE);
	if (file_found_p (fullname))
	  return uniq_str (fullname);
      }
    }
    for (size_t i = 0; system_header_dirs[i] != NULL; i++) {
      fullname = get_full_name (system_header_dirs[i], name, TRUE);
      if (file_found_p (fullname))
	return uniq_str (fullname);
    }
  }
  return name;
}

static int digits_p (const char *str) {
  while ('0' <= *str && *str <= '9')
    str++;
  return *str == '\0';
}

static pos_t check_line_directive_args (VARR (token_t) *buffer) {
  size_t i, len = VARR_LENGTH (token_t, buffer);
  token_t *buffer_arr = VARR_ADDR (token_t, buffer);
  const char *fname;
  pos_t pos;
  int lno;
  unsigned long long l;
  
  if (len == 0)
    return no_pos;
  i = buffer_arr[0]->code == ' ' ? 1 : 0;
  fname = buffer_arr[i]->pos.fname;
  if (i >= len || buffer_arr[i]->code != T_NUMBER)
    return no_pos;
  if (! digits_p (buffer_arr[i]->repr))
    return no_pos;
  errno = 0;
  lno = l = strtoll (buffer_arr[i]->repr, NULL, 10);
  if (errno || l > ((1ul << 31) - 1))
    error (buffer_arr[i]->pos, "#line with too big value: %s", buffer_arr[i]->repr);
  i++;
  if (i < len && buffer_arr[i]->code == ' ')
    i++;
  if (i < len && buffer_arr[i]->code == T_STR) {
    fname = buffer_arr[i]->node->u.s; i++;
  }
  if (i == len) {
    pos.fname = fname; pos.lno = lno; pos.ln_pos = 0;
    return pos;
  }
  return no_pos;
}

static void check_pragma (token_t t, VARR (token_t) *tokens) {
  token_t *tokens_arr = VARR_ADDR (token_t, tokens);
  size_t i, tokens_len = VARR_LENGTH (token_t, tokens);
  
  i = 0;
  if (i < tokens_len && tokens_arr[i]->code == ' ')
    i++;
  if (i >= tokens_len || tokens_arr[i]->code != T_ID
      || strcmp (tokens_arr[i]->repr, "STDC") != 0) {
    warning (t->pos, "unknown pragma");
    return;
  }
  i++;
  if (i < tokens_len && tokens_arr[i]->code == ' ')
    i++;
  if (i >= tokens_len || tokens_arr[i]->code != T_ID) {
    error (t->pos, "wrong STDC pragma");
    return;
  }
  if (strcmp (tokens_arr[i]->repr, "FP_CONTRACT") != 0
      && strcmp (tokens_arr[i]->repr, "FENV_ACCESS") != 0
      && strcmp (tokens_arr[i]->repr, "CX_LIMITED_RANGE") != 0) {
    error (t->pos, "unknown STDC pragma %s", tokens_arr[i]->repr);
    return;
  }
  i++;
  if (i < tokens_len && tokens_arr[i]->code == ' ')
    i++;
  if (i >= tokens_len || tokens_arr[i]->code != T_ID) {
    error (t->pos, "wrong STDC pragma value");
    return;
  }
  if (strcmp (tokens_arr[i]->repr, "ON") != 0 && strcmp (tokens_arr[i]->repr, "OFF") != 0
      && strcmp (tokens_arr[i]->repr, "DEFAULT") != 0) {
    error (t->pos, "unknown STDC pragma value", tokens_arr[i]->repr);
    return;
  }
  i++;
  if (i < tokens_len && (tokens_arr[i]->code == ' ' || tokens_arr[i]->code == '\n'))
    i++;
  if (i < tokens_len)
    error (t->pos, "garbage at STDC pragma end");
}

static void pop_macro_call (void) {
  macro_call_t mc;

  mc = VARR_POP (macro_call_t, macro_call_stack);
  mc->macro->ignore_p = FALSE;
  free_macro_call (mc);
}

static void find_args (macro_call_t mc) { /* we have just read a parenthesis */
  macro_t m;
  token_t t;
  int va_p, level = 0;
  size_t params_len;
  VARR (token_arr_t) *args;
  VARR (token_t) *arg, *temp_arr;
  
  m = mc->macro;
  VARR_CREATE (token_arr_t, args, 16);
  VARR_CREATE (token_t, arg, 16);
  params_len = VARR_LENGTH (token_t, m->params);
  va_p = params_len == 1 && VARR_GET (token_t, m->params, 0)->code == T_DOTS;
  for (;;) {
    t = get_next_pptoken ();
    if (t->code == T_EOR) {
      t = get_next_pptoken ();
      pop_macro_call ();
    }
    if (t->code == T_EOF || t->code == T_EOU || t->code == T_EOR || t->code == T_EOA)
      break;
    if (level == 0 && t->code == ')' )
      break;
    if (level == 0 && ! va_p && t->code == ',') {
      VARR_PUSH (token_arr_t, args, arg);
      VARR_CREATE (token_t, arg, 16);
      if (VARR_LENGTH (token_arr_t, args) == params_len - 1
	  && strcmp (VARR_GET (token_t, m->params, params_len - 1)->repr, "...") == 0)
	va_p = 1;
    } else {
      VARR_PUSH (token_t, arg, t);
      if (t->code == ')')
	level--;
      else if (t->code == '(')
	level++;
    }
  }
  if (t->code != ')')
    error (t->pos, "unfinished call of macro %s", m->id->repr);
  VARR_PUSH (token_arr_t, args, arg);
  if (params_len == 0 && VARR_LENGTH (token_arr_t, args) == 1
      && VARR_LENGTH (token_t, VARR_GET (token_arr_t, args, 0)) == 0) {
    temp_arr = VARR_POP (token_arr_t, args);
    VARR_DESTROY (token_t, temp_arr);
  } else if (VARR_LENGTH (token_arr_t, args) > params_len) {
    t = VARR_GET (token_t, VARR_GET (token_arr_t, args, params_len), 0);
    while (VARR_LENGTH (token_arr_t, args) > params_len) {
      temp_arr = VARR_POP (token_arr_t, args);
      VARR_DESTROY (token_t, temp_arr);
    }
    error (t->pos, "too many args for call of macro %s", m->id->repr);
  } else if (VARR_LENGTH (token_arr_t, args) < params_len) {
    for (; VARR_LENGTH (token_arr_t, args) < params_len;) {
      VARR_CREATE (token_t, arg, 16);
      VARR_PUSH (token_arr_t, args, arg);
    }
    error (t->pos, "not enough args for call of macro %s", m->id->repr);
  }
  mc->args = args;
}

static token_t token_concat (token_t t1, token_t t2) {
  token_t t, next;
  
  VARR_TRUNC (char, temp_string, 0);
  add_to_temp_string (t1->repr);
  add_to_temp_string (t2->repr);
  reverse (temp_string);
  set_string_stream (VARR_ADDR (char, temp_string), t1->pos, NULL);
  t = get_next_pptoken ();
  next = get_next_pptoken ();
  if (next->code != T_EOF) {
    error (t1->pos, "wrong result of ##: %s", reverse (temp_string));
    remove_string_stream ();
  }
  return t;
}

static void add_token (VARR (token_t) *to, token_t t) {
  if ((t->code != ' ' && t->code != '\n') || VARR_LENGTH (token_t, to) == 0
      || (VARR_LAST (token_t, to)->code != ' ' && VARR_LAST (token_t, to)->code != '\n'))
    VARR_PUSH (token_t, to, t);
}

static void add_replacement_tokens (VARR (token_t) *to, VARR (token_t) *from) {
  for (int i = 0; i < VARR_LENGTH (token_t, from); i++)
    add_token (to, VARR_GET (token_t, from, i));
}

static void add_tokens (VARR (token_t) *to, VARR (token_t) *from) {
  for (size_t i = 0; i < VARR_LENGTH (token_t, from); i++)
    add_token (to, VARR_GET (token_t, from , i));
}

static void del_tokens (VARR (token_t) *tokens, int from, int len) {
  int diff, tokens_len = VARR_LENGTH (token_t, tokens);
  token_t *addr = VARR_ADDR (token_t, tokens);
  
  if (len < 0)
    len = tokens_len - from;
  assert (from + len <= tokens_len);
  if ((diff = tokens_len - from - len) > 0)
    memmove (addr + from, addr + from + len, diff * sizeof (token_t));
  VARR_TRUNC (token_t, tokens, tokens_len - len);
}

static VARR (token_t) *do_concat (VARR (token_t) *tokens) {
  int i, j, k, len = VARR_LENGTH (token_t, tokens);
  token_t t;
  
  for (i = len - 1; i >= 0 ; i--)
    if (VARR_GET (token_t, tokens, i)->code == T_RDBLNO) {
      j = i + 1; k = i - 1;
      if (VARR_GET (token_t, tokens, j)->code == ' '
	  || VARR_GET (token_t, tokens, j)->code == '\n')
	j++;
      if (VARR_GET (token_t, tokens, k)->code == ' '
	  || VARR_GET (token_t, tokens, k)->code == '\n')
	k--;
      if (VARR_GET (token_t, tokens, j)->code == T_PLM) {
	if (k != i - 1 && j + 1 < len
	    && (VARR_GET (token_t, tokens, j + 1)->code == ' '
		|| VARR_GET (token_t, tokens, j + 1)->code == '\n'))
	  j++;
	del_tokens (tokens, i, j - i + 1);
      } else if (VARR_GET (token_t, tokens, k)->code == T_PLM) {
	if (j != i + 1 && k != 0
	    && (VARR_GET (token_t, tokens, k - 1)->code == ' '
		|| VARR_GET (token_t, tokens, k - 1)->code == '\n'))
	  k--;
	del_tokens (tokens, k, i - k + 1);
      } else {
	t = token_concat (VARR_GET (token_t, tokens, k), VARR_GET (token_t, tokens, j));
	del_tokens (tokens, k + 1, j - k);
	VARR_SET (token_t, tokens, k, t);
      }
      i = k;
      len = VARR_LENGTH (token_t, tokens);
    }
  for (i = len - 1; i >= 0 ; i--)
    VARR_GET (token_t, tokens, i)->processed_p = TRUE;
  return tokens;
}

static void process_replacement (macro_call_t mc) {
  macro_t m;
  token_t t, *m_repl;
  VARR (token_t) *arg;
  int i, m_repl_len, sharp_pos;
  
  m = mc->macro; sharp_pos = -1;
  m_repl = VARR_ADDR (token_t, m->replacement);
  m_repl_len = VARR_LENGTH (token_t, m->replacement);
  for (;;) {
    if (mc->repl_pos >= m_repl_len) {
      t = get_next_pptoken ();
      unget_next_pptoken (t);
      unget_next_pptoken (new_token (t->pos, "", T_EOR, N_IGNORE));
      push_back (do_concat (mc->repl_buffer));
      m->ignore_p = TRUE;
      return;
    }
    t = m_repl[mc->repl_pos++];
    if (t->code == T_ID) {
      i = find_param (m->params, t->repr);
      if (i >= 0) {
	arg = VARR_GET (token_arr_t, mc->args, i);
	if (sharp_pos >= 0) {
	  del_tokens (mc->repl_buffer, sharp_pos, -1);
	  if (VARR_LENGTH (token_t, arg) != 0
	      && (VARR_GET (token_t, arg, 0)->code == ' '
		  || VARR_GET (token_t, arg, 0)->code == '\n'))
	    del_tokens (arg, 0, 1);
	  if (VARR_LENGTH (token_t, arg) != 0
	      && (VARR_LAST (token_t, arg)->code == ' ' || VARR_LAST (token_t, arg)->code == '\n'))
	    VARR_POP (token_t, arg);
	  t = token_stringify (mc->macro->id, arg);
	} else if ((mc->repl_pos >= 2 && m_repl[mc->repl_pos - 2]->code == T_RDBLNO)
		   || (mc->repl_pos >= 3 && m_repl[mc->repl_pos - 2]->code == ' '
		       && m_repl[mc->repl_pos - 3]->code == T_RDBLNO)
		   || (mc->repl_pos < m_repl_len && m_repl[mc->repl_pos]->code == T_RDBLNO)
		   || (mc->repl_pos + 1 < m_repl_len && m_repl[mc->repl_pos + 1]->code == T_RDBLNO
		       && m_repl[mc->repl_pos]->code == ' ')) {
	  if (VARR_LENGTH (token_t, arg) == 0) {
	    t = new_token (t->pos, "", T_PLM, N_IGNORE);
	  } else {
	    add_tokens (mc->repl_buffer, arg);
	    continue;
	  }
	} else {
	  unget_next_pptoken (new_token (t->pos, "", T_EOA, N_IGNORE));
	  push_back (arg);
	  return;
	}
      }
    } else if (t->code == '#') {
      sharp_pos = VARR_LENGTH (token_t, mc->repl_buffer);
    } else if (t->code != ' ') {
      sharp_pos = -1;
    }
    add_token (mc->repl_buffer, t);
  }
}

static void prepare_pragma_string (const char *repr, VARR (char) *to) {
  destringify (repr, to);
  reverse (to);
}

static int process_pragma (token_t t) {
  token_t t1, t2;

  if (strcmp (t->repr, "_Pragma") != 0)
    return FALSE;
  VARR_TRUNC (token_t, temp_tokens, 0);
  t1 = get_next_pptoken ();
  VARR_PUSH (token_t, temp_tokens, t1);
  if (t1->code == ' ' || t1->code == '\n') {
    t1 = get_next_pptoken ();
    VARR_PUSH (token_t, temp_tokens, t1);
  }
  if (t1->code != '(') {
    push_back (temp_tokens);
    return FALSE;
  }
  t1 = get_next_pptoken ();
  VARR_PUSH (token_t, temp_tokens, t1);
  if (t1->code == ' ' || t1->code == '\n') {
    t1 = get_next_pptoken ();
    VARR_PUSH (token_t, temp_tokens, t1);
  }
  if (t1->code != T_STR) {
    push_back (temp_tokens);
    return FALSE;
  }
  t2 = t1;
  t1 = get_next_pptoken ();
  VARR_PUSH (token_t, temp_tokens, t1); 
  if (t1->code == ' ' || t1->code == '\n') {
    t1 = get_next_pptoken ();
    VARR_PUSH (token_t, temp_tokens, t1);
  }
  if (t1->code != ')') {
    push_back (temp_tokens);
    return FALSE;
  }
  set_string_stream (t2->repr, t2->pos, prepare_pragma_string);
  VARR_TRUNC (token_t, temp_tokens, 0);
  for (t1 = get_next_pptoken (); t1->code != T_EOF; t1 = get_next_pptoken ())
    VARR_PUSH (token_t, temp_tokens, t1);
  check_pragma (t2, temp_tokens);
  return TRUE;
}

static void flush_buffer (void) {
  for (size_t i = 0; i < VARR_LENGTH (token_t, buffer); i++)
    pre_out_token_func (VARR_GET (token_t, buffer, i));
  VARR_TRUNC (token_t, buffer, 0);
}

static void out_token (token_t t) {
  if (no_out_p || VARR_LENGTH (macro_call_t, macro_call_stack) != 0) {
    VARR_PUSH (token_t, buffer, t);
    return;
  }
  flush_buffer ();
  pre_out_token_func (t);
}

struct val {
  int uns_p;
  union {
    mir_llong i_val;
    mir_ullong u_val;
  } u;
};
 
static void move_tokens (VARR (token_t) *to, VARR (token_t) *from) {
  VARR_TRUNC (token_t, to, 0);
  for (int i = 0; i < VARR_LENGTH (token_t, from); i++)
    VARR_PUSH (token_t, to, VARR_GET (token_t, from, i));
  VARR_TRUNC (token_t, from, 0);
}

static void reverse_move_tokens (VARR (token_t) *to, VARR (token_t) *from) {
  VARR_TRUNC (token_t, to, 0);
  while (VARR_LENGTH (token_t, from) != 0)
    VARR_PUSH (token_t, to, VARR_POP (token_t, from)); 
}

static void processing (int ignore_directive_p);

static struct val eval_expr (VARR (token_t) *buffer, token_t if_token);

static void process_directive (void) {
  token_t t, t1;
  int i, true_p;
  VARR (token_t) *temp_buffer;
  pos_t pos;
  struct macro macro;
  macro_t tab_macro;
  const char *name;
  
  t = get_next_pptoken ();
  if (t->code == '\n')
    return;
  if (t->code == ' ')
    t = get_next_pptoken ();
  if (t->code != T_ID) {
    if (! skip_if_part_p)
      error (t->pos, "wrong directive name %s", t->repr);
    skip_nl (NULL,  NULL);
    return;
  }
  VARR_CREATE (token_t, temp_buffer, 64);
  if (strcmp (t->repr, "ifdef") == 0 || strcmp (t->repr, "ifndef") == 0) {
    t1 = t;
    if (VARR_LENGTH (ifstate_t, ifs) != 0 && VARR_LAST (ifstate_t, ifs)->skip_p) {
      skip_if_part_p = true_p = TRUE;
      skip_nl (NULL, NULL);
    } else {
      t = get_next_pptoken ();
      skip_if_part_p = FALSE;
      if (t->code == ' ')
	t = get_next_pptoken ();
      if (t->code != T_ID) {
	error (t->pos, "wrong #%s", t1->repr);
      } else {
	macro.id = t;
	skip_if_part_p = HTAB_DO (macro_t, macro_tab, &macro, HTAB_FIND, tab_macro);
      }
      t = get_next_pptoken ();
      if (t->code != '\n') {
	error (t1->pos, "garbage at the end of #%s", t1->repr);
	skip_nl (NULL, NULL);
      }
      if (strcmp (t1->repr, "ifdef") == 0)
	skip_if_part_p = ! skip_if_part_p;
      true_p = ! skip_if_part_p;
    }
    VARR_PUSH (ifstate_t, ifs, new_ifstate (skip_if_part_p, true_p, FALSE, t1->pos));
  } else if (strcmp (t->repr, "endif") == 0 || strcmp (t->repr, "else") == 0) {
    t1 = t;
    t = get_next_pptoken ();
    if (t->code != '\n') {
      error (t1->pos, "garbage at the end of #%s", t1->repr);
      skip_nl (NULL, NULL);
    }
    if (VARR_LENGTH (ifstate_t, ifs) < cs->ifs_length_at_stream_start)
      error (t1->pos, "unmatched #%s", t1->repr);
    else if (strcmp (t1->repr, "endif") == 0) {
      pop_ifstate ();
      skip_if_part_p = VARR_LENGTH (ifstate_t, ifs) == 0 ? 0 : VARR_LAST (ifstate_t, ifs)->skip_p;
    } else if (VARR_LAST (ifstate_t, ifs)->else_p) {
      error (t1->pos, "repeated #else");
      VARR_LAST (ifstate_t, ifs)->skip_p = 1;
      skip_if_part_p = TRUE;
    } else {
      skip_if_part_p = VARR_LAST (ifstate_t, ifs)->true_p;
      VARR_LAST (ifstate_t, ifs)->true_p = TRUE;
      VARR_LAST (ifstate_t, ifs)->skip_p = skip_if_part_p;
      VARR_LAST (ifstate_t, ifs)->else_p = FALSE;
    }
  } else if (strcmp (t->repr, "if") == 0 || strcmp (t->repr, "elif") == 0) {
    if_id = t;
    if (strcmp (t->repr, "elif") == 0 && VARR_LENGTH (ifstate_t, ifs) == 0) {
      error (t->pos, "#elif without #if");
    } else if (strcmp (t->repr, "elif") == 0 && VARR_LAST (ifstate_t, ifs)->else_p)  {
      error (t->pos, "#elif after #else");
      skip_if_part_p = TRUE;
    } else if (strcmp (t->repr, "if") == 0 && VARR_LENGTH (ifstate_t, ifs) != 0
	       && VARR_LAST (ifstate_t, ifs)->skip_p) {
      skip_if_part_p = true_p = TRUE;
      skip_nl (NULL, NULL);
      VARR_PUSH (ifstate_t, ifs, new_ifstate (skip_if_part_p, true_p, FALSE, t->pos));
    } else if (strcmp (t->repr, "elif") == 0 && VARR_LAST (ifstate_t, ifs)->true_p) {
      VARR_LAST (ifstate_t, ifs)->skip_p = skip_if_part_p = TRUE;
      skip_nl (NULL, NULL);
    } else {
      struct val val;
      
      skip_if_part_p = FALSE; /* for eval expr */
      skip_nl (NULL, temp_buffer);
      val = eval_expr (temp_buffer, t);
      true_p = val.uns_p ? val.u.u_val != 0 : val.u.i_val != 0;
      skip_if_part_p = ! true_p;
      if (strcmp (t->repr, "if") == 0)
	VARR_PUSH (ifstate_t, ifs, new_ifstate (skip_if_part_p, true_p, FALSE, t->pos));
      else {
	VARR_LAST (ifstate_t, ifs)->skip_p = skip_if_part_p;
	VARR_LAST (ifstate_t, ifs)->true_p = true_p;
      }
    }
  } else if (skip_if_part_p) {
    skip_nl (NULL, NULL);
  } else if (strcmp (t->repr, "define") == 0) {
    define ();
  } else if (strcmp (t->repr, "include") == 0) {
    t = get_next_include_pptoken ();
    if (t->code == ' ')
      t = get_next_include_pptoken ();
    t1 = get_next_pptoken ();
    if ((t->code == T_STR || t->code == T_HEADER) && t1->code == '\n')
      name = get_include_fname (t);
    else {
      VARR_PUSH (token_t, temp_buffer, t);
      skip_nl (t1, temp_buffer);
      unget_next_pptoken (new_token (t->pos, "", T_EOP, N_IGNORE));
      push_back (temp_buffer);
      assert (VARR_LENGTH (macro_call_t, macro_call_stack) == 0 && ! no_out_p);
      no_out_p = TRUE;
      processing (TRUE);
      no_out_p = FALSE;
      reverse_move_tokens (temp_buffer, buffer);
      i = 0;
      if (VARR_LENGTH (token_t, temp_buffer) != 0 && VARR_GET (token_t, temp_buffer, 0)->code == ' ')
	i++;
      if (i != VARR_LENGTH (token_t, temp_buffer) - 1
	  || (VARR_GET (token_t, temp_buffer, i)->code != T_STR
	      && VARR_GET (token_t, temp_buffer, i)->code != T_HEADER)) {
	error (t->pos, "wrong #include");
	goto ret;
      }
      name = get_include_fname (VARR_GET (token_t, temp_buffer, i));
    }
    if (VARR_LENGTH (stream_t, streams) >= max_nested_includes + 1) {
      error (t->pos, "more %d include levels", VARR_LENGTH (stream_t, streams) - 1);
      goto ret;
    }
    add_include_stream (name);
  } else if (strcmp (t->repr, "line") == 0) {
    skip_nl (NULL, temp_buffer);
    unget_next_pptoken (new_token (t->pos, "", T_EOP, N_IGNORE));
    push_back (temp_buffer);
    assert (VARR_LENGTH (macro_call_t, macro_call_stack) == 0 && ! no_out_p);
    no_out_p = 1;
    processing (TRUE);
    no_out_p = 0;
    move_tokens (temp_buffer, buffer);
    pos = check_line_directive_args (temp_buffer);
    if (pos.lno < 0) {
      error (t->pos, "wrong #line");
    } else {
      change_stream_pos (pos);
    }
  } else if (strcmp (t->repr, "error") == 0) {
    VARR_TRUNC (char, temp_string, 0);
    add_to_temp_string ("#error");
    for (t1 = get_next_pptoken (); t1->code != '\n'; t1 = get_next_pptoken ())
      add_to_temp_string (t1->repr);
    error (t->pos, "%s", VARR_ADDR (char, temp_string));
  } else if (strcmp (t->repr, "pragma") == 0) {
    skip_nl (NULL, temp_buffer);
    check_pragma (t, temp_buffer);
  } else if (strcmp (t->repr, "undef") == 0) {
    t = get_next_pptoken ();
    if (t->code == ' ')
      t = get_next_pptoken ();
    if (t->code == '\n') {
      error (t->pos, "no ident after #undef");
      goto ret;
    }
    if (t->code != T_ID) {
      error (t->pos, "no ident after #undef");
      skip_nl (t, NULL);
      goto ret;
    }
    if (strcmp (t->repr, "defined") == 0) {
      error (t->pos, "#undef of %s", t->repr);
    } else {
      macro.id = t;
      if (HTAB_DO (macro_t, macro_tab, &macro, HTAB_FIND, tab_macro)) {
	if (tab_macro->replacement == NULL)
	  error (t->pos, "#undef of standard macro %s", t->repr);
	else
	  HTAB_DO (macro_t, macro_tab, &macro, HTAB_DELETE, tab_macro);
      }
    }
  }
 ret:
  VARR_DESTROY (token_t, temp_buffer);
}

static VARR (token_t) *pre_expr;

static int pre_match (int c, pos_t *pos, node_code_t *node_code, node_t *node) {
  token_t t;
  
  if (VARR_LENGTH (token_t, pre_expr) == 0)
    return FALSE;
  t = VARR_LAST (token_t, pre_expr);
  if (t->code != c)
    return FALSE;
  if (pos != NULL)
    *pos = t->pos;
  if (node_code != NULL)
    *node_code = t->node_code;
  if (node != NULL)
    *node = t->node;
  VARR_POP (token_t, pre_expr);
  return TRUE;
}

static node_t pre_cond_expr (void);

/* Expressions: */
static node_t pre_primary_expr (void) {
  node_t r;
  
  if (pre_match (T_NUMBER, NULL, NULL, &r) || pre_match (T_CH, NULL, NULL, &r))
    return r;
  if (pre_match ('(', NULL, NULL, NULL)) {
    if ((r = pre_cond_expr ()) == NULL)
      return r;
    if (pre_match (')', NULL, NULL, NULL))
      return r;
  }
  return NULL;
}

static node_t pre_unary_expr (void) {
  node_t r;
  node_code_t code;
  pos_t pos;
  
  if (! pre_match (T_UNOP, &pos, &code, NULL) && ! pre_match (T_ADDOP, &pos, &code, NULL))
    return pre_primary_expr ();
  if ((r = pre_unary_expr ()) == NULL)
    return r;
  r = new_pos_node1 (code, pos, r);
  return r;
}

static node_t pre_left_op (int token, int token2, node_t (*f) (void)) {
  node_code_t code;
  node_t r, n;
  pos_t pos;
  
  if ((r = f ()) == NULL)
    return r;
  while (pre_match (token, &pos, &code, NULL)
	 || (token2 >= 0 && pre_match (token2, &pos, &code, NULL))) {
    n = new_pos_node1 (code, pos, r);
    if ((r = f ()) == NULL)
      return r;
    op_append (n, r);
    r = n;
  }
  return r;
}

static node_t pre_mul_expr (void) { return pre_left_op (T_DIVOP, '*', pre_unary_expr); }
static node_t pre_add_expr (void) { return pre_left_op (T_ADDOP, -1, pre_mul_expr); }
static node_t pre_sh_expr (void) { return pre_left_op (T_SH, -1, pre_add_expr); }
static node_t pre_rel_expr (void) { return pre_left_op (T_CMP, -1, pre_sh_expr); }
static node_t pre_eq_expr (void) { return pre_left_op (T_EQNE, -1, pre_rel_expr); }
static node_t pre_and_expr (void) { return pre_left_op ('&', -1, pre_eq_expr); }
static node_t pre_xor_expr (void) { return pre_left_op ('^', -1, pre_and_expr); }
static node_t pre_or_expr (void) { return pre_left_op ('|', -1, pre_xor_expr); }
static node_t pre_land_expr (void) { return pre_left_op (T_ANDAND, -1, pre_or_expr); }
static node_t pre_lor_expr (void) { return pre_left_op (T_OROR, -1, pre_land_expr); }

static node_t pre_cond_expr (void) {
  node_t r, n;
  pos_t pos;
  
  if ((r = pre_lor_expr ()) == NULL)
    return r;
  if (! pre_match ('?', &pos, NULL, NULL))
    return r;
  n = new_pos_node1 (N_COND, pos, r);
  if ((r = pre_cond_expr ()) == NULL)
    return r;
  op_append (n, r);
  if (! pre_match (':', NULL, NULL, NULL))
    return NULL;
  if ((r = pre_cond_expr ()) == NULL)
    return r;
  op_append (n, r);
  return n;
}

static node_t parse_pre_expr (VARR (token_t) *expr) {
  node_t r;
  token_t t;
  
  pre_expr = expr;
  t = VARR_LAST (token_t, expr);
  if ((r = pre_cond_expr ()) != NULL && VARR_LENGTH (token_t, expr) == 0)
    return r;
  if (VARR_LENGTH (token_t, expr) != 0)
    t = VARR_POP (token_t, expr);
  error (t->pos, "wrong preprocessor expression");
  return NULL;
}

static struct val eval (node_t tree);

static struct val eval_expr (VARR (token_t) *expr_buffer, token_t if_token) {
  int i, j, k, len;
  token_t t, id, ppt;
  const char *res;
  struct macro macro_struct;
  macro_t tab_macro;
  VARR (token_t) *temp_buffer;
  node_t tree;

  for (i = 0; i < VARR_LENGTH (token_t, expr_buffer); i++) {
    /* Change defined ident and defined (ident) */
    t = VARR_GET (token_t, expr_buffer, i);
    if (t->code == T_ID && strcmp (t->repr, "defined") == 0) {
      j = i + 1;
      len = VARR_LENGTH (token_t, expr_buffer);
      if (j < len && VARR_GET (token_t, expr_buffer, j)->code == ' ')
	j++;
      if (j >= len)
	continue;
      if ((id = VARR_GET (token_t, expr_buffer, j))->code == T_ID) {
	macro_struct.id = id;
	res = HTAB_DO (macro_t, macro_tab, &macro_struct, HTAB_FIND, tab_macro) ? "1" : "0";
	VARR_SET (token_t, expr_buffer, i, new_token (t->pos, res, T_NUMBER, N_IGNORE)); // ???
	del_tokens (expr_buffer, i + 1, j - i);
	continue;
      }
      if (j >= len || VARR_GET (token_t, expr_buffer, j)->code != '(')
	continue;
      j++;
      if (j < len && VARR_GET (token_t, expr_buffer, j)->code == ' ')
	j++;
      if (j >= len || VARR_GET (token_t, expr_buffer, j)->code != T_ID)
	continue;
      k = j; j++;
      if (j < len && VARR_GET (token_t, expr_buffer, j)->code == ' ')
	j++;
      if (j >= len || VARR_GET (token_t, expr_buffer, j)->code != ')')
	continue;
      macro_struct.id = VARR_GET (token_t, expr_buffer, k);
      res = HTAB_DO (macro_t, macro_tab, &macro_struct, HTAB_FIND, tab_macro) ? "1" : "0";
      VARR_SET (token_t, expr_buffer, i, new_token (t->pos, res, T_NUMBER, N_IGNORE)); // ???
      del_tokens (expr_buffer, i + 1, j - i);
    }
  }
  assert (VARR_LENGTH (token_t, buffer) == 0
	  && VARR_LENGTH (macro_call_t, macro_call_stack) == 0 && ! no_out_p);
  /* macro substitution */
  unget_next_pptoken (new_token (if_token->pos, "", T_EOP, N_IGNORE));
  push_back (expr_buffer);
  no_out_p = TRUE;
  processing (TRUE);
  no_out_p = FALSE;
  reverse_move_tokens (expr_buffer, buffer);
  VARR_CREATE (token_t, temp_buffer, VARR_LENGTH (token_t, expr_buffer));
  for (i = j = 0; i < VARR_LENGTH (token_t, expr_buffer); i++) {
    int change_p = TRUE;

    /* changing PP tokens to tokens and idents to "0" */
    ppt = VARR_GET (token_t, expr_buffer, i);
    t = pptoken2token (ppt, FALSE);
    if (t == NULL || t->code == ' ' || t->code == '\n')
      continue;
    if (t->code == T_NUMBER
	&& (t->node->code == N_F || t->node->code == N_D || t->node->code == N_LD)) {
      error (ppt->pos, "floating point in #if/#elif: %s", ppt->repr);
    } else if (t->code == T_STR) {
      error (ppt->pos, "string in #if/#elif: %s", ppt->repr);
    } else if (t->code != T_ID) {
      change_p = FALSE;
    }
    if (change_p)
      t = new_node_token (ppt->pos, "0", T_NUMBER, new_ll_node (0, ppt->pos));
    VARR_PUSH (token_t, temp_buffer, t);
  }
  no_out_p = TRUE;
  tree = parse_pre_expr (temp_buffer);
  no_out_p = FALSE;
  VARR_DESTROY (token_t, temp_buffer);
  if (tree == NULL) {
    struct val val;
    
    val.uns_p = FALSE; val.u.i_val = 0;
    return val;
  }
  return eval (tree);
}

static int eval_binop_operands (node_t tree, struct val *v1, struct val *v2) {
  *v1 = eval (NL_HEAD (tree->ops));
  *v2 = eval (NL_EL (tree->ops, 1));
  if (v1->uns_p && ! v2->uns_p) {
    v2->uns_p = TRUE; v2->u.u_val = v2->u.i_val;
  } else if (! v1->uns_p && v2->uns_p) {
    v1->uns_p = TRUE; v1->u.u_val = v1->u.i_val;
  }
  return v1->uns_p;
}

static struct val eval (node_t tree) {
  int cond;
  struct val res, v1, v2;

#define UNOP(op)			\
  do {					\
    v1 = eval (NL_HEAD (tree->ops));	\
    res = v1;				\
    if (res.uns_p)			\
      res.u.u_val = op res.u.u_val;	\
    else				\
      res.u.i_val = op res.u.i_val;	\
  } while (0)

#define BINOP(op)					\
  do {							\
    res.uns_p = eval_binop_operands (tree, &v1, &v2);	\
    if (res.uns_p)					\
      res.u.u_val = v1.u.u_val op v2.u.u_val;		\
    else						\
      res.u.i_val = v1.u.i_val op v2.u.i_val; 		\
  } while (0)

  switch (tree->code) {
  case N_CH:
    res.uns_p = ! char_is_signed_p () || MIR_CHAR_MAX > MIR_INT_MAX;
    if (res.uns_p)
      res.u.u_val = tree->u.ch;
    else
      res.u.i_val = tree->u.ch;
    break;
  case N_I:
  case N_L:
    res.uns_p = FALSE; res.u.i_val = tree->u.l;
    break;
  case N_LL:
    res.uns_p = FALSE; res.u.i_val = tree->u.ll;
    break;
  case N_U:
  case N_UL:
    res.uns_p = TRUE; res.u.u_val = tree->u.ul;
    break;
  case N_ULL:
    res.uns_p = TRUE; res.u.u_val = tree->u.ull;
    break;
  case N_BITWISE_NOT:
    UNOP (~); break;
  case N_NOT:
    UNOP (!); break;
  case N_EQ:
    BINOP (==); break;
  case N_NE:
    BINOP (!=); break;
  case N_LT:
    BINOP (<); break;
  case N_LE:
    BINOP (<=); break;
  case N_GT:
    BINOP (>); break;
  case N_GE:
    BINOP (>=); break;
  case N_ADD:
    if (NL_EL (tree->ops, 1) == NULL) {
      UNOP (+);
    } else {
      BINOP (+);
    }
    break;
  case N_SUB:
    if (NL_EL (tree->ops, 1) == NULL) {
      UNOP (-);
    } else {
      BINOP (-);
    }
    break;
  case N_AND:
    BINOP (&); break;
  case N_OR:
    BINOP (|); break;
  case N_XOR:
    BINOP (^); break;
  case N_LSH:
    BINOP (<<); break;
  case N_RSH:
    BINOP (>>); break;
  case N_MUL:
    BINOP (*); break;
  case N_DIV: case N_MOD: {
    int zero_p;
    
    res.uns_p = eval_binop_operands (tree, &v1, &v2);
    if (res.uns_p) {
      res.u.u_val = ((zero_p = v2.u.u_val == 0) ? 1
		     : tree->code == N_DIV ? v1.u.u_val / v2.u.u_val : v1.u.u_val % v2.u.u_val);
    } else {
      res.u.i_val = ((zero_p = v2.u.i_val == 0) ? 1
		     : tree->code == N_DIV ? v1.u.i_val / v2.u.i_val : v1.u.i_val % v2.u.i_val);
    }
    if (zero_p)
      error (tree->pos, "division (%s) by zero in preporocessor", tree->code == N_DIV ? "/" : "%");
    break;
  }
  case N_ANDAND:
  case N_OROR:
    v1 = eval (NL_HEAD (tree->ops));
    cond = v1.uns_p ? v1.u.u_val != 0 : v1.u.i_val != 0;
    if (tree->code == N_ANDAND ? cond : ! cond) {
      v2 = eval (NL_EL (tree->ops, 1));
      cond = v2.uns_p ? v2.u.u_val != 0 : v2.u.i_val != 0;
    }
    res.uns_p = FALSE; res.u.i_val = cond;
    break;
  case N_COND:
    v1 = eval (NL_HEAD (tree->ops));
    cond = v1.uns_p ? v1.u.u_val != 0 : v1.u.i_val != 0;
    res = eval (NL_EL (tree->ops, cond ? 1 : 2));
    break;
  default:
    assert (FALSE);
  }
  return res;
}

static void processing (int ignore_directive_p) {
  token_t t, t1, t2;
  struct macro macro_struct;
  macro_t m;
  macro_call_t mc;
  int newln_p;
  
  for (newln_p = TRUE;;) { /* Main loop. */
    t = get_next_pptoken ();
    if (t->code == T_EOP)
      return; /* end of processing */
    if (newln_p && ! ignore_directive_p && t->code == '#') {
      process_directive ();
      continue;
    }
    if (t->code == '\n') {
      newln_p = TRUE;
      out_token (t);
      continue;
    } else if (t->code == ' ') {
      out_token (t);
      continue;
    } else if (t->code == T_EOF || t->code == T_EOU) {
      if (VARR_LENGTH (ifstate_t, ifs) > eof_s->ifs_length_at_stream_start) {
	error (VARR_LAST (ifstate_t, ifs)->if_pos, "unfinished #if");
      }
      if (t->code == T_EOU)
	return;
      while (VARR_LENGTH (ifstate_t, ifs) > eof_s->ifs_length_at_stream_start)
	pop_ifstate ();
      skip_if_part_p = VARR_LENGTH (ifstate_t, ifs) == 0 ? 0 : VARR_LAST (ifstate_t, ifs)->skip_p;
      newln_p = TRUE;
      continue;
    } else if (skip_if_part_p) {
      skip_nl (t, NULL);
      newln_p = TRUE;
      continue;
    }
    newln_p = FALSE;
    if (t->code == T_EOR) { // finish macro call
      pop_macro_call ();
      continue;
    } else if (t->code == T_EOA) { /* arg end: add the result to repl_buffer */
      mc = VARR_LAST (macro_call_t, macro_call_stack);
      add_replacement_tokens (mc->repl_buffer, buffer);
      VARR_TRUNC (token_t, buffer, 0);
      process_replacement (mc);
      continue;
    } else if (t->code != T_ID) {
      out_token (t);
      continue;
    }
    macro_struct.id = t;
    if (! HTAB_DO (macro_t, macro_tab, &macro_struct, HTAB_FIND, m)) {
      if (! process_pragma (t))
	out_token (t);
      continue;
    }
    if (m->replacement == NULL) { /* standard macro */
      if (strcmp (t->repr, "__STDC__") == 0) {
	out_token (new_token (t->pos, "1", T_NUMBER, N_IGNORE));
      } else if (strcmp (t->repr, "__STDC_HOSTED__") == 0) {
	out_token (new_token (t->pos, "1", T_NUMBER, N_IGNORE));
      } else if (strcmp (t->repr, "__STDC_VERSION__") == 0) {
	out_token (new_token (t->pos, "201112L", T_NUMBER, N_IGNORE)); // ???
      } else if (strcmp (t->repr, "__FILE__") == 0) { 
	stringify (t->pos.fname, temp_string);
	VARR_PUSH (char, temp_string, '\0');
	out_token (new_token (t->pos, uniq_str (VARR_ADDR (char, temp_string)), T_STR, N_IGNORE));
      } else if (strcmp (t->repr, "__LINE__") == 0) {
	char str[50];
	
	sprintf (str, "%d", t->pos.lno);
	out_token (new_token (t->pos, uniq_str (str), T_NUMBER, N_IGNORE));
      } else if (strcmp (t->repr, "__DATE__") == 0) {
	out_token (new_token (t->pos, date_str, T_STR, N_IGNORE));
      } else if (strcmp (t->repr, "__TIME__") == 0) {
	out_token (new_token (t->pos, time_str, T_STR, N_IGNORE));
      } else {
	assert (FALSE);
      }
      continue;
    }
    if (m->ignore_p) {
      t->code = T_NO_MACRO_IDENT;
      out_token (t);
      continue;
    }
    if (m->params == NULL) { /* macro without parameters */
      unget_next_pptoken (new_token (t->pos, "", T_EOR, N_IGNORE));
      push_back (do_concat (m->replacement));
      mc = new_macro_call (m);
      m->ignore_p = TRUE;
      VARR_PUSH (macro_call_t, macro_call_stack, mc);
    } else { /* macro with parameters */
      t2 = NULL;
      t1 = get_next_pptoken ();
      if (t1->code == T_EOR) {
	pop_macro_call ();
	t1 = get_next_pptoken ();
      }
      if (t1->code == ' ' || t1->code == '\n') {
	t2 = t1;
	t1 = get_next_pptoken ();
      }
      if (t1->code != '(') { /* no args: it is not a macro call */
	unget_next_pptoken (t1);
	if (t2 != NULL)
	  unget_next_pptoken (t2);
	out_token (t);
	continue;
      }
      mc = new_macro_call (m);
      find_args (mc);
      VARR_PUSH (macro_call_t, macro_call_stack, mc);
      process_replacement (mc);
    }
  }
}

static token_t pre_last_token;
static pos_t shouldbe_pre_pos, actual_pre_pos;

static void pre_text_out (token_t t) { /* NULL means end of output */
  int i;

  if (t == NULL && pre_last_token != NULL && pre_last_token->code == '\n') {
    printf ("\n");
    return;
  }
  pre_last_token = t;
  if (! t->processed_p) {
    shouldbe_pre_pos = t->pos;
  }
  if (t->code == '\n')
    return;
  if (actual_pre_pos.fname != shouldbe_pre_pos.fname
      || actual_pre_pos.lno != shouldbe_pre_pos.lno) {
    if (actual_pre_pos.fname == shouldbe_pre_pos.fname
	&& actual_pre_pos.lno < shouldbe_pre_pos.lno
	&& actual_pre_pos.lno + 4 >= shouldbe_pre_pos.lno) {
      for (; actual_pre_pos.lno != shouldbe_pre_pos.lno; actual_pre_pos.lno++)
	printf ("\n");
    } else {
      if (pre_last_token != NULL)
	printf ("\n");
      printf ("#line %d", shouldbe_pre_pos.lno);
      if (actual_pre_pos.fname != shouldbe_pre_pos.fname) {
	stringify (t->pos.fname, temp_string);
	VARR_PUSH (char, temp_string, '\0');
	printf (" %s", VARR_ADDR (char, temp_string));
      }
      printf ("\n");
    }
    for (i = 0; i < shouldbe_pre_pos.ln_pos; i++)
      printf (" ");
    actual_pre_pos = shouldbe_pre_pos;
  }
  printf ("%s", t->code == ' ' ? " " : t->repr);
}

static VARR (token_t) *recorded_tokens;
static int record_level;
static size_t next_token_index;

static void pre_out (token_t t) {
  if (t == NULL) {
    t = new_token (pre_last_token == NULL ? no_pos : pre_last_token->pos, "<EOF>", T_EOF, N_IGNORE);
  } else {
    assert (t->code != T_EOU && t->code != EOF);
    pre_last_token = t;
    if ((t = pptoken2token (t, TRUE)) == NULL)
      return;
  }
  VARR_PUSH (token_t, recorded_tokens, t);
}

static unsigned long pptokens_num;

static void common_pre_out (token_t t) {
  pptokens_num++;
  (prepro_only_p ? pre_text_out : pre_out) (t);
}

static void pre (const char *start_source_name) {
  pre_last_token = NULL;
  actual_pre_pos.fname = NULL;
  shouldbe_pre_pos.fname = start_source_name; shouldbe_pre_pos.lno = 1; shouldbe_pre_pos.ln_pos = 0;
  pre_out_token_func = common_pre_out;
  pptokens_num = 0;
  if (! no_prepro_p) {
    processing (FALSE);
  } else {
    for (;;) {
      token_t t = get_next_pptoken ();

      if (t->code == T_EOF || t->code == T_EOU)
	break;
      pre_out_token_func (t);
    }
  }
  pre_out_token_func (NULL);
  if (verbose_p)
    fprintf (stderr, "    preprocessor tokens -- %lu, parse tokens -- %lu\n",
	     pptokens_num, (unsigned long) VARR_LENGTH (token_t, recorded_tokens));
  next_token_index = 0;
}

/* ------------------------- Preprocessor End ------------------------------ */

static token_t curr_token;

static void read_token (void) {
  curr_token = VARR_GET (token_t, recorded_tokens, next_token_index);
  next_token_index++;
}

static size_t record_start (void) {
  assert (next_token_index > 0 && record_level >= 0);
  record_level++;
  return next_token_index - 1;
}

static void record_stop (size_t mark, int restore_p) {
  assert (record_level > 0);
  record_level--;
  if (! restore_p)
    return;
  next_token_index = mark;
  read_token ();
}

static void syntax_error (const char *expected_name) {
  print_pos (stderr, curr_token->pos, TRUE);
  fprintf (stderr, "syntax error on %s", get_token_name (curr_token->code));
  fprintf (stderr, " (expected '%s'):", expected_name);
#if 0
  {
    static const int context_len = 5;
    
    for (int i = 0; i < context_len && curr_token->code != T_EOF; i++) {
      fprintf (stderr, " %s", curr_token->repr);
    }
  }
#endif
  fprintf (stderr, "\n");
}

static node_t top_scope, curr_scope;

typedef struct {
  node_t id, scope;
} tpname_t;

DEF_HTAB (tpname_t);
static HTAB (tpname_t) *tpname_tab;

static int tpname_eq (tpname_t tpname1, tpname_t tpname2) {
  return tpname1.id->u.s == tpname2.id->u.s && tpname1.scope == tpname2.scope;
}

static htab_hash_t tpname_hash (tpname_t tpname) {
  return (mir_hash_finish
	  (mir_hash_step
	   (mir_hash_step (mir_hash_init (0x42),
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
  if (! M(t)) {						        \
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

static int C (int c) { return curr_token->code == c; }

static int match (int c, pos_t *pos, node_code_t *node_code, node_t *node) {
  if (curr_token->code != c)
    return FALSE;
  if (pos != NULL)
    *pos = curr_token->pos;
  if (node_code != NULL)
    *node_code = curr_token->node_code;
  if (node != NULL)
    *node = curr_token->node;
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
  
  if (MN (T_ID, r) || MN (T_NUMBER, r) || MN (T_CH, r) || MN (T_STR, r)) {
    return r;
  } else if (M ('(')) {
    P (expr);
    if (M (')'))
      return r;
  } else if (MP (T_GENERIC, pos)) {
    PT ('('); P (assign_expr); PT (',');
    list = new_node (N_LIST);
    n = new_pos_node2 (N_GENERIC, pos, r, list);
    for (;;) { /* generic-assoc-list , generic-association */
      if (MP (T_DEFAULT, pos)) {
	op = new_node (N_IGNORE);
      } else {
	P (type_name);
	op = r; pos = op->pos;
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
    } else if (! MP ('(', pos)) {
      break;
    } else {
      op = r; r = NULL; code = N_CALL;
      list = new_node (N_LIST);
      if (! C (')')) {
	for (;;) {
	  P (assign_expr);
	  op_append (list, r);
	  if ( ! M (','))
	    break;
	}
      }
      r = list;
      PT (')');
    }
    n = new_pos_node1 (code, pos, op);
    if (r != NULL)
      op_append (n, r);
    r = n;
  }
  return r;
}

D (post_expr) {
  node_t r;
  
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
      P (unary_expr);
      r = new_node2 (N_CAST, t, r);
    } else {
      P (initializer_list);
      if (! M ('}'))
	return &err_node;
      r = new_pos_node2 (N_COMPOUND_LITERAL, pos, t, r);
      PA (post_expr_part, r);
    }
    return r;
  } else if (MP (T_SIZEOF, pos)) {
    if ((r = TRY (par_type_name)) != &err_node) {
      r = new_pos_node1 (N_SIZEOF, pos, r);
      return r;
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
    P (post_expr);
    return r;
  } else if (code == N_AND) {
    code = N_ADDR;
  } else if (code == N_MUL) {
    code = N_DEREF;
  }
  P (unary_expr);
  r = new_pos_node1 (code, pos, r);
  return r;
}

static node_t left_op (int no_err_p, int token, int token2, nonterm_func_t f) {
  node_code_t code;
  node_t r, n;
  pos_t pos;
  
  P (f);
  while (MC (token, pos, code) || (token2 >= 0 && MC (token2, pos, code))) {
    n = new_pos_node1 (code, pos, r);
    P (f);
    op_append (n, r);
    r = n;
  }
  return r;
}

static node_t right_op (int no_err_p, int token, int token2,
			nonterm_func_t left, nonterm_func_t right) {
  node_code_t code;
  node_t r, n;
  pos_t pos;
  
  P (left);
  if (MC (token, pos, code) || (token2 >= 0 && MC (token2, pos, code))) {
    n = new_pos_node1 (code, pos, r);
    P (right);
    op_append (n, r);
    r = n;
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
  pos_t pos;
  
  P (lor_expr);
  if (! MP ('?', pos))
    return r;
  n = new_pos_node1 (N_COND, pos, r);
  P (expr);
  op_append (n, r);
  if (! M (':'))
    return &err_node;
  P (cond_expr);
  op_append (n, r);
  return n;
}

#define const_expr cond_expr

D (assign_expr) { return right_op (no_err_p, T_ASSIGN, '=', cond_expr, assign_expr); }
D (expr) { return right_op (no_err_p, ',', -1, assign_expr, expr); }

/* Declarations; */
D (declaration_specs); D (sc_spec); D (type_spec); D (struct_declaration_list);
D (struct_declaration); D (spec_qual_list); D (type_qual); D (func_spec); D (align_spec);
D (declarator); D (direct_declarator); D (pointer); D (type_qual_list); D (param_type_list);
D (id_list); D (abstract_declarator); D (direct_abstract_declarator); D (typedef_name);
D (initializer); D (st_assert);

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
      for (op = NL_HEAD (spec->ops); op != NULL; op = NL_NEXT (op))
	if (op->code == N_TYPEDEF)
	  break;
      typedef_p = op != NULL;
      for (;;) { /* init-declarator */
	P (declarator);
	decl = r;
	assert (decl->code == N_DECL);
	if (typedef_p) {
	  op = NL_HEAD (decl->ops);
	  tpname_add (op, curr_scope);
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
    r = list;
    PT (';');
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
    } else
      break;
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
    if (record_level == 0)
      error (pos, "complex numbers are not supported");
    return &err_node;
  } else if (MP (T_ATOMIC, pos)) { /* atomic-type-specifier */
    PT ('('); P (type_name); PT (')');
    error (pos, "Atomic types are not supported"); 
  } else if ((struct_p = MP (T_STRUCT, pos)) || MP (T_UNION, pos)) {
    /* struct-or-union-specifier, struct-or-union */
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
      for (el = NL_HEAD (r->ops); el != NULL; el = next_el) {
	next_el = NL_NEXT (el);
	NL_REMOVE (r->ops, el);
	op_append (res, el);
      }
    }
    if (C ('}'))
      break;
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
	op = new_pos_node3 (N_MEMBER, op->pos, new_node1 (N_SHARE, spec), op, r);
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
    if (record_level == 0)
      syntax_error ("a type qualifier");
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
    if (record_level == 0)
      syntax_error ("a function specifier");
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
    list = NL_NEXT (NL_HEAD (r->ops));
    assert (list->code == N_LIST);
    for (el = NL_HEAD (p->ops); el != NULL; el = next_el) {
      next_el = NL_NEXT (el);
      NL_REMOVE (p->ops, el);
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
  list = NL_NEXT (NL_HEAD (res->ops));
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
      PT (']');
      op_append (list, new_node3 (N_ARR,
				  static_p
				  ? new_pos_node (N_STATIC, static_pos)
				  : new_node (N_IGNORE),
				  tql, ae));
    } else
      break;
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
    list = NL_NEXT (NL_HEAD (r->ops));
    assert (list->code == N_LIST);
    for (el = NL_HEAD (p->ops); el != NULL; el = next_el) {
      next_el = NL_NEXT (el);
      NL_REMOVE (p->ops, el);
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
  pos_t pos, pos2 = no_pos;
  
  if ((res = TRY (par_abstract_declarator)) != &err_node) {
    if (! C ('(') && ! C ('['))
      return res;
  } else {
    res = new_node2 (N_DECL, new_node (N_IGNORE), new_node (N_LIST));
  }
  list = NL_NEXT (NL_HEAD (res->ops));
  assert (list->code == N_LIST);
  for (;;) {
    if (MP ('(', pos)) {
      P (param_type_list); PT (')'); op_append (list, new_pos_node1 (N_FUNC, pos, r));
    } else {
      PTP ('[', pos);
      if (MP ('*', pos2)) {
	r = new_pos_node3 (N_ARR, pos, new_node (N_IGNORE),
			   new_node (N_IGNORE), new_pos_node (N_STAR, pos2));
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
	r = new_pos_node3 (N_ARR, pos,
			   static_p ? new_pos_node (N_STATIC, pos2) : new_node (N_IGNORE),
			   tql, ae);
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
  
  PTP (T_STATIC_ASSERT, pos); PT ('('); P (const_expr); op1 = r;
  PT (','); PTN (T_STR); PT (')');  PT (';');
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
    op_append (n, l);
    op_append (n, op1);
    op_append (n, op2);
    op_append (n, op3);
    op_append (n, r);
    r = n;
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
  if (debug_p)
    fprintf (stderr, "error recovery: skipping");
  for (;;) {
    if (curr_token->code == T_EOF || (par_lev == 0 && curr_token->code == ';'))
      break;
    if (curr_token->code == '{') {
      par_lev++;
    } else if (curr_token->code == '}') {
      if (--par_lev <= 0)
	break;
    }
    if (debug_p)
      fprintf (stderr, " %s(%d:%d)",
	       get_token_name (curr_token->code), curr_token->pos.lno, curr_token->pos.ln_pos);
    read_token ();
  }
  if (debug_p)
    fprintf (stderr, " %s\n", get_token_name (curr_token->code));
  read_token ();
}

D (compound_stmt) {
  node_t n, list, r;
  pos_t pos;
  
  PTE ('{', pos, err0); list = new_node (N_LIST);
  n = new_pos_node1 (N_BLOCK, pos, list); n->u.scope = curr_scope; curr_scope = n;
  while (! C ('}') && ! C (T_EOF)) { /* block-item-list, block_item */
    if ((r = TRY (declaration)) != &err_node) {
    } else {
      PE (stmt, err1);
    }
    op_flat_append (list, r);
    continue;
  err1:
    error_recovery (1);
  }
  curr_scope = n->u.scope;
  if (! C (T_EOF))
    PT ('}');
  return n;
 err0:
  error_recovery (0);
  return &err_node;
}
 
D (transl_unit) {
  node_t list, ds, d, dl, r;

  //curr_token->code = ';'; /* for error recovery */
  read_token ();
  list = new_node (N_LIST);
  while (! C (T_EOF)) { /* external-declaration */
    if ((r = TRY (declaration)) != &err_node) {
    } else {
      PE (declaration_specs, err); ds = r;
      PE (declarator, err); d = r;
      dl = new_node (N_LIST);
      d->u.scope = curr_scope; curr_scope = d;
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
  return new_node1 (N_MODULE, list);
}

static void fatal_error (C_error_code_t code, const char *message) {
  fprintf (stderr, "%s\n", message);
  exit (1);
}

static void kw_add (const char *name, token_code_t tc, size_t flags) {
  str_add (name, tc, flags, TRUE);
}

static void parse_init (void) {
  error_func = fatal_error; record_level = 0;
  reg_memory_init ();
  curr_uid = 0;
  init_streams ();
  VARR_CREATE (char, symbol_text, 128);
  VARR_CREATE (char, temp_string, 128);
  VARR_CREATE (token_t, buffered_tokens, 32);
  VARR_CREATE (token_t, recorded_tokens, 32);
  str_init ();
  pre_init ();
  kw_add ("_Bool", T_BOOL, 0);
  kw_add ("_Complex", T_COMPLEX, 0);
  kw_add ("_Alignas", T_ALIGNAS, 0);
  kw_add ("_Alignof", T_ALIGNOF, 0);
  kw_add ("_Atomic", T_ATOMIC, 0);
  kw_add ("_Generic", T_GENERIC, 0);
  kw_add ("_Noreturn", T_NO_RETURN, 0);
  kw_add ("_Static_assert", T_STATIC_ASSERT, 0);
  kw_add ("_Thread_local", T_THREAD_LOCAL, 0);
  kw_add ("auto", T_AUTO, 0);
  kw_add ("break", T_BREAK, 0);
  kw_add ("case", T_CASE, 0);
  kw_add ("char", T_CHAR, 0);
  kw_add ("const", T_CONST, 0);
  kw_add ("continue", T_CONTINUE, 0);
  kw_add ("default", T_DEFAULT, 0);
  kw_add ("do", T_DO, 0);
  kw_add ("double", T_DOUBLE, 0);
  kw_add ("else", T_ELSE, 0);
  kw_add ("enum", T_ENUM, 0);
  kw_add ("extern", T_EXTERN, 0);
  kw_add ("float", T_FLOAT, 0);
  kw_add ("for", T_FOR, 0);
  kw_add ("goto", T_GOTO, 0);
  kw_add ("if", T_IF, 0);
  kw_add ("inline", T_INLINE, FLAG_EXT89);
  kw_add ("int", T_INT, 0);
  kw_add ("long", T_LONG, 0);
  kw_add ("register", T_REGISTER, 0);
  kw_add ("restrict", T_RESTRICT, FLAG_C89);
  kw_add ("return", T_RETURN, 0);
  kw_add ("short", T_SHORT, 0);
  kw_add ("signed", T_SIGNED, 0);
  kw_add ("sizeof", T_SIZEOF, 0);
  kw_add ("static", T_STATIC, 0);
  kw_add ("struct", T_STRUCT, 0);
  kw_add ("switch", T_SWITCH, 0);
  kw_add ("typedef", T_TYPEDEF, 0);
  kw_add ("typeof", T_TYPEOF, FLAG_EXT);
  kw_add ("union", T_UNION, 0);
  kw_add ("unsigned", T_UNSIGNED, 0);
  kw_add ("void", T_VOID, 0);
  kw_add ("volatile", T_VOLATILE, 0);
  kw_add ("while", T_WHILE, 0);
  kw_add ("__restrict", T_RESTRICT, FLAG_EXT); kw_add ("__restrict__", T_RESTRICT, FLAG_EXT);
  kw_add ("__inline", T_INLINE, FLAG_EXT); kw_add ("__inline__", T_INLINE, FLAG_EXT);
  tpname_init ();
}

#ifndef SOURCEDIR
#define SOURCEDIR "./"
#endif

#ifndef INSTALLDIR
#define INSTALLDIR "/usr/bin/"
#endif

static void add_standard_includes (void) {
  FILE *f;
  const char *str1, *str2;
  
  for (int i = 0; i < sizeof (standard_includes) / sizeof (char *); i++) {
    VARR_TRUNC (char, temp_string, 0);
    add_to_temp_string (SOURCEDIR); add_to_temp_string (standard_includes[i]);
    str1 = uniq_str (VARR_ADDR (char, temp_string));
    VARR_TRUNC (char, temp_string, 0);
    add_to_temp_string (INSTALLDIR); add_to_temp_string ("../"); add_to_temp_string (standard_includes[i]);
    str2 = uniq_str (VARR_ADDR (char, temp_string));

    if ((f = fopen (str1, "r")) != NULL) {
      add_stream (f, str1);
    } else if ((f = fopen (str2, "r")) != NULL) {
      add_stream (f, str2);
    } else {
      fprintf (stderr, "Cannot open %s or %s -- good bye\n", str1, str2);
      exit (0);
    }
  }
}

static node_t parse (void) {
  return transl_unit (FALSE);
}

static void parse_finish (void) {
  VARR_DESTROY (char, symbol_text);
  VARR_DESTROY (char, temp_string);
  VARR_DESTROY (token_t, buffered_tokens);
  VARR_DESTROY (token_t, recorded_tokens);
  pre_finish ();
  str_finish ();
  tpname_finish ();
  finish_streams ();
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

/* ------------------------- Parser End ------------------------------ */


/* ---------------------- Context Checker Start ---------------------- */

/* The context checker is AST traversing pass which checks C11
   constraints.  It also augmenting AST nodes by type and layout
   information.  Here are the created node attributes:

1. expr nodes have attribute "struct expr", N_ID not expr context has NULL attribute.
2. N_SWITCH has attribute "struct switch_attr"
3. N_SPEC_DECL (only with ID), N_MEMBER, N_FUNC_DEF have attribute "struct decl"
4. N_GOTO hash attribute node_t (target stmt)
5. N_STRUCT, N_UNION have attribute "struct node_scope" if they have a decl list
6. N_MODULE, N_BLOCK, N_FOR, N_FUNC have attribute "struct node_scope"
7. declaration_specs or spec_qual_list N_LISTs have attribute "struct decl_spec"
8. N_ENUM_CONST has attribute "struct enum_value"
9. N_CASE and N_DEFAULT have attribute "struct case_attr"

*/

static int supported_alignment_p (mir_llong align) { return TRUE; } // ???

enum symbol_mode {
  S_REGULAR, S_TAG, S_LABEL
};

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
  return (mir_hash_finish
	  (mir_hash_step
	   (mir_hash_step
	    (mir_hash_step (mir_hash_init (0x42), (uint64_t) s.mode),
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

static VARR (node_t) *gotos;

static node_t func_block_scope;

enum basic_type get_int_basic_type (size_t s) {
  return (s == sizeof (mir_int) ? TP_INT
	  : s == sizeof (mir_short) ? TP_SHORT
	  : s == sizeof (mir_long) ? TP_LONG
	  : s == sizeof (mir_schar) ? TP_SCHAR : TP_LLONG);
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
  res.volatile_p = tq1->volatile_p || tq2->volatile_p;
  res.atomic_p = tq1->atomic_p || tq2->atomic_p;
  return res;
}

static void init_type (struct type *type) {
  clear_type_qual (&type->type_qual);
  type->pos_node = NULL; type->incomplete_p = FALSE;
  type->align = -1; type->raw_size = MIR_SIZE_MAX;
}

static void set_type_pos_node (struct type *type, node_t n) {
  if (type->pos_node == NULL)
    type->pos_node = n;
}

static int standard_integer_type_p (struct type *type) {
  return (type->mode == TM_BASIC
	  && type->u.basic_type >= TP_BOOL && type->u.basic_type <= TP_ULLONG);
}

static int integer_type_p (struct type *type) {
  return standard_integer_type_p (type) || type->mode == TM_ENUM;
}

static int signed_integer_type_p (struct type *type) {
  if (standard_integer_type_p (type)) {
    enum basic_type tp = type->u.basic_type;
    
    return ((tp == TP_CHAR && char_is_signed_p ())
	    || tp == TP_SCHAR || tp == TP_SHORT
	    || tp == TP_INT || tp == TP_LONG || tp == TP_LLONG);
  }
  if (type->mode == TM_ENUM) { // ???
    return TRUE;
  }
  return FALSE;
}

static int floating_type_p (struct type *type) {
  return type->mode == TM_BASIC && (type->u.basic_type == TP_FLOAT
				    || type->u.basic_type == TP_DOUBLE
				    || type->u.basic_type == TP_LDOUBLE);
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
  if (type->mode == TM_BASIC && TP_LONG <= type->u.basic_type && type->u.basic_type <= TP_ULLONG) {
    res.u.basic_type = type->u.basic_type;
    return res;
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
    if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_LDOUBLE)
	|| (type2->mode == TM_BASIC && type2->u.basic_type == TP_LDOUBLE)) {
      res.u.basic_type = TP_LDOUBLE;
    } else if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_DOUBLE)
	       || (type2->mode == TM_BASIC && type2->u.basic_type == TP_DOUBLE)) {
      res.u.basic_type = TP_DOUBLE;
    } else if ((type1->mode == TM_BASIC && type1->u.basic_type == TP_FLOAT)
	       || (type2->mode == TM_BASIC && type2->u.basic_type == TP_FLOAT)) {
      res.u.basic_type = TP_FLOAT;
    }
    return res;
  }
  t1 = integer_promotion (type1);
  t2 = integer_promotion (type2);
  if (signed_integer_type_p (&t1) == signed_integer_type_p (&t2)) {
    res.u.basic_type = t1.u.basic_type < t2.u.basic_type ? t2.u.basic_type : t1.u.basic_type;
  } else {
    struct type t;
    
    if (signed_integer_type_p (&t1))
      SWAP (t1, t2, t);
    assert (! signed_integer_type_p (&t1) && signed_integer_type_p (&t2));
    if ((t1.u.basic_type == TP_ULONG && t2.u.basic_type < TP_LONG)
	|| (t1.u.basic_type == TP_ULLONG && t2.u.basic_type < TP_LLONG)) {
      res.u.basic_type = t1.u.basic_type;
    } else if ((t1.u.basic_type == TP_UINT && t2.u.basic_type >= TP_LONG
		&& MIR_LONG_MAX >= MIR_UINT_MAX)
	       || (t1.u.basic_type == TP_ULONG && t2.u.basic_type >= TP_LLONG
		   && MIR_LLONG_MAX >= MIR_ULONG_MAX)) {
      res.u.basic_type = t2.u.basic_type;
    } else {
      res.u.basic_type = t1.u.basic_type;
    }
  }
  return res;
}

struct expr {
  unsigned int const_p : 1;
  node_t lvalue_node, def_node;
  struct type *type;
  union {
    mir_llong i_val;
    mir_ullong u_val;
    mir_ldouble d_val;
  } u;
};

static int compatible_types_p (struct type *type1, struct type *type2, int ignore_quals_p) {
  if (type1->mode != type2->mode)
    return FALSE;
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

    if (NL_LENGTH (ft1->param_list->ops) != NL_LENGTH (ft2->param_list->ops))
      return FALSE;
    // ???
  } else {
    assert (type1->mode == TM_STRUCT || type1->mode == TM_UNION || type1->mode == TM_ENUM);
    return (type1->u.tag_type == type2->u.tag_type
	    && (ignore_quals_p || type_qual_eq_p (&type1->type_qual, &type2->type_qual)));
  }
  return TRUE;
}

static struct type composite_type (struct type *tp1, struct type *tp2) {
  struct type t = *tp1;
  
  assert (compatible_types_p (tp1, tp2, FALSE) && tp1->mode == tp2->mode);
  if (tp1->mode == TM_ARR) {
    struct arr_type *arr_type;

    t.u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
    *arr_type = *tp1->u.arr_type;
    if (arr_type->size == N_IGNORE)
      arr_type->size = tp2->u.arr_type->size;
    *arr_type->el_type = composite_type (tp1->u.arr_type->el_type, tp2->u.arr_type->el_type);
  } else if (tp1->mode == TM_FUNC) {
  }
  return t;
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
  unsigned int typedef_p : 1, extern_p : 1, static_p : 1;
  unsigned int auto_p : 1, register_p : 1, thread_local_p : 1;
  unsigned int inline_p : 1, no_return_p : 1; /* func specifiers  */
  int align; // negative value means undefined
  node_t align_node; //  strictest valid N_ALIGNAS node
  node_code_t linkage; // N_IGNORE - none, N_STATIC - internal, N_EXTERN - external
  struct type *type;
};

struct enum_value {
  mir_int val;
};

struct node_scope {
  unsigned func_scope_num;
  mir_size_t size, offset;
  node_t scope;
};

struct decl {
  unsigned addr_p : 1, reg_p : 1; /* true if address is taken; true if reg can be used */
  int bit_offset, width; /* for bitfields, -1 bit_offset for non bitfields. */
  mir_size_t offset; /* var offset in frame or bss */
  node_t scope; /* declaration scope */
  struct decl_spec decl_spec;
  MIR_item_t item; /* MIR_item for some declarations */
};

typedef struct decl *decl_t;

typedef struct case_attr *case_t;

DEF_DLIST_LINK (case_t);

struct case_attr {
  node_t case_node, case_target_node;
  DLIST_LINK (case_t) case_link;
};

DEF_DLIST (case_t, case_link);

struct switch_attr {
  struct type type; /* integer promoted type */
  DLIST (case_t) case_labels; /* default if any is always a tail */
};

static int basic_type_size (enum basic_type bt) {
  switch (bt) {
  case TP_BOOL:
    return sizeof (mir_bool);
  case TP_CHAR:
    return sizeof (mir_char);
  case TP_SCHAR:
    return sizeof (mir_schar);
  case TP_UCHAR:
    return sizeof (mir_uchar);
  case TP_SHORT:
    return sizeof (mir_short);
  case TP_USHORT:
    return sizeof (mir_ushort);
  case TP_INT:
    return sizeof (mir_int);
  case TP_UINT:
    return sizeof (mir_uint);
  case TP_LONG:
    return sizeof (mir_long);
  case TP_ULONG:
    return sizeof (mir_ulong);
  case TP_LLONG:
    return sizeof (mir_llong);
  case TP_ULLONG:
    return sizeof (mir_ullong);
  case TP_FLOAT:
    return sizeof (mir_float);
  case TP_DOUBLE:
    return sizeof (mir_double);
  case TP_LDOUBLE:
    return sizeof (mir_ldouble);
  case TP_VOID:
    return 1; // ???
  default:
    abort ();
  }
}

static int basic_type_align (enum basic_type bt) {
  return basic_type_size (bt);
}

static int type_align (struct type *type) {
  assert (type->align >= 0);
  return type->align; }

static void aux_set_type_align (struct type *type) {
  /* Should be called only from set_type_layout. */
  int align, member_align;
  
  if (type->align >= 0)
    return;
  if (type->mode == TM_BASIC) {
    align = basic_type_align (type->u.basic_type);
  } else if (type->mode == TM_PTR) {
    align = sizeof (mir_size_t);
  } else if (type->mode == TM_ENUM) {
    align = basic_type_align (TP_INT);
  } else if (type->mode == TM_FUNC) {
    align = sizeof (mir_size_t);
  } else if (type->mode == TM_ARR) {
    align = type_align (type->u.arr_type->el_type);
  } else {
    assert (type->mode == TM_STRUCT || type->mode == TM_UNION);
    align =  1;
    if (! type->incomplete_p)
      for (node_t member = NL_HEAD (NL_EL (type->u.tag_type->ops, 1)->ops);
	   member != NULL;
	   member = NL_NEXT (member))
	if (member->code == N_MEMBER) {
	  decl_t decl = member->attr;
	  
	  member_align = type_align (decl->decl_spec.type);
	  if (align < member_align)
	    align = member_align;
	}
  }
#ifdef ADJUST_TYPE_ALIGNMENT
  align = ADJUST_TYPE_ALIGNMENT (align, type);
#endif
  type->align = align;
}

static mir_size_t type_size (struct type *type) {
  assert (type->raw_size != MIR_SIZE_MAX && type->align >= 0);
  return (type->raw_size + type->align - 1) / type->align * type->align;
}


/* BOUND_BIT is used only if BF_P.  */
static void update_field_layout (int *bf_p, mir_size_t *overall_size,
				 mir_size_t *offset, int *bound_bit,
				 mir_size_t prev_size, mir_size_t size,
				 int align, int bits) {
  mir_size_t prev_field_offset = *offset, bytes = 0;
  int start_bit, diff;
  
  assert (size > 0);
  if (! *bf_p) { /* field -> bit field or field */
    if (bits >= 0 && size > prev_size) {
      *bound_bit = prev_size * MIR_CHAR_BIT;
    } else {
      prev_field_offset += prev_size;
      *offset = prev_field_offset / align * align;
      *bound_bit = (prev_field_offset - *offset) * MIR_CHAR_BIT;
      prev_field_offset = *offset;
    }
  }
  *bf_p = bits >= 0;
  if (bits < 0) {
    bytes = size - 1;
    bits = MIR_CHAR_BIT;
  }
  *offset = prev_field_offset / align * align;
  diff = prev_field_offset - *offset;
  for (;;) {
    start_bit = *bound_bit + diff * MIR_CHAR_BIT;
    if (start_bit < 0)
      start_bit = 0;
    if ((start_bit + bits - 1) / MIR_CHAR_BIT + 1 + bytes <= size) {
      *bound_bit = start_bit + bits;
      break;
    }
    *offset += align;
    diff -= align;
    if (bytes >= align)
      bytes -= align;
  }
  if (*overall_size < *offset + size)
    *overall_size = *offset + size;
}

static void set_type_layout (struct type *type) {
  mir_size_t overall_size = 0;

  if (type->raw_size != MIR_SIZE_MAX)
    return; /* defined */
  if (type->mode == TM_BASIC) {
    overall_size = basic_type_size (type->u.basic_type);
  } else if (type->mode == TM_PTR) {
    overall_size = sizeof (mir_size_t);
  } else if (type->mode == TM_ENUM) {
    overall_size = basic_type_size (TP_INT);
  } else if (type->mode == TM_FUNC) {
    overall_size = sizeof (mir_size_t);
  } else if (type->mode == TM_ARR) {
    struct arr_type *arr_type = type->u.arr_type;
    struct expr *cexpr = arr_type->size->attr;
    mir_size_t nel = (arr_type->size->code == N_IGNORE || ! cexpr->const_p ? 1 : cexpr->u.i_val);

    set_type_layout (arr_type->el_type);
    overall_size = type_size (arr_type->el_type) * nel;
  } else {
    int bf_p = FALSE, bits = -1, bound_bit = 0;
    mir_size_t offset = 0, prev_size = 0;
    
    assert (type->mode == TM_STRUCT || type->mode == TM_UNION);
    if (! type->incomplete_p)
      for (node_t member = NL_HEAD (NL_EL (type->u.tag_type->ops, 1)->ops);
	   member != NULL;
	   member = NL_NEXT (member))
	if (member->code == N_MEMBER) {
	  decl_t decl = member->attr;
	  int member_align;
	  mir_size_t member_size;
	  node_t width = NL_EL (member->ops, 2);
	  struct expr *expr;
	  
	  set_type_layout (decl->decl_spec.type);
	  member_size = type_size (decl->decl_spec.type);
	  member_align = type_align (decl->decl_spec.type);
	  bits = width->code == N_IGNORE || !(expr = width->attr)->const_p ? -1 : expr->u.u_val;
	  if (bits != 0) {
	    update_field_layout (&bf_p, &overall_size, &offset, &bound_bit,
				 prev_size, member_size, member_align, bits);
	    prev_size = member_size;
	    decl->offset = offset;
	    decl->bit_offset = bits < 0 ? -1 : bound_bit - bits;
	  } else { /* Finish the last unit */
	    bf_p = FALSE;
	    offset = (offset + member_align - 1) / member_align;
	    /* The offset and bit_offset do not matter, but make
	       bit_offset less member_size in bits */
	    decl->offset = offset + bound_bit / (member_size * MIR_CHAR_BIT);
	    decl->bit_offset = bound_bit % (member_size * MIR_CHAR_BIT);
	  }
	  decl->width = bits;
	  if (type->mode == TM_UNION) {
	    offset = prev_size = 0;
	    bf_p = FALSE;
	    bits = -1;
	    bound_bit = 0;
	  }
	}
  }
  /* we might need raw_size for alignment calculations */
  type->raw_size = overall_size;
  aux_set_type_align (type);
  if (type->mode == TM_PTR)  /* Visit the pointed but after setting size to avoid looping */
    set_type_layout (type->u.ptr_type);
}

static int int_bit_size (struct type *type) {
  assert (type->mode == TM_BASIC);
  return basic_type_size (type->u.basic_type) * MIR_CHAR_BIT;
}

static int void_ptr_p (struct type *type) {
  return (type->mode == TM_PTR
	  && type->u.ptr_type->mode == TM_BASIC && type->u.ptr_type->u.basic_type == TP_VOID);
}

static int null_const_p (struct expr *expr, struct type *type) {
  return  (void_ptr_p (type) && expr->const_p && expr->u.u_val == 0
	   && type_qual_eq_p (&type->type_qual, &zero_type_qual));
}

static void convert_value (struct expr *e, struct type *t) {
}

static int non_reg_decl_spec_p (struct decl_spec *ds) {
  return (ds->typedef_p || ds->extern_p || ds->static_p || ds->auto_p
	  || ds->thread_local_p || ds->inline_p || ds->no_return_p || ds->align_node);
}

static unsigned curr_func_scope_num;

static void create_node_scope (node_t node) {
  struct node_scope *ns = reg_malloc (sizeof (struct node_scope));
  
  assert (node != curr_scope);
  ns->func_scope_num = curr_func_scope_num++;
  ns->size = 0;
  ns->offset = curr_scope == NULL ? 0 : ((struct node_scope *) curr_scope->attr)->offset;
  node->attr = ns; ns->scope = curr_scope; curr_scope = node;
}

static void finish_scope (void) {
  struct node_scope *ns = (struct node_scope *) curr_scope->attr;
  mir_size_t size = ns->size;
  
  curr_scope = ns->scope;
  if (curr_scope != NULL && curr_scope != top_scope) {
    ns = (struct node_scope *) curr_scope->attr;
    if (ns->size < size)
      ns->size = size;
  }
}

static void set_type_qual (node_t r, struct type_qual *tq, enum type_mode tmode) {
  for (node_t n = NL_HEAD (r->ops); n != NULL; n = NL_NEXT (n))
    switch (n->code) {
      /* Type qualifiers: */
    case N_CONST:
      tq->const_p = TRUE;
      break;
    case N_RESTRICT:
      tq->restrict_p = TRUE;
      if (tmode != TM_PTR && tmode != TM_UNDEF)
	error (n->pos, "restrict requires a pointer");
      break;
    case N_VOLATILE:
      tq->volatile_p = TRUE;
      break;
    case N_ATOMIC:
      tq->atomic_p = TRUE;
      if (tmode == TM_ARR)
	error (n->pos, "_Atomic qualifying array");
      else if (tmode == TM_FUNC)
	error (n->pos, "_Atomic qualifying function");
      break;
    default:
      break;  /* Ignore */
    }
}

static void check_type_duplication (struct type *type, node_t n, const char *name,
				    int size, int sign) {
  if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
    error (n->pos, "%s with another type", name);
  else if (type->mode != TM_BASIC && size != 0)
    error (n->pos, "size with non-numeric type");
  else if (type->mode != TM_BASIC && sign != 0)
    error (n->pos, "sign attribute with non-integer type");
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
    error (id->pos, "kind of tag %s is unmatched with previous declaration", id->u.s);
  } else if ((tab_decl_list = NL_EL (sym.def_node->ops, 1))->code != N_IGNORE
	     && decl_list->code != N_IGNORE) {
    error (id->pos, "tag %s redeclaration", id->u.s);
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

static void def_symbol (enum symbol_mode mode, node_t id, node_t scope,
			node_t def_node, node_code_t linkage) {
  symbol_t sym;
  struct decl_spec tab_decl_spec, decl_spec;
  
  if (id->code == N_IGNORE)
    return;
  assert (id->code == N_ID && scope != NULL);
  assert (scope->code == N_MODULE || scope->code == N_BLOCK || scope->code == N_STRUCT
	  || scope->code == N_UNION || scope->code == N_FUNC || scope->code == N_FOR);
  decl_spec = ((decl_t) def_node->attr)->decl_spec;
  if (decl_spec.thread_local_p && ! decl_spec.static_p && ! decl_spec.extern_p)
    error (id->pos, "auto %s is declared as thread local", id->u.s);
  if (! symbol_find (mode, id, scope, &sym)) {
    symbol_insert (mode, id, scope, def_node, NULL);
    return;
  }
  tab_decl_spec = ((decl_t) sym.def_node->attr)->decl_spec;
  if (linkage == N_IGNORE) {
    if (! decl_spec.typedef_p || ! tab_decl_spec.typedef_p
	|| decl_spec.type != tab_decl_spec.type)
      error (id->pos, "repeated declaration %s", id->u.s);
  } else if (! compatible_types_p (decl_spec.type, tab_decl_spec.type, FALSE)) {
    error (id->pos, "incompatible types of %s declarations", id->u.s);
  }
  if (tab_decl_spec.thread_local_p != decl_spec.thread_local_p) {
    error (id->pos, "thread local and non-thread local declarations of %s", id->u.s);
  }
}

static int in_params_p;

static void check (node_t node, node_t context);
    
static struct decl_spec check_decl_spec (node_t r, node_t decl) {
  int n_sc = 0, sign = 0, size = 0;
  struct decl_spec *res;
  struct type *type;
  
  if (r->attr != NULL)
    return *(struct decl_spec *) r->attr;
  r->attr = res = reg_malloc (sizeof (struct decl_spec));
  res->typedef_p = res->extern_p = res->static_p = FALSE;
  res->auto_p = res->register_p = res->thread_local_p = FALSE;
  res->inline_p = res->no_return_p = FALSE;
  res->align = -1; res->align_node = NULL; res->linkage = N_IGNORE;
  res->type = type = create_type (NULL); type->pos_node = r;
  type->mode = TM_BASIC; type->u.basic_type = TP_UNDEF;
  for (node_t n = NL_HEAD (r->ops); n != NULL; n = NL_NEXT (n))
    if (n->code == N_SIGNED || n->code == N_UNSIGNED) {
      if (sign != 0)
	error (n->pos, "more than one sign qualifier");
      else
	sign = n->code == N_SIGNED ? 1 : -1;
    } else if (n->code == N_SHORT) {
      if (size != 0)
	error (n->pos, "more than one type");
      else
	size = 1;
    } else if (n->code == N_LONG) {
      if (size == 2)
	size = 3;
      else if (size == 3)
	error (n->pos, "more than two long");
      else if (size == 1)
	error (n->pos, "short with long");
      else
	size = 2;
    }
  for (node_t n = NL_HEAD (r->ops); n != NULL; n = NL_NEXT (n))
    switch (n->code) {
      /* Type qualifiers are already processed. */
    case N_CONST: case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: break;
      /* Func specifiers: */
    case N_INLINE:
      if (decl->code != N_FUNC_DEF)
	error (n->pos, "non-function declaration with inline");
      else
	res->inline_p = TRUE;
      break;
    case N_NO_RETURN:
      if (decl->code != N_FUNC_DEF)
	error (n->pos, "non-function declaration with _Noreturn");
      else
	res->no_return_p = TRUE;
      break;
      /* Storage specifiers: */
    case N_TYPEDEF:
    case N_AUTO:
    case N_REGISTER:
      if (n_sc != 0)
	error (n->pos, "more than one storage specifier");
      else if (n->code == N_TYPEDEF)
	res->typedef_p = TRUE;
      else if (n->code == N_AUTO)
	res->auto_p = TRUE;
      else
	res->register_p = TRUE;
      n_sc++;
      break;
    case N_EXTERN:
    case N_STATIC:
      if (n_sc != 0 && (n_sc != 1 || !res->thread_local_p))
	error (n->pos, "more than one storage specifier");
      else if (n->code == N_EXTERN)
	res->extern_p = TRUE;
      else
	res->static_p = TRUE;
      n_sc++;
      break;
    case N_THREAD_LOCAL:
      if (n_sc != 0 && (n_sc != 1 || (!res->extern_p && !res->static_p)))
	error (n->pos, "more than one storage specifier");
      else
	res->thread_local_p = TRUE;
      n_sc++;
      break;
    case N_VOID:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	error (n->pos, "void with another type");
      else if (sign != 0)
	error (n->pos, "void with sign qualifier");
      else if (size != 0)
	error (n->pos, "void with short or long");
      else {
	type->u.basic_type = TP_VOID; type->incomplete_p = TRUE;
      }
      break;
    case N_UNSIGNED:
    case N_SIGNED:
    case N_SHORT:
    case N_LONG:
      set_type_pos_node (type, n);
      break;
    case N_CHAR:
    case N_INT:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF) {
	error (n->pos, "char or int with another type");
      } else if (n->code == N_CHAR) {
	if (size != 0)
	  error (n->pos, "char with short or long");
	else
	  type->u.basic_type = sign == 0 ? TP_CHAR : sign < 0 ? TP_UCHAR : TP_SCHAR;
      } else if (size == 0)
	type->u.basic_type = sign >= 0 ? TP_INT : TP_UINT;
      else if (size == 1)
	type->u.basic_type = sign >= 0 ? TP_SHORT : TP_USHORT;
      else if (size == 2)
	type->u.basic_type = sign >= 0 ? TP_LONG : TP_ULONG;
      else
	type->u.basic_type = sign >= 0 ? TP_LLONG : TP_ULLONG;
      break;
    case N_BOOL:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	error (n->pos, "_Bool with another type");
      else if (sign != 0)
	error (n->pos, "_Bool with sign qualifier");
      else if (size != 0)
	error (n->pos, "_Bool with short or long");
      type->u.basic_type = TP_BOOL;
      break;
    case N_FLOAT:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	error (n->pos, "float with another type");
      else if (sign != 0)
	error (n->pos, "float with sign qualifier");
      else if (size != 0)
	error (n->pos, "float with short or long");
      else
	type->u.basic_type = TP_FLOAT;
      break;
    case N_DOUBLE:
      set_type_pos_node (type, n);
      if (type->mode != TM_BASIC || type->u.basic_type != TP_UNDEF)
	error (n->pos, "double with another type");
      else if (sign != 0)
	error (n->pos, "double with sign qualifier");
      else if (size == 0)
	type->u.basic_type = TP_DOUBLE;
      else if (size == 2)
	type->u.basic_type = TP_LDOUBLE;
      else
	error (n->pos, "double with short");
      break;
    case N_ID: {
      node_t def = find_def (S_REGULAR, n, curr_scope, NULL);
      decl_t decl;
      
      set_type_pos_node (type, n);
      if (def == NULL) {
	error (n->pos, "unknown type %s", n->u.s);
	init_type (type);
	type->mode = TM_BASIC; type->u.basic_type = TP_INT;
      } else {
	assert (def->code == N_SPEC_DECL);
	decl = def->attr;
	assert (decl->decl_spec.typedef_p);
	*type = *decl->decl_spec.type;
      }
      break;
    }
    case N_STRUCT:
    case N_UNION: {
      node_t res, id = NL_HEAD (n->ops);
      node_t decl_list = NL_NEXT (id);

      set_type_pos_node (type, n);
      res = process_tag (n, id, decl_list);
      check_type_duplication (type, n, n->code == N_STRUCT ? "struct" : "union", size, sign);
      type->mode = n->code == N_STRUCT ? TM_STRUCT : TM_UNION; type->u.tag_type = res;
      type->incomplete_p = NL_EL (res->ops, 1)->code == N_IGNORE;
      if (decl_list->code != N_IGNORE) {
	create_node_scope (res);
	check (decl_list, n);
	finish_scope ();
      }
      break;
    }
    case N_ENUM: {
      node_t res, id = NL_HEAD (n->ops);
      node_t enum_list = NL_NEXT (id);
      
      set_type_pos_node (type, n);
      res = process_tag (n, id, enum_list);
      check_type_duplication (type, n, "enum", size, sign);
      type->mode = TM_ENUM; type->u.tag_type = res;
      type->incomplete_p = NL_EL (res->ops, 1)->code == N_IGNORE;
      if (enum_list->code == N_IGNORE) {
	if (type->incomplete_p)
	  error (n->pos, "enum storage size is unknown");
      } else {
	mir_int curr_val = 0;
	
	for (node_t en = NL_HEAD (enum_list->ops); en != NULL; en = NL_NEXT (en)) { // ??? id
	  node_t id, const_expr;
	  symbol_t sym;
	  struct enum_value *enum_value;

	  assert (en->code == N_ENUM_CONST);
	  id = NL_HEAD (en->ops); const_expr = NL_NEXT (id);
	  check (const_expr, n);
	  if (symbol_find (S_REGULAR, id, curr_scope, &sym)) {
	    error (id->pos, "enum constant %s redeclaration", id->u.s);
	  } else {
	    symbol_insert (S_REGULAR, id, curr_scope, en, n);
	  }
	  if (const_expr->code != N_IGNORE) {
	    struct expr *cexpr = const_expr->attr;
	    
	    if (! cexpr->const_p)
	      error (const_expr->pos, "non-constant value in enum const expression");
	    else if (! integer_type_p (cexpr->type))
	      error (const_expr->pos, "enum const expression is not of an integer type");
	    else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val > MIR_INT_MAX)
		     || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val > MIR_INT_MAX))
	      error (const_expr->pos, "enum const expression is not represented by int");
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
	error (n->pos, "_Alignas for function");
      } else if (decl->code == N_MEMBER && (el = NL_EL (decl->ops, 3)) != NULL
		 && el->code != N_IGNORE) {
	error (n->pos, "_Alignas for a bit-field");
      } else if (decl->code == N_SPEC_DECL && in_params_p) {
	error (n->pos, "_Alignas for a function parameter");
      } else {
	node_t op = NL_HEAD (n->ops);

	check (op, n);
	if (op->code == N_TYPE) {
	  struct decl_spec *decl_spec = op->attr;
	  
	  align = type_align (decl_spec->type);
	} else {
	  struct expr *cexpr = op->attr;

	  if (! cexpr->const_p) {
	    error (op->pos, "non-constant value in _Alignas");
	  } else if (! integer_type_p (cexpr->type)) {
	    error (op->pos, "constant value in _Alignas is not of an integer type");
	  } else if (! signed_integer_type_p (cexpr->type)
		     || ! supported_alignment_p (cexpr->u.i_val)) {
	    error (op->pos, "constant value in _Alignas specifies unspported alignment");
	  } else if (invalid_alignment (cexpr->u.i_val)) {
	    error (op->pos, "unsupported alignmnent");
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
      error (r->pos, "no any type specifier");
    else if (size == 0)
      type->u.basic_type = sign >= 0 ? TP_INT : TP_UINT;
    else if (size == 1)
      type->u.basic_type = sign >= 0 ? TP_SHORT : TP_USHORT;
    else if (size == 2)
      type->u.basic_type = sign >= 0 ? TP_LONG : TP_ULONG;
    else
      type->u.basic_type = sign >= 0 ? TP_LLONG : TP_ULLONG;
  }
  set_type_qual (r, &type->type_qual, type->mode);
  if (res->align_node) {
    if (res->typedef_p)
      error (res->align_node->pos, "_Alignas in typedef");
    else if (res->register_p)
      error (res->align_node->pos, "_Alignas with register");
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
  if (head->mode != TM_PTR && (*holder)->incomplete_p
      && (head->mode != TM_FUNC
	  || (*holder)->mode != TM_BASIC || (*holder)->u.basic_type != TP_VOID))
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
  node_t list = NL_EL (r->ops, 1);
  
  assert (r->code == N_DECL);
  if (NL_HEAD (list->ops) == NULL)
    return NULL;
  for (node_t n = NL_HEAD (list->ops); n != NULL; n = NL_NEXT (n)) {
    type = create_type (NULL);
    type->pos_node = n;
    switch (n->code) {
    case N_POINTER: {
      node_t type_qual = NL_HEAD (n->ops);
      
      type->mode = TM_PTR; type->pos_node = n; type->u.ptr_type = NULL;
      set_type_qual (type_qual, &type->type_qual, TM_PTR);
      break;
    }
    case N_ARR: {
      struct arr_type *arr_type;
      node_t static_node = NL_HEAD (n->ops);
      node_t type_qual = NL_NEXT (static_node);
      node_t size = NL_NEXT (type_qual);
      
      type->mode = TM_ARR; type->pos_node = n;
      type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
      clear_type_qual (&arr_type->ind_type_qual);
      set_type_qual (type_qual, &arr_type->ind_type_qual, TM_UNDEF);
      check (size, n);
      arr_type->size = size;
      arr_type->static_p = static_node->code == N_STATIC; arr_type->el_type = NULL;
      break;
    }
    case N_FUNC: {
      struct func_type *func_type;
      node_t first_param, param_list = NL_HEAD (n->ops);
      node_t last = NL_TAIL (param_list->ops);
      int saved_in_params_p = in_params_p;
      
      type->mode = TM_FUNC; type->pos_node = n;
      type->u.func_type = func_type = reg_malloc (sizeof (struct func_type));
      func_type->ret_type = NULL;
      func_type->proto_item = NULL;
      if ((func_type->dots_p = last != NULL && last->code == N_DOTS))
	NL_REMOVE (param_list->ops, last);
      if (! func_def_p)
	create_node_scope (n);
      func_type->param_list = param_list;
      in_params_p = TRUE;
      first_param = NL_HEAD (param_list->ops);
      if (first_param != NULL && first_param->code != N_ID)
	check (first_param, n);
      if (void_param_p (first_param)) {
	struct decl_spec *ds = first_param->attr;
	
	if (non_reg_decl_spec_p (ds) || ds->register_p
	    || ! type_qual_eq_p (&ds->type->type_qual, &zero_type_qual)) {
	  error (first_param->pos, "qualified void parameter");
	}
	if (NL_NEXT (first_param) != NULL) {
	  error (first_param->pos, "void must be the only parameter");
	}
      } else {
	for (node_t p = first_param; p != NULL; p = NL_NEXT (p)) {
	  struct decl_spec *decl_spec_ptr;
	  struct type *type;
	  
	  if (p->code == N_ID) {
	    if (! func_def_p)
	      error (p->pos, "parameters identifier list can be only in function definition");
	    break;
	  } else {
	    if (p != first_param)
	      check (p, n);
	    if (p->code == N_TYPE) {
	      decl_spec_ptr = p->attr;
	    } else {
	      node_t declarator = NL_EL (p->ops, 1);
	      
	      assert (p->code == N_SPEC_DECL && declarator != NULL && declarator->code == N_DECL);
	      decl_spec_ptr = &((decl_t) p->attr)->decl_spec;
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
      if (! func_def_p)
	finish_scope ();
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
  for (node_t l = NL_HEAD (labels->ops); l != NULL; l = NL_NEXT (l)) {
    if (l->code == N_LABEL) {
      symbol_t sym;
      node_t id = NL_HEAD (l->ops);
      
      if (symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	error (id->pos, "label %s redeclaration", id->u.s);
      } else {
	symbol_insert (S_LABEL, id, func_block_scope, target, NULL);
      }
    } else if (curr_switch == NULL) {
      error (l->pos, "%s not within a switch-stmt",
	     l->code == N_CASE ? "case label" : "default label");
    } else {
      struct switch_attr *switch_attr = curr_switch->attr;
      struct type *type = &switch_attr->type;
      node_t case_expr = l->code == N_CASE ? NL_HEAD (l->ops) : NULL;
      case_t case_attr, tail = DLIST_TAIL (case_t, switch_attr->case_labels);
      int ok_p = FALSE, default_p = tail != NULL && tail->case_node->code == N_DEFAULT;
      struct expr *expr;
      
      if (case_expr == NULL) {
	if (default_p) {
	  error (l->pos, "multiple default labels in one switch");
	} else {
	  ok_p = TRUE;
	}
      } else {
	check (case_expr, target);
	expr = case_expr->attr;
	if (! expr->const_p) {
	  error (case_expr->pos, "case-expr is not a constant expression");
	} else if (! integer_type_p (expr->type)) {
	  error (case_expr->pos, "case-expr is not an integer type expression");
	} else {
	  convert_value (expr, type);
	  ok_p = TRUE;
	}
      }
      if (ok_p) {
	case_attr = reg_malloc (sizeof (struct case_attr));
	case_attr->case_node = l;
	case_attr->case_target_node = target;
	if (default_p)
	  DLIST_INSERT_BEFORE (case_t, switch_attr->case_labels, tail, case_attr);
	else 
	  DLIST_APPEND (case_t, switch_attr->case_labels, case_attr);
      }
    }
  }
}

static node_code_t get_id_linkage (int func_p, node_t id, node_t scope,
				   struct decl_spec decl_spec) {
  node_code_t linkage;
  node_t def = find_def (S_REGULAR, id, scope, NULL);
  
  if (decl_spec.typedef_p)
    return N_IGNORE; // p6: no linkage
  if (decl_spec.static_p && scope == NULL)
    return N_STATIC; // p3: internal linkage
  if (decl_spec.extern_p && def != NULL
      && (linkage = ((decl_t) def->attr)->decl_spec.linkage) != N_IGNORE)
    return linkage; // p4: previous linkage
  if (decl_spec.extern_p
      && (def == NULL || ((decl_t) def->attr)->decl_spec.linkage == N_IGNORE))
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
    node_t id = NL_HEAD (type->u.tag_type->ops);
    node_t decl_list = NL_NEXT (id);

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
      error (size_node->pos, "variable size arrays are not supported");
    } else {
      struct expr *cexpr = size_node->attr;
      
      if (! integer_type_p (cexpr->type)) {
	error (size_node->pos, "non-integer array size type");
      } else if (! cexpr->const_p) {
	error (size_node->pos, "variable size arrays are not supported");
      } else if ((signed_integer_type_p (cexpr->type) && cexpr->u.i_val <= 0)
		 || (! signed_integer_type_p (cexpr->type) && cexpr->u.u_val == 0)) {
	error (size_node->pos, "array size should be positive");
      }
    }
    check_type (el_type, level + 1, FALSE);
    if (el_type->mode == TM_FUNC) {
      error (type->pos_node->pos, "array of functions");
    } else if (el_type->incomplete_p) {
      error (type->pos_node->pos, "incomplete array element type");
      type->incomplete_p = TRUE;
    } else if (! in_params_p || level != 0) {
      if (arr_type->static_p)
	error (type->pos_node->pos, "static should be only in parameter outermost");
      else if (! type_qual_eq_p (&arr_type->ind_type_qual, &zero_type_qual))
	error (type->pos_node->pos, "type qualifiers should be only in parameter outermost array");
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
      error (ret_type->pos_node->pos, "function returning a function");
    } else if (ret_type->mode == TM_ARR) {
      error (ret_type->pos_node->pos, "function returning an array");
    }
    first_param = NL_HEAD (param_list->ops);
    if (! void_param_p (first_param)) {
      for (node_t p = first_param; p != NULL; p = NL_NEXT (p)) {
	if (p->code == N_TYPE) {
	  decl_spec = *((struct decl_spec *) p->attr);
	  check_type (decl_spec.type, level + 1, FALSE);
	} else if (p->code == N_SPEC_DECL) {
	  decl_spec = ((decl_t) p->attr)->decl_spec;
	  check_type (decl_spec.type, level + 1, FALSE);
	} else {
	  assert (p->code == N_ID);
	  break;
	}
	if (non_reg_decl_spec_p (&decl_spec)) {
	  error (p->pos, "prohibited specifier in a function parameter");
	} else if (func_def_p) {
	  if (p->code == N_TYPE)
	    error (p->pos, "parameter type without a name in function definition");
	  else if (decl_spec.type->incomplete_p)
	    error (p->pos, "incomplete parameter type in function definition");
	}
      }
    }
    break;
  }
  default:
    break; // ???
  }
}

static void check_assignment_types (struct type *left, struct type *right, node_t assign_node) {
  node_code_t code = assign_node->code;
  pos_t pos = assign_node->pos;
  const char *msg;
  
  if (arithmetic_type_p (left)) {
    if (! arithmetic_type_p (right)
	&& (left->mode != TM_BASIC || left->u.basic_type != TP_BOOL || right->mode != TM_PTR)) {
      msg = (code == N_CALL ? "incompatible argument type for arithemtic type parameter"
	     : code != N_RETURN ? "incompatible types in assignment to an arithemtic type lvalue"
	     : "incompatible return-expr type in function returning an arithemtic value");
      error (pos, "%s", msg);
    }
  } else if (left->mode == TM_STRUCT || left->mode == TM_UNION) {
    if ((right->mode != TM_STRUCT && right->mode != TM_UNION)
	|| ! compatible_types_p (left, right, TRUE)) {
      msg = (code == N_CALL ? "incompatible argument type for struct/union type parameter"
	     : code != N_RETURN ? "incompatible types in assignment to struct/union"
	     : "incompatible return-expr type in function returning a struct/union");
      error (pos, "%s", msg);
    }
  } else if (left->mode == TM_PTR) {
    if (right->mode != TM_PTR
	|| (! compatible_types_p (left->u.ptr_type, right->u.ptr_type, TRUE)
	    && ! void_ptr_p (left) && ! void_ptr_p (right))) {
      msg = (code == N_CALL ? "incompatible argument type for pointer type parameter"
	     : code == N_RETURN ? "incompatible return-expr type in function returning a pointer"
	     : "incompatible types in assignment to a pointer");
      error (pos, "%s", msg);
    } else if (right->u.ptr_type->type_qual.atomic_p) {
      msg = (code == N_CALL ? "passing a pointer of an atomic type"
	     : code == N_RETURN ? "returning a pointer of an atomic type"
	     : "assignment of pointer of an atomic type");
      error (pos, "%s", msg);
    } else if (! type_qual_subset_p (&right->u.ptr_type->type_qual,
				     &left->u.ptr_type->type_qual)) {
      msg = (code == N_CALL ? "discarding type qualifiers in passing argument"
	     : code == N_RETURN ? "return discards a type qualifier from a pointer"
	     : "assignment discards a type qualifier from a pointer");
      error (pos, "%s", msg);
    }
  }
}

static void check_initializer (struct type *type, node_t initializer,
			       int const_only_p, int top_p) {
  struct expr *cexpr;
  node_t des_list, curr_des, init, last_member, value, size_node, temp;
  mir_llong last_index, max_index, size_val;
  symbol_t sym;
  struct expr *sexpr;
  
 scalar:
  if (initializer->code != N_LIST) {
    if (type->mode == TM_ARR || type->mode == TM_STRUCT  || type->mode == TM_UNION) {
      error (initializer->pos, "invalid initializer -- {} should be used");
    } else if (! (cexpr = initializer->attr)->const_p && const_only_p) {
      error (initializer->pos,
	     "initializer of static or thread local object should be a constant expression");
    } else {
      check_assignment_types (cexpr->type, type, initializer);
    }
    return;
  }
  init = NL_HEAD (initializer->ops);
  assert (init->code == N_INIT);
  des_list = NL_HEAD (init->ops);
  assert (des_list->code == N_LIST);
  if (type->mode != TM_ARR && type->mode != TM_STRUCT  && type->mode != TM_UNION) {
    if ((temp = NL_NEXT (init)) != NULL) {
      error (temp->pos, "excess elements in scalar initializer");
      return;
    }
    if ((temp = NL_HEAD (des_list->ops)) != NULL) {
      error (temp->pos, "designator in scalar initializer");
      return;
    }
    initializer = NL_NEXT (des_list);
    if (! top_p) {
      error (init->pos, "braces around scalar initializer");
      return;
    }
    top_p = FALSE;
    goto scalar;
  }
  last_member = NULL; size_val = -1;
  if (type->mode == TM_ARR) {
    size_node = type->u.arr_type->size; sexpr = size_node->attr;
    size_val = (size_node->code != N_IGNORE && sexpr->const_p && integer_type_p (sexpr->type)
		? sexpr->u.i_val : -1);
  }
  max_index = last_index = -1; last_member = NULL;
  for (; init != NULL; init = NL_NEXT (init)) {
    assert (init->code == N_INIT);
    des_list = NL_HEAD (init->ops);
    value = NL_NEXT (des_list);
    if (0&&value->code == N_LIST && type->mode != TM_ARR
	&& type->mode != TM_STRUCT  && type->mode != TM_UNION) {
      error (init->pos, "braces around scalar initializer");
      continue;
    }
    if (value->code != N_LIST && ! ((struct expr *) value->attr)->const_p && const_only_p) {
      error (init->pos,
	     "initializer of static or thread local object should be a constant expression");
      continue;
    }
    if ((curr_des = NL_HEAD (des_list->ops)) == NULL) {
      if (type->mode == TM_ARR) {
	check_initializer (type->u.arr_type->el_type, value, const_only_p, FALSE);
	last_index++;
	if (max_index < last_index)
	  max_index = last_index;
	if (last_index >= 0 && size_val >= 0 && size_val <= last_index)
	  error (init->pos, "excess elements in array initializer");
      } else if (type->mode == TM_STRUCT || type->mode == TM_UNION) {
	int first_p = last_member == NULL;
	
	if (last_member != NULL) {
	  last_member = NL_NEXT (last_member);
	} else {
	  node_t declaration_list = NL_EL (type->u.tag_type->ops, 1);

	  assert (declaration_list != NULL && declaration_list->code == N_LIST);
	  last_member = NL_HEAD (declaration_list->ops);
	}
	while (last_member != NULL && last_member->code != N_MEMBER)
	  last_member = NL_NEXT (last_member);
	if (last_member == NULL || (! first_p && type->mode == TM_UNION)) {
	  error (init->pos, "excess elements in struct/union initializer");
	} else {
	  check_initializer (((decl_t) last_member->attr)->decl_spec.type,
			     value, const_only_p, FALSE);
	}
      }
    } else {
      for (; curr_des != NULL; curr_des = NL_NEXT (curr_des)) {
	if (curr_des->code == N_FIELD_ID) {
	  node_t id = NL_HEAD (curr_des->ops);
	  
	  if (type->mode != TM_STRUCT && type->mode != TM_UNION) {
	    error (curr_des->pos, "field name not in struct or union initializer");
	  } else if (! symbol_find (S_REGULAR, id, type->u.tag_type, &sym)) {
	    error (curr_des->pos, "unknown field %s in initializer", id->u.s);
	  } else {
	    last_member = sym.def_node;
	    assert (last_member->code == N_MEMBER);
	    check_initializer (((decl_t) last_member->attr)->decl_spec.type, value,
			       const_only_p, FALSE);
	  }
	} else if (type->mode != TM_ARR) {
	  error (curr_des->pos, "array index in initializer for non-array");
	} else if (! (cexpr = curr_des->attr)->const_p) {
	  error (curr_des->pos, "nonconstant array index in initializer");
	} else if (integer_type_p (cexpr->type)) {
	  error (curr_des->pos, "array index in initializer not of integer type");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  error (curr_des->pos, "negative array index in initializer");
	} else if (size_val >= 0
		   && (! signed_integer_type_p (cexpr->type) || size_val <= cexpr->u.i_val)) {
	  error (curr_des->pos, "array index in initializer exceeds array bounds");
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
  if (decl_spec->align < 0)
    return;
  if (decl_spec->align < type_align (decl_spec->type))
    error (decl_spec->align_node->pos,
	   "requested alignment is less than minimum alignment for the type");
}

DEF_VARR (decl_t);
static VARR (decl_t) *decls_for_allocation;

static void create_decl (node_t scope, node_t decl_node, struct decl_spec decl_spec,
			 node_t width, node_t initializer) {
  int func_def_p = decl_node->code == N_FUNC_DEF, func_p = FALSE;
  node_t id, list_head, declarator;
  struct type *type;
  decl_t decl = reg_malloc (sizeof (struct decl));
  
  assert (decl_node->code == N_MEMBER
	  || decl_node->code == N_SPEC_DECL || decl_node->code == N_FUNC_DEF);
  decl->addr_p = FALSE; decl->reg_p = FALSE; decl->offset = 0; decl->bit_offset = -1;
  decl->scope = curr_scope;
  declarator = NL_EL (decl_node->ops, 1);
  if (declarator->code == N_IGNORE) {
    assert (decl_node->code == N_MEMBER);
    type = decl_spec.type; decl_spec.linkage = N_IGNORE;
  } else {
    assert (declarator->code == N_DECL);
    type = check_declarator (declarator, func_def_p);
    type = append_type (type, decl_spec.type);
    decl_spec.type = type;
  }
  check_type (type, 0, func_def_p);
  if (declarator->code == N_DECL) {
    id = NL_HEAD (declarator->ops);
    list_head = NL_HEAD (NL_NEXT (id)->ops);
    func_p = list_head && list_head->code == N_FUNC;
    decl_spec.linkage = get_id_linkage (func_p, id, scope, decl_spec);
  }
  decl->decl_spec = decl_spec; decl_node->attr = decl;
  if (declarator->code == N_DECL) {
    def_symbol (S_REGULAR, id, scope, decl_node, decl_spec.linkage);
    if (decl_spec.linkage == N_EXTERN)
      def_symbol (S_REGULAR, id, top_scope, decl_node, N_EXTERN);
    if (func_p && decl_spec.thread_local_p) {
      error (id->pos, "thread local function declaration");
      if (id->code != N_IGNORE)
	fprintf (stderr, " of %s", id->u.s);
      fprintf (stderr, "\n");
    }
  }
  if (decl_node->code != N_MEMBER) {
    set_type_layout (type);
    check_decl_align (&decl_spec);
    if (! decl_spec.typedef_p && ! decl_spec.type->incomplete_p && decl_spec.type->mode != TM_FUNC)
      VARR_PUSH (decl_t, decls_for_allocation, decl);
  }
  if (initializer == NULL || initializer->code == N_IGNORE)
    return;
  if (type->incomplete_p && (type->mode != TM_ARR || type->u.arr_type->el_type->incomplete_p)) {
    error (initializer->pos, "initialization of incomplete type variable");
    return;
  }
  if (decl_spec.linkage != N_IGNORE && scope != NULL) {
    error (initializer->pos,
	   "initialization for block scope identifier with external or internal linkage");
    return;
  }
  check (initializer, decl_node);
  check_initializer (type, initializer, decl_spec.static_p || decl_spec.thread_local_p, TRUE);
}

static struct type *adjust_type (struct type *type) {
  struct type *res = type;
  
  if (type->mode == TM_ARR) {
    res = create_type (NULL);
    res->mode = TM_PTR; res->incomplete_p = FALSE; res->u.ptr_type = type->u.arr_type->el_type;
    res->type_qual = type->u.arr_type->ind_type_qual;
  } else if (type->mode == TM_FUNC) {
    res = create_type (NULL);
    res->mode = TM_PTR; res->incomplete_p = FALSE;
    res->pos_node = type->pos_node; res->u.ptr_type = type;
  }
  return res;
}

static void process_unop (node_t r, node_t *op, struct expr **e, struct type **t, node_t context) {
  *op = NL_HEAD (r->ops);
  check (*op, context);
  *e = (*op)->attr; *t = (*e)->type;
}

static void process_bin_ops (node_t r, node_t *op1, node_t *op2,
			     struct expr **e1, struct expr **e2,
			     struct type **t1, struct type **t2, node_t context) {
  *op1 = NL_HEAD (r->ops);
  *op2 = NL_NEXT (*op1);
  check (*op1, context);
  check (*op2, context);
  *e1 = (*op1)->attr; *e2 = (*op2)->attr; *t1 = (*e1)->type; *t2 = (*e2)->type;
}

static void process_type_bin_ops (node_t r, node_t *op1, node_t *op2,
				  struct expr **e2, struct type **t2, node_t context) {
  *op1 = NL_HEAD (r->ops);
  *op2 = NL_NEXT (*op1);
  check (*op1, context);
  check (*op2, context);
  *e2 = (*op2)->attr; *t2 = (*e2)->type;
}

static struct expr *create_expr (node_t r) {
  struct expr *e = reg_malloc (sizeof (struct expr));
  
  r->attr = e;
  e->type = create_type (NULL);
  e->type->pos_node = r; e->lvalue_node = NULL; e->const_p = FALSE;
  return e;
}

static struct expr *create_basic_type_expr (node_t r, enum basic_type bt) {
  struct expr *e = create_expr (r);
  
  e->type->mode = TM_BASIC; e->type->u.basic_type = bt;
  return e;
}

static node_t n_i1_node;

static void get_one_node (node_t *op, struct expr **e, struct type **t) {
  *op = n_i1_node; *e = (*op)->attr; *t = (*e)->type;
  init_type (*t);
  (*e)->type->mode = TM_BASIC; (*e)->type->u.basic_type = TP_INT; (*e)->u.i_val = 1;
}

static struct expr *check_assign_op (node_t r, node_t op1, node_t op2, struct expr *e1, struct expr *e2,
				     struct type *t1, struct type *t2) {
  struct expr *e, *te;
  struct type t, *tt;

  switch (r->code) {
  case N_AND: case N_OR: case N_XOR:
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN:
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! integer_type_p (t1) || ! integer_type_p (t2)) {
      error (r->pos, "bitwise operation operands should be of an integer type");
    } else {
      t = arithmetic_conversion (t1, t2);
      e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	convert_value (e1, &t);
	convert_value (e2, &t);
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
      error (r->pos, "shift operands should be of an integer type");
    } else {
      t = integer_promotion (t1);
      e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	struct type rt = integer_promotion (t2);
	
	convert_value (e1, &t);
	convert_value (e2, &rt);
	e->const_p = TRUE;
	if (signed_integer_type_p (&t)) {
	  if (signed_integer_type_p (&rt))
	    e->u.i_val
	      = r->code == N_LSH ? e1->u.i_val << e2->u.i_val : e1->u.i_val >> e2->u.i_val;
	  else
	    e->u.i_val
	      = r->code == N_LSH ? e1->u.i_val << e2->u.u_val : e1->u.i_val >> e2->u.u_val;
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
    int add_p = (r->code == N_ADD || r->code == N_ADD_ASSIGN
		 || r->code == N_INC || r->code == N_POST_INC);
    
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (arithmetic_type_p (t1) && arithmetic_type_p (t2)) {
      t = arithmetic_conversion (t1, t2);
      e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	convert_value (e1, &t);
	convert_value (e2, &t);
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
	error (r->pos, "invalid operand types of +");
      } else if (t1->u.ptr_type->incomplete_p) {
	error (r->pos, "pointer to incomplete type as an operand of +");
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
	error (r->pos, "pointer to incomplete type as an operand of -");
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
	error (r->pos, "pointer to incomplete type as an operand of -");
      } else if (t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p) {
	error (r->pos, "pointer to atomic type as an operand of -");
      } else {
	e->type->mode = TM_BASIC;
	e->type->u.basic_type = get_int_basic_type (sizeof (mir_ptrdiff_t));
	set_type_layout (e->type);
	if (e1->const_p && e2->const_p) {
	  size = type_size (t1->u.ptr_type);
	  e->const_p = TRUE;
	  e->u.i_val = (e1->u.u_val > e2->u.u_val
			? (mir_ptrdiff_t) ((e1->u.u_val - e2->u.u_val) / size)
			: -(mir_ptrdiff_t) ((e2->u.u_val - e1->u.u_val) / size));
	}
      }
    } else {
      error (r->pos, "invalid operand types of -");
    }
    break;
  }
  case N_MUL: case N_DIV: case N_MOD:
  case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN:
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_MOD && (! integer_type_p (t1) || ! integer_type_p (t2))) {
      error (r->pos, "invalid operand types of %%");
    } else if (r->code != N_MOD && (! arithmetic_type_p (t1) || ! arithmetic_type_p (t2))) {
      error (r->pos, "invalid operand types of %s", r->code == N_MUL ? "*" : "/");
    } else {
      t = arithmetic_conversion (t1, t2);
      e->type->u.basic_type = t.u.basic_type;
      if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	convert_value (e1, &t);
	convert_value (e2, &t);
	if (r->code == N_MUL) {
	  if (floating_type_p (&t))
	    e->u.d_val = e1->u.d_val * e2->u.d_val;
	  else if (signed_integer_type_p (&t))
	    e->u.i_val = e1->u.i_val * e2->u.i_val;
	  else
	    e->u.u_val = e1->u.u_val * e2->u.u_val;
	} else if ((floating_type_p (&t) && e2->u.d_val == 0.0)
		   || (signed_integer_type_p (&t) && e2->u.i_val == 0)
		   || (integer_type_p (&t) && ! signed_integer_type_p (&t) && e2->u.u_val == 0)) {
	  error (r->pos, "Division by zero");
	  if (floating_type_p (&t))
	    e->u.d_val = 0.0;
	  else if (signed_integer_type_p (&t))
	    e->u.i_val = 0;
	  else
	    e->u.u_val = 0;
	} else if (r->code != N_MOD && floating_type_p (&t)) {
	  e->u.d_val = e1->u.d_val / e2->u.d_val;
	} else if (signed_integer_type_p (&t)) {// ??? zero
	  e->u.i_val = r->code == N_DIV ? e1->u.i_val / e2->u.i_val : e1->u.i_val % e2->u.i_val;
	} else {
	  e->u.u_val = r->code == N_DIV ? e1->u.u_val / e2->u.u_val : e1->u.u_val % e2->u.u_val;
	}
      }
    }
    break;
  default:
    assert (FALSE);
  }
  return e;
}

DEF_HTAB (case_t);
static HTAB (case_t) *case_tab;

static unsigned case_hash (case_t el) {
  node_t case_expr = NL_HEAD (el->case_node->ops);
  struct expr *expr;
  
  assert (el->case_node->code == N_CASE);
  expr = case_expr->attr;
  assert (expr->const_p);
  if (signed_integer_type_p (expr->type))
    return mir_hash (&expr->u.i_val, sizeof (expr->u.i_val), 0x42);
  return mir_hash (&expr->u.u_val, sizeof (expr->u.u_val), 0x42);
}

static int case_eq (case_t el1, case_t el2) {
  node_t case_expr1 = NL_HEAD (el1->case_node->ops);
  node_t case_expr2 = NL_HEAD (el2->case_node->ops);
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

static void check (node_t r, node_t context) {
  node_t op1, op2;
  struct expr *e = NULL, *e1, *e2;
  struct type t, *t1, *t2;
  
  switch (r->code) {
  case N_IGNORE: case N_STAR: case N_FIELD_ID:
    break; /* do nothing */
  case N_LIST: {
    for (node_t n = NL_HEAD (r->ops); n != NULL; n = NL_NEXT (n))
      check (n, r);
    break;
  }
  case N_I:
  case N_L:
    e = create_basic_type_expr (r, r->code == N_I ? TP_INT : TP_LONG);
    e->const_p = TRUE; e->u.i_val = r->u.l;
    break;
  case N_LL:
    e = create_basic_type_expr (r, TP_LLONG);
    e->const_p = TRUE; e->u.i_val = r->u.ll;
    break;
  case N_U:
  case N_UL:
    e = create_basic_type_expr (r, r->code == N_U ? TP_UINT : TP_ULONG);
    e->const_p = TRUE; e->u.u_val = r->u.ul;
    break;
  case N_ULL:
    e = create_basic_type_expr (r, TP_ULLONG);
    e->const_p = TRUE; e->u.u_val = r->u.ull;
    break;
  case N_F:
    e = create_basic_type_expr (r, TP_FLOAT);
    e->const_p = TRUE; e->u.d_val = r->u.f;
    break;
  case N_D:
    e = create_basic_type_expr (r, TP_DOUBLE);
    e->const_p = TRUE; e->u.d_val = r->u.d;
    break;
  case N_LD:
    e = create_basic_type_expr (r, TP_LDOUBLE);
    e->const_p = TRUE; e->u.d_val = r->u.ld;
    break;
  case N_CH:
    e = create_basic_type_expr (r, TP_CHAR);
    e->const_p = TRUE;
    if (char_is_signed_p ())
      e->u.i_val = r->u.ch;
    else
      e->u.u_val = r->u.ch;
    break;
  case N_STR: {
    struct arr_type *arr_type;
    
    e = create_expr (r);
    e->lvalue_node = r;
    e->type->mode = TM_ARR; e->type->pos_node = r;
    e->type->u.arr_type = arr_type = reg_malloc (sizeof (struct arr_type));
    clear_type_qual (&arr_type->ind_type_qual);
    arr_type->static_p = FALSE;
    arr_type->el_type = create_type (NULL); arr_type->el_type->pos_node = r;
    arr_type->el_type->mode = TM_BASIC; arr_type->el_type->u.basic_type = TP_CHAR;
    arr_type->size = new_i_node (strlen (r->u.s) + 1, r->pos);
    check (arr_type->size, NULL);
    break;
  }
  case N_ID: {
    node_t aux_node = NULL;
    decl_t decl;
    
    op1 = find_def (S_REGULAR, r, curr_scope, &aux_node);
    e = create_expr (r);
    e->def_node = op1;
    if (op1 == NULL) {
      error (r->pos, "undeclared identifier %s", r->u.s);
    } else if (op1->code == N_IGNORE) {
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    } else if (op1->code == N_SPEC_DECL) {
      decl = op1->attr;
      if (decl->decl_spec.typedef_p) {
	error (r->pos, "typedef name %s as an operand", r->u.s);
      }
      *e->type = *decl->decl_spec.type;
      if (decl->decl_spec.linkage != N_EXTERN) { // ??? definition and external linkage
	e->lvalue_node = op1;
      }
    } else if (op1->code == N_FUNC_DEF) {
      decl = op1->attr;
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
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    e = create_expr (r);
    *e->type = *e2->type;
    break;
  case N_ANDAND: case N_OROR:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1) || ! scalar_type_p (t2)) {
      error (r->pos, "invalid operand types of %s", r->code == N_ANDAND ? "&&" : "||");
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
	error (r->pos, "incompatible pointer types in comparison");
      } else if ((t1->u.ptr_type->type_qual.atomic_p || t2->u.ptr_type->type_qual.atomic_p)
		 && ((r->code != N_EQ && r->code != N_NE)
		     || ! (null_const_p (e1, t1) || null_const_p (e2, t2)))) {
	error (r->pos, "pointer to atomic type as a comparison operand");
      } else if (e1->const_p && e2->const_p) {
	e->const_p = TRUE;
	e->u.i_val = (r->code == N_EQ ? e1->u.u_val == e2->u.u_val
		      : r->code == N_NE ? e1->u.u_val != e2->u.u_val
		      : r->code == N_LT ? e1->u.u_val < e2->u.u_val
		      : r->code == N_LE ? e1->u.u_val <= e2->u.u_val
		      : r->code == N_GT ? e1->u.u_val > e2->u.u_val
		      : e1->u.u_val >= e2->u.u_val);
      }
    } else if (arithmetic_type_p (t1) && arithmetic_type_p (t2)) {
      if (e1->const_p && e2->const_p) {
	t = arithmetic_conversion (t1, t2); convert_value (e1, &t); convert_value (e2, &t);
	e->const_p = TRUE;
	if (floating_type_p (&t))
	  e->u.i_val = (r->code == N_EQ ? e1->u.d_val == e2->u.d_val
			: r->code == N_NE ? e1->u.d_val != e2->u.d_val
			: r->code == N_LT ? e1->u.d_val < e2->u.d_val
			: r->code == N_LE ? e1->u.d_val <= e2->u.d_val
			: r->code == N_GT ? e1->u.d_val > e2->u.d_val
			: e1->u.d_val >= e2->u.d_val);
	else if (signed_integer_type_p (&t))
	  e->u.i_val = (r->code == N_EQ ? e1->u.i_val == e2->u.i_val
			: r->code == N_NE ? e1->u.i_val != e2->u.i_val
			: r->code == N_LT ? e1->u.i_val < e2->u.i_val
			: r->code == N_LE ? e1->u.i_val <= e2->u.i_val
			: r->code == N_GT ? e1->u.i_val > e2->u.i_val
			: e1->u.i_val >= e2->u.i_val);
	else
	  e->u.i_val = (r->code == N_EQ ? e1->u.u_val == e2->u.u_val
			: r->code == N_NE ? e1->u.u_val != e2->u.u_val
			: r->code == N_LT ? e1->u.u_val < e2->u.u_val
			: r->code == N_LE ? e1->u.u_val <= e2->u.u_val
			: r->code == N_GT ? e1->u.u_val > e2->u.u_val
			: e1->u.u_val >= e2->u.u_val);
      }
    } else {
      error (r->pos, "invalid types of comparison operands");
    }
    break;
  case N_BITWISE_NOT:
  case N_NOT:
    process_unop (r, &op1, &e1, &t1, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (r->code == N_BITWISE_NOT && ! integer_type_p (t1)) {
      error (r->pos, "bitwise-not operand should be of an integer type");
    } else if (r->code == N_NOT && ! scalar_type_p (t1)) {
      error (r->pos, "not operand should be of a scalar type");
    } else if (r->code == N_BITWISE_NOT) {
      t = integer_promotion (t1);
      e->type->u.basic_type = t.u.basic_type;
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
    saved_expr = *e1;
    t1 = e1->type = adjust_type (e1->type);
    get_one_node (&op2, &e2, &t2);
    e = check_assign_op (r, op1, op2, e1, e2, t1, t2);
    t2 = ((struct expr *) r->attr)->type; *e1 = saved_expr; t1 = e1->type;
    goto assign;
    break;
  }
  case N_ADD: case N_SUB:
    if (NL_NEXT (NL_HEAD (r->ops)) == NULL) { /* unary */
      process_unop (r, &op1, &e1, &t1, r);
      e = create_expr (r);
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      if (! arithmetic_type_p (t1)) {
	error (r->pos, "unary + or - operand should be of an arithmentic type");
      } else {
	if (e1->const_p)
	  e->const_p = TRUE;
	if (floating_type_p (t1)) {
	  e->type->u.basic_type = t1->u.basic_type;
	  if (e->const_p)
	    e->u.d_val = (r->code == N_ADD ? +e1->u.d_val : -e1->u.d_val);
	} else {
	  t = integer_promotion (t1);
	  e->type->u.basic_type = t.u.basic_type;
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
    e = check_assign_op (r, op1, op2, e1, e2, t1, t2);
    break;
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN: case N_LSH_ASSIGN: case N_RSH_ASSIGN:
  case N_ADD_ASSIGN: case N_SUB_ASSIGN: case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN: {
    struct expr saved_expr;
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, NULL);
    saved_expr = *e1; 
    t1 = e1->type = adjust_type (e1->type);
    t2 = e2->type = adjust_type (e2->type);
    e = check_assign_op (r, op1, op2, e1, e2, t1, t2);
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
      error (r->pos, "lvalue required as left operand of assignment");
    }
    check_assignment_types (t1, t2, r);
    *e->type = *t1;
    break;
  case N_IND:
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    e = create_expr (r);
    e->lvalue_node = r; e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR && t1->mode != TM_ARR) {
      error (r->pos, "subscripted value is neither array nor pointer");
    } else if (t1->mode == TM_PTR) {
      *e->type = *t1->u.ptr_type;
      if (t1->u.ptr_type->incomplete_p) {
	error (r->pos, "pointer to incomplete type in array subscription");
      }
    } else {
      *e->type = *t1->u.arr_type->el_type;
      e->type->type_qual = t1->u.arr_type->ind_type_qual;
      if (e->type->incomplete_p) {
	error (r->pos, "array type has incomplete element type");
      }
    }
    if (! integer_type_p (t2)) {
      error (r->pos, "array subscript is not an integer");
    }
    break;
  case N_ADDR:
    process_unop (r, &op1, &e1, &t1, r); e = create_expr (r);
    if (op1->code == N_DEREF) {
      node_t deref_op = NL_HEAD (op1->ops);
      
      *e->type = *((struct expr *) deref_op->attr)->type;
      break;
    } else if (e1->type->mode == TM_PTR && e1->type->u.ptr_type->mode == TM_FUNC) {
      *e->type = *e1->type;
      break;
    } else if (! e1->lvalue_node) {
      e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
      error (r->pos, "lvalue required as unary & operand");
      break;
    }
    if (op1->code == N_IND) {
      t2 = create_type (t1);
    } else if (op1->code == N_ID) {
      node_t decl_node = e1->lvalue_node;
      decl_t decl = decl_node->attr;

      decl->addr_p = TRUE;
      if (decl->decl_spec.register_p)
	error (r->pos, "address of register variable %s requested", op1->u.s);
      t2 = create_type (decl->decl_spec.type);
    } else if (e1->lvalue_node->code == N_MEMBER) {
      node_t declarator = NL_EL (e1->lvalue_node->ops, 1);
      node_t width = NL_NEXT (declarator);
      decl_t decl = e1->lvalue_node->attr;
      
      assert (declarator->code == N_DECL);
      if (width->code != N_IGNORE) {
	error (r->pos, "cannot take address of bit-field %s", NL_HEAD (declarator->ops)->u.s);
      }
      t2 = create_type (decl->decl_spec.type);
      if (op1->code == N_DEREF_FIELD && (e2 = NL_HEAD (op1->ops)->attr)->const_p) {
	e->const_p = TRUE;
	e->u.u_val = e2->u.u_val + decl->offset;
      }
    }
    e->type->mode = TM_PTR; e->type->u.ptr_type = t2;
    break;
  case N_DEREF:
    process_unop (r, &op1, &e1, &t1, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (t1->mode != TM_PTR) {
      error (r->pos, "invalid type argument of unary *");
    } else {
      *e->type = *t1->u.ptr_type;
    }
    break;
  case N_FIELD: case N_DEREF_FIELD: {
    symbol_t sym;
    decl_t decl;
    
    process_unop (r, &op1, &e1, &t1, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    op2 = NL_NEXT (op1);
    assert (op2->code == N_ID);
    if (r->code == N_DEREF_FIELD && t1->mode == TM_PTR) {
      t1 = t1->u.ptr_type;
    }
    if (t1->mode != TM_STRUCT && t1->mode != TM_UNION) {
      error (r->pos, "request for member %s in something not a structure or union", op2->u.s);
    } else if (! symbol_find (S_REGULAR, op2, t1->u.tag_type, &sym)) {
      error (r->pos, "%s has no member %s", t1->mode == TM_STRUCT ? "struct" : "union", op2->u.s);
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
    int v = 0, first_p;
    
    process_bin_ops (r, &op1, &op2, &e1, &e2, &t1, &t2, r);
    op3 = NL_NEXT (op2); check (op3, r);
    e3 = op3->attr;
    e3->type = adjust_type (e3->type);
    t3 = e3->type;
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT;
    if (! scalar_type_p (t1)) {
      error (r->pos, "condition should be of a scalar type");
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
      t = arithmetic_conversion (t2, t3);
      *e->type = t;
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
    } else if ((t2->mode == TM_STRUCT || t2->mode == TM_UNION)
	       && (t3->mode == TM_STRUCT || t3->mode == TM_UNION)
	       && t2->u.tag_type == t3->u.tag_type) {
      *e->type = *t2;
    } else if (t2->mode != TM_PTR && t3->mode != TM_PTR) {
      error (r->pos, "incompatible types in true and false parts of cond-expression");
      break;
    } else if (compatible_types_p (t2, t3, TRUE)) {
      t = composite_type (t2->u.ptr_type, t3->u.ptr_type);
      e->type->mode = TM_PTR; e->type->pos_node = r;
      e->type->u.ptr_type = create_type (&t);
      e->type->u.ptr_type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual,
							&t3->u.ptr_type->type_qual);
      if ((t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p)
	  && ! null_const_p (e2, t2) && ! null_const_p (e3, t3)) {
	error (r->pos, "pointer to atomic type in true or false parts of cond-expression");
      }
    } else if ((first_p = void_ptr_p (t2)) || void_ptr_p (t3)) {
      e->type->mode = TM_PTR; e->type->pos_node = r;
      e->type->u.ptr_type = create_type (NULL);
      e->type->u.ptr_type->pos_node = r;
      if (first_p && null_const_p (e2, t2)) {
	e->type->u.ptr_type = e2->type->u.ptr_type;
      } else if (null_const_p (e3, t3)) {
	e->type->u.ptr_type = e3->type->u.ptr_type;
      } else {
	if (t2->u.ptr_type->type_qual.atomic_p || t3->u.ptr_type->type_qual.atomic_p) {
	  error (r->pos, "pointer to atomic type in true or false parts of cond-expression");
	}
	e->type->u.ptr_type->mode = TM_BASIC; e->type->u.ptr_type->u.basic_type = TP_VOID;
      }
      e->type->u.ptr_type->type_qual = type_qual_union (&t2->u.ptr_type->type_qual,
							&t3->u.ptr_type->type_qual);
    } else {
      error (r->pos, "incompatible pointer types in true and false parts of cond-expression");
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

    op1 = NL_HEAD (r->ops);
    check (op1, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT; // ???
    if (r->code == N_ALIGNOF && op1->code == N_IGNORE) {
      error (r->pos, "_Alignof of non-type");
      break;
    }
    assert (op1->code == N_TYPE);
    decl_spec = op1->attr;
    if (decl_spec->type->incomplete_p) {
      error (r->pos, "%s of incomplete type requested",
	     r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else if (decl_spec->type->mode == TM_FUNC) {
      error (r->pos, "%s of function type requested",
	     r->code == N_ALIGNOF ? "_Alignof" : "sizeof");
    } else {
      e->const_p = TRUE;
      e->u.i_val = (r->code == N_SIZEOF
		    ? type_size (decl_spec->type) : type_align  (decl_spec->type));
    }
    break;
  }
  case N_EXPR_SIZEOF:
    process_unop (r, &op1, &e1, &t1, r);
    e = create_expr (r);
    e->type->mode = TM_BASIC; e->type->u.basic_type = TP_INT; // ???
    if (t1->incomplete_p) {
      error (r->pos, "sizeof of incomplete type requested");
    } else if (t1->mode == TM_FUNC) {
      error (r->pos, "sizeof of function type requested");
    } else if (e1->lvalue_node && e1->lvalue_node->code == N_MEMBER) {
      node_t declarator = NL_EL (e1->lvalue_node->ops, 1);
      node_t width = NL_NEXT (declarator);
      
      assert (declarator->code == N_DECL);
      if (width->code != N_IGNORE) {
	error (r->pos, "sizeof applied to a bit-field %s", NL_HEAD (declarator->ops)->u.s);
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
      error (r->pos, "conversion to non-scalar type requested");
    } else if (! scalar_type_p (t2)) {
      error (r->pos, "conversion of non-scalar value requested");
    } else if (t2->mode == TM_PTR && floating_type_p (decl_spec->type)) {
      error (r->pos, "conversion of a pointer to floating value requested");
    } else if (decl_spec->type->mode == TM_PTR && floating_type_p (t2)) {
      error (r->pos, "conversion of floating point value to a pointer requested");
    } else if (e2->const_p && ! void_p) {
      
#define CONV(TP, cast, mto, mfrom) case TP: e->u.mto = (cast) e2->u.mfrom; break;
#define BASIC_FROM_CONV(mfrom)									 \
      switch (decl_spec->type->u.basic_type) {							 \
	CONV (TP_BOOL, mir_bool, u_val, mfrom) CONV (TP_UCHAR, mir_uchar, u_val, mfrom);	 \
	CONV (TP_USHORT, mir_ushort, u_val, mfrom) CONV (TP_UINT, mir_uint, u_val, mfrom);	 \
	CONV (TP_ULONG, mir_ulong, u_val, mfrom) CONV (TP_ULLONG, mir_ullong, u_val, mfrom);     \
	CONV (TP_SCHAR, mir_char, i_val, mfrom);						 \
	CONV (TP_SHORT, mir_short, i_val, mfrom) CONV (TP_INT, mir_int, i_val, mfrom);		 \
	CONV (TP_LONG, mir_long, i_val, mfrom) CONV (TP_LLONG, mir_llong, i_val, mfrom);	 \
	CONV (TP_FLOAT, mir_float, d_val, mfrom) CONV (TP_DOUBLE, mir_double, d_val, mfrom);	 \
	CONV (TP_LDOUBLE, mir_ldouble, d_val, mfrom);					 	 \
      case TP_CHAR:										 \
	if (char_is_signed_p ())								 \
	  e->u.i_val = (mir_char) e2->u.mfrom;							 \
	else											 \
	  e->u.u_val = (mir_char) e2->u.mfrom;							 \
	break;											 \
      default:											 \
	assert (FALSE);										 \
      }
      
#define BASIC_TO_CONV(cast, mto)								 \
      switch (t2->u.basic_type) {								 \
      case TP_BOOL: case TP_UCHAR: case TP_USHORT: case TP_UINT: case TP_ULONG: case TP_ULLONG:	 \
	e->u.mto = (cast) e2->u.u_val; break;							 \
      case TP_CHAR:										 \
	if (! char_is_signed_p ()) {								 \
	  e->u.mto = (cast) e2->u.u_val; break;							 \
	}											 \
	/* Fall through: */									 \
      case TP_SCHAR: case TP_SHORT: case TP_INT: case TP_LONG: case TP_LLONG:			 \
	e->u.mto = (cast) e2->u.i_val; break;							 \
      case TP_FLOAT: case TP_DOUBLE: case TP_LDOUBLE:					 \
	e->u.mto = (cast) e2->u.d_val; break;							 \
      default:											 \
	assert (FALSE);										 \
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
	case TP_BOOL: case TP_UCHAR: case TP_USHORT: case TP_UINT: case TP_ULONG: case TP_ULLONG:
	  BASIC_FROM_CONV (u_val);
	  break;
	case TP_CHAR:
	  if (! char_is_signed_p ()) {
	    BASIC_FROM_CONV (u_val);
	    break;
	  }
	  /* Fall through: */
	case TP_SCHAR: case TP_SHORT: case TP_INT: case TP_LONG: case TP_LLONG:
	  BASIC_FROM_CONV (i_val);
	  break;
	case TP_FLOAT: case TP_DOUBLE: case TP_LDOUBLE:
	  BASIC_FROM_CONV (d_val);
	  break;
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
    
    op1 = NL_HEAD (r->ops);
    list = NL_NEXT (op1);
    assert (op1->code == N_TYPE && list->code == N_LIST);
    check (op1, r); decl_spec = op1->attr; t1 = decl_spec->type; check (list, r);
    if (t1->incomplete_p && (t1->mode != TM_ARR || t1->u.arr_type->size != N_IGNORE
			     || t1->u.arr_type->el_type->incomplete_p)) {
      error (r->pos, "compound literal of incomplete type");
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
    
    VARR_PUSH (node_t, call_nodes, r);
    op1 = NL_HEAD (r->ops);
    check (op1, r); e1 = op1->attr; t1 = e1->type;
    if (t1->mode != TM_PTR || (t1 = t1->u.ptr_type)->mode != TM_FUNC) {
      error (r->pos, "called object is not a function or function pointer");
      break;
    }
    func_type = t1->u.func_type;
    ret_type = func_type->ret_type;
    e = create_expr (r);
    *e->type = *ret_type;
    if ((ret_type->mode != TM_BASIC || ret_type->u.basic_type != TP_VOID)
	&& ret_type->incomplete_p) {
      error (r->pos, "function return type is incomplete");
    }
    param_list = func_type->param_list;
    param = start_param = NL_HEAD (param_list->ops);
    arg_list = NL_NEXT (op1);
    if (void_param_p (start_param)) { /* f(void) */
      if ((arg = NL_HEAD (arg_list->ops)) != NULL)
	error (arg->pos, "too many arguments");
      break;
    }
    for (node_t arg = NL_HEAD (arg_list->ops); arg != NULL; arg = NL_NEXT (arg)) {
      check (arg, r);
      e2 = arg->attr;
      if (start_param == NULL || start_param->code == N_ID)
	continue;  /* no params or ident list */
      if (param == NULL) {
	if (! func_type->dots_p)
	  error (arg->pos, "too many arguments");
	start_param = NULL; /* ignore the rest args */
	continue;
      }
      assert (param->code == N_SPEC_DECL || param->code == N_TYPE);
      decl_spec = param->code == N_TYPE ? param->attr : &((decl_t) param->attr)->decl_spec;
      check_assignment_types (decl_spec->type, e2->type, r);
      param = NL_NEXT (param);
    }
    if (param != NULL) {
      error (r->pos, "too few arguments");
    }
    break;
  }
  case N_GENERIC: {
    node_t list, ga, ga2, type_name, type_name2, expr;
    node_t default_case = NULL, ga_case = NULL;
    struct decl_spec *decl_spec;
    
    op1 = NL_HEAD (r->ops);
    check (op1, r);
    e1 = op1->attr; t = *e1->type;
    if (integer_type_p (&t))
      t = integer_promotion (&t);
    list = NL_NEXT (op1);
    for (ga = NL_HEAD (list->ops); ga != NULL; ga = NL_NEXT (ga)) {
      assert (ga->code == N_GENERIC_ASSOC);
      type_name = NL_HEAD (ga->ops);
      expr = NL_NEXT (type_name);
      check (type_name, r);
      check (expr, r);
      if (type_name->code == N_IGNORE) {
	if (default_case)
	  error (ga->pos, "duplicate default case in _Generic");
	default_case = ga;
	continue;
      }
      assert (type_name->code == N_TYPE);
      decl_spec = type_name->attr;
      if (decl_spec->type->incomplete_p) {
	error (ga->pos, "_Generic case has incomplete type");
      } else if (compatible_types_p (&t, decl_spec->type, TRUE)) {
	if (ga_case)
	  error (ga_case->pos,
		 "_Generic expr type is compatible with more than one generic association type");
	ga_case = ga;
      } else {
	for (ga2 = NL_HEAD (list->ops); ga2 != ga; ga2 = NL_NEXT (ga2)) {
	  type_name2 = NL_HEAD (ga2->ops);
	  if (type_name2->code != N_IGNORE
	      && ! (t2 = ((struct decl_spec *) type_name2->attr)->type)->incomplete_p
	      && compatible_types_p (t2, decl_spec->type, TRUE)) {
	    error (ga->pos, "two or more compatible generic association types");
	    break;
	  }
	}
      }
    }
    e = create_expr (r);
    if (default_case == NULL && ga_case == NULL) {
      error (r->pos, "expression type is not compatible with generic association");
    } else { /* make compatible association a list head  */
      if (ga_case == NULL)
	ga_case = default_case;
      NL_REMOVE (list->ops, ga_case);
      NL_PREPEND (list->ops, ga_case);
      t2 = e->type;
      *e = *(struct expr *) NL_EL (ga_case->ops, 1)->attr;
      *t2 = *e->type; e->type = t2;
	
    }
    break;
  }
  case N_SPEC_DECL: {
    node_t specs = NL_HEAD (r->ops);
    node_t declarator = NL_NEXT (specs);
    node_t initializer = NL_NEXT (declarator);
    node_t unshared_specs = specs->code != N_SHARE ? specs : NL_HEAD (specs->ops);
    struct decl_spec decl_spec = check_decl_spec (unshared_specs, r);
    
    if (declarator->code != N_IGNORE) {
      create_decl (curr_scope, r, decl_spec, NULL, initializer);
    } else if (decl_spec.type->mode == TM_STRUCT || decl_spec.type->mode == TM_UNION) {
      if (NL_HEAD (decl_spec.type->u.tag_type->ops)->code != N_ID)
	error (r->pos, "unnamed struct/union with no instances");
    } else if (decl_spec.type->mode != TM_ENUM) {
      error (r->pos, "useless declaration");
    }
    /* We have at least one enum constant according to the syntax. */
    break;
  }
  case N_ST_ASSERT: {
    int ok_p;
    
    op1 = NL_HEAD (r->ops);
    check (op1, r);
    e1 = op1->attr; t1 = e1->type;
    if (! e1->const_p) {
      error (r->pos, "expression in static assertion is not constant");
    } else if (! integer_type_p (t1)) {
      error (r->pos, "expression in static assertion is not an integer");
    } else {
      if (signed_integer_type_p (t1))
	ok_p = e1->u.i_val != 0;
      else
	ok_p = e1->u.u_val != 0;
      if (! ok_p) {
	assert (NL_NEXT (op1) != NULL && NL_NEXT (op1)->code == N_STR);
	error (r->pos, "static assertion failed: \"%s\"", NL_NEXT (op1)->u.s);
      }
    }
    break;
  }
  case N_MEMBER: {
    struct type *type;
    node_t specs = NL_HEAD (r->ops);
    node_t declarator = NL_NEXT (specs);
    node_t const_expr = NL_NEXT (declarator);
    node_t unshared_specs = specs->code != N_SHARE ? specs : NL_HEAD (specs->ops);
    struct decl_spec decl_spec = check_decl_spec (unshared_specs, r);
    
    create_decl (curr_scope, r, decl_spec, const_expr, NULL);
    type = ((decl_t) r->attr)->decl_spec.type;
    if (const_expr->code != N_IGNORE) {
      struct expr *cexpr;
      
      check (const_expr, r);
      cexpr = const_expr->attr;
      if (cexpr != NULL) {
	if (type->type_qual.atomic_p)
	  error (const_expr->pos, "bit field with _Atomic");
	if (! cexpr->const_p) {
	  error (const_expr->pos, "bit field is not a constant expr");
	} else if (! integer_type_p (type)
		   && (type->mode != TM_BASIC || type->u.basic_type != TP_BOOL)) {
	  error (const_expr->pos,
		 "bit field type should be _Bool, a signed integer, or an unsigned integer type");
	} else if (! integer_type_p (cexpr->type)
		   && (cexpr->type->mode != TM_BASIC || cexpr->type->u.basic_type != TP_BOOL)) {
	  error (const_expr->pos, "bit field width is not of an integer type");
	} else if (signed_integer_type_p (cexpr->type) && cexpr->u.i_val < 0) {
	  error (const_expr->pos, "bit field width is negative");
	} else if (cexpr->u.i_val == 0 && declarator->code == N_DECL) {
	  error (const_expr->pos, "zero bit field width for %s", NL_HEAD (declarator->ops)->u.s);
	} else if ((! signed_integer_type_p (cexpr->type)
		    && cexpr->u.u_val > int_bit_size (cexpr->type))
		   || (signed_integer_type_p (cexpr->type)
		       && cexpr->u.i_val > int_bit_size (cexpr->type))) {
	  error (const_expr->pos, "bit field width exceeds its type");
	}
      }
    }
    if (declarator->code == N_IGNORE) {
      if (const_expr->code == N_IGNORE)
	error (r->pos, "no declarator in struct or union declaration");
    } else {
      node_t id = NL_HEAD (declarator->ops);

      if (type->mode == TM_FUNC) {
	error (id->pos, "field %s is declared as a function", id->u.s);
      } else if (type->incomplete_p) {
	/* el_type is checked on completness in N_ARR */
	if (type->mode != TM_ARR || type->u.arr_type->size->code != N_IGNORE)
	  error (id->pos, "field %s has incomplete type", id->u.s);
      }
    }
    break;
  }
  case N_INIT: {
    node_t des_list = NL_HEAD (r->ops), initializer = NL_NEXT (des_list);

    check (des_list, r); check (initializer, r);
    break;
  }
  case N_FUNC_DEF: {
    node_t specs = NL_HEAD (r->ops);
    node_t declarator = NL_NEXT (specs);
    node_t declarations = NL_NEXT (declarator);
    node_t block = NL_NEXT (declarations);
    struct decl_spec decl_spec = check_decl_spec (specs, r);
    node_t p, next_p, param_list, param_id, param_declarator, func;
    symbol_t sym;
    
    curr_func_scope_num = 0;
    create_node_scope (block);
    func_block_scope = curr_scope;
    curr_func_def = r; curr_switch = curr_loop = curr_loop_switch = NULL;
    create_decl (top_scope, r, decl_spec, NULL, NULL);
    curr_scope = func_block_scope;
    check (declarations, r);
    /* Process parameter identifier list:  */
    assert (declarator->code == N_DECL);
    func = NL_HEAD (NL_EL (declarator->ops, 1)->ops);
    assert (func != NULL && func->code == N_FUNC);
    param_list = NL_HEAD (func->ops);
    for (p = NL_HEAD (param_list->ops); p != NULL; p = next_p) {
      next_p = NL_NEXT (p);
      if (p->code != N_ID)
	break;
      NL_REMOVE (param_list->ops, p);
      if (! symbol_find (S_REGULAR, p, curr_scope, &sym)) {
	error (p->pos, "parameter %s has no type", p->u.s);
      } else {
	node_t decl = sym.def_node;
	struct decl_spec decl_spec;
	
	assert (decl->code == N_SPEC_DECL);
	NL_REMOVE (declarations->ops, decl);
	NL_APPEND (param_list->ops, decl);
	param_declarator = NL_EL (decl->ops, 1);
	assert (param_declarator->code == N_DECL);
	param_id = NL_HEAD (param_declarator->ops);
	if (NL_NEXT (param_declarator)->code != N_IGNORE) {
	  error (p->pos, "initialized parameter %s", param_id->u.s);
	}
	decl_spec = ((decl_t) decl->attr)->decl_spec;
	if (decl_spec.typedef_p || decl_spec.extern_p || decl_spec.static_p
	    || decl_spec.auto_p || decl_spec.thread_local_p) {
	  error (param_id->pos, "storage specifier in a function parameter %s", param_id->u.s);
	}
      }
    }
    /* Process the rest declarations: */
    for (p = NL_HEAD (declarations->ops); p != NULL; p = NL_NEXT (p)) {
      if (p->code == N_ST_ASSERT)
	continue;
      assert (p->code == N_SPEC_DECL);
      param_declarator = NL_EL (p->ops, 1);
      assert (param_declarator->code == N_DECL);
      param_id = NL_HEAD (param_declarator->ops);
      assert (param_id->code == N_ID);
      error (param_id->pos, "declaration for parameter %s but no such parameter", param_id->u.s);
    }
    check (block, r);
    /* Process all gotos: */
    for (size_t i = 0; i < VARR_LENGTH (node_t, gotos); i++) {
      symbol_t sym;
      node_t n = VARR_GET (node_t, gotos, i);
      node_t id = NL_NEXT (NL_HEAD (n->ops));

      if (! symbol_find (S_LABEL, id, func_block_scope, &sym)) {
	error (id->pos, "undefined label %s", id->u.s);
      } else {
	n->attr = sym.def_node;
      }
    }
    VARR_TRUNC (node_t, gotos, 0);
    assert (curr_scope == top_scope); /* set up in the block */
    func_block_scope = top_scope;
    break;
  }
  case N_TYPE: {
    struct type *type;
    node_t specs = NL_HEAD (r->ops);
    node_t abstract_declarator = NL_NEXT (specs);
    struct decl_spec decl_spec = check_decl_spec (specs, r); /* only spec_qual_list here */
    
    type = check_declarator (abstract_declarator, FALSE);
    assert (NL_HEAD (abstract_declarator->ops)->code == N_IGNORE);
    decl_spec.type = append_type (type, decl_spec.type);
    r->attr = reg_malloc (sizeof (struct decl_spec));
    *((struct decl_spec *) r->attr) = decl_spec;
    check_type (((struct decl_spec *) r->attr)->type, 0, FALSE);
    set_type_layout (((struct decl_spec *) r->attr)->type);
    check_decl_align (r->attr);
    break;
  }
  case N_BLOCK:
    if (curr_scope != r)
      create_node_scope (r); /* it happens if it is the top func block */
    check (NL_HEAD (r->ops), r);
    finish_scope ();
    break;
  case N_MODULE:
    create_node_scope (r);
    top_scope = curr_scope;
    check (NL_HEAD (r->ops), r);
    finish_scope ();
    break;
  case N_IF: {
    node_t labels = NL_HEAD (r->ops);
    node_t expr = NL_NEXT (labels);
    node_t if_stmt = NL_NEXT (expr);
    node_t else_stmt = NL_NEXT (if_stmt);
 
    check_labels (labels, r);
    check (expr, r);
    e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      error (expr->pos, "if-expr should be of a scalar type");
    }
    check (if_stmt, r);
    check (else_stmt, r);
    break;
  }
  case N_SWITCH: {
    node_t saved_switch = curr_switch;
    node_t saved_loop_switch = curr_loop_switch;
    node_t labels = NL_HEAD (r->ops);
    node_t expr = NL_NEXT (labels);
    node_t stmt = NL_NEXT (expr);
    struct type t, *type;
    struct switch_attr *switch_attr;
    case_t el;
    
    check_labels (labels, r);
    check (expr, r);
    type = ((struct expr *) expr->attr)->type;
    if (! integer_type_p (type)) {
      init_type (&t);
      t.mode = TM_BASIC; t.u.basic_type = TP_INT;
      error (expr->pos, "switch-expr is of non-integer type");
    } else {
      t = integer_promotion (type);
    }
    curr_switch = curr_loop_switch = r;
    switch_attr = curr_switch->attr = reg_malloc (sizeof (struct switch_attr));
    switch_attr->type = t;
    DLIST_INIT (case_t, ((struct switch_attr *) curr_switch->attr)->case_labels);
    check (stmt, r);
    for (case_t c = DLIST_HEAD (case_t, switch_attr->case_labels);
	 c != NULL;
	 c = DLIST_NEXT (case_t, c)) {
      if (c->case_node->code == N_DEFAULT)
	continue;
      if (HTAB_DO (case_t, case_tab, c, HTAB_FIND, el)) {
	error (c->case_node->pos, "duplicate case value");
	continue;
      }
      HTAB_DO (case_t, case_tab, c, HTAB_INSERT, el);
    }
    HTAB_CLEAR (case_t, case_tab, NULL);
    curr_switch = saved_switch; curr_loop_switch = saved_loop_switch;
    break;
  }
  case N_DO:
  case N_WHILE: {
    node_t labels = NL_HEAD (r->ops);
    node_t expr = NL_NEXT (labels);
    node_t stmt = NL_NEXT (expr);
    node_t saved_loop = curr_loop;
    node_t saved_loop_switch = curr_loop_switch;

    check_labels (labels, r);
    check (expr, r);
    e1 = expr->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      error (expr->pos, "while-expr should be of a scalar type");
    }
    curr_loop = curr_loop_switch = r;
    check (stmt, r);
    curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
    break;
  }
  case N_FOR: {
    node_t labels = NL_HEAD (r->ops);
    node_t init = NL_NEXT (labels);
    node_t cond = NL_NEXT (init);
    node_t iter = NL_NEXT (cond);
    node_t stmt = NL_NEXT (iter);
    decl_t decl;
    node_t saved_loop = curr_loop;
    node_t saved_loop_switch = curr_loop_switch;
    
    check_labels (labels, r);
    create_node_scope (r);
    curr_loop = curr_loop_switch = r;
    check (init, r);
    if (init->code == N_LIST) {
      for (node_t spec_decl = NL_HEAD (init->ops);
	   spec_decl != NULL;
	   spec_decl = NL_NEXT (spec_decl)) {
	assert (spec_decl->code == N_SPEC_DECL);
	decl = spec_decl->attr;
	if (decl->decl_spec.typedef_p || decl->decl_spec.extern_p
	    || decl->decl_spec.static_p || decl->decl_spec.thread_local_p) {
	  error (spec_decl->pos, "wrong storage specifier of for-loop initial declaration");
	  break;
	}
      }
    }
    check (cond, r);
    e1 = cond->attr; t1 = e1->type;
    if (! scalar_type_p (t1)) {
      error (cond->pos, "for-condition should be of a scalar type");
    }
    check (iter, r);
    check (stmt, r);
    finish_scope ();
    curr_loop_switch = saved_loop_switch; curr_loop = saved_loop;
    break;
  }
  case N_GOTO: {
    node_t labels = NL_HEAD (r->ops);
    
    check_labels (labels, r);
    VARR_PUSH (node_t, gotos, r);
    break;
  }
  case N_CONTINUE:
  case N_BREAK: {
    node_t labels = NL_HEAD (r->ops);
    
    if (r->code == N_BREAK && curr_loop_switch == NULL) {
      error (r->pos, "break statement not within loop or switch");
    } else if (r->code == N_CONTINUE && curr_loop == NULL) {
      error (r->pos, "continue statement not within a loop");
    }
    check_labels (labels, r);
    break;
  }
  case N_RETURN: {
    node_t labels = NL_HEAD (r->ops);
    node_t expr = NL_NEXT (labels);
    decl_t decl = curr_func_def->attr;
    struct type *ret_type, *type = decl->decl_spec.type;

    assert (type->mode == TM_FUNC);
    check_labels (labels, r);
    check (expr, r);
    ret_type = type->u.func_type->ret_type;
    if (expr->code != N_IGNORE
	&& ret_type->mode == TM_BASIC && ret_type->u.basic_type == TP_VOID) {
      error (r->pos, "return with a value in function returning void");
    } else if (expr->code == N_IGNORE
	       && (ret_type->mode != TM_BASIC || ret_type->u.basic_type != TP_VOID)) {
      error (r->pos, "return with no value in function returning non-void");
    } else if (expr->code != N_IGNORE) {
      check_assignment_types (ret_type, ((struct expr *) expr->attr)->type, r);
    }
    break;
  }
  case N_EXPR: {
    node_t labels = NL_HEAD (r->ops);
    node_t expr = NL_NEXT (labels);
    
    check_labels (labels, r); check (expr, r);
    break;
  }
  default:
    abort ();
  }
  if (e != NULL) {
    if (context && context->code != N_ALIGNOF
	&& context->code != N_SIZEOF && context->code != N_ADDR)
      e->type = adjust_type (e->type);
    set_type_layout (e->type);
  }
}

static void context (node_t r) {
  VARR_TRUNC (decl_t, decls_for_allocation, 0);
  VARR_TRUNC (node_t, call_nodes, 0);
  check (r, NULL);
  /* Process decls in the original order: */
  for (int i = 0; i < VARR_LENGTH (decl_t, decls_for_allocation); i++) {
    decl_t decl = VARR_GET (decl_t, decls_for_allocation, i);
    struct node_scope *ns = (struct node_scope *) decl->scope->attr;
    struct type *type = decl->decl_spec.type;
    
    if (scalar_type_p (type) && ! decl->addr_p) {
      decl->reg_p = TRUE;
      continue;
    }
    ns->offset = (ns->offset + type->align - 1) / type->align * type->align;
    decl->offset = ns->offset;
    ns->offset += type_size (type);
    if (ns->size < ns->offset)
      ns->size = ns->offset;
  }
}

static void context_init (void) {
  n_i1_node = new_i_node (1, no_pos);
  check (n_i1_node, NULL);
  func_block_scope = curr_scope = NULL;
  VARR_CREATE (node_t, gotos, 0);
  symbol_init ();
  in_params_p = FALSE;
  HTAB_CREATE (case_t, case_tab, 100, case_hash, case_eq);
  VARR_CREATE (decl_t, decls_for_allocation, 1024);
}

static void context_finish (void) {
  VARR_DESTROY (node_t, gotos);
  symbol_finish ();
  HTAB_DESTROY (case_t, case_tab);
  VARR_DESTROY (decl_t, decls_for_allocation);
}

/* ------------------------ Context Checker Finish ---------------------------- */



/* -------------------------- MIR generator start ----------------------------- */

#define FP_NAME "fp"

/* New attribute for non-empty label LIST is a MIR label.  */

/* MIR var naming:
   {I|U|i|u|f|d}_<integer> -- temporary of I64, U64, I32, U32, F, D type
   {I|U|i|u|f|d}<scope_number>_<name> -- variable with of original <name> of the corresponding
                                         type in scope with <scope_number>
*/

struct op {
  decl_t decl;
  MIR_op_t mir_op;
};

typedef struct op op_t;

static op_t new_op (decl_t decl, MIR_op_t mir_op) {
  op_t res;

  res.decl = decl; res.mir_op = mir_op;
  return res;
}

static op_t zero_op, one_op;

static MIR_item_t curr_func;

struct reg_var {
  const char *name;
  MIR_reg_t reg;
};

typedef struct reg_var reg_var_t;

DEF_HTAB (reg_var_t);
static HTAB (reg_var_t) *reg_var_tab;

static htab_hash_t reg_var_hash (reg_var_t r) { return mir_hash (r.name, strlen (r.name), 0x42); }
static int reg_var_eq (reg_var_t r1, reg_var_t r2) { return strcmp (r1.name, r2.name) == 0; }

static int reg_free_mark;

static void init_reg_vars (void) {
  reg_free_mark = 0;
  HTAB_CREATE (reg_var_t, reg_var_tab, 128, reg_var_hash, reg_var_eq);
}

static void finish_curr_func_reg_vars (void) {
  reg_free_mark = 0;
  HTAB_CLEAR (reg_var_t, reg_var_tab, NULL);
}

static void finish_reg_vars (void) {
  HTAB_DESTROY (reg_var_t, reg_var_tab);
}

static reg_var_t get_reg_var (MIR_type_t t, const char *reg_name) {
  reg_var_t reg_var, el;
  char *str;
  MIR_reg_t reg;
  
  reg_var.name = reg_name;
  if (HTAB_DO (reg_var_t, reg_var_tab, reg_var, HTAB_FIND, el))
    return el;
  t = t == MIR_T_I32 || t == MIR_T_U32 ? MIR_T_I64 : t;
  reg = MIR_new_func_reg (curr_func->u.func, t, reg_name);
  str = reg_malloc ((strlen (reg_name) + 1) * sizeof (char));
  strcpy (str, reg_name);
  reg_var.name = str;
  reg_var.reg = reg;
  HTAB_DO (reg_var_t, reg_var_tab, reg_var, HTAB_INSERT, el);
  return reg_var;
}

static int temp_reg_p (MIR_op_t op) {
  return op.mode == MIR_OP_REG && MIR_reg_name (op.u.reg, curr_func->u.func)[1] == '_';
}

static MIR_type_t reg_type (MIR_reg_t reg) {
  const char *n = MIR_reg_name (reg, curr_func->u.func);
  MIR_type_t res = (n[0] == 'I' ? MIR_T_I64 : n[0] == 'U' ? MIR_T_U64 : n[0] == 'i' ? MIR_T_I32
		    : n[0] == 'u' ? MIR_T_U32 : n[0] == 'f' ? MIR_T_F : n[0] == 'd' ? MIR_T_D
		    : MIR_T_BOUND);
  
  assert (res != MIR_T_BOUND);
  return res;
}

static op_t get_new_temp (MIR_type_t t) {
  static char reg_name[50];
  MIR_reg_t reg;

  assert (t == MIR_T_I64 || t == MIR_T_U64 || t == MIR_T_I32 || t == MIR_T_U32 || t == MIR_T_F || t == MIR_T_D);
  sprintf (reg_name, t == MIR_T_I64 ? "I_%u" : t == MIR_T_U64 ? "U_%u" : t == MIR_T_I32 ? "i_%u"
	   : t == MIR_T_U32 ? "u_%u" : t == MIR_T_F ? "f_%u" : "d_%u", reg_free_mark++);
  reg = get_reg_var (t, reg_name).reg;
  return new_op (NULL, MIR_new_reg_op (reg));
}

static MIR_type_t get_int_mir_type (size_t size) {
  return size == 1 ? MIR_T_I8 : size == 2 ? MIR_T_I16 : size == 4 ? MIR_T_I32 : MIR_T_I64;
}

static int get_int_mir_type_size (MIR_type_t t) {
  return (t == MIR_T_I8 || t == MIR_T_U8 ? 1 : t == MIR_T_I16 || t == MIR_T_U16 ? 2
	  : t == MIR_T_I32 || t == MIR_T_U32 ? 4 : 8);
}

static MIR_type_t get_mir_type (struct type *type) {
  size_t size = type->raw_size;
  int int_p = ! floating_type_p (type), signed_p = signed_integer_type_p (type);
  
  if (! scalar_type_p (type))
    return MIR_T_BLOCK;
  assert (type->mode == TM_BASIC || type->mode == TM_PTR || type->mode == TM_ENUM);
  if (! int_p) {
    assert (size == 4 || size == 8);
    return size == 4 ? MIR_T_F : MIR_T_D;
  }
  assert (size <= 2 || size == 4 || size == 8);
  if (signed_p)
    return get_int_mir_type (size);
  return size == 1 ? MIR_T_U8 : size == 2 ? MIR_T_U16 : size == 4 ? MIR_T_U32 : MIR_T_U64;
}

static MIR_type_t promote_mir_int_type (MIR_type_t t) {
  return t == MIR_T_I8 || MIR_T_I16 ? MIR_T_I32 : t == MIR_T_U8 || MIR_T_U16 ? MIR_T_U32 : t;
}

static MIR_type_t get_op_type (op_t op) {
  switch (op.mir_op.mode) {
  case MIR_OP_MEM: return op.mir_op.u.mem.type;
  case MIR_OP_REG: return reg_type (op.mir_op.u.reg);
  case MIR_OP_INT: return MIR_T_I64;
  case MIR_OP_UINT: return MIR_T_U64;
  case MIR_OP_FLOAT: return MIR_T_F;
  case MIR_OP_DOUBLE: return MIR_T_D;
  default: assert (FALSE);
  }
}

static op_t gen (node_t r, MIR_label_t true_label, MIR_label_t false_label, int val_p);

static int push_const_val (node_t r, op_t *res) {
  struct expr *e = (struct expr *) r->attr;
  
  if (! e->const_p)
    return FALSE;
  if (floating_type_p (e->type)) {
    /* MIR support only IEEE float and double */
    *res = new_op (NULL, (get_mir_type (e->type) == MIR_T_F
			  ? MIR_new_float_op (e->u.d_val) : MIR_new_double_op (e->u.d_val)));
  } else {
    assert (integer_type_p (e->type) || e->type->mode == TM_PTR);
    *res = new_op (NULL, (signed_integer_type_p (e->type)
			  ? MIR_new_int_op (e->u.i_val) : MIR_new_uint_op (e->u.u_val)));
  }
  return TRUE;
}

/* Change t1 = expr; v = t1 to v = expr */
static void emit_insn (MIR_insn_t insn) {
  MIR_insn_t tail;
  int out_p;
  
  if ((insn->code == MIR_MOV || insn->code == MIR_FMOV || insn->code == MIR_DMOV)
      && (tail = DLIST_TAIL (MIR_insn_t, curr_func->u.func->insns)) != NULL
      && MIR_insn_nops (tail) > 0 && temp_reg_p (insn->ops[1]) && temp_reg_p (tail->ops[0])
      && insn->ops[1].u.reg == tail->ops[0].u.reg) {
    MIR_insn_op_mode (tail, 0, &out_p);
    if (out_p) {
      tail->ops[0] = insn->ops[0];
      return;
    }
  }
  MIR_append_insn (curr_func, insn);
}

static void emit1 (MIR_insn_code_t code, MIR_op_t op1) {emit_insn (MIR_new_insn (code, op1)); }
static void emit2 (MIR_insn_code_t code, MIR_op_t op1, MIR_op_t op2) {
  emit_insn (MIR_new_insn (code, op1, op2));
}
static void emit3 (MIR_insn_code_t code, MIR_op_t op1, MIR_op_t op2, MIR_op_t op3) {
  emit_insn (MIR_new_insn (code, op1, op2, op3));
}

static op_t promote (op_t op, MIR_type_t t) {
  op_t res;
  MIR_type_t op_type;
  MIR_insn_code_t insn_code = MIR_INSN_BOUND, insn_code2 = MIR_INSN_BOUND;
  
  assert (t == MIR_T_I64 || t == MIR_T_U64 || t == MIR_T_I32 || t == MIR_T_U32 || t == MIR_T_F || t == MIR_T_D);
  switch (op.mir_op.mode) {
  case MIR_OP_MEM:
    op_type = op.mir_op.u.mem.type;
    goto all_types;
  case MIR_OP_REG:
    op_type = reg_type (op.mir_op.u.reg);
  all_types:
    if (op_type == MIR_T_F) goto float_val;
    if (op_type == MIR_T_D) goto double_val;
    if (t == MIR_T_I64) {
      insn_code = (op_type == MIR_T_I32 ? MIR_EXT32 : op_type == MIR_T_U32 ? MIR_UEXT32
		   : op_type == MIR_T_F ? MIR_F2I : op_type == MIR_T_D ? MIR_D2I : MIR_INSN_BOUND);
    } else if (t == MIR_T_U64) {
      insn_code = (op_type == MIR_T_I32 ? MIR_EXT32 : op_type == MIR_T_U32 ? MIR_UEXT32
		   : op_type == MIR_T_F ? MIR_F2I : op_type == MIR_T_D ? MIR_D2I : MIR_INSN_BOUND);
    } else if (t == MIR_T_I32) {
      insn_code = op_type == MIR_T_F ? MIR_F2I : op_type == MIR_T_D ? MIR_D2I : MIR_INSN_BOUND;
    } else if (t == MIR_T_U32) {
      insn_code = op_type == MIR_T_F ? MIR_F2I : op_type == MIR_T_D ? MIR_D2I : MIR_INSN_BOUND;
    } else if (t == MIR_T_F) {
      insn_code = op_type == MIR_T_I32 ? MIR_EXT32 : op_type == MIR_T_U32 ? MIR_UEXT32 : MIR_INSN_BOUND;
      insn_code2 = (op_type == MIR_T_I64 || op_type == MIR_T_U64 ? MIR_I2F
		    : op_type == MIR_T_I32 || op_type == MIR_T_U32 ? MIR_I2F : MIR_INSN_BOUND);
    } else if (t == MIR_T_D) {
      insn_code = op_type == MIR_T_I32 ? MIR_EXT32 : op_type == MIR_T_U32 ? MIR_UEXT32 : MIR_INSN_BOUND;
      insn_code2 = (op_type == MIR_T_I64 || op_type == MIR_T_U64 ? MIR_I2D
		    : op_type == MIR_T_I32 || op_type == MIR_T_U32 ? MIR_I2D : MIR_INSN_BOUND);
    }
    break;
  case MIR_OP_INT: case MIR_OP_UINT:
    insn_code = t == MIR_T_F ? MIR_I2F : t == MIR_T_D ? MIR_I2D : MIR_INSN_BOUND;
    break;
  case MIR_OP_FLOAT:
  float_val:
    insn_code = (t == MIR_T_I64 || t == MIR_T_U64 ? MIR_F2I : t == MIR_T_I32 || t == MIR_T_U32 ? MIR_F2I
		 : t == MIR_T_D ? MIR_F2D : MIR_INSN_BOUND);
    break;
  case MIR_OP_DOUBLE:
  double_val:
    insn_code = (t == MIR_T_I64 || t == MIR_T_U64  ? MIR_D2I : t == MIR_T_I32 || t == MIR_T_U32 ? MIR_D2I
		 : t == MIR_T_F ? MIR_D2F : MIR_INSN_BOUND);
    break;
  default:
    break;
  }
  if (insn_code == MIR_INSN_BOUND && insn_code2 == MIR_INSN_BOUND)
    return op;
  res = get_new_temp (t);
  if (insn_code == MIR_INSN_BOUND) {
    emit2 (insn_code2, res.mir_op, op.mir_op);
  } else if (insn_code2 == MIR_INSN_BOUND) {
    emit2 (insn_code, res.mir_op, op.mir_op);
  } else {
    emit2 (insn_code, res.mir_op, op.mir_op);
    emit2 (insn_code2, res.mir_op, res.mir_op);
  }
  return res;
}

static op_t force_val (op_t op) {
  op_t temp_op;
  int sh, size;
  
  if (op.decl == NULL || op.decl->bit_offset < 0)
    return op;
  assert (op.mir_op.mode == MIR_OP_MEM);
  temp_op = get_new_temp (MIR_T_I64);
  emit2 (MIR_MOV, temp_op.mir_op, op.mir_op);
  size = get_int_mir_type_size (op.mir_op.u.mem.type);
  sh = op.decl->bit_offset + (64 - size * 8);
  if (sh != 0)
    emit3 (MIR_LSH, temp_op.mir_op, temp_op.mir_op, MIR_new_int_op (sh));
  emit3 (signed_integer_type_p (op.decl->decl_spec.type) ? MIR_RSH : MIR_URSH,
	 temp_op.mir_op, temp_op.mir_op, MIR_new_int_op (64 - op.decl->width));
  return temp_op;
}

static int gen_unary_op (node_t r, op_t *op, op_t *res) {
  MIR_type_t t;
  
  if (push_const_val (r, res))
    return FALSE;
  *op = gen (NL_HEAD (r->ops), NULL, NULL, TRUE);
  t = get_mir_type (((struct expr *) r->attr)->type);
  *op = promote (*op, t);
  *res = get_new_temp (t);
  return TRUE;
}

static int gen_bin_op (node_t r, op_t *op1, op_t *op2, op_t *res, op_t *var) {
  MIR_type_t t;
  struct type *type = ((struct expr *) r->attr)->type;
  
  if (push_const_val (r, res))
    return FALSE;
  t = get_mir_type (type);
  *op1 = gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
  *op2 = gen (NL_EL (r->ops, 1), NULL, NULL, TRUE);
  *op2 = promote (*op2, t);
  if (var != NULL)
    *var = *op1;
  *op1 = force_val (*op1);
  *res = get_new_temp (t);
  return TRUE;
}

static MIR_insn_code_t get_mir_insn_code (node_t r) {
  struct expr *e = (struct expr *) r->attr;
  struct type *type = e->type;
  MIR_type_t t = get_mir_type (type);
  
  switch (r->code) {
  case N_INC: case N_POST_INC: case N_ADD: case N_ADD_ASSIGN:
    return (t == MIR_T_F ? MIR_FADD : t == MIR_T_D ? MIR_DADD
	    : t == MIR_T_I64 || t == MIR_T_U64 ? MIR_ADD : MIR_ADDS);
  case N_DEC: case N_POST_DEC: case N_SUB: case N_SUB_ASSIGN:
    return (t == MIR_T_F ? MIR_FSUB : t == MIR_T_D ? MIR_DSUB
	    : t == MIR_T_I64 || t == MIR_T_U64 ? MIR_SUB : MIR_SUBS);
  case N_MUL: case N_MUL_ASSIGN: return (t == MIR_T_F ? MIR_FMUL : t == MIR_T_D ? MIR_DMUL
					 : t == MIR_T_I64 || t == MIR_T_U64 ? MIR_MUL : MIR_MULS);
  case N_DIV: case N_DIV_ASSIGN: return (t == MIR_T_F ? MIR_FDIV : t == MIR_T_D ? MIR_DDIV
					 : t == MIR_T_I64 ? MIR_DIV : t == MIR_T_U64 ? MIR_UDIV
					 : t == MIR_T_I32 ? MIR_DIVS : MIR_UDIVS);
  case N_MOD: case N_MOD_ASSIGN: return (t == MIR_T_I64 ? MIR_MOD : t == MIR_T_U64 ? MIR_UMOD
					 : t == MIR_T_I32 ? MIR_MODS : MIR_UMODS);
  case N_AND: case N_AND_ASSIGN: return (t == MIR_T_I64 || t == MIR_T_U64 ? MIR_AND : MIR_ANDS);
  case N_OR: case N_OR_ASSIGN: return (t == MIR_T_I64 || t == MIR_T_U64 ? MIR_OR : MIR_ORS);
  case N_XOR: case N_XOR_ASSIGN: return (t == MIR_T_I64 || t == MIR_T_U64 ? MIR_XOR : MIR_XORS);
  case N_LSH: case N_LSH_ASSIGN: return (t == MIR_T_I64 || t == MIR_T_U64 ? MIR_LSH : MIR_LSHS);
  case N_RSH: case N_RSH_ASSIGN: return (t == MIR_T_I64 ? MIR_RSH : t == MIR_T_U64 ? MIR_URSH
					 : t == MIR_T_I32 ? MIR_RSHS : MIR_URSHS);
  case N_EQ: return (t == MIR_T_F ? MIR_FEQ : t == MIR_T_D ? MIR_DEQ
		     : t == MIR_T_I64 || t == MIR_T_U64 ? MIR_EQ : MIR_EQS);
  case N_NE: return (t == MIR_T_F ? MIR_FNE : t == MIR_T_D ? MIR_DNE
		     : t == MIR_T_I64 || t == MIR_T_U64 ? MIR_NE : MIR_NES);
  case N_LT: return (t == MIR_T_F ? MIR_FLT : t == MIR_T_D ? MIR_DLT : t == MIR_T_I64 ? MIR_LT
		     : t == MIR_T_U64 ? MIR_ULT : t == MIR_T_I32 ? MIR_LTS : MIR_ULTS);
  case N_LE: return (t == MIR_T_F ? MIR_FLE : t == MIR_T_D ? MIR_DLE : t == MIR_T_I64 ? MIR_LE
		     : t == MIR_T_U64 ? MIR_ULE : t == MIR_T_I32 ? MIR_LES : MIR_ULES);
  case N_GT: return (t == MIR_T_F ? MIR_FGT : t == MIR_T_D ? MIR_DGT : t == MIR_T_I64 ? MIR_GT
		     : t == MIR_T_U64 ? MIR_UGT : t == MIR_T_I32 ? MIR_GTS : MIR_UGTS);
  case N_GE: return (t == MIR_T_F ? MIR_FGE : t == MIR_T_D ? MIR_DGE : t == MIR_T_I64 ? MIR_GE
		     : t == MIR_T_U64 ? MIR_UGE : t == MIR_T_I32 ? MIR_GES : MIR_UGES);
  default:
    assert (FALSE);
  }
}

static MIR_insn_code_t get_compare_branch_code (MIR_insn_code_t code) {
#define B(n) case MIR_ ## n: return MIR_B ## n;                 \
             case MIR_ ## n ## S: return MIR_B ## n ## S;       \
             case MIR_F ## n: return MIR_FB ## n;               \
	     case MIR_D ## n: return MIR_DB ## n;
#define BCMP(n) B(n)                                            \
                case MIR_U ## n: return MIR_UB ## n;            \
                case MIR_U ## n ## S: return MIR_UB ## n ## S;
  switch (code) {
    B (EQ) B (NE) BCMP (LT) BCMP (LE) BCMP (GT) BCMP (GE)
  default:
    assert (FALSE);
  }
#undef B
#undef BCMP
}

static op_t force_reg (op_t op, MIR_type_t t) {
  op_t res;
  
  if (op.mir_op.mode == MIR_OP_REG)
    return op;
  res = get_new_temp (t);
  emit2 (MIR_MOV, res.mir_op, op.mir_op);
  return res;
}

static void emit_label (node_t r) {
  node_t labels = NL_HEAD (r->ops);

  assert (labels->code == N_LIST);
  if (NL_HEAD (labels->ops) == NULL)
    return;
  if (labels->attr == NULL)
    labels->attr = MIR_new_label ();
  emit_insn (labels->attr);
}

static MIR_label_t get_label (node_t target) {
  node_t labels = NL_HEAD (target->ops);

  assert (labels->code == N_LIST && NL_HEAD (labels->ops) != NULL);
  if (labels->attr != NULL)
    return labels->attr;
  return labels->attr = MIR_new_label ();
}

static MIR_label_t continue_label, break_label;

static void top_gen (node_t r, MIR_label_t true_label, MIR_label_t false_label) {
  int saved_reg_free_mark = reg_free_mark;

  gen (r, true_label, false_label, FALSE);
  reg_free_mark = saved_reg_free_mark; /* free used temp regs */
}

static op_t modify_for_block_move (op_t mem, op_t index) {
  op_t base;
  
  assert (mem.mir_op.mode == MIR_OP_MEM && index.mir_op.mode == MIR_OP_REG);
  if (mem.mir_op.u.mem.base != 0 && mem.mir_op.u.mem.index != 0) {
    base = get_new_temp (MIR_T_I64);
    if (mem.mir_op.u.mem.scale != 1)
      emit3 (MIR_MUL, base.mir_op, MIR_new_reg_op (mem.mir_op.u.mem.index),
	     MIR_new_int_op (mem.mir_op.u.mem.scale));
    else
      emit2 (MIR_MOV, base.mir_op, MIR_new_reg_op (mem.mir_op.u.mem.index));
    emit3 (MIR_ADD, base.mir_op, base.mir_op, MIR_new_reg_op (mem.mir_op.u.mem.base));
    mem.mir_op.u.mem.base = base.mir_op.u.reg;
    mem.mir_op.u.mem.index = index.mir_op.u.reg; mem.mir_op.u.mem.scale = 1;
  }
  return mem;
}

DEF_VARR (MIR_op_t);
static VARR (MIR_op_t) *ops;

static op_t gen (node_t r, MIR_label_t true_label, MIR_label_t false_label, int val_p) {
  op_t res, op1, op2, var, val;
  MIR_type_t t;
  MIR_insn_code_t insn_code;
  struct expr *e;
  struct type *type;
  decl_t decl;
  long double ld;
  long long ll;
  unsigned long long ull;
  int saved_reg_free_mark = reg_free_mark;
  
  assert ((true_label == NULL && false_label == NULL)
	  || (true_label != NULL && false_label != NULL));
  switch (r->code) {
  case N_LIST:
    for (node_t n = NL_HEAD (r->ops); n != NULL; n = NL_NEXT (n))
      gen (n, true_label, false_label, FALSE);
    break;
  case N_IGNORE:
    break; /* do nothing */
  case N_I:
  case N_L:
    ll = r->u.l;
    goto int_val;
  case N_LL:
    ll = r->u.ll;
  int_val:
    res = new_op (NULL, MIR_new_int_op (ll));
    break;
  case N_U:
  case N_UL:
    ull = r->u.ul;
    goto uint_val;
  case N_ULL:
    ull = r->u.ull;
  uint_val:
    res = new_op (NULL, MIR_new_uint_op (ull));
    break;
  case N_F:
    ld = r->u.f;
    goto float_val;
  case N_D:
    ld = r->u.d;
    goto float_val;
  case N_LD:
    ld = r->u.ld;
  float_val:
    res = new_op (NULL, (get_mir_type (((struct expr *) r->attr)->type) == MIR_T_F
			 ? MIR_new_float_op (ld) : MIR_new_double_op (ld)));
    break;
  case N_CH:
    ll = r->u.ch;
    goto int_val;
  case N_STR:
    res = new_op (NULL, MIR_new_str_op (r->u.s)); // ??? what to do with decl and str in initializer
    break;
  case N_COMMA:
    gen (NL_HEAD (r->ops), NULL, NULL, TRUE);
    res = gen (NL_EL (r->ops, 1), true_label, false_label, TRUE);
    break;
  case N_ANDAND: case N_OROR:
    if (! push_const_val (r, &res)) {
      MIR_label_t temp_label = MIR_new_label (), t_label = true_label, f_label = false_label;
      int make_val_p = t_label == NULL;
      
      if (make_val_p) {
	t_label = MIR_new_label ();
	f_label = MIR_new_label ();
      }
      gen (NL_HEAD (r->ops), r->code == N_ANDAND ? temp_label : t_label,
	   r->code == N_ANDAND ? f_label : temp_label, TRUE);
      emit_insn (temp_label);
      gen (NL_EL (r->ops, 1), t_label, f_label, TRUE);
      if (make_val_p) {
	MIR_label_t end_label = MIR_new_label ();
	
	type = ((struct expr *) r->attr)->type;
	res = get_new_temp (get_mir_type (type));
	emit_insn (t_label);
	emit2 (MIR_MOV, res.mir_op, one_op.mir_op);
	emit1 (MIR_JMP, MIR_new_label_op (end_label));
	emit_insn (f_label);
	emit2 (MIR_MOV, res.mir_op, zero_op.mir_op);
	emit_insn (end_label);
      }      
    } else if (true_label != NULL) {
      int true_p;
      
      assert (res.mir_op.mode == MIR_OP_INT || res.mir_op.mode == MIR_OP_UINT
	      || res.mir_op.mode == MIR_OP_FLOAT || res.mir_op.mode == MIR_OP_DOUBLE);
      true_p = ((res.mir_op.mode == MIR_OP_INT && res.mir_op.u.i != 0)
		|| (res.mir_op.mode == MIR_OP_UINT && res.mir_op.u.u != 0)
		|| (res.mir_op.mode == MIR_OP_FLOAT && res.mir_op.u.f != 0.0f)
		|| (res.mir_op.mode == MIR_OP_DOUBLE && res.mir_op.u.d != 0.0));
      emit1 (MIR_JMP, MIR_new_label_op (true_p ? true_label : false_label));
      true_label = false_label = NULL;
    }
    break;
  case N_BITWISE_NOT:
    if (gen_unary_op (r, &op1, &res)) {
      emit3 (get_mir_insn_code (r), res.mir_op, op1.mir_op, zero_op.mir_op);
    }
    break;
  case N_NOT:
    if (true_label != NULL) {
      gen (NL_HEAD (r->ops), false_label, true_label, TRUE);
      true_label = false_label = NULL;
    } else {
      MIR_label_t end_label = MIR_new_label ();
      MIR_label_t t_label = MIR_new_label (), f_label = MIR_new_label ();
      
      res = get_new_temp (MIR_T_I64);
      gen (NL_EL (r->ops, 1), t_label, f_label, TRUE);
      emit_insn (t_label);
      emit2 (MIR_MOV, res.mir_op, zero_op.mir_op);
      emit1 (MIR_JMP, MIR_new_label_op (end_label));
      emit_insn (f_label);
      emit2 (MIR_MOV, res.mir_op, one_op.mir_op);
      emit_insn (end_label);
    }
    break;
  case N_ADD: case N_SUB: // ptr ???
    if (NL_NEXT (NL_HEAD (r->ops)) == NULL) { /* unary */
      if (gen_unary_op (r, &op1, &res)) {
	MIR_insn_code_t ic = get_mir_insn_code (r);
	  
	if (r->code == N_ADD) {
	  ic = ic == MIR_FADD ? MIR_FMOV : ic == MIR_DADD ? MIR_DMOV : MIR_MOV;
	  emit2 (ic, res.mir_op, op1.mir_op);
	} else {
	  ic = ic == MIR_FSUB ? MIR_FNEG : ic == MIR_DSUB ? MIR_DNEG : ic == MIR_SUB ? MIR_NEG : MIR_NEGS;
	  emit2 (ic, res.mir_op, op1.mir_op);
	}
      }
      break;
    }
    /* Fall through: */
  case N_AND: case N_OR: case N_XOR: case N_LSH: case N_RSH:
  case N_MUL: case N_DIV: case N_MOD:
    if (gen_bin_op (r, &op1, &op2, &res, NULL)) {
      emit3 (get_mir_insn_code (r), res.mir_op, op1.mir_op, op2.mir_op);
    }
    break;
  case N_EQ: case N_NE: case N_LT: case N_LE: case N_GT: case N_GE:
    if (! gen_bin_op (r, &op1, &op2, &res, NULL))
      break;
    insn_code = get_mir_insn_code (r);
    if (true_label == NULL) {
      emit3 (insn_code, res.mir_op, op1.mir_op, op2.mir_op);
    } else {
      insn_code = get_compare_branch_code (insn_code);
      emit3 (insn_code, MIR_new_label_op (true_label), op1.mir_op, op2.mir_op);
      emit1 (MIR_JMP, MIR_new_label_op (false_label));
      true_label = false_label = NULL;
    }
    break;
  case N_INC: case N_DEC: case N_POST_INC: case N_POST_DEC: // ??? ptr
    t = get_mir_type (((struct expr *) r->attr)->type);
    var = gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
    op1 = promote (force_val (var), t);
    op2 = promote (one_op, t);
    res = get_new_temp (t);
    val = get_new_temp (t);
    emit3 (get_mir_insn_code (r), val.mir_op, op1.mir_op, op2.mir_op);
    emit2 (t == MIR_T_F ? MIR_FMOV : t == MIR_T_D ? MIR_DMOV : MIR_MOV, res.mir_op,
	   r->code == N_INC || r->code == N_DEC ? val.mir_op : op1.mir_op);
    goto assign;
  case N_AND_ASSIGN: case N_OR_ASSIGN: case N_XOR_ASSIGN: case N_LSH_ASSIGN: case N_RSH_ASSIGN:
  case N_ADD_ASSIGN: case N_SUB_ASSIGN: case N_MUL_ASSIGN: case N_DIV_ASSIGN: case N_MOD_ASSIGN: // ptr ???
    if (! gen_bin_op (r, &op1, &op2, &res, &var)) /* stack: var, var op val */
      assert (FALSE); /* Can not be a constant */
    emit3 (get_mir_insn_code (r), res.mir_op, op1.mir_op, op2.mir_op);
    val = res;
    goto assign;
    break;
  case N_ASSIGN:
    var = gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
    res = val = gen (NL_EL (r->ops, 1), NULL, NULL, TRUE);
    t = get_mir_type (((struct expr *) r->attr)->type);
    //???    res = promote (res, t);
  assign:
    if (scalar_type_p (((struct expr *) r->attr)->type)) {
      t = get_op_type (var);
      t = promote_mir_int_type (t);
      op2 = promote (val, t);
      if (var.decl == NULL || var.decl->bit_offset < 0) {
	emit2 (t == MIR_T_F ? MIR_FMOV : t == MIR_T_D ? MIR_DMOV : MIR_MOV, var.mir_op, val.mir_op);
      } else {
	int size, sh;
	uint64_t mask, mask2;
	op_t temp_op1, temp_op2;

	assert (var.mir_op.mode == MIR_OP_MEM);
	size = get_int_mir_type_size (var.mir_op.u.mem.type);
	sh = size  * 8 - var.decl->bit_offset - var.decl->width;
	mask = 0xffffffffffffffff >> (64 - var.decl->width); mask2 = ~(mask << sh);
	temp_op1 = get_new_temp (MIR_T_I64);
	temp_op2 = get_new_temp (MIR_T_I64);
	emit2 (MIR_MOV, temp_op2.mir_op, var.mir_op);
	emit3 (MIR_AND, temp_op2.mir_op, temp_op2.mir_op, MIR_new_uint_op (mask2));
	emit3 (MIR_AND, temp_op1.mir_op, val.mir_op, MIR_new_uint_op (mask));
	if (sh != 0)
	  emit3 (MIR_LSH, temp_op1.mir_op, temp_op1.mir_op, MIR_new_int_op (sh));
	emit3 (MIR_OR, temp_op1.mir_op, temp_op1.mir_op, temp_op2.mir_op);
	emit2 (MIR_MOV, var.mir_op, temp_op1.mir_op);
      }
    } else { /* block move */
      MIR_label_t repeat_label = MIR_new_label ();
      mir_size_t size = type_size (((struct expr *) r->attr)->type);
      assert (r->code == N_ASSIGN);
      op1 = get_new_temp (MIR_T_I64);
      emit2 (MIR_MOV, op1.mir_op, MIR_new_int_op (size));
      var = modify_for_block_move (var, op1);
      val = modify_for_block_move (val, op1);
      emit_insn (repeat_label);
      emit3 (MIR_SUB, op1.mir_op, op1.mir_op, one_op.mir_op);
      emit2 (MIR_MOV, var.mir_op, val.mir_op);
      emit3 (MIR_BGT, MIR_new_label_op (repeat_label), op1.mir_op, zero_op.mir_op);
    }
    break;
  case N_ID: {
    char prefix[50];
    
    e = r->attr;
    if (push_const_val (r, &res)) {
    } else if (e->lvalue_node == NULL) {
      assert (e->def_node != NULL);
      res = new_op (NULL, MIR_new_ref_op (((decl_t) e->def_node->attr)->item));
    } else if (! (decl = e->lvalue_node->attr)->reg_p) {
      t = get_mir_type (e->type);
      res = new_op (decl, MIR_new_mem_op (t, decl->offset, MIR_reg (FP_NAME, curr_func->u.func), 0, 1));
    } else {
      t = get_mir_type (e->type);
      assert (t != MIR_T_BLOCK);
      t = promote_mir_int_type (t);
      sprintf (prefix, t == MIR_T_I64 ? "I%u_" : t == MIR_T_U64 ? "U%u_" : t == MIR_T_I32 ? "i%u_"
	       : t == MIR_T_U32 ? "u%u_" : t == MIR_T_F ? "f%u_" : "d%u_",
	       (unsigned) ((struct node_scope *) decl->scope->attr)->func_scope_num);
      VARR_TRUNC (char, temp_string, 0);
      add_to_temp_string (prefix);
      add_to_temp_string (r->u.s);
      res = new_op (decl, MIR_new_reg_op (get_reg_var (t, VARR_ADDR (char, temp_string)).reg));
    }
    break;
  }
  case N_IND: {
    MIR_type_t ind_t;
    mir_size_t size = type_size (((struct expr *) r->attr)->type);
    
    t = get_mir_type (((struct expr *) r->attr)->type);
    op1 = gen (NL_HEAD (r->ops), NULL, NULL, TRUE);
    op2 = gen (NL_EL (r->ops, 1), NULL, NULL, TRUE);
    ind_t = promote_mir_int_type (get_mir_type (((struct expr *) NL_EL (r->ops, 1)->attr)->type));
    op2 = force_reg (op2, ind_t);
    assert (op2.mir_op.mode == MIR_OP_REG && op1.mir_op.mode == MIR_OP_MEM);
    res = op1;
    if (res.mir_op.u.mem.base == 0 && size == 1) {
      res.mir_op.u.mem.base = op2.mir_op.u.reg;
    } else if (op1.mir_op.u.mem.index == 0 && size <= MIR_MAX_SCALE) {
      res.mir_op.u.mem.index = op2.mir_op.u.reg; res.mir_op.u.mem.scale = size;
    } else {
      op_t temp_op;
      
      temp_op = get_new_temp (MIR_T_I64);
      emit3 (MIR_MUL, temp_op.mir_op, op2.mir_op, MIR_new_int_op (size));
      if (res.mir_op.u.mem.base != 0)
	emit3 (MIR_ADD, temp_op.mir_op, temp_op.mir_op, MIR_new_reg_op (res.mir_op.u.mem.base));
      res.mir_op.u.mem.base = temp_op.mir_op.u.reg;
    }
    res.mir_op.u.mem.type = t;
    break;
  }
  case N_ADDR: {
    int add_p = FALSE;
    
    op1 = gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
    assert (op1.mir_op.mode == MIR_OP_MEM);
    t = get_mir_type (((struct expr *) r->attr)->type);
    res = get_new_temp (t);
    if (op1.mir_op.u.mem.index != 0) {
      emit3 (MIR_MUL, res.mir_op, MIR_new_reg_op (op1.mir_op.u.mem.index),
	     MIR_new_int_op (op1.mir_op.u.mem.scale));
      add_p = TRUE;
    }
    if (op1.mir_op.u.mem.disp != 0) {
      if (add_p)
	emit3 (MIR_ADD, res.mir_op, res.mir_op, MIR_new_int_op (op1.mir_op.u.mem.disp));
      else
	emit2 (MIR_MOV, res.mir_op, MIR_new_int_op (op1.mir_op.u.mem.disp));
      add_p = TRUE;
    }
    if (op1.mir_op.u.mem.base != 0) {
      if (add_p)
	emit3 (MIR_ADD, res.mir_op, res.mir_op, MIR_new_reg_op (op1.mir_op.u.mem.base));
      else
	emit2 (MIR_MOV, res.mir_op, MIR_new_reg_op (op1.mir_op.u.mem.base));
    }
    break;
  }
  case N_DEREF:
    op1 = gen (NL_HEAD (r->ops), NULL, NULL, TRUE);
    op1 = force_reg (op1, MIR_T_I64);
    assert (op1.mir_op.mode == MIR_OP_REG);
    t = get_mir_type (((struct expr *) r->attr)->type);
    op1.mir_op = MIR_new_mem_op (t, 0, op1.mir_op.u.reg, 0, 1);
    res = new_op (NULL, op1.mir_op);
    break;
  case N_FIELD: case N_DEREF_FIELD: {
    node_t def_node;

    e = r->attr;
    def_node = e->lvalue_node;
    assert (def_node != NULL && def_node->code == N_MEMBER); 
    decl = def_node->attr;
    op1 = gen (NL_HEAD (r->ops), NULL, NULL, r->code == N_DEREF_FIELD);
    t = get_mir_type (decl->decl_spec.type);
    if (r->code == N_FIELD) {
      assert (op1.mir_op.mode == MIR_OP_MEM);
      op1.mir_op = MIR_new_mem_op (t, op1.mir_op.u.mem.disp + decl->offset, op1.mir_op.u.mem.base,
				   op1.mir_op.u.mem.index, op1.mir_op.u.mem.scale);
    } else {
      op1 = force_reg (op1, MIR_T_I64);
      assert (op1.mir_op.mode == MIR_OP_REG);
      op1.mir_op = MIR_new_mem_op (t, decl->offset, op1.mir_op.u.reg, 0, 1);
    }
    res = new_op (decl, op1.mir_op);
    break;
  }
  case N_COND: {
    node_t cond = NL_HEAD (r->ops);
    node_t true_expr = NL_NEXT (cond);
    node_t false_expr = NL_NEXT (true_expr);
    MIR_label_t true_label = MIR_new_label (), false_label = MIR_new_label ();
    MIR_label_t end_label = MIR_new_label ();

    t = get_mir_type (((struct expr *) r->attr)->type);
    res = get_new_temp (t);
    gen (cond, true_label, false_label, TRUE);
    emit_insn (true_label);
    op1 = gen (true_expr, NULL, NULL, TRUE);
    emit2 (MIR_MOV, res.mir_op, op1.mir_op);
    emit1 (MIR_JMP, MIR_new_label_op (end_label));
    emit_insn (false_label);
    op1 = gen (false_expr, NULL, NULL, TRUE);
    emit2 (MIR_MOV, res.mir_op, op1.mir_op);
    emit_insn (end_label);
    break;
  }
  case N_ALIGNOF: case N_SIZEOF: case N_EXPR_SIZEOF:
    if (gen_unary_op (r, &op1, &res))
      assert (FALSE); /* should be a constant expression */
    break;
  case N_CAST:
    op1 = gen (NL_EL (r->ops, 1), NULL, NULL, TRUE);
    t = get_mir_type (((struct expr *) r->attr)->type);
    res = promote (op1, t);
    break;
  case N_COMPOUND_LITERAL:
    break; // ???
  case N_CALL: { // proto ???
    node_t func, args = NL_EL (r->ops, 1);
    size_t ops_start;
    struct type *func_type, *type = ((struct expr *) r->attr)->type;
    MIR_item_t proto_item;
    
    ops_start = VARR_LENGTH (MIR_op_t, ops);
    func = NL_HEAD (r->ops);
    func_type = ((struct expr *) func->attr)->type;
    assert (func_type->mode == TM_PTR && func_type->u.ptr_type->mode == TM_FUNC);
    func_type = func_type->u.ptr_type;
    proto_item = func_type->u.func_type->proto_item;
    VARR_PUSH (MIR_op_t, ops, MIR_new_ref_op (proto_item));
    op1 = gen (func, NULL, NULL, TRUE);
    VARR_PUSH (MIR_op_t, ops, op1.mir_op);
    if (type->mode != TM_BASIC || type->u.basic_type != TP_VOID) {
      t = get_mir_type (type);
      res = get_new_temp (t);
      VARR_PUSH (MIR_op_t, ops, res.mir_op);
    }
    for (node_t arg = NL_HEAD (args->ops); arg != NULL; arg = NL_NEXT (arg)) {
      op2 = gen (arg, NULL, NULL, TRUE);
      VARR_PUSH (MIR_op_t, ops, op2.mir_op);
    }
    // VARR_SET (MIR_op_t, ops, 1, MIR_new_int_op (nargs));
    MIR_append_insn (curr_func, MIR_new_insn_arr (MIR_CALL, VARR_LENGTH (MIR_op_t, ops) - ops_start,
						  VARR_ADDR (MIR_op_t, ops) + ops_start));
    VARR_TRUNC (MIR_op_t, ops, ops_start);
    break;
  }
  case N_GENERIC: {
    node_t list = NL_EL (r->ops, 1);
    node_t ga_case = NL_HEAD (list->ops);

    /* first element is now a compatible generic association case */
    op1 = gen (NL_EL (ga_case->ops, 1), NULL, NULL, TRUE);
    t = get_mir_type (((struct expr *) r->attr)->type);
    res = promote (op1, t);
    break;
  }
  case N_SPEC_DECL: { // ???
    node_t specs = NL_HEAD (r->ops);
    node_t declarator = NL_NEXT (specs);
    node_t id;
    
    decl = (decl_t) r->attr;
    if (declarator != NULL && decl->decl_spec.linkage == N_EXTERN && decl->item == NULL) {
      id = NL_HEAD (declarator->ops);
      decl->item = MIR_new_import (id->u.s);
    }
    break;
  }
  case N_ST_ASSERT: /* do nothing */
    break;
  case N_INIT:
    break; // ???
  case N_FUNC_DEF: {
    node_t decl_specs = NL_HEAD (r->ops);
    node_t declarator = NL_NEXT (decl_specs);
    node_t decls = NL_NEXT (declarator);
    node_t stmt = NL_NEXT (decls);
    MIR_reg_t fp_reg;
    
    assert (declarator != NULL && declarator->code == N_DECL && NL_HEAD (declarator->ops)->code == N_ID);
    curr_func = MIR_new_func (NL_HEAD (declarator->ops)->u.s, MIR_T_I32, 0, 0); // ???
    ((decl_t) r->attr)->item = curr_func;
    fp_reg = MIR_new_func_reg (curr_func->u.func, MIR_T_I64, FP_NAME);
    MIR_append_insn (curr_func, MIR_new_insn (MIR_ALLOCA, MIR_new_reg_op (fp_reg), MIR_new_int_op (81900)));
    gen (stmt, NULL, NULL, FALSE);
    MIR_finish_func ();
    finish_curr_func_reg_vars ();
    break;
  }
  case N_BLOCK:
    gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
    break;
  case N_MODULE:
    gen (NL_HEAD (r->ops), NULL, NULL, FALSE);
    break; // ???
  case N_IF: {
    node_t expr = NL_EL (r->ops, 1);
    node_t if_stmt = NL_NEXT (expr);
    node_t else_stmt = NL_NEXT (if_stmt);
    MIR_label_t if_label = MIR_new_label (), else_label = MIR_new_label ();
    MIR_label_t end_label = MIR_new_label ();

    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    top_gen (expr, if_label, else_label);
    emit_insn (if_label);
    gen (if_stmt, NULL, NULL, FALSE);
    emit1 (MIR_JMP, MIR_new_label_op (end_label));
    emit_insn (else_label);
    gen (else_stmt, NULL, NULL, FALSE);
    emit_insn (end_label);
    break;
  }
  case N_SWITCH: {
    node_t expr = NL_EL (r->ops, 1);
    node_t stmt = NL_NEXT (expr);
    struct switch_attr *switch_attr = r->attr;
    op_t case_reg_op;
    case_t c;
    
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    break_label = MIR_new_label ();
    case_reg_op = gen (expr, NULL, NULL, TRUE);
    case_reg_op = force_reg (case_reg_op, get_mir_type (((struct expr *) expr->attr)->type));
    for (c = DLIST_HEAD (case_t, switch_attr->case_labels); c != NULL; c = DLIST_NEXT (case_t, c)) {
      MIR_label_t label = get_label (c->case_target_node);
      node_t case_expr;
      
      if (c->case_node->code == N_DEFAULT) {
	assert (DLIST_NEXT (case_t, c) == NULL);
	emit1 (MIR_JMP, MIR_new_label_op (label));
	break;
      }
      case_expr = NL_HEAD (c->case_node->ops);
      e = case_expr->attr;
      assert (e->const_p && integer_type_p (e->type));
      emit3 (MIR_BEQ, MIR_new_label_op (label), case_reg_op.mir_op, MIR_new_int_op (e->u.i_val));
    }
    if (c == NULL) /* no default: */
      emit1 (MIR_JMP, MIR_new_label_op (break_label));
    top_gen (stmt, NULL, NULL);
    emit_insn (break_label);
    break;
  }
  case N_DO: {
    node_t expr = NL_EL (r->ops, 1);
    node_t stmt = NL_NEXT (expr);

    assert (false_label == NULL && true_label == NULL);
    continue_label = MIR_new_label ();
    break_label = MIR_new_label ();
    emit_label (r);
    emit_insn (continue_label);
    gen (stmt, NULL, NULL, FALSE);
    top_gen (expr, continue_label, break_label);
    emit_insn (break_label);
    break;
  }
  case N_WHILE: {
    node_t expr = NL_EL (r->ops, 1);
    node_t stmt = NL_NEXT (expr);
    MIR_label_t stmt_label = MIR_new_label ();

    assert (false_label == NULL && true_label == NULL);
    continue_label = MIR_new_label ();
    break_label = MIR_new_label ();
    emit_label (r);
    emit_insn (continue_label);
    top_gen (expr, stmt_label, break_label);
    emit_insn (stmt_label);
    gen (stmt, NULL, NULL, FALSE);
    emit1 (MIR_JMP, MIR_new_label_op (continue_label));
    emit_insn (break_label);
    break;
  }
  case N_FOR: {
    node_t init = NL_EL (r->ops, 1);
    node_t cond = NL_NEXT (init);
    node_t iter = NL_NEXT (cond);
    node_t stmt = NL_NEXT (iter);
    MIR_label_t start_label = MIR_new_label (), stmt_label = MIR_new_label ();
    MIR_label_t saved_continue_label = continue_label, saved_break_label = break_label;

    assert (false_label == NULL && true_label == NULL);
    continue_label = MIR_new_label ();
    break_label = MIR_new_label ();
    emit_label (r);
    top_gen (init, NULL, NULL);
    emit_insn (start_label);
    top_gen (cond, stmt_label, break_label);
    emit_insn (stmt_label);
    gen (stmt, NULL, NULL, FALSE);
    emit_insn (continue_label);
    top_gen (iter, NULL, NULL);
    emit1 (MIR_JMP, MIR_new_label_op (start_label));
    emit_insn (break_label);
    continue_label = saved_continue_label; break_label = saved_break_label;
    break;
  }
  case N_GOTO: {
    node_t target = r->attr;
    
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    emit1 (MIR_JMP, MIR_new_label_op (get_label (target)));
    break;
  }
  case N_CONTINUE:
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    emit1 (MIR_JMP, MIR_new_label_op (continue_label));
    break;
  case N_BREAK:
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    emit1 (MIR_JMP, MIR_new_label_op (break_label));
    break;
  case N_RETURN:
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    if (NL_EL (r->ops, 1) == NULL) {
      emit1 (MIR_RET, zero_op.mir_op);
      break;
    }
    op1 = gen (NL_EL (r->ops, 1), NULL, NULL, TRUE);
    t = get_op_type (op1);
    emit1 (t == MIR_T_F ? MIR_FRET : t == MIR_T_D ? MIR_DRET : MIR_RET, op1.mir_op);
    reg_free_mark = saved_reg_free_mark; /* free used temp regs */
    break;
  case N_EXPR:
    assert (false_label == NULL && true_label == NULL);
    emit_label (r);
    top_gen (NL_EL (r->ops, 1), NULL, NULL);
    break;
  default:
    abort ();
  }
  if (true_label != NULL) {
    res = force_val (res);
    emit2 (MIR_BT, MIR_new_label_op (true_label), res.mir_op);
    emit1 (MIR_JMP, MIR_new_label_op (false_label));
  } else if (val_p) {
    res = force_val (res);
  }
  return res;
}

static void generate_mir_protos (void) {
  VARR (MIR_var_t) *vars;
  node_t call, func, declarator, id, first_param, p;
  struct type *type;
  struct func_type *func_type;
  struct decl_spec *decl_spec_ptr;
  MIR_var_t var;
  char buf[30];
  int n = 0;
  
  VARR_CREATE (MIR_var_t, vars, 64);
  for (size_t i = 0; i < VARR_LENGTH (node_t, call_nodes); i++) {
    call = VARR_GET (node_t, call_nodes, i);
    assert (call->code == N_CALL);
    func = NL_HEAD (call->ops); type = ((struct expr *) func->attr)->type;
    assert (type->mode == TM_PTR && type->u.ptr_type->mode == TM_FUNC);
    set_type_layout (type);
    func_type = type->u.ptr_type->u.func_type;
    first_param = NL_HEAD (func_type->param_list->ops);
    VARR_TRUNC (MIR_var_t, vars, 0);
    if (first_param != NULL && ! void_param_p (first_param)) {
      for (p = first_param; p != NULL; p = NL_NEXT (p)) {
	if (p->code == N_TYPE) {
	  var.name = NULL;
	  decl_spec_ptr = p->attr;
	} else {
	  declarator = NL_EL (p->ops, 1);
	  assert (p->code == N_SPEC_DECL && declarator != NULL && declarator->code == N_DECL);
	  id = NL_HEAD (declarator->ops);
	  var.name = id->u.s;
	  decl_spec_ptr = &((decl_t) p->attr)->decl_spec;
	}
	var.type = get_mir_type (decl_spec_ptr->type);
      }
    }
    set_type_layout (func_type->ret_type);
    sprintf (buf, "proto%d", n++);
    func_type->proto_item = ((func_type->dots_p ? MIR_new_vararg_proto_arr : MIR_new_proto_arr)
			     (buf, get_mir_type (func_type->ret_type),
			      VARR_LENGTH (MIR_var_t, vars), VARR_ADDR (MIR_var_t, vars)));
  }
  VARR_DESTROY (MIR_var_t, vars);
}

static void generate_mir (node_t r) {
  zero_op = new_op (NULL, MIR_new_int_op (0));
  one_op = new_op (NULL, MIR_new_int_op (1));
  init_reg_vars ();
  generate_mir_protos ();
  VARR_CREATE (MIR_op_t, ops, 32);
  top_gen (r, NULL, NULL);
  finish_reg_vars ();
  VARR_DESTROY (MIR_op_t, ops);
}

/* ------------------------- MIR generator finish ----------------------------- */



static const char *get_node_name (node_code_t code) {
#define C(n) case N_##n: return #n;
  switch (code) {
    C (IGNORE) C (I) C (L) C (LL) C (U) C (UL) C (ULL) C (F) C (D) C (LD) C (CH) C (STR) C (ID) C (COMMA)
    C (ANDAND) C (OROR) C (EQ) C (NE) C (LT) C (LE) C (GT) C (GE) C (ASSIGN) C (BITWISE_NOT)
    C (NOT) C (AND) C (AND_ASSIGN) C (OR) C (OR_ASSIGN) C (XOR) C (XOR_ASSIGN) C (LSH)
    C (LSH_ASSIGN) C (RSH) C (RSH_ASSIGN) C (ADD) C (ADD_ASSIGN) C (SUB) C (SUB_ASSIGN) C (MUL)
    C (MUL_ASSIGN) C (DIV) C (DIV_ASSIGN) C (MOD) C (MOD_ASSIGN) C (IND) C (FIELD) C (ADDR)
    C (DEREF) C (DEREF_FIELD) C (COND) C (INC) C (DEC) C (POST_INC) C (POST_DEC) C (ALIGNOF)
    C (SIZEOF) C (EXPR_SIZEOF) C (CAST) C (COMPOUND_LITERAL) C (CALL) C (GENERIC) C (GENERIC_ASSOC)
    C (IF) C (SWITCH) C (WHILE) C (DO) C (FOR) C (GOTO) C (CONTINUE) C (BREAK) C (RETURN) C (EXPR)
    C (BLOCK) C (CASE) C (DEFAULT) C (LABEL) C (LIST) C (SPEC_DECL) C (SHARE) C (TYPEDEF)
    C (EXTERN) C (STATIC) C (AUTO) C (REGISTER) C (THREAD_LOCAL) C (DECL) C (VOID) C (CHAR)
    C (SHORT) C (INT) C (LONG) C (FLOAT) C (DOUBLE) C (SIGNED) C (UNSIGNED) C (BOOL)
    C (STRUCT) C (UNION) C (ENUM) C (ENUM_CONST) C (MEMBER) C (CONST) C (RESTRICT) C (VOLATILE)
    C (ATOMIC) C (INLINE) C (NO_RETURN) C (ALIGNAS) C (FUNC) C (STAR) C (POINTER) C (DOTS) C (ARR)
    C (INIT) C (FIELD_ID) C (TYPE) C (ST_ASSERT) C (FUNC_DEF) C (MODULE)
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

static void print_node (FILE *f, node_t n, int indent, int attr_p);

static void print_ops (FILE *f, node_t n, int indent, int attr_p) {
  int i;
  node_t op;
  
  for (i = 0; (op = get_op (n, i)) != NULL; i++)
    print_node (f, op, indent + 2, attr_p);
}

static void print_qual (FILE *f, struct type_qual type_qual) {
  if (type_qual.const_p)
    fprintf (f, ", const");
  if (type_qual.restrict_p)
    fprintf (f, ", restrict");
  if (type_qual.volatile_p)
    fprintf (f, ", volatile");
  if (type_qual.atomic_p)
    fprintf (f, ", atomic");
}

static void print_type (FILE *f, struct type *type) {
  switch (type->mode) {
  case TM_UNDEF:
    fprintf (f, "undef type mode");
    break;
  case TM_BASIC:
    switch (type->u.basic_type) {
    case TP_UNDEF: fprintf (f, "undef type"); break;
    case TP_VOID: fprintf (f, "void"); break;
    case TP_BOOL: fprintf (f, "bool"); break;
    case TP_CHAR: fprintf (f, "char"); break;
    case TP_SCHAR: fprintf (f, "signed char"); break;
    case TP_UCHAR: fprintf (f, "unsigned char"); break;
    case TP_SHORT: fprintf (f, "short"); break;
    case TP_USHORT: fprintf (f, "unsigned short"); break;
    case TP_INT: fprintf (f, "int"); break;
    case TP_UINT: fprintf (f, "unsigned int"); break;
    case TP_LONG: fprintf (f, "long"); break;
    case TP_ULONG: fprintf (f, "unsigned long"); break;
    case TP_LLONG: fprintf (f, "long long"); break;
    case TP_ULLONG: fprintf (f, "unsigned long long"); break;
    case TP_FLOAT: fprintf (f, "float"); break;
    case TP_DOUBLE: fprintf (f, "double"); break;
    case TP_LDOUBLE: fprintf (f, "long double"); break;
    default:
      assert (FALSE);
    }
    break;
  case TM_ENUM:
    fprintf (f, "enum node %lu", type->u.tag_type->uid);
    break;
  case TM_PTR:
    fprintf (f, "ptr (");
    print_type (f, type->u.ptr_type);
    fprintf (f, ")");
    break;
  case TM_STRUCT:
    fprintf (f, "struct node %lu", type->u.tag_type->uid);
    break;
  case TM_UNION:
    fprintf (f, "union node %lu", type->u.tag_type->uid);
    break;
  case TM_ARR:
    fprintf (f, "array [%s", type->u.arr_type->static_p ? "static " : "");
    print_qual (f, type->u.arr_type->ind_type_qual);
    fprintf (f, "size node %lu] (", type->u.arr_type->size->uid);
    print_type (f, type->u.arr_type->el_type);
    fprintf (f, ")");
    break;
  case TM_FUNC:
    fprintf (f, "func ");
    print_type (f, type->u.func_type->ret_type);
    fprintf (f, "(params node %lu", type->u.func_type->param_list->uid);
    fprintf (f, type->u.func_type->dots_p ? ", ...)" : ")");
    break;
  default:
    assert (FALSE);
  }
  print_qual (f, type->type_qual);
  if (type->incomplete_p)
    fprintf (f, ", incomplete");
  if (type->raw_size != MIR_SIZE_MAX)
    fprintf (f, ", raw size = %llu", (unsigned long long) type->raw_size);
  if (type->align >= 0)
    fprintf (f, ", align = %d", type->align);
  fprintf (f, " ");
}

static void print_decl_spec (FILE *f, struct decl_spec *decl_spec) {
  if (decl_spec->typedef_p)
    fprintf (f, " typedef, ");
  if (decl_spec->extern_p)
    fprintf (f, " extern, ");
  if (decl_spec->static_p)
    fprintf (f, " static, ");
  if (decl_spec->auto_p)
    fprintf (f, " auto, ");
  if (decl_spec->register_p)
    fprintf (f, " register, ");
  if (decl_spec->thread_local_p)
    fprintf (f, " thread local, ");
  if (decl_spec->inline_p)
    fprintf (f, " inline, ");
  if (decl_spec->no_return_p)
    fprintf (f, " no return, ");
  if (decl_spec->align >= 0)
    fprintf (f, " align = %d, ", decl_spec->align);
  if (decl_spec->align_node != NULL)
    fprintf (f, " strictest align node %lu, ", decl_spec->align_node->uid);
  if (decl_spec->linkage != N_IGNORE)
    fprintf (f, " %s linkage, ", decl_spec->linkage == N_STATIC ? "static" : "extern");
  print_type (f, decl_spec->type);
}

static void print_decl (FILE *f, decl_t decl) {
  if (decl == NULL)
    return;
  fprintf (f, ": ");
  print_decl_spec (f, &decl->decl_spec);
  if (decl->addr_p)
    fprintf (f, ", addressable");
  if (decl->reg_p)
    fprintf (f, ", reg");
  else {
    fprintf (f, ", offset = %llu", (unsigned long long) decl->offset);
    if (decl->bit_offset >= 0)
      fprintf (f, ", bit offset = %d", decl->bit_offset);
  }
}

static void print_expr (FILE *f, struct expr *e) {
  if (e == NULL)
    return; /* e.g. N_ID which is not an expr */
  fprintf (f, ": ");
  if (e->lvalue_node)
    fprintf (f, "lvalue, ");
  print_type (f, e->type);
  if (e->const_p) {
    fprintf (f, ", const = ");
    if (! integer_type_p (e->type)) {
      fprintf (f, " %.*Lg\n", LDBL_DECIMAL_DIG, (long double) e->u.d_val);
    } else if (signed_integer_type_p (e->type)) {
      fprintf (f, "%lld", (long long) e->u.i_val);
    } else {
      fprintf (f, "%llu", (unsigned long long) e->u.u_val);
    }
  }
}

static void print_node (FILE *f, node_t n, int indent, int attr_p) {
  int i;
  
  fprintf (f, "%6lu: ", n->uid);
  for (i = 0; i < indent; i++)
    fprintf (f, " ");
  if (n == &err_node) {
    fprintf (f, "<error>\n");
    return;
  }
  fprintf (f, "%s (", get_node_name (n->code));
  print_pos (f, n->pos, FALSE);
  fprintf (f, ")");
  switch (n->code) {
  case N_IGNORE: fprintf (f, "\n"); break;
  case N_I: fprintf (f, " %lld", (long long) n->u.l); goto expr;
  case N_L: fprintf (f, " %lldl", (long long) n->u.l); goto expr;
  case N_LL: fprintf (f, " %lldll", (long long) n->u.ll); goto expr;
  case N_U: fprintf (f, " %lluu", (unsigned long long) n->u.ul); goto expr;
  case N_UL: fprintf (f, " %lluul", (unsigned long long) n->u.ul); goto expr;
  case N_ULL: fprintf (f, " %lluull", (unsigned long long) n->u.ull); goto expr;
  case N_F: fprintf (f, " %.*g", FLT_DECIMAL_DIG, (double) n->u.f); goto expr;
  case N_D: fprintf (f, " %.*g", DBL_DECIMAL_DIG, (double) n->u.d); goto expr;
  case N_LD: fprintf (f, " %.*Lg", LDBL_DECIMAL_DIG, (long double) n->u.ld); goto expr;
  case N_CH: fprintf (f, " '"); print_char (f, n->u.ch); fprintf (f, "'"); goto expr;
  case N_STR: fprintf (f, " \""); print_chars (f, n->u.s); fprintf (f, "\""); goto expr;
  case N_ID:
    fprintf (f, " %s", n->u.s);
  expr:
    if (attr_p)
      print_expr (f, n->attr);
    fprintf (f, "\n");
    break;
  case N_COMMA: case N_ANDAND: case N_OROR: case N_EQ: case N_NE: case N_LT: case N_LE:
  case N_GT: case N_GE: case N_ASSIGN: case N_BITWISE_NOT: case N_NOT: case N_AND:
  case N_AND_ASSIGN: case N_OR: case N_OR_ASSIGN: case N_XOR: case N_XOR_ASSIGN: case N_LSH:
  case N_LSH_ASSIGN: case N_RSH: case N_RSH_ASSIGN: case N_ADD: case N_ADD_ASSIGN: case N_SUB:
  case N_SUB_ASSIGN: case N_MUL: case N_MUL_ASSIGN: case N_DIV: case N_DIV_ASSIGN: case N_MOD:
  case N_MOD_ASSIGN: case N_IND: case N_FIELD: case N_ADDR: case N_DEREF: case N_DEREF_FIELD:
  case N_COND: case N_INC: case N_DEC: case N_POST_INC: case N_POST_DEC: case N_ALIGNOF:
  case N_SIZEOF: case N_EXPR_SIZEOF: case N_CAST: case N_COMPOUND_LITERAL: case N_CALL:
  case N_GENERIC:
    if (attr_p)
      print_expr (f, n->attr);
    fprintf (f, "\n");
    print_ops (f, n, indent, attr_p);
    break;
  case N_GENERIC_ASSOC: case N_IF: case N_WHILE: case N_DO: case N_CONTINUE: case N_BREAK:
  case N_RETURN: case N_EXPR: case N_CASE: case N_DEFAULT: case N_LABEL: case N_SHARE:
  case N_TYPEDEF: case N_EXTERN: case N_STATIC: case N_AUTO: case N_REGISTER: case N_THREAD_LOCAL:
  case N_DECL: case N_VOID: case N_CHAR: case N_SHORT: case N_INT: case N_LONG: case N_FLOAT:
  case N_DOUBLE: case N_SIGNED: case N_UNSIGNED: case N_BOOL: case N_ENUM: case N_CONST:
  case N_RESTRICT: case N_VOLATILE: case N_ATOMIC: case N_INLINE: case N_NO_RETURN: case N_ALIGNAS:
  case N_STAR: case N_POINTER: case N_DOTS: case N_ARR: case N_INIT: case N_FIELD_ID: case N_TYPE:
  case N_ST_ASSERT:
    fprintf (f, "\n");
    print_ops (f, n, indent, attr_p);
    break;
  case N_LIST:
    if (attr_p && n->attr != NULL) {
      fprintf (f, ": ");
      print_decl_spec (f, (struct decl_spec *) n->attr);
    }
    fprintf (f, "\n");
    print_ops (f, n, indent, attr_p);
    break;
  case N_SPEC_DECL: case N_MEMBER: case N_FUNC_DEF:
    if (attr_p)
      print_decl (f, (decl_t) n->attr);
    fprintf (f, "\n");
    print_ops (f, n, indent, attr_p);
    break;
  case N_FUNC:
    if (! attr_p || n->attr == NULL) {
      fprintf (f, "\n");
      print_ops (f, n, indent, attr_p);
      break;
    }
    /* fall through: */
  case N_STRUCT: case N_UNION: case N_MODULE: case N_BLOCK: case N_FOR:
    if (! attr_p || ((n->code == N_STRUCT || n->code == N_UNION)
		     && (NL_EL (n->ops, 1) == NULL || NL_EL (n->ops, 1)->code == N_IGNORE)))
      fprintf (f, "\n");
    else if (n->code == N_MODULE)
      fprintf (f, ": the top scope");
    else
      fprintf (f, ": higher scope node %lu", ((struct node_scope *) n->attr)->scope->uid);
    if (n->code == N_STRUCT || n->code == N_UNION)
      fprintf (f, "\n");
    else
      fprintf (f, ", size = %llu\n", (unsigned long long) ((struct node_scope *) n->attr)->size);
    print_ops (f, n, indent, attr_p);
    break;
  case N_SWITCH:
    if (attr_p) {
      fprintf (f, ": ");
      print_type (f, &((struct switch_attr *) n->attr)->type);
    }
    fprintf (f, "\n");
    print_ops (f, n, indent, attr_p);
    break;
  case N_GOTO:
    if (attr_p)
      fprintf (f, ": target node %lu\n", ((node_t) n->attr)->uid);
    print_ops (f, n, indent, attr_p);
    break;
  case N_ENUM_CONST: 
    if (attr_p)
      fprintf (f, ": val = %lld\n", (long long) ((struct enum_value *) n->attr)->val);
    print_ops (f, n, indent, attr_p);
    break;
  default:
    abort ();
  }
}

typedef const char *char_ptr_t;

DEF_VARR (char_ptr_t);
static VARR (char_ptr_t) *headers;
static VARR (char_ptr_t) *system_headers;

static void init_options (int argc, const char *argv[],
			  int (*other_option_func) (int, int, const char **)) {
  const char *str;
  
  debug_p = verbose_p = asm_p = no_prepro_p = prepro_only_p = FALSE;
  VARR_CREATE (char_ptr_t, headers, 0);
  VARR_CREATE (char_ptr_t, system_headers, 0);
  for (int i = 1; i < argc; i++) {
    if (strcmp (argv[i], "-d") == 0) {
      verbose_p = debug_p = TRUE;
    } else if (strcmp (argv[i], "-S") == 0) {
      asm_p = TRUE;
    } else if (strcmp (argv[i], "-v") == 0) {
      verbose_p = TRUE;
    } else if (strcmp (argv[i], "-E") == 0) {
      prepro_only_p = TRUE;
    } else if (strcmp (argv[i], "-fpreprocessed") == 0) {
      no_prepro_p = TRUE;
    } else if (strncmp (argv[i], "-I", 2) == 0) {
      char *i_dir;
      const char *dir = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;
      
      if (*dir == '\0')
	continue;
      i_dir = reg_malloc (strlen (dir) + 1);
      strcpy (i_dir, dir);
      VARR_PUSH (char_ptr_t, headers, i_dir);
      VARR_PUSH (char_ptr_t, system_headers, i_dir);
    } else if (strncmp (argv[i], "-U", 2) == 0 || strncmp (argv[i], "-D", 2) == 0) {
      int ok_p;
      pos_t pos;
      token_t t, id;
      struct macro macro;
      macro_t tab_m;
      VARR (token_t) *repl;
      const char *bound, *def = strlen (argv[i]) == 2 && i + 1 < argc ? argv[++i] : argv[i] + 2;

      pos.fname = "<command line>"; pos.lno = 1; pos.ln_pos = 0;
      VARR_CREATE (token_t, repl, 16);
      if (argv[i][1] == 'U' || (bound = strchr (def, '=')) == NULL) {
	id = new_id_token (pos, def);
	VARR_PUSH (token_t, repl, new_token (pos, "1", T_NUMBER, N_IGNORE));
      } else {
	VARR_TRUNC (char, temp_string, 0);
	while (def < bound)
	  VARR_PUSH (char, temp_string, *def++);
	VARR_PUSH (char, temp_string, '\0');
	id = new_id_token (pos, VARR_ADDR (char, temp_string));
	for (def++; *def != '\0'; def++)
	  VARR_PUSH (char, temp_string, *def);
	VARR_PUSH (char, temp_string, '\0');
	reverse (temp_string);
	set_string_stream (VARR_ADDR (char, temp_string), pos, NULL);
	while ((t = get_next_pptoken ())->code != T_EOF && t->code != T_EOU)
	  VARR_PUSH (token_t, repl, t);
      }
      if ((ok_p = isalpha (id->repr[0]))) {
	for (int i = 1; id->repr[i] != '\0'; i++)
	  if (! isalnum (id->repr[i])) {
	    ok_p = FALSE;
	    break;
	  }
      }
      if (! ok_p) {
	fprintf (stderr, "macro name %s is not an identifier\n", id->repr);
      } else {
	macro.id = id;
	if (argv[i][1] == 'U') {
	  HTAB_DO (macro_t, macro_tab, &macro, HTAB_DELETE, tab_m);
	} else {
	  if (HTAB_DO (macro_t, macro_tab, &macro, HTAB_FIND, tab_m)) {
	    if (! replacement_eq_p (tab_m->replacement, repl))
	      fprintf (stderr, "warning -- redefinition of macro %s on the command line\n", id->repr);
	    HTAB_DO (macro_t, macro_tab, &macro, HTAB_DELETE, tab_m);
	  }
	  new_macro (macro.id, NULL, repl);
	}
      }
    } else {
      i = other_option_func (i, argc, argv);
    }
  }
  VARR_PUSH (char_ptr_t, headers, NULL);
  for (int i = 0; i < sizeof (standard_include_dirs) / sizeof (char *); i++) {
    VARR_TRUNC (char, temp_string, 0);
    add_to_temp_string (SOURCEDIR); add_to_temp_string (standard_include_dirs[i]);
    str = uniq_str (VARR_ADDR (char, temp_string));
    VARR_PUSH (char_ptr_t, system_headers, str);
    VARR_TRUNC (char, temp_string, 0);
    add_to_temp_string (INSTALLDIR); add_to_temp_string ("../");
    add_to_temp_string (standard_include_dirs[i]);
    str = uniq_str (VARR_ADDR (char, temp_string));
    VARR_PUSH (char_ptr_t, system_headers, str);
  }
#ifdef __linux__
  VARR_PUSH (char_ptr_t, system_headers, "/usr/include");
#endif
  VARR_PUSH (char_ptr_t, system_headers, NULL);
  header_dirs = (const char **) VARR_ADDR (char_ptr_t, headers);
  system_header_dirs = (const char **) VARR_ADDR (char_ptr_t, system_headers);
}

static void finish_options (void) {
  VARR_DESTROY (char_ptr_t, headers);
  VARR_DESTROY (char_ptr_t, system_headers);
}

static int curr_module_num;

static void compile_init (int argc, const char *argv[],
			  int (*getc_func) (void), void (*ungetc_func) (int),
			  int other_option_func (int, int, const char **)) {
  n_errors = n_warnings = 0;
  curr_module_num = 0;
  c_getc = getc_func; c_ungetc = ungetc_func;
  parse_init ();
  curr_scope = NULL;
  context_init ();
  init_options (argc, argv, other_option_func);
  VARR_CREATE (node_t, call_nodes, 128); /* used in context and gen */
}

#include <sys/time.h>

static double
real_usec_time(void) {
  struct timeval  tv;

  gettimeofday(&tv, NULL);
  return tv.tv_usec + tv.tv_sec * 1000000.0;
}

static const char *get_module_name (void) {
  static char str[50];

  sprintf (str, "M%d", curr_module_num);
  return str;
}

static int compile (const char *source_name) {
  double start_time = real_usec_time ();
  node_t r;
  unsigned n_error_before;
  
  if (verbose_p)
    fprintf (stderr, "compiler init end           -- %.0f usec\n", real_usec_time () - start_time);
  add_stream (NULL, source_name);
  add_standard_includes ();
  pre (source_name);
  if (verbose_p)
    fprintf (stderr, "  preprocessor end    -- %.0f usec\n", real_usec_time () - start_time);
  if (! prepro_only_p) {
    r = parse ();
    if (verbose_p)
      fprintf (stderr, "  parser end          -- %.0f usec\n", real_usec_time () - start_time);
    if (verbose_p && n_errors)
      fprintf (stderr, "parser - FAIL\n");
    n_error_before = n_errors;
    context (r);
    if (n_errors > n_error_before) {
      if (debug_p)
	print_node (stderr, r, 0, FALSE);
      if (verbose_p)
	fprintf (stderr, "context checker - FAIL\n");
    } else {
      if (debug_p)
	print_node (stderr, r, 0, TRUE);
      if (verbose_p)
	fprintf (stderr, "  context checker end -- %.0f usec\n", real_usec_time () - start_time);
      MIR_init ();
      MIR_new_module (get_module_name ());
      generate_mir (r);
      if (asm_p)
	MIR_output (stderr);
      MIR_finish_module ();
      MIR_finish ();
      if (verbose_p)
	fprintf (stderr, "  generator end       -- %.0f usec\n", real_usec_time () - start_time);
    }
  }
  if (verbose_p)
    fprintf (stderr, "compiler end                -- %.0f usec\n", real_usec_time () - start_time);
  return n_errors == 0;
}

static void compile_finish (void) {
  parse_finish ();
  context_finish ();
  finish_options ();
  VARR_DESTROY (node_t, call_nodes);
}

/* ------------------------- Small test example ------------------------- */
#ifdef TEST_C2MIR
static size_t curr_char;
static const char *code;

static int t_getc (void) {
  int c = code[curr_char];

  if (c == 0)
    c = EOF;
  else
    curr_char++;
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

static const char *source_name;
static VARR (char) *input;

static int other_option_func (int i, int argc, const char *argv[]) {
  FILE *f = NULL;
  int c;
  
  if (strcmp (argv[i], "-i") == 0) {
    f = stdin; source_name = "<stdin>";
  } else if (strcmp (argv[i], "-c") == 0 && i + 1 < argc) {
    code = argv[++i]; source_name = "<command-line>";
  } else if (*argv[i] != '-') {
    source_name = argv[i];
    if ((f = fopen (argv[i], "r")) == NULL) {
      error (no_pos, "can not open %s -- goodbye", argv[i]);
      exit (1);
    }
  } else {
    finish_options ();
    error (no_pos, "unknow command line option %s (use -h for usage) -- goodbye", argv[i]);
    exit (1);
  }
  if (f) {
    while ((c = getc (f)) != EOF)
      VARR_PUSH (char, input, c);
    VARR_PUSH (char, input, 0);
    code = VARR_ADDR (char, input);
    fclose (f);
  }
  return i;
}

int main (int argc, const char *argv[]) {
  int ok_p;
  
  code = NULL; source_name = NULL;
  VARR_CREATE (char, input, 100);
  curr_char = 0;
  compile_init (argc, argv, t_getc, t_ungetc, other_option_func);
  if (code == NULL) {
    code =
"int printf (const char *, ...);\n"
"#define SieveSize 819000\n"
"int sieve (void) {\n"
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
    source_name = "<example>";
  }
  assert (source_name != NULL);
  ok_p = compile (source_name);
  compile_finish ();
  VARR_DESTROY (char, input);
  return ! ok_p;
}
#endif
