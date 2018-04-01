#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <setjmp.h>

static void util_error (const char *message);
#define MIR_VARR_ERROR util_error
#define MIR_HTAB_ERROR MIR_VARR_ERROR 

#include "mir-varr.h"
#include "mir-htab.h"
#include "mir-mum.h"
#include "mir-read.h"

static void util_error (const char *message) { (*MIR_get_error_func ()) (MIR_alloc_error, message); }

static size_t curr_line_num;

typedef struct insn_name {
  const char *name;
  MIR_insn_code_t code;
} insn_name_t;

static int insn_name_eq (insn_name_t in1, insn_name_t in2) { return strcmp (in1.name, in2.name) == 0; }
static htab_hash_t insn_name_hash (insn_name_t in) { return mum_hash (in.name, strlen (in.name), 0x42); }

DEF_HTAB (insn_name_t);
static HTAB (insn_name_t) *insn_name_tab;

enum token_code { TC_INT, TC_FLOAT, TC_DOUBLE, TC_NAME, TC_STR, TC_NL, TC_EOF, TC_LEFT_PAR, TC_RIGHT_PAR, TC_COMMA, TC_SEMICOL, TC_COL };

typedef struct token {
  enum token_code code;
  union {
    int64_t i;
    float f;
    double d;
    const char *name;
    const char *str;
  } u;
} token_t;

DEF_VARR (char);
static VARR (char) *token_text;

static jmp_buf error_jmp_buf;

static void (*read_error_func) (MIR_error_type_t error_type, const char *message);

static void default_read_error_func (MIR_error_type_t error_type, const char *message) {
  fprintf (stderr, "%s\n", message);
}

static void MIR_NO_RETURN process_error (enum MIR_error_type error_type, const char *message) {
  (*read_error_func) (error_type, message);
  longjmp (error_jmp_buf, TRUE);
}

MIR_read_error_func_t MIR_get_read_error_func (void) { return read_error_func; }

void MIR_set_read_error_func (MIR_read_error_func_t func) { read_error_func = func; }

/* Read number using GET_CHAR and UNGET_CHAR and already read
   character CH.  It should be guaranted that the input has a righ
   prefix (+|-)?[0-9].  Return base, float and double flag through
   BASE, FLOAT_P, DOUBLE_P.  Put number representation (0x or 0X
   prefix is removed) into TOKEN_TEXT.  */
static void read_number (int ch, int get_char (void), void unget_char (int),
			 int *base, int *float_p, int *double_p) {
  enum read_number_code {NUMBER_OK, ABSENT_EXPONENT, NON_DECIMAL_FLOAT, WRONG_OCTAL_INT} err_code = NUMBER_OK;
  int dec_p, hex_p, hex_char_p;
  
  *base = 10;
  *double_p = *float_p = FALSE;
  if (ch == '+' || ch == '-') {
    VARR_PUSH (char, token_text, ch);
    ch = get_char ();
  }
  assert ('0' <= ch && ch <= '9');
  if (ch == '0') {
    ch = get_char ();
    if (ch != 'x' && ch != 'X') {
      *base = 8;
      unget_char (ch);
      ch = '0';
    } else {
      ch = get_char ();
      *base = 16;
    }
  }
  dec_p = hex_p = FALSE;
  for (;;) {
    if (ch != '_')
      VARR_PUSH (char, token_text, ch);
    ch = get_char ();
    if (ch == '8' || ch == '9')
      dec_p = TRUE;
    hex_char_p = (('a' <= ch && ch <= 'f') || ('A' <= ch && ch <= 'F'));
    if (ch != '_' && ! isdigit (ch) && (*base != 16 || ! hex_char_p))
      break;
    if (hex_char_p)
      hex_p = TRUE;
  }
  assert (*base == 16 || ! hex_p);
  if (ch == '.') {
    *double_p = TRUE;
    do {
      if (ch != '_')
	VARR_PUSH (char, token_text, ch);
      ch = get_char ();
    } while (isdigit (ch) || ch == '_');
  }
  if (ch == 'e' || ch == 'E') {
    *double_p = TRUE;
    ch = get_char ();
    if (ch != '+' && ch != '-' && ! isdigit (ch))
      err_code = ABSENT_EXPONENT;
    else {
      VARR_PUSH (char, token_text, 'e');
      if (ch == '+' || ch == '-') {
	VARR_PUSH (char, token_text, '-');
	ch = get_char ();
	if (! isdigit (ch))
	  err_code = ABSENT_EXPONENT;
      }
      if (err_code == NUMBER_OK)
	do {
	  if (ch != '_')
	    VARR_PUSH (char, token_text, ch);
	  ch = get_char ();
	} while (isdigit (ch) || ch == '_');
    }
  }
  if (*double_p) {
    if (*base == 16)
      err_code = NON_DECIMAL_FLOAT;
    else if (ch == 'f' || ch == 'F') {
      *float_p = TRUE; *double_p = FALSE;
    }
  } else if (*base == 8 && dec_p)
    err_code = WRONG_OCTAL_INT;
  VARR_PUSH (char, token_text, '\0');
  unget_char (ch);
}

static const char *input_string;
static size_t input_string_char_num;

static int get_string_char (void) {
  int ch = input_string[input_string_char_num];

  if (ch == '\0')
    return EOF;
  input_string_char_num++;
  return ch;
}

static void unget_string_char (int ch) {
  if (input_string_char_num == 0 || ch == EOF)
    return;
  input_string_char_num--;
  assert (input_string[input_string_char_num] == ch);
}

static token_t read_token (int (*get_char) (void), void (*unget_char) (int)) {
  int ch;
  token_t token;
  
  for (;;) {
    ch = get_char ();
    switch (ch) {
    case EOF:
      token.code = TC_EOF;
      return token;
    case ' ': case '\t':
      break;
    case '#':
      while ((ch = get_char ()) != '\n' && ch != EOF)
	;
      /* Fall through: */
    case '\n':
      curr_line_num++;
      token.code = TC_NL;
      return token;
      break;
    case '(':
      token.code = TC_LEFT_PAR;
      return token;
      break;
    case ')':
      token.code = TC_RIGHT_PAR;
      return token;
      break;
    case ',':
      token.code = TC_COMMA;
      return token;
    case ';':
      token.code = TC_SEMICOL;
      return token;
    case ':':
      token.code = TC_COL;
      return token;
    default:
      VARR_TRUNC (char, token_text, 0);
      if (isalpha (ch) || ch == '_') {
	do {
	  VARR_PUSH (char, token_text, ch);
	  ch = get_char ();
	} while (isalpha (ch) || isdigit (ch) || ch == '_');
	VARR_PUSH (char, token_text, '\0');
	unget_char (ch);
	token.u.str = _MIR_uniq_string (VARR_ADDR (char, token_text));
	token.code = TC_NAME;
	return token;
      } else if (ch == '+' || ch == '-' || isdigit (ch)) {
	const char *repr;
	char *end;
	int next_ch, base, float_p, double_p;
	float f;
	double d;
	int64_t i;
	
	if (ch == '+' || ch == '-') {
	  next_ch = get_char ();
	  if (! isdigit (next_ch))
	    process_error (MIR_syntax_error, "no number after a sign");
	  unget_char (next_ch);
	}
	read_number (ch, get_char, unget_char, &base, &float_p, &double_p);
	repr = VARR_ADDR (char, token_text);
	errno = 0;
	if (float_p) {
	  token.code = TC_FLOAT;
	  token.u.f = strtof (repr, &end);
	} else if (double_p) {
	  token.code = TC_DOUBLE;
	  token.u.d = strtod (repr, &end);
	} else {
	  token.code = TC_INT;
	  token.u.i = sizeof (long) == sizeof (int64_t) ? strtol (repr, &end, base) : strtoll (repr, &end, base);
	}
	assert (*end == '\0');
	if (errno != 0)
	  ;
	return token;
      } else {
	process_error (MIR_syntax_error, "wrong char");
      }
    }
  }
}

typedef const char *label_name_t;
DEF_VARR (label_name_t);
static VARR (label_name_t) *label_names;

typedef struct label_desc {
  const char *name;
  MIR_label_t label;
} label_desc_t;

DEF_HTAB (label_desc_t);
static HTAB (label_desc_t) *label_desc_tab;

static int label_eq (label_desc_t l1, label_desc_t l2) { return strcmp (l1.name, l2.name) == 0; }
static htab_hash_t label_hash (label_desc_t l) { return mum_hash (l.name, strlen (l.name), 0x42); }

static MIR_label_t create_label_desc (const char *name) {
  MIR_label_t label;
  label_desc_t label_desc;

  label_desc.name = name;
  if (HTAB_DO (label_desc_t, label_desc_tab, label_desc, HTAB_FIND, label_desc)) {
    label = label_desc.label;
  } else {
    label_desc.label = label = MIR_new_label ();
    HTAB_DO (label_desc_t, label_desc_tab, label_desc, HTAB_INSERT, label_desc);
  }
  return label;
}

DEF_VARR (MIR_op_t);
static VARR (MIR_op_t) *insn_ops;

DEF_VARR (MIR_var_t);
static VARR (MIR_var_t) *func_vars;

MIR_type_t MIR_str2type (const char *type_name) {
  if (strcmp (type_name, "i64") == 0)
    return MIR_I64;
  if (strcmp (type_name, "f") == 0)
    return MIR_F;
  if (strcmp (type_name, "d") == 0)
    return MIR_D;
  if (strcmp (type_name, "i32") == 0)
    return MIR_I32;
  if (strcmp (type_name, "u32") == 0)
    return MIR_U32;
  if (strcmp (type_name, "i16") == 0)
    return MIR_I16;
  if (strcmp (type_name, "u16") == 0)
    return MIR_U16;
  if (strcmp (type_name, "i8") == 0)
    return MIR_I8;
  if (strcmp (type_name, "u8") == 0)
    return MIR_U8;
  return MIR_T_BOUND;
}

static MIR_error_func_t saved_error_func;

/* Syntax:
     program: { insn / sep }
     sep : ';' | NL
     insn : {label ':'}* [ code [ {op / ','} ] ]
     label : name
     code : name
     op : name | int | float | double | mem | str
     mem : type ':' addr
     addr : disp
          | [ disp ] '(' sib ')'
     sib : name | [ name ] ',' name [ ',' scale]
     disp : int | name
     scale : int

*/

MIR_item_t MIR_read_string (const char *str) {
  token_t t;
  const char *name;
  MIR_item_t func = NULL;
  MIR_insn_code_t insn_code;
  MIR_insn_t insn;
  MIR_type_t type;
  MIR_op_t op, *op_addr;
  MIR_label_t label;
  MIR_var_t var;
  size_t n;
  int64_t i, frame_size, nargs, nlocals;
  int func_p, end_func_p, read_p, disp_p;
  insn_name_t in, el;

  saved_error_func = MIR_get_error_func ();
  MIR_set_error_func (process_error);
  input_string = str;
  input_string_char_num = 0;
  t.code = TC_NL;
  for (;;) {
    if (setjmp (error_jmp_buf)) {
      while (t.code != TC_NL && t.code != EOF)
	t = read_token (get_string_char, unget_string_char);
      if (t.code == TC_EOF)
	break;
    }
    VARR_TRUNC (label_name_t, label_names, 0);
    t = read_token (get_string_char, unget_string_char);
    while (t.code == TC_NL)
      t = read_token (get_string_char, unget_string_char);
    if (t.code == TC_EOF)
      break;
    for (;;) { /* label_names */
      if (t.code != TC_NAME)
	process_error (MIR_syntax_error, "insn should start with label or insn name");
      name = t.u.name;
      t = read_token (get_string_char, unget_string_char);
      if (t.code != TC_COL)
	break;
      VARR_PUSH (label_name_t, label_names, name);
      t = read_token (get_string_char, unget_string_char);
      if (t.code == TC_NL)
	t = read_token (get_string_char, unget_string_char); /* label_names without insn */
    }
    end_func_p = func_p = FALSE;
    if (strcmp (name, "func") == 0) {
      func_p = TRUE;
      if (VARR_LENGTH (label_name_t, label_names) != 1)
	process_error (MIR_syntax_error, "only one label should be used for func");
    } else if (strcmp (name, "endfunc") == 0) {
      end_func_p = TRUE;
      if (VARR_LENGTH (label_name_t, label_names) != 0)
	process_error (MIR_syntax_error, "endfunc should have no labels");
    } else {
      in.name = name;
      if (! HTAB_DO (insn_name_t, insn_name_tab, in, HTAB_FIND, el))
	process_error (MIR_syntax_error, "Unknown insn");
      insn_code = el.code;
      for (n = 0; n < VARR_LENGTH (label_name_t, label_names); n++) {
	label = create_label_desc (VARR_GET (label_name_t, label_names, n));
	if (func != NULL)
	  MIR_append_insn (func, label);
      }
    }
    VARR_TRUNC (MIR_op_t, insn_ops, 0);
    for (;;) { /* ops */
      if (t.code == TC_NL || t.code == TC_SEMICOL) {
	/* insn end */
	break;
      }
      read_p = TRUE;
      switch (t.code) {
      case TC_NAME: {
	name = t.u.name;
	t = read_token (get_string_char, unget_string_char);
	read_p = FALSE;
	if (t.code != TC_COL) {
	  if (! end_func_p && ! func_p && MIR_branch_code_p (insn_code)
	      && VARR_LENGTH (MIR_op_t, insn_ops) == 0) {
	    op = MIR_new_label_op (create_label_desc (name));
	  } else {
	    op.mode = MIR_OP_REG;
	    op.u.reg = MIR_reg (name);
	  }
	  break;
	}
	/* Memory or arg */
	type = MIR_str2type (name);
	if (type == MIR_T_BOUND)
	  process_error (MIR_syntax_error, "Unknown type");
	else if (func_p && type != MIR_I64 && type != MIR_F && type != MIR_D)
	  process_error (MIR_syntax_error, "wrong type for arg or local");
	t = read_token (get_string_char, unget_string_char);
	op.mode = MIR_OP_MEM;
	op.u.mem.type = type; op.u.mem.scale = 1;
	op.u.mem.base = op.u.mem.index = 0; op.u.mem.disp = 0;
	if (func_p) {
	  if (t.code != TC_NAME)
	    process_error (MIR_syntax_error, "wrong arg or local");
	  op.u.mem.disp = (MIR_disp_t) t.u.name;
	  t = read_token (get_string_char, unget_string_char);
	} else {
	  if (t.code == TC_INT) {
	    op.u.mem.disp = t.u.i;
	    t = read_token (get_string_char, unget_string_char);
	  } else if (t.code == TC_NAME) {
	    op.u.mem.disp = (MIR_disp_t) t.u.name;
	    t = read_token (get_string_char, unget_string_char);
	  }
	  if (t.code == TC_LEFT_PAR) {
	    t = read_token (get_string_char, unget_string_char);
	    if (t.code == TC_NAME) {
	      op.u.mem.base = MIR_reg (t.u.name);
	      t = read_token (get_string_char, unget_string_char);
	    }
	    if (t.code == TC_COMMA) {
	      t = read_token (get_string_char, unget_string_char);
	      if (t.code != TC_NAME)
		process_error (MIR_syntax_error, "wrong index");
	      op.u.mem.index = MIR_reg (t.u.name);
	      t = read_token (get_string_char, unget_string_char);
	      if (t.code == TC_COMMA) {
		t = read_token (get_string_char, unget_string_char);
		if (t.code != TC_INT)
		  process_error (MIR_syntax_error, "wrong index");
		if (t.u.i != 1 && t.u.i != 2 && t.u.i != 4 && t.u.i != 8)
		  process_error (MIR_syntax_error, "scale is not 1, 2, 4, or 8");
		op.u.mem.scale = t.u.i;
		t = read_token (get_string_char, unget_string_char);
	      }
	    }  
	    if (t.code != TC_RIGHT_PAR)
	      process_error (MIR_syntax_error, "wrong memory op");
	    t = read_token (get_string_char, unget_string_char);
	  } else if (! disp_p)
	    process_error (MIR_syntax_error, "wrong memory");
	}
	break;
      }
      case TC_INT:
	op.mode = MIR_OP_INT;
	op.u.i = t.u.i;
	break;
      case TC_FLOAT:
	op.mode = MIR_OP_FLOAT;
	op.u.f = t.u.f;
	break;
      case TC_DOUBLE:
	op.mode = MIR_OP_DOUBLE;
	op.u.d = t.u.d;
	break;
      case TC_STR:
	abort ();
      default:
	break;
      }
      VARR_PUSH (MIR_op_t, insn_ops, op);
      if (read_p)
	t = read_token (get_string_char, unget_string_char);
      if (t.code != TC_COMMA)
	break;
      t = read_token (get_string_char, unget_string_char);
    }
    if (t.code != TC_NL && t.code != TC_EOF && t.code != TC_SEMICOL)
      process_error (MIR_syntax_error, "wrong insn end");
    if (func_p) {
      VARR_TRUNC (MIR_var_t, func_vars, 0);
      if (func != NULL)
	process_error (MIR_syntax_error, "nested func");
      op_addr = VARR_ADDR (MIR_op_t, insn_ops);
      if ((n = VARR_LENGTH (MIR_op_t, insn_ops)) < 3)
	process_error (MIR_syntax_error, "too few params in func");
      if (op_addr[0].mode != MIR_OP_INT || (frame_size = op_addr[0].u.i) < 0)
	process_error (MIR_syntax_error, "wrong frame size");
      if (op_addr[1].mode != MIR_OP_INT || (nargs = op_addr[1].u.i) < 0)
	process_error (MIR_syntax_error, "wrong args number");
      if (op_addr[2].mode != MIR_OP_INT || (nlocals = op_addr[2].u.i) < 0)
	process_error (MIR_syntax_error, "wrong local number");
      if (nargs + nlocals != n - 3)
	process_error (MIR_syntax_error, "discrepency in number of args and locals and number of their names");
      for (i = 0; i < nargs + nlocals; i++) {
	assert (op_addr[i + 3].mode == MIR_OP_MEM);
	var.type = op_addr[i + 3].u.mem.type;
	var.name = (const char *) op_addr[i + 3].u.mem.disp;
	VARR_PUSH (MIR_var_t, func_vars, var);
      }
      func = MIR_new_func_arr (VARR_GET (label_name_t, label_names, 0), frame_size, nargs, nlocals, VARR_ADDR (MIR_var_t, func_vars));
      HTAB_CLEAR (label_desc_t, label_desc_tab);
    } else if (end_func_p) {
      if (func == NULL)
	process_error (MIR_syntax_error, "standalone endfunc");
      if (VARR_LENGTH (MIR_op_t, insn_ops) != 0)
	process_error (MIR_syntax_error, "endfunc should have no params");
      func = NULL;
      MIR_finish_func ();
    } else {
      insn = MIR_new_insn_arr (insn_code, VARR_LENGTH (MIR_op_t, insn_ops), VARR_ADDR (MIR_op_t, insn_ops));
      if (func != NULL)
	MIR_append_insn (func, insn);
    }
  }
  if (func != NULL)
    process_error (MIR_syntax_error, "absent endfunc");
  MIR_set_error_func (saved_error_func);
  return NULL;
}

void MIR_read_init (void) {
  insn_name_t in, el;
  size_t i;
  
  read_error_func = default_read_error_func;
  VARR_CREATE (char, token_text, 0);
  VARR_CREATE (label_name_t, label_names, 0);
  VARR_CREATE (MIR_op_t, insn_ops, 0);
  VARR_CREATE (MIR_var_t, func_vars, 0);
  HTAB_CREATE (label_desc_t, label_desc_tab, 100, label_hash, label_eq);
  HTAB_CREATE (insn_name_t, insn_name_tab, MIR_INSN_BOUND, insn_name_hash, insn_name_eq);
  for (i = 0; i < MIR_INSN_BOUND; i++) {
    in.code = i;
    in.name = MIR_insn_name (i);
    HTAB_DO (insn_name_t, insn_name_tab, in, HTAB_INSERT, el);
  }
}

void MIR_read_finish (void) {
  VARR_DESTROY (char, token_text);
  VARR_DESTROY (label_name_t, label_names);
  VARR_DESTROY (MIR_op_t, insn_ops);
  VARR_DESTROY (MIR_var_t, func_vars);
  HTAB_DESTROY (label_desc_t, label_desc_tab);
  HTAB_DESTROY (insn_name_t, insn_name_tab);
}

#ifdef MIR_TEST_READ

int main (void) {
  MIR_init ();
  MIR_read_init ();
  MIR_read_string ("\n\
loop: func 0, 1, 1, i64:limit, i64:count # a comment\n\
\n\
       mov count, 0\n\
       bge L1, count, limit\n\
L2:    # a separate label\n\
       add count, count, 1; blt L2, count, limit # 2 insn on a line\n\
L1:    ret count  # label with insn\n\
       endfunc\n\
  ");
  MIR_read_string ("\n\
sieve: func 819000, 0, 7, i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags\n\
       sub flags, fp, 819000\n\
       mov iter, 0\n\
loop:  bge fin, iter, 1000\n\
       mov count, 0;  mov i, 0\n\
loop2: bgt fin2, i, 819000\n\
       mov u8:(flags, i), 1;  add i, i, 1\n\
       jmp loop2\n\
fin2:  mov i, 0\n\
loop3: bgt fin3, i, 819000\n\
       beq cont3, u8:(flags,i), 0\n\
       add temp, i, i;  add prime, temp, 3;  add k, i, prime\n\
loop4: bgt fin4, k, 819000\n\
       mov u8:(flags, k), 0;  add k, k, prime\n\
       jmp loop4\n\
fin4:  add count, count, 1\n\
cont3: add i, i, 1\n\
       jmp loop3\n\
fin3:  add iter, iter, 1\n\
       jmp loop\n\
fin:   ret count\n\
       endfunc\n\
");
  MIR_output (stderr);
  fprintf (stderr, "+++++++++++++After sieve simplification:\n");
  MIR_simplify_func (DLIST_TAIL (MIR_item_t, MIR_items));
  MIR_output (stderr);
  MIR_read_finish ();
  MIR_finish ();
  return 0;
}
#endif
