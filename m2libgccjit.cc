#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <libgccjit.h>
#include <climits>
#include <map>
#include "mir.h"

#undef NDEBUG
#include <assert.h>

static gcc_jit_type *
get_jit_type_for_mir_type (gcc_jit_context *jit_ctxt,
			   MIR_type_t mir_type)
{
  switch (mir_type)
    {
    default:
      assert (0); // TODO
    case MIR_T_I8:
      return gcc_jit_context_get_int_type (jit_ctxt, 1, 1);
    case MIR_T_U8:
      return gcc_jit_context_get_int_type (jit_ctxt, 1, 0);
    case MIR_T_I16:
      return gcc_jit_context_get_int_type (jit_ctxt, 2, 1);
    case MIR_T_U16:
      return gcc_jit_context_get_int_type (jit_ctxt, 2, 0);
    case MIR_T_I32:
      return gcc_jit_context_get_int_type (jit_ctxt, 4, 1);
    case MIR_T_U32:
      return gcc_jit_context_get_int_type (jit_ctxt, 4, 0);
    case MIR_T_I64:
      return gcc_jit_context_get_int_type (jit_ctxt, 8, 1);
    case MIR_T_U64:
      return gcc_jit_context_get_int_type (jit_ctxt, 8, 0);
    }
}

static gcc_jit_type *
get_lval_type (gcc_jit_lvalue *lval)
{
  return gcc_jit_rvalue_get_type (gcc_jit_lvalue_as_rvalue (lval));
}

class jit_module_conversion
{
public:
  jit_module_conversion (gcc_jit_context *jit_ctxt,
			 MIR_context_t mir_ctxt,
			 int verbose)
  : m_jit_ctxt (jit_ctxt), m_mir_ctxt (mir_ctxt), m_verbose (verbose)
  {}

  void add_function (MIR_func_t func);
  void add_bss_item (MIR_item_t item);

  gcc_jit_lvalue *
  mir_bss_item_to_lvalue (MIR_item_t item) const
  {
    mir_assert (item->item_type == MIR_bss_item);
    return (*m_map_bss_item_to_global.find (item)).second;
  }

  //private:
  gcc_jit_context *m_jit_ctxt;
  MIR_context_t m_mir_ctxt;
  int m_verbose;
  std::map<MIR_item_t, gcc_jit_lvalue *> m_map_bss_item_to_global;
};

/* A class encapsulating the conversion of a specific MIR_func_t
   to a gcc_jit_context.  */

class jit_func_conversion
{
 public:
  jit_func_conversion (jit_module_conversion *modconv, MIR_func_t func)
  : m_modconv (modconv),
    m_jit_ctxt (modconv->m_jit_ctxt),
    m_bool_t (gcc_jit_context_get_type (m_jit_ctxt, GCC_JIT_TYPE_BOOL)),
    m_int8_t (gcc_jit_context_get_int_type (m_jit_ctxt, 1, 1)),
    m_int16_t (gcc_jit_context_get_int_type (m_jit_ctxt, 2, 1)),
    m_uint16_t (gcc_jit_context_get_int_type (m_jit_ctxt, 2, 0)),
    m_int32_t (gcc_jit_context_get_int_type (m_jit_ctxt, 4, 1)),
    m_uint32_t (gcc_jit_context_get_int_type (m_jit_ctxt, 4, 0)),
    m_int64_t (gcc_jit_context_get_int_type (m_jit_ctxt, 8, 1)),
    m_uint64_t (gcc_jit_context_get_int_type (m_jit_ctxt, 8, 0)),
    m_lvals_for_regs (NULL),
    m_return_type (NULL),
    m_jit_func (NULL),
    m_curr_block (NULL)
  {
    m_lvals_for_regs
      = (gcc_jit_lvalue **)calloc (VARR_LENGTH (MIR_var_t, func->vars),
				   sizeof (gcc_jit_lvalue *));
    gcc_jit_param **params
      = (gcc_jit_param **)calloc (func->nargs, sizeof (gcc_jit_param *));
    for (uint32_t arg_idx = 0; arg_idx  < func->nargs; arg_idx++)
      {
	MIR_var_t var = VARR_GET (MIR_var_t, func->vars, arg_idx);
	gcc_jit_type *type = get_jit_type_for_mir_type (m_jit_ctxt, var.type);
	params[arg_idx] = gcc_jit_context_new_param (m_jit_ctxt, NULL, type,
						     var.name);
	m_lvals_for_regs[arg_idx] = gcc_jit_param_as_lvalue (params[arg_idx]);
      }

    // Can only cope with 0 or 1 return values for now.
    if (func->nres > 1)
      assert (0); // TODO: error handling
    if (func->nres == 1)
      m_return_type = get_jit_type_for_mir_type (m_jit_ctxt,
						 func->res_types[0]);
    else
      m_return_type = gcc_jit_context_get_type (m_jit_ctxt, GCC_JIT_TYPE_VOID);

    m_jit_func
      = gcc_jit_context_new_function (m_jit_ctxt, NULL,
				      GCC_JIT_FUNCTION_EXPORTED,
				      m_return_type,
				      func->name,
				      func->nargs, params,
				      func->vararg_p);
    free (params);

    size_t i, nlocals;
    nlocals = VARR_LENGTH (MIR_var_t, func->vars) - func->nargs;
    for (i = 0; i < nlocals; i++) {
      MIR_var_t var = VARR_GET (MIR_var_t, func->vars, i + func->nargs);
      gcc_jit_type *type = get_jit_type_for_mir_type (m_jit_ctxt, var.type);
      gcc_jit_lvalue *jit_lval = gcc_jit_function_new_local (m_jit_func, NULL,
							     type, var.name);
      m_lvals_for_regs[func->nargs + i] = jit_lval;
      // FIXME: MIR_T_BLK?

      /* FIXME: how to map from MIR_var_t to MIR_reg_t?
	 I think there's an offset by 1.
	 new_func_arr has:
    create_func_reg (ctx, func, vars[i].name, i + 1,
                     type == MIR_T_F || type == MIR_T_D || type == MIR_T_LD ? type : MIR_T_I64,
                     FALSE);
      */
    }
    m_curr_block = gcc_jit_function_new_block (m_jit_func, "initial");
  }

  ~jit_func_conversion ()
  {
    free (m_lvals_for_regs);
  }

  void on_mir_label (MIR_insn_t insn)
  {
    mir_assert (insn->code == MIR_LABEL);
    MIR_op_t op = insn->ops[0];
    assert (op.mode == MIR_OP_INT);
    char buf[16];
    snprintf (buf, sizeof (buf), "L%" PRId64, op.u.i);
    gcc_jit_block *block = gcc_jit_function_new_block (m_jit_func, buf);
    m_map_label_to_block[insn] = block;
  }

  void on_mir_insn (MIR_insn_t insn)
  {
    mir_assert (insn != NULL);
    MIR_op_t *ops = insn->ops;
    switch (insn->code)
      {
      default:
	assert (0); // TODO
	break;
      case MIR_MOV:
      case MIR_FMOV:
      case MIR_DMOV: out_op2 (ops); break;
      case MIR_LDMOV:
	assert (0); // TODO
	break;
      case MIR_EXT8: out_ext (ops, m_int8_t); break;
      case MIR_EXT16:
	assert (0); // TODO
	break;
      case MIR_EXT32: out_ext (ops, m_int32_t); break;
      case MIR_UEXT8:
	assert (0); // TODO
	break;
      case MIR_UEXT16: out_ext (ops, m_uint16_t); break;
      case MIR_UEXT32:
	assert (0); // TODO
	break;
      case MIR_I2F:
	assert (0); // TODO
	break;
      case MIR_I2D:
	assert (0); // TODO
	break;
      case MIR_I2LD:
	assert (0); // TODO
	break;
      case MIR_UI2F:
	assert (0); // TODO
	break;
      case MIR_UI2D:
	assert (0); // TODO
	break;
      case MIR_UI2LD:
	assert (0); // TODO
	break;
      case MIR_F2I:
	assert (0); // TODO
	break;
      case MIR_D2I:
	assert (0); // TODO
	break;
      case MIR_LD2I:
	assert (0); // TODO
	break;
      case MIR_F2D:
	assert (0); // TODO
	break;
      case MIR_F2LD:
	assert (0); // TODO
	break;
      case MIR_D2F:
	assert (0); // TODO
	break;
      case MIR_D2LD:
	assert (0); // TODO
	break;
      case MIR_LD2F:
	assert (0); // TODO
	break;
      case MIR_LD2D:
	assert (0); // TODO
	break;
      case MIR_NEG:
	assert (0); // TODO
	break;
      case MIR_NEGS:
	assert (0); // TODO
	break;
      case MIR_FNEG:
	assert (0); // TODO
	break;
      case MIR_DNEG:
	assert (0); // TODO
	break;
      case MIR_LDNEG:
	assert (0); // TODO
	break;
      case MIR_ADD: out_op3 (ops, GCC_JIT_BINARY_OP_PLUS); break;
      case MIR_ADDS: out_sop3 (ops, GCC_JIT_BINARY_OP_PLUS); break;
      case MIR_FADD:
	assert (0); // TODO
	break;
      case MIR_DADD:
	assert (0); // TODO
	break;
      case MIR_LDADD:
	assert (0); // TODO
	break;
      case MIR_SUB:
	assert (0); // TODO
	break;
      case MIR_SUBS:
	out_sop3 (ops, GCC_JIT_BINARY_OP_MINUS);
	break;
      case MIR_FSUB:
	assert (0); // TODO
	break;
      case MIR_DSUB:
	assert (0); // TODO
	break;
      case MIR_LDSUB:
	assert (0); // TODO
	break;
      case MIR_MUL:
	assert (0); // TODO
	break;
      case MIR_MULS: out_sop3 (ops, GCC_JIT_BINARY_OP_MULT); break;
      case MIR_FMUL:
	assert (0); // TODO
	break;
      case MIR_DMUL:
	assert (0); // TODO
	break;
      case MIR_LDMUL:
	assert (0); // TODO
	break;
      case MIR_DIV:
	assert (0); // TODO
	break;
      case MIR_DIVS: out_sop3 (ops, GCC_JIT_BINARY_OP_DIVIDE); break;
      case MIR_UDIV:
	assert (0); // TODO
	break;
      case MIR_UDIVS:
	assert (0); // TODO
	break;
      case MIR_FDIV:
	assert (0); // TODO
	break;
      case MIR_DDIV:
	assert (0); // TODO
	break;
      case MIR_LDDIV:
	assert (0); // TODO
	break;
      case MIR_MOD:
	assert (0); // TODO
	break;
      case MIR_MODS: out_sop3 (ops, GCC_JIT_BINARY_OP_MODULO); break;
      case MIR_UMOD:
	assert (0); // TODO
	break;
      case MIR_UMODS:
	assert (0); // TODO
	break;
      case MIR_AND: out_op3 (ops, GCC_JIT_BINARY_OP_BITWISE_AND); break;
      case MIR_ANDS: out_sop3 (ops, GCC_JIT_BINARY_OP_BITWISE_AND); break;
      case MIR_OR: out_op3 (ops, GCC_JIT_BINARY_OP_BITWISE_OR); break;
      case MIR_ORS: out_sop3 (ops, GCC_JIT_BINARY_OP_BITWISE_OR); break;
      case MIR_XOR:
	assert (0); // TODO
	break;
      case MIR_XORS: out_sop3 (ops, GCC_JIT_BINARY_OP_BITWISE_XOR); break;
      case MIR_LSH: out_op3 (ops, GCC_JIT_BINARY_OP_LSHIFT); break;
      case MIR_LSHS: out_sop3 (ops, GCC_JIT_BINARY_OP_LSHIFT); break;
      case MIR_RSH:
	assert (0); // TODO
	break;
      case MIR_RSHS: out_sop3 (ops, GCC_JIT_BINARY_OP_RSHIFT); break;
      case MIR_URSH: out_uop3 (ops, GCC_JIT_BINARY_OP_RSHIFT); break;
      case MIR_URSHS: out_usop3 (ops, GCC_JIT_BINARY_OP_RSHIFT); break;
      case MIR_EQ:
	assert (0); // TODO
	break;
      case MIR_EQS:
	assert (0); // TODO
	break;
      case MIR_FEQ:
	assert (0); // TODO
	break;
      case MIR_DEQ:
	assert (0); // TODO
	break;
      case MIR_LDEQ:
	assert (0); // TODO
	break;
      case MIR_NE:
	assert (0); // TODO
	break;
      case MIR_NES:
	assert (0); // TODO
	break;
      case MIR_FNE:
	assert (0); // TODO
	break;
      case MIR_DNE:
	assert (0); // TODO
	break;
      case MIR_LDNE:
	assert (0); // TODO
	break;
      case MIR_LT:
	assert (0); // TODO
	break;
      case MIR_LTS:
	assert (0); // TODO
	break;
      case MIR_ULT:
	assert (0); // TODO
	break;
      case MIR_ULTS:
	assert (0); // TODO
	break;
      case MIR_FLT:
	assert (0); // TODO
	break;
      case MIR_DLT:
	assert (0); // TODO
	break;
      case MIR_LDLT:
	assert (0); // TODO
	break;
      case MIR_LE:
	assert (0); // TODO
	break;
      case MIR_LES:
	assert (0); // TODO
	break;
      case MIR_ULE:
	assert (0); // TODO
	break;
      case MIR_ULES:
	assert (0); // TODO
	break;
      case MIR_FLE:
	assert (0); // TODO
	break;
      case MIR_DLE:
	assert (0); // TODO
	break;
      case MIR_LDLE:
	assert (0); // TODO
	break;
      case MIR_GT:
	assert (0); // TODO
	break;
      case MIR_GTS:
	assert (0); // TODO
	break;
      case MIR_UGT:
	assert (0); // TODO
	break;
      case MIR_UGTS:
	assert (0); // TODO
	break;
      case MIR_FGT:
	assert (0); // TODO
	break;
      case MIR_DGT:
	assert (0); // TODO
	break;
      case MIR_LDGT:
	assert (0); // TODO
	break;
      case MIR_GE:
	assert (0); // TODO
	break;
      case MIR_GES:
	assert (0); // TODO
	break;
      case MIR_UGE:
	assert (0); // TODO
	break;
      case MIR_UGES:
	assert (0); // TODO
	break;
      case MIR_FGE:
	assert (0); // TODO
	break;
      case MIR_DGE:
	assert (0); // TODO
	break;
      case MIR_LDGE:
	assert (0); // TODO
	break;
      case MIR_JMP:
	{
	  gcc_jit_block *next_block = get_block_for_label (ops[0]);
	  if (m_curr_block)
	    gcc_jit_block_end_with_jump (m_curr_block, NULL, next_block);
	  m_curr_block = NULL;
	}
	break;
      case MIR_BT:
	{
	  gcc_jit_rvalue *condition = mir_op_to_rvalue (ops[1], m_int64_t);
	  out_branch (ops, condition);
	}
	break;
      case MIR_BTS:
	{
	  /* FIXME: I'm guessing about this one.  */
	  gcc_jit_rvalue *condition = mir_op_to_rvalue (ops[1], m_int32_t);
	  out_branch (ops, condition);
	}
	break;
      case MIR_BF:
	{
	  gcc_jit_rvalue *condition
	    = gcc_jit_context_new_unary_op (m_jit_ctxt, NULL,
					    GCC_JIT_UNARY_OP_LOGICAL_NEGATE,
					    m_int64_t,
					    mir_op_to_rvalue (ops[1],
							      m_int64_t));
	  out_branch (ops, condition);
	}
	break;
      case MIR_BFS:
	assert (0); // TODO
	break;
      case MIR_BEQ:
	assert (0); // TODO
	break;
      case MIR_BEQS: out_bscmp (ops, GCC_JIT_COMPARISON_EQ); break;
      case MIR_FBEQ:
	assert (0); // TODO
	break;
      case MIR_DBEQ:
	assert (0); // TODO
	break;
      case MIR_LDBEQ:
	assert (0); // TODO
	break;
      case MIR_BNE:
	assert (0); // TODO
	break;
      case MIR_BNES: out_bscmp (ops, GCC_JIT_COMPARISON_NE); break;
      case MIR_FBNE:
	assert (0); // TODO
	break;
      case MIR_DBNE:
	assert (0); // TODO
	break;
      case MIR_LDBNE:
	assert (0); // TODO
	break;
      case MIR_BLT:
	assert (0); // TODO
	break;
      case MIR_BLTS: out_bscmp (ops, GCC_JIT_COMPARISON_LT); break;
      case MIR_UBLT:
	assert (0); // TODO
	break;
      case MIR_UBLTS:
	assert (0); // TODO
	break;
      case MIR_FBLT:
	assert (0); // TODO
	break;
      case MIR_DBLT:
	assert (0); // TODO
	break;
      case MIR_LDBLT:
	assert (0); // TODO
	break;
      case MIR_BLE: out_bcmp (ops, GCC_JIT_COMPARISON_LE); break;
      case MIR_BLES: out_bscmp (ops, GCC_JIT_COMPARISON_LE); break;
      case MIR_UBLE:
	assert (0); // TODO
	break;
      case MIR_UBLES:
	assert (0); // TODO
	break;
      case MIR_FBLE:
	assert (0); // TODO
	break;
      case MIR_DBLE:
	assert (0); // TODO
	break;
      case MIR_LDBLE:
	assert (0); // TODO
	break;
      case MIR_BGT: out_bcmp (ops, GCC_JIT_COMPARISON_GT); break;
      case MIR_BGTS: out_bscmp (ops, GCC_JIT_COMPARISON_GT); break;
      case MIR_UBGT:
	assert (0); // TODO
	break;
      case MIR_UBGTS:
	assert (0); // TODO
	break;
      case MIR_FBGT:
	assert (0); // TODO
	break;
      case MIR_DBGT:
	assert (0); // TODO
	break;
      case MIR_LDBGT:
	assert (0); // TODO
	break;
      case MIR_BGE:
	assert (0); // TODO
	break;
      case MIR_BGES: out_bscmp (ops, GCC_JIT_COMPARISON_GE); break;
      case MIR_UBGE:
	assert (0); // TODO
	break;
      case MIR_UBGES:
	assert (0); // TODO
	break;
      case MIR_FBGE:
	assert (0); // TODO
	break;
      case MIR_DBGE:
	assert (0); // TODO
	break;
      case MIR_LDBGE:
	assert (0); // TODO
	break;
      case MIR_CALL:
	assert (0); // TODO
	break;
      case MIR_INLINE:
	assert (0); // TODO
	break;
      case MIR_SWITCH:
	assert (0); // TODO
	break;
      case MIR_RET:
	if (insn->nops != 0)
	  gcc_jit_block_end_with_return (m_curr_block, NULL,
					 mir_op_to_rvalue (ops[0],
							   m_return_type));
	else
	  gcc_jit_block_end_with_void_return (m_curr_block, NULL);
	m_curr_block = NULL;
	break;
      case MIR_ALLOCA:
	{
	  gcc_jit_function *builtin_alloca
	    = gcc_jit_context_get_builtin_function (m_jit_ctxt,
						    "__builtin_alloca");
	  /* TODO:
	     libgccjit.so: error: unimplemented primitive type for builtin: 48
	  */
	  gcc_jit_rvalue *arg = mir_op_to_rvalue (ops[1]);
	  gcc_jit_rvalue *call
	    = gcc_jit_context_new_call (m_jit_ctxt, NULL,
					builtin_alloca,
					1, &arg);
	  out_assign_to_dst (ops, call);
	}
	break;
      case MIR_BSTART:
	assert (0); // TODO
	break;
      case MIR_BEND:
	assert (0); // TODO
	break;
      case MIR_VA_ARG:
	assert (0); // TODO
	break;
      case MIR_VA_STACK_ARG:
	assert (0); // TODO
	break;
      case MIR_VA_START:
	assert (0); // TODO
	break;
      case MIR_VA_END:
	assert (0); // TODO
	break;
      case MIR_LABEL:
	{
	  gcc_jit_block *next_block = get_block_for_label (insn);
	  if (m_curr_block)
	    gcc_jit_block_end_with_jump (m_curr_block, NULL, next_block);
	  m_curr_block = next_block;
	}
	break;
      case MIR_UNSPEC:
	assert (0); // TODO
	break;

      }
#if 0
    fprintf (f, "\t%s", MIR_insn_name (ctx, insn->code));
    nops = MIR_insn_nops (ctx, insn);
    for (i = 0; i < nops; i++) {
      fprintf (f, i == 0 ? "\t" : ", ");
      MIR_output_op (ctx, f, insn->ops[i], func);
    }
    if (insn->code == MIR_UNSPEC)
      fprintf (f, " # %s", VARR_GET (MIR_proto_t, unspec_protos, insn->ops[0].u.u)->name);
    if (newline_p) fprintf (f, "\n");
#endif
  }

private:
  gcc_jit_rvalue *
  cast_to_int32_t (gcc_jit_rvalue *rval) const
  {
    return gcc_jit_context_new_cast (m_jit_ctxt, NULL, rval, m_int32_t);
  }

  gcc_jit_lvalue *
  mir_reg_to_lvalue (MIR_reg_t reg) const
  {
    // FIXME: note the offset by -1.
    return m_lvals_for_regs[reg - 1];
  }

  gcc_jit_rvalue *
  mir_reg_to_rvalue (MIR_reg_t reg) const
  {
    return gcc_jit_lvalue_as_rvalue (mir_reg_to_lvalue (reg));
  }

  gcc_jit_lvalue *
  mir_op_to_lvalue (MIR_op_t op) const
  {
    switch (op.mode)
      {
      default:
	assert (0);
      case MIR_OP_REG:
	return mir_reg_to_lvalue (op.u.reg);
      case MIR_OP_MEM:
	// TODO
	return NULL;
      }
  }

  gcc_jit_rvalue *
  mir_op_to_rvalue (MIR_op_t op) const
  {
    switch (op.mode)
      {
      default:
	assert (0);
	return NULL; // TODO
	break;
      case MIR_OP_REG:
	return mir_reg_to_rvalue (op.u.reg);
      case MIR_OP_INT:
	// FIXME: should by int64_t
	return gcc_jit_context_new_rvalue_from_long (m_jit_ctxt, m_int64_t,
						     op.u.i);
      case MIR_OP_UINT:
	// FIXME: should by uint64_t
	return gcc_jit_context_new_rvalue_from_long (m_jit_ctxt, m_uint64_t,
						     op.u.u);
      case MIR_OP_REF:
	// TODO:
	//assert (0);
	//case MIR_OP_REF: fprintf (f, "%s", MIR_item_name (ctx, op.u.ref)); break;
	return NULL;
      case MIR_OP_MEM:
	// TODO
	return NULL;
      }
  }

  gcc_jit_rvalue *
  mir_op_to_rvalue (MIR_op_t op, gcc_jit_type *as_type) const
  {
    assert (as_type);
    gcc_jit_rvalue *rval = mir_op_to_rvalue (op);
    return gcc_jit_context_new_cast (m_jit_ctxt, NULL, rval, as_type);
  }

  gcc_jit_rvalue *
  mir_op_to_S_rvalue (MIR_op_t op) const
  {
    return mir_op_to_rvalue (op, m_int32_t);
  }

  gcc_jit_rvalue *
  mir_op_to_U_rvalue (MIR_op_t op) const
  {
    return mir_op_to_rvalue (op, m_uint32_t);
  }

  void
  out_assign_to_dst (MIR_op_t *ops, gcc_jit_rvalue *rval) const
  {
    gcc_jit_lvalue *dst_0 = mir_op_to_lvalue (ops[0]);
    gcc_jit_rvalue *cast_result
      = gcc_jit_context_new_cast (m_jit_ctxt, NULL,
				  rval, get_lval_type (dst_0));
    gcc_jit_block_add_assignment (m_curr_block, NULL,
				  dst_0, cast_result);
  }

  /* For use on MIR_UEXT16 etc.  Coerce ops[1] to TYPE.  */
  void
  out_ext (MIR_op_t *ops, gcc_jit_type *type)
  {
    gcc_jit_rvalue *rval = mir_op_to_rvalue (ops[1], type);
    out_assign_to_dst (ops, rval);
  }

  void
  out_op2 (MIR_op_t *ops) const
  {
    gcc_jit_rvalue *rval = mir_op_to_rvalue (ops[1]);
    out_assign_to_dst (ops, rval);

    /* Compare with out_op2 in mir2c.c.  */
#if 0
    out_op (ctx, f, ops[0]);
  fprintf (f, " = ");
  if (str != NULL) fprintf (f, "%s ", str);
  out_op (ctx, f, ops[1]);
  fprintf (f, ";\n");
#endif
  }

  void
  out_op3_for_type (MIR_op_t *ops, enum gcc_jit_binary_op jit_bin_op,
		    gcc_jit_type *type) const
  {
    /* Compare with out_op3/out_uop3/out_sop3/out_usop_3 in mir2c.c.  */
    gcc_jit_rvalue *src_1 = mir_op_to_rvalue (ops[1], type);
    gcc_jit_rvalue *src_2 = mir_op_to_rvalue (ops[2], type);
    gcc_jit_rvalue *result
      = gcc_jit_context_new_binary_op (m_jit_ctxt, NULL,
				       jit_bin_op, type,
				       src_1, src_2);
    out_assign_to_dst (ops, result);
  }
  void
  out_op3 (MIR_op_t *ops, enum gcc_jit_binary_op jit_bin_op) const
  {
    /* Compare with out_op3 in mir2c.c.  */
    out_op3_for_type (ops, jit_bin_op, m_int64_t);
  }
  void
  out_uop3 (MIR_op_t *ops, enum gcc_jit_binary_op jit_bin_op) const
  {
    /* Compare with out_uop3 in mir2c.c.  */
    out_op3_for_type (ops, jit_bin_op, m_uint64_t);
  }
  void
  out_sop3 (MIR_op_t *ops, enum gcc_jit_binary_op jit_bin_op) const
  {
    /* Compare with out_sop3 in mir2c.c.  */
    out_op3_for_type (ops, jit_bin_op, m_int32_t);
  }
  void
  out_usop3 (MIR_op_t *ops, enum gcc_jit_binary_op jit_bin_op) const
  {
    /* Compare with out_usop3 in mir2c.c.  */
    out_op3_for_type (ops, jit_bin_op, m_uint32_t);
  }

  gcc_jit_block *get_block_for_label (MIR_op_t label_op) const
  {
    mir_assert (label_op.mode == MIR_OP_LABEL);
    return get_block_for_label (label_op.u.label);
  }
  gcc_jit_block *get_block_for_label (MIR_insn_t label) const
  {
    mir_assert (label->code == MIR_LABEL);
    return (*m_map_label_to_block.find (label)).second;
  }

  void out_branch (MIR_op_t *ops, gcc_jit_rvalue *condition)
  {
    gcc_jit_block *branch_tgt = get_block_for_label (ops[0]);
    gcc_jit_block *fallthrough = gcc_jit_function_new_block (m_jit_func, NULL);
    gcc_jit_rvalue *bool_cond
      = gcc_jit_context_new_cast (m_jit_ctxt, NULL, condition, m_bool_t);
    gcc_jit_block_end_with_conditional (m_curr_block, NULL, bool_cond,
					branch_tgt, fallthrough);
    m_curr_block = fallthrough;
  }

  void out_bcmp_for_type (MIR_op_t *ops, enum gcc_jit_comparison op,
			  gcc_jit_type *type)
  {
    /* Compare with out_bcmp/out_bscmp etc in mir2c.c.  */
    gcc_jit_rvalue *src_1 = mir_op_to_rvalue (ops[1], type);
    gcc_jit_rvalue *src_2 = mir_op_to_rvalue (ops[2], type);
    gcc_jit_rvalue *cmp
      = gcc_jit_context_new_comparison (m_jit_ctxt, NULL, op, src_1, src_2);
    out_branch (ops, cmp);
  }

  void out_bcmp (MIR_op_t *ops, enum gcc_jit_comparison op)
  {
    /* Compare with out_bcmp in mir2c.c.  */
    out_bcmp_for_type (ops, op, m_int64_t);
  }
  void out_bscmp (MIR_op_t *ops, enum gcc_jit_comparison op)
  {
    /* Compare with out_bscmp in mir2c.c.  */
    out_bcmp_for_type (ops, op, m_int32_t);
  }

  jit_module_conversion *m_modconv;
  gcc_jit_context *m_jit_ctxt;
  gcc_jit_type *m_bool_t;
  gcc_jit_type *m_int8_t;
  gcc_jit_type *m_int16_t;
  gcc_jit_type *m_uint16_t;
  gcc_jit_type *m_int32_t;
  gcc_jit_type *m_uint32_t;
  gcc_jit_type *m_int64_t;
  gcc_jit_type *m_uint64_t;
  gcc_jit_lvalue **m_lvals_for_regs;
  gcc_jit_type *m_return_type;
  gcc_jit_function *m_jit_func;
  gcc_jit_block *m_curr_block;
  std::map<MIR_label_t, gcc_jit_block *> m_map_label_to_block;
};

void
jit_module_conversion::add_function (MIR_func_t func)
{
  if (m_verbose)
    printf ("func name: \"%s\"\n", func->name);

  jit_func_conversion fc (this, func);
  MIR_insn_t insn;
  /* First pass: create blocks for labels.  */
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn))
    {
      if (insn->code != MIR_LABEL)
	continue;
      if (m_verbose)
	MIR_output_insn (m_mir_ctxt, stderr, insn, func, TRUE);
      fc.on_mir_label (insn);
    }
  /* Second pass: populate blocks based on other insns.  */
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn))
    {
      if (m_verbose)
	MIR_output_insn (m_mir_ctxt, stderr, insn, func, TRUE);
      fc.on_mir_insn (insn);
    }
}

void
jit_module_conversion::add_bss_item (MIR_item_t item)
{
  MIR_bss_t bss = item->u.bss;
  if (m_verbose)
    printf ("bss_item name: \"%s\"\n", bss->name);

  assert (bss->len <= INT_MAX);
  gcc_jit_type *byte
    = gcc_jit_context_get_type (m_jit_ctxt,
				GCC_JIT_TYPE_UNSIGNED_CHAR);
  gcc_jit_type *array_type
    = gcc_jit_context_new_array_type(m_jit_ctxt, NULL,
				     byte, bss->len);
  gcc_jit_lvalue *lval
    = gcc_jit_context_new_global(m_jit_ctxt, NULL,
				 GCC_JIT_GLOBAL_EXPORTED,
				 array_type, bss->name);
  m_map_bss_item_to_global[item] = lval;
}


void
gcc_jit_context_add_from_mir (gcc_jit_context *jit_ctxt,
			      MIR_context_t mir_ctxt,
			      int verbose)
{
  jit_module_conversion jc (jit_ctxt, mir_ctxt, verbose);

  MIR_module_t module;
  for (module = DLIST_HEAD (MIR_module_t, *MIR_get_module_list (mir_ctxt));
       module != NULL;
       module = DLIST_NEXT (MIR_module_t, module))
    {
      MIR_item_t item;
      for (item = DLIST_HEAD (MIR_item_t, module->items);
	   item != NULL;
	   item = DLIST_NEXT (MIR_item_t, item))
	{
	  // TODO: compare with MIR_output_item
	  switch (item->item_type)
	    {
	    default:
	      // TODO
	      // assert (0);
	    case MIR_func_item:
	      jc.add_function (item->u.func);
	      break;
	    case MIR_proto_item:
	      // TODO
	      // assert (0);
	      break;
	    case MIR_import_item:
	      //assert (0);
	      // TODO
	      break;
	    case MIR_export_item:
	      // TODO
	      // assert (0);
	      break;
	    case MIR_forward_item:
	      // TODO
	      // assert (0);
	      break;
	    case MIR_data_item:
	      assert (0);
	      break;
	    case MIR_ref_data_item:
	      assert (0);
	      break;
	    case MIR_expr_data_item:
	      assert (0);
	      break;
	    case MIR_bss_item:
	      jc.add_bss_item (item);
	      break;
	    }
	}
    }
}

struct options
{
  options ()
  : m_verbose (false),
    m_optimization_level (0),
    m_debug (false),
    m_output_kind (GCC_JIT_OUTPUT_KIND_EXECUTABLE),
    m_out_fname ("gccjit.out"),
    m_in_bmir_fname (NULL)
  {
  }

  /* Adapted from c2mir-driver.c:init_options.  */
  void init (int argc, char *argv[])
  {
    for (int i = 1; i < argc; i++) {
      if (strcmp (argv[i], "-g") == 0) {
	m_debug = true;
      } else if (strcmp (argv[i], "-S") == 0) {
	m_output_kind = GCC_JIT_OUTPUT_KIND_ASSEMBLER;
      } else if (strcmp (argv[i], "-c") == 0) {
	m_output_kind = GCC_JIT_OUTPUT_KIND_OBJECT_FILE;
      } else if (strcmp (argv[i], "-v") == 0) {
	m_verbose = true;
      } else if (strncmp (argv[i], "-O", 2) == 0) {
	m_optimization_level = argv[i][2] != '\0' ? atoi (&argv[i][2]) : 2;
      } else if (strcmp (argv[i], "-o") == 0) {
	if (i + 1 >= argc)
	  fprintf (stderr, "-o without argument\n");
	else
	  m_out_fname = argv[++i];
      } else if (strcmp (argv[i], "-h") == 0) {
	// FIXME:
	fprintf (stderr,
		 "Usage: %s OPTIONS INPUT_BMIR where OPTIONS are\n",
		 argv[0]);
	fprintf (stderr, "\n");
	fprintf (stderr, "  -v -- verbose\n");
	fprintf (stderr, "  -S, -c -- generate assembler or object files\n");
	fprintf (stderr, "  -o file -- put output code into given file\n");
	fprintf (stderr, "  -On -- use given optimization level in libgccjit\n");
	fprintf (stderr, "  -g -- enable debuginfo\n");
	exit (0);
      } else {
	if (!m_in_bmir_fname)
	  m_in_bmir_fname = argv[i];
	else
	  {
	    fprintf (stderr,
		     "unknown command line option %s (use -h for usage)\n",
		     argv[i]);
	    exit (1);
	  }
      }
    }
  }

  bool m_verbose;
  int  m_optimization_level;
  bool m_debug;
  enum gcc_jit_output_kind m_output_kind;
  const char *m_out_fname;
  const char *m_in_bmir_fname;
};

int main (int argc, char *argv[])
{
  struct options opts;
  opts.init (argc, argv);

  MIR_context_t mir_ctxt = MIR_init ();

  /* Load a mir binary.  */
  FILE *f = fopen (opts.m_in_bmir_fname, "rb");
  MIR_read (mir_ctxt, f);
  fclose (f);

  if (opts.m_verbose)
    MIR_output (mir_ctxt, stderr);

  gcc_jit_context *jit_ctxt = gcc_jit_context_acquire ();

  if (opts.m_verbose)
    gcc_jit_context_set_logfile (jit_ctxt, stderr, 0, 0);

  gcc_jit_context_set_str_option (jit_ctxt, GCC_JIT_STR_OPTION_PROGNAME,
				  argv[0]);
  gcc_jit_context_set_bool_option (jit_ctxt, GCC_JIT_BOOL_OPTION_DEBUGINFO,
				   opts.m_debug);
  gcc_jit_context_set_int_option (jit_ctxt,
				  GCC_JIT_INT_OPTION_OPTIMIZATION_LEVEL,
				  opts.m_optimization_level);
  gcc_jit_context_set_bool_allow_unreachable_blocks (jit_ctxt, 1);

  /* Populate gcc_jit_context.  */
  gcc_jit_context_add_from_mir (jit_ctxt, mir_ctxt, opts.m_verbose);

  MIR_finish (mir_ctxt);

  // Debugging:
  if (0)
    gcc_jit_context_dump_to_file (jit_ctxt, "/tmp/test.c", 1); // TODO

  /* Compile.  */
  gcc_jit_context_compile_to_file (jit_ctxt,
				   opts.m_output_kind,
				   opts.m_out_fname);

  gcc_jit_context_release (jit_ctxt);

  return 0;
}
