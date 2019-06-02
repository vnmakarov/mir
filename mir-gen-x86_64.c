/* This file is a part of MIR project.
   Copyright (C) 2018, 2019 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

#include <limits.h>

enum {
  AX_HARD_REG = 0, CX_HARD_REG, DX_HARD_REG, BX_HARD_REG, SP_HARD_REG, BP_HARD_REG, SI_HARD_REG, DI_HARD_REG,
  R8_HARD_REG, R9_HARD_REG, R10_HARD_REG, R11_HARD_REG, R12_HARD_REG, R13_HARD_REG, R14_HARD_REG, R15_HARD_REG, 
  XMM0_HARD_REG, XMM1_HARD_REG, XMM2_HARD_REG, XMM3_HARD_REG, XMM4_HARD_REG, XMM5_HARD_REG, XMM6_HARD_REG, XMM7_HARD_REG, 
  XMM8_HARD_REG, XMM9_HARD_REG, XMM10_HARD_REG, XMM11_HARD_REG, XMM12_HARD_REG, XMM13_HARD_REG, XMM14_HARD_REG, XMM15_HARD_REG, 
};

static const MIR_reg_t MAX_HARD_REG = XMM15_HARD_REG;
static const MIR_reg_t HARD_REG_FRAME_POINTER = BP_HARD_REG;

/* Hard regs not used in machinized code, preferably call used ones. */
const MIR_reg_t TEMP_INT_HARD_REG1 = R10_HARD_REG, TEMP_INT_HARD_REG2 = R11_HARD_REG;
const MIR_reg_t TEMP_FLOAT_HARD_REG1 = XMM8_HARD_REG, TEMP_FLOAT_HARD_REG2 = XMM9_HARD_REG;
const MIR_reg_t TEMP_DOUBLE_HARD_REG1 = XMM8_HARD_REG, TEMP_DOUBLE_HARD_REG2 = XMM9_HARD_REG;

static inline int hard_reg_type_ok_p (MIR_reg_t hard_reg, MIR_type_t type) {
  assert (hard_reg <= MAX_HARD_REG);
  return type == MIR_T_F || type == MIR_T_D ? hard_reg >= XMM0_HARD_REG : hard_reg < XMM0_HARD_REG;
}

static inline int fixed_hard_reg_p (MIR_reg_t hard_reg) {
  assert (hard_reg <= MAX_HARD_REG);
  return (hard_reg == BP_HARD_REG || hard_reg == SP_HARD_REG
	  || hard_reg == TEMP_INT_HARD_REG1 || hard_reg == TEMP_INT_HARD_REG2
	  || hard_reg == TEMP_FLOAT_HARD_REG1 || hard_reg == TEMP_FLOAT_HARD_REG2
	  || hard_reg == TEMP_DOUBLE_HARD_REG1 || hard_reg == TEMP_DOUBLE_HARD_REG2);
}

static inline int call_used_hard_reg_p (MIR_reg_t hard_reg) {
  assert (hard_reg <= MAX_HARD_REG);
  return ! (hard_reg == BX_HARD_REG
	    || (hard_reg >= R12_HARD_REG && hard_reg <= R15_HARD_REG));
}

static MIR_disp_t get_stack_slot_offset (MIR_reg_t slot) { /* slot is 0, 1, ... */
  return - (MIR_disp_t) (slot + 1) * sizeof (int64_t);
}

static int alloca_p;

static MIR_insn_code_t two_op_insn_codes [] = { /* see possible patterns */
  MIR_FADD, MIR_DADD, MIR_SUB, MIR_SUBS, MIR_FSUB, MIR_DSUB,
  MIR_MUL, MIR_MULS, MIR_FMUL, MIR_DMUL, MIR_DIV, MIR_DIVS, MIR_UDIV, MIR_FDIV, MIR_DDIV,
  MIR_MOD, MIR_MODS, MIR_UMOD, MIR_UMODS, MIR_AND, MIR_ANDS, MIR_OR, MIR_ORS, MIR_XOR, MIR_XORS,
  MIR_LSH, MIR_LSHS, MIR_RSH, MIR_RSHS, MIR_URSH, MIR_URSHS,
};

typedef enum {
  GC_INSN_PUSH = MIR_INSN_BOUND,
  GC_INSN_BOUND
} MIR_full_insn_code_t;

static MIR_insn_code_t get_ext_code (MIR_type_t type) {
  switch (type) {
  case MIR_T_I8: return MIR_EXT8;
  case MIR_T_U8: return MIR_UEXT8;
  case MIR_T_I16: return MIR_EXT16;
  case MIR_T_U16: return MIR_UEXT16;
  case MIR_T_I32: return MIR_EXT32;
  case MIR_T_U32: return MIR_UEXT32;
  default: return MIR_INVALID_INSN;
  }
}

static MIR_reg_t get_arg_reg (MIR_type_t arg_type,
			      size_t *int_arg_num, size_t *fp_arg_num, MIR_insn_code_t *mov_code) {
  MIR_reg_t arg_reg;
  
  if (arg_type == MIR_T_F || arg_type == MIR_T_D) {
    switch (*fp_arg_num) {
    case 0: case 1: case 2: case 3:
#ifndef _WIN64
    case 4: case 5: case 6: case 7:
#endif
      arg_reg = XMM0_HARD_REG + *fp_arg_num;
      break;
    default: arg_reg = MIR_NON_HARD_REG; break;
    }
    (*fp_arg_num)++;
    *mov_code = arg_type == MIR_T_F ? MIR_FMOV : MIR_DMOV;
  } else {
    switch (*int_arg_num
#ifdef _WIN64
	    + 2
#endif
	    ) {
    case 0: arg_reg = DI_HARD_REG; break;
    case 1: arg_reg = SI_HARD_REG; break;
#ifdef _WIN64
    case 2: arg_reg = CX_HARD_REG; break;
    case 3: arg_reg = DX_HARD_REG; break;
#else
    case 2: arg_reg = DX_HARD_REG; break;
    case 3: arg_reg = CX_HARD_REG; break;
#endif
    case 4: arg_reg = R8_HARD_REG; break;
    case 5: arg_reg = R9_HARD_REG; break;
    default:
      arg_reg = MIR_NON_HARD_REG; break;
    }
    (*int_arg_num)++;
    *mov_code = MIR_MOV;
  }
  return arg_reg;
}

static void machinize_call (MIR_item_t func_item, MIR_insn_t call_insn) {
  MIR_func_t func = func_item->u.func;
  MIR_proto_t proto = call_insn->ops[0].u.ref->u.proto;
  size_t nargs, nops = MIR_insn_nops (call_insn), start = proto->res_type != MIR_T_V ? 3 : 2;
  size_t int_arg_num = 0, fp_arg_num = 0, mem_size = 0;
  MIR_type_t type, mem_type;
  MIR_var_t *arg_vars = NULL;
  MIR_reg_t arg_reg;
  MIR_op_t arg_op, temp_op, arg_reg_op, ret_reg_op, mem_op;
  MIR_insn_code_t new_insn_code, ext_code;
  MIR_insn_t new_insn, prev_insn, next_insn;
  MIR_insn_t prev_call_insn = DLIST_PREV (MIR_insn_t, call_insn);
  MIR_insn_t next_call_insn = DLIST_NEXT (MIR_insn_t, call_insn);
  
  if (proto->args == NULL) {
    nargs = 0;
  } else {
    nargs = VARR_LENGTH (MIR_var_t, proto->args);
    arg_vars = VARR_ADDR (MIR_var_t, proto->args);
  }
  mir_assert (nops - start == nargs);
  for (size_t i = start; i < nops; i++) {
    arg_op = call_insn->ops[i];
    mir_assert (arg_op.mode == MIR_OP_REG || arg_op.mode == MIR_OP_HARD_REG);
    type = arg_vars[i - start].type;
    if ((ext_code = get_ext_code (type)) != MIR_INVALID_INSN) { /* extend arg if necessary */
      temp_op = MIR_new_reg_op (gen_new_temp_reg (MIR_T_I64, func_item->u.func));
      new_insn = MIR_new_insn (ext_code, temp_op, arg_op);
      gen_add_insn_before (func_item, call_insn, new_insn);
      call_insn->ops[i] = arg_op = temp_op;
    }
    if ((arg_reg = get_arg_reg (type, &int_arg_num, &fp_arg_num, &new_insn_code)) != MIR_NON_HARD_REG) {
      /* put arguments to argument hard regs */
      arg_reg_op = _MIR_new_hard_reg_op (arg_reg);
      new_insn = MIR_new_insn (new_insn_code, arg_reg_op, arg_op);
      gen_add_insn_before (func_item, call_insn, new_insn);
      call_insn->ops[i] = arg_reg_op;
    } else { /* put arguments on the stack */
      mem_type = type == MIR_T_F || type == MIR_T_D ? type : MIR_T_I64;
      new_insn_code = type == MIR_T_F ? MIR_FMOV : type == MIR_T_D ? MIR_DMOV : MIR_MOV;
      mem_op = _MIR_new_hard_reg_mem_op (mem_type, mem_size, SP_HARD_REG, MIR_NON_HARD_REG, 1);
      new_insn = MIR_new_insn (new_insn_code, mem_op, arg_op);
      mir_assert (prev_call_insn != NULL); /* call_insn should not be the first after simplification */
      MIR_insert_insn_after (func_item, prev_call_insn, new_insn);
      prev_insn = DLIST_PREV (MIR_insn_t, new_insn); next_insn = DLIST_NEXT (MIR_insn_t, new_insn);
      create_new_bb_insns (func_item, prev_insn, next_insn);
      call_insn->ops[i] = mem_op;
      mem_size += 8;
    }
  }
#if 0
  /* vector args number for varags or no prototype calls */
  new_insn = MIR_new_insn (MIR_MOV, _MIR_new_hard_reg_op (AX_HARD_REG), MIR_new_int_op (0));
  MIR_insert_insn_before (func_item, call_insn, new_insn);
  create_new_bb_insns (func_item, DLIST_PREV (MIR_insn_t, new_insn), call_insn);
#endif
  if (proto->res_type != MIR_T_V) { /* assign return register to call result op */
    ret_reg_op = call_insn->ops[2];
    mir_assert (ret_reg_op.mode == MIR_OP_REG || ret_reg_op.mode == MIR_OP_HARD_REG);
    if (proto->res_type == MIR_T_F) {
      new_insn = MIR_new_insn (MIR_FMOV, ret_reg_op, _MIR_new_hard_reg_op (XMM0_HARD_REG));
    } else if (proto->res_type == MIR_T_D) {
      new_insn = MIR_new_insn (MIR_DMOV, ret_reg_op, _MIR_new_hard_reg_op (XMM0_HARD_REG));
    } else {
      new_insn = MIR_new_insn (MIR_MOV, ret_reg_op, _MIR_new_hard_reg_op (AX_HARD_REG));
    }
    MIR_insert_insn_after (func_item, call_insn, new_insn);
    call_insn->ops[2] = new_insn->ops[1];
    if ((ext_code = get_ext_code (func->res_type)) != MIR_INVALID_INSN) {
      MIR_insert_insn_after (func_item, new_insn, MIR_new_insn (ext_code, ret_reg_op, ret_reg_op));
      new_insn = DLIST_NEXT (MIR_insn_t, new_insn);
    }
    create_new_bb_insns (func_item, call_insn, DLIST_NEXT (MIR_insn_t, new_insn));
  }
  if (mem_size != 0) { /* allocate/deallocate stack for args passed on stack */
    new_insn = MIR_new_insn (MIR_SUB, _MIR_new_hard_reg_op (SP_HARD_REG),
			     _MIR_new_hard_reg_op (SP_HARD_REG), MIR_new_int_op (mem_size));
    MIR_insert_insn_after (func_item, prev_call_insn, new_insn);
    next_insn = DLIST_NEXT (MIR_insn_t, new_insn);
    create_new_bb_insns (func_item, prev_call_insn, next_insn);
    new_insn = MIR_new_insn (MIR_ADD, _MIR_new_hard_reg_op (SP_HARD_REG),
			     _MIR_new_hard_reg_op (SP_HARD_REG), MIR_new_int_op (mem_size));
    MIR_insert_insn_after (func_item, call_insn, new_insn);
    next_insn = DLIST_NEXT (MIR_insn_t, new_insn);
    create_new_bb_insns (func_item, call_insn, next_insn);
  }
}

static float mir_ui2f (uint64_t i) { return i; }
static double mir_ui2d (uint64_t i) { return i; }
static const char *UI2F = "mir.ui2f";
static const char *UI2D = "mir.ui2d";
static const char *UI2F_P = "mir.ui2f.p";
static const char *UI2D_P = "mir.ui2d.p";

static void get_builtin (MIR_item_t func_item, MIR_insn_code_t code,
			 MIR_item_t *proto_item, MIR_item_t *func_import_item) {
  switch (code) {
  case MIR_UI2F:
    *proto_item = _MIR_builtin_proto (func_item->module, UI2F_P, MIR_T_F, 1, MIR_T_I64, NULL);
    *func_import_item = _MIR_builtin_func (func_item->module, UI2F, mir_ui2f);
    break;
  case MIR_UI2D:
    *proto_item = _MIR_builtin_proto (func_item->module, UI2D_P, MIR_T_D, 1, MIR_T_I64, NULL);
    *func_import_item = _MIR_builtin_func (func_item->module, UI2D, mir_ui2d);
    break;
  default:
    assert (FALSE);
  }
}

static void machinize (MIR_item_t func_item) {
  MIR_func_t func;
  MIR_type_t type, mem_type;
  MIR_insn_code_t code, new_insn_code;
  MIR_insn_t insn, next_insn, new_insn;
  MIR_reg_t ret_reg, arg_reg;
  MIR_op_t ret_reg_op, arg_reg_op, mem_op;
  size_t i, int_arg_num, fp_arg_num, mem_size;

  assert (func_item->item_type == MIR_func_item);
  func = func_item->u.func;
  for (i = int_arg_num = fp_arg_num = mem_size = 0; i < func->nargs; i++) {
    /* Argument extensions is already done in simplify */
    /* Prologue: generate arg_var = hard_reg|stack mem ... */
    type = VARR_GET (MIR_var_t, func->vars, i).type;
    arg_reg = get_arg_reg (type, &int_arg_num, &fp_arg_num, &new_insn_code);
    if (arg_reg != MIR_NON_HARD_REG) {
      arg_reg_op = _MIR_new_hard_reg_op (arg_reg);
      new_insn = MIR_new_insn (new_insn_code, MIR_new_reg_op (i + 1), arg_reg_op);
      MIR_prepend_insn (func_item, new_insn);
      create_new_bb_insns (func_item, NULL, DLIST_NEXT (MIR_insn_t, new_insn));
    } else {
      /* arg is on the stack */
      mem_type = type == MIR_T_F || type == MIR_T_D ? type : MIR_T_I64;
      new_insn_code = type == MIR_T_F ? MIR_FMOV : type == MIR_T_D ? MIR_DMOV : MIR_MOV;
      mem_op = _MIR_new_hard_reg_mem_op (mem_type, mem_size + 16 /* old BP and ret address */,
					HARD_REG_FRAME_POINTER, MIR_NON_HARD_REG, 1);
      new_insn = MIR_new_insn (new_insn_code, MIR_new_reg_op (i + 1), mem_op);
      MIR_prepend_insn (func_item, new_insn);
      next_insn = DLIST_NEXT (MIR_insn_t, new_insn);
      create_new_bb_insns (func_item, NULL, next_insn);
      mem_size += 8;
    }
  }
  alloca_p = FALSE;
  for (insn = DLIST_HEAD (MIR_insn_t, func->insns); insn != NULL; insn = next_insn) {
    next_insn = DLIST_NEXT (MIR_insn_t, insn);
    code = insn->code;
    if (code == MIR_UI2F || code == MIR_UI2D) {
      /* Use a builtin func call: mov freg, func ref; call proto, freg, res_reg, op_reg */
      MIR_item_t proto_item, func_import_item;
      MIR_op_t freg_op, res_reg_op = insn->ops[0], op_reg_op = insn->ops[1], ops[4];
      
      get_builtin (func_item, code, &proto_item, &func_import_item);
      assert (res_reg_op.mode == MIR_OP_REG && op_reg_op.mode == MIR_OP_REG);
      freg_op = MIR_new_reg_op (gen_new_temp_reg (MIR_T_I64, func_item->u.func));
      next_insn = new_insn = MIR_new_insn (MIR_MOV, freg_op, MIR_new_ref_op (func_import_item));
      gen_add_insn_before (func_item, insn, new_insn);
      ops[0] = MIR_new_ref_op (proto_item); ops[1] = freg_op; ops[2] = res_reg_op; ops[3] = op_reg_op;
      new_insn = MIR_new_insn_arr (MIR_CALL, 4, ops);
      gen_add_insn_before (func_item, insn, new_insn);
      gen_delete_insn (func_item, insn);
    } else if (code == MIR_CALL) {
      machinize_call (func_item, insn);
    } else if (code == MIR_ALLOCA) {
      alloca_p = TRUE;
    } else if (code == MIR_RET || code == MIR_FRET || code == MIR_DRET) {
      /* In simplify we already transformed code for one return insn
	 and added extension in return (if any).  */
      assert (insn->ops[0].mode == MIR_OP_REG);
      ret_reg = code == MIR_RET ? AX_HARD_REG :  XMM0_HARD_REG;
      ret_reg_op = _MIR_new_hard_reg_op (ret_reg);
      new_insn_code = code == MIR_RET ? MIR_MOV : code == MIR_FRET ? MIR_FMOV : MIR_DMOV;
      new_insn = MIR_new_insn (new_insn_code, ret_reg_op, insn->ops[0]);
      gen_add_insn_before (func_item, insn, new_insn);
      insn->ops[0] = ret_reg_op;
    } else if (code == MIR_EQ || code == MIR_NE || code == MIR_LT || code == MIR_ULT || code == MIR_LE
	       || code == MIR_ULE || code == MIR_GT || code == MIR_UGT || code == MIR_GE || code == MIR_UGE
	       || code == MIR_EQS || code == MIR_NES || code == MIR_LTS || code == MIR_ULTS
	       || code == MIR_LES || code == MIR_ULES || code == MIR_GTS || code == MIR_UGT
	       || code == MIR_GES || code == MIR_UGES
	       || code == MIR_FEQ || code == MIR_FNE || code == MIR_FLT || code == MIR_FLE
	       || code == MIR_FGT || code == MIR_FGE
	       || code == MIR_DEQ || code == MIR_DNE || code == MIR_DLT || code == MIR_DLE
	       || code == MIR_DGT || code == MIR_DGE) {
      /* We can access only 4 regs in setxx -- use ax as the result: */
      MIR_op_t areg_op = _MIR_new_hard_reg_op (AX_HARD_REG);

      new_insn = MIR_new_insn (MIR_MOV, insn->ops[0], areg_op);
      gen_add_insn_after (func_item, insn, new_insn);
      insn->ops[0] = areg_op;
    }
  }
}

static void make_prolog_epilog (MIR_item_t func_item,
				bitmap_t used_hard_regs, size_t stack_slots_num) {
  MIR_func_t func;
  MIR_insn_t anchor, new_insn;
  MIR_op_t sp_reg_op, fp_reg_op;
  size_t i, n, saved_hard_regs_num, overall_frame_size;

  assert (func_item->item_type == MIR_func_item);
  func = func_item->u.func;
  for (i = saved_hard_regs_num = 0; i <= MAX_HARD_REG; i++)
    if (! call_used_hard_reg_p (i) && bitmap_bit_p (used_hard_regs, i))
      saved_hard_regs_num++;
  sp_reg_op.mode = fp_reg_op.mode = MIR_OP_HARD_REG;
  sp_reg_op.u.hard_reg = SP_HARD_REG; fp_reg_op.u.hard_reg = BP_HARD_REG;
  /* Prologue: */
  anchor = DLIST_HEAD (MIR_insn_t, func->insns);
  new_insn = MIR_new_insn (MIR_SUB, sp_reg_op, sp_reg_op,
			   MIR_new_int_op (8 * saved_hard_regs_num + 8));
  gen_add_insn_before (func_item, anchor, new_insn); /* sp -= size of saved regs and bp */
  new_insn = MIR_new_insn (MIR_MOV,
			   _MIR_new_hard_reg_mem_op (MIR_T_I64, 0, SP_HARD_REG, MIR_NON_HARD_REG, 1),
			   fp_reg_op);
  gen_add_insn_before (func_item, anchor, new_insn); /* (sp) = bp */
  for (i = n = 0; i <= MAX_HARD_REG; i++)
    if (! call_used_hard_reg_p (i) && bitmap_bit_p (used_hard_regs, i)) {
      new_insn = MIR_new_insn (MIR_MOV,
			       _MIR_new_hard_reg_mem_op (MIR_T_I64, ++n * 8, SP_HARD_REG, MIR_NON_HARD_REG, 1),
			       _MIR_new_hard_reg_op (i));
      gen_add_insn_before (func_item, anchor, new_insn);  /* disp(sp) = hard reg */
    }
  overall_frame_size = ((func->frame_size + 7) / 8 + stack_slots_num) * 8; /* round */
  assert (overall_frame_size <= INT_MAX); /* ??? */
  if (overall_frame_size != 0) {
    new_insn = MIR_new_insn (MIR_SUB, sp_reg_op, sp_reg_op, MIR_new_int_op (overall_frame_size));
    gen_add_insn_before (func_item, anchor, new_insn);  /* sp -= frame and stack slot size */
  }
  new_insn = MIR_new_insn (MIR_MOV, fp_reg_op, sp_reg_op);
  gen_add_insn_before (func_item, anchor, new_insn);  /* bp = sp */
  /* Epilogue: */
  anchor = DLIST_TAIL (MIR_insn_t, func->insns);
  if (alloca_p) {
    new_insn = MIR_new_insn (MIR_ADD, sp_reg_op, fp_reg_op,
			     MIR_new_int_op (stack_slots_num * 8 - overall_frame_size));
    gen_add_insn_before (func_item, anchor, new_insn);  /* sp = bp - frame size */
  } else if (overall_frame_size != 0) {
    new_insn = MIR_new_insn (MIR_ADD, sp_reg_op, sp_reg_op, MIR_new_int_op (overall_frame_size));
    gen_add_insn_before (func_item, anchor, new_insn);  /* sp -= frame and stack slot size */
  }
  for (i = n = 0; i <= MAX_HARD_REG; i++)
    if (! call_used_hard_reg_p (i) && bitmap_bit_p (used_hard_regs, i)) {
      new_insn = MIR_new_insn (MIR_MOV, _MIR_new_hard_reg_op (i),
			       _MIR_new_hard_reg_mem_op (MIR_T_I64, ++n * 8, SP_HARD_REG, MIR_NON_HARD_REG, 1));
      gen_add_insn_before (func_item, anchor, new_insn);  /* hard reg =  disp(sp) */
    }
  new_insn = MIR_new_insn (MIR_MOV, fp_reg_op,
			   _MIR_new_hard_reg_mem_op (MIR_T_I64, 0, SP_HARD_REG, MIR_NON_HARD_REG, 1));
  gen_add_insn_before (func_item, anchor, new_insn); /* bp = (sp) */
  new_insn = MIR_new_insn (MIR_ADD, sp_reg_op, sp_reg_op,
			   MIR_new_int_op (8 * saved_hard_regs_num + 8));
  gen_add_insn_before (func_item, anchor, new_insn); /* sp += size of saved regs and bp */
}

struct pattern {
  MIR_insn_code_t code;
  /* Pattern elements:
     blank - ignore
     X - match everything
     $ - finish successfully matching
     r - register (we don't care about bp and sp because they are fixed and used correctly)
     h[0-31] - hard register with given number
     z - operand is zero
     i[0-3] - immediate of size 8,16,32,64-bits
     p[0-3] - reference
     s - immediate 1, 2, 4, or 8 (scale)
     m[0-3] - int (signed or unsigned) type memory of size 8,16,32,64-bits
     ms[0-3] - signed int type memory of size 8,16,32,64-bits
     mu[0-3] - unsigned int type memory of size 8,16,32,64-bits
     mf - memory of float
     md - memory of double
     l - label which can be present by 32-bit
     [0-9] - an operand matching n-th operand (n should be less than given operand number)

     Remmeber we have no float or double immediate at this stage. They are represented by
     a reference to data item.  */
  const char *pattern;
  /* Replacement elements:
     blank - ignore
     ; - insn separation
     X - REX byte with W=1
     Y - Optional REX byte with W=0
     [0-9A-F]+ pairs of hexidecimal digits opcode
     r[0-2] = n-th operand in ModRM:reg
     R[0-2] = n-th operand in ModRM:rm with mod == 3
     m[0-2] = n-th operand is mem
     ap = 2 and 3 operand forms address by plus (1st reg to base, 2nd reg to index, disp to disp)
     am = 2 and 3 operand forms address by mult (1st reg to index and mult const to scale)
     ad<value> - forms address: 1th operand is base reg and <value> is displacement
     i[0-2] - n-th operand in byte immediate (should be imm of type i8)
     I[0-2] - n-th operand in 4 byte immediate (should be imm of type i32)
     J[0-2] - n-th operand in 8 byte immediate
     P[0-2] - n-th operand in 8 byte address
     l[0-2] - n-th operand-label in 32-bit
     /[0-7] - opmod with given value (reg of MOD-RM)
     +[0-2] - lower 3-bit part of opcode used for n-th reg operand
     c<value> - address of 32-bit or 64-bit constant in memory pool (we keep always 64-bit in memory pool. x86_64 is LE)
     h<one or two digits> - hardware register with given number in reg of ModRM:reg; one bit of 8-15 in REX.R
     H<one or two digits> - hardware register with given number in rm of MOD-RM with and mod=3 (register); one bit of 8-15 in REX.B
     v<value> - 8-bit immediate with given hex value
     V<value> - 32-bit immediate with given hex value
  */
  const char *replacement;
};

// make imm always second operand (symplify for cmp and commutative op)
// make result of cmp op always a register and memory only the 2nd operand if first is reg, but not for FP (NAN) (simplify)
// for FP cmp first operand should be always reg (machinize)

#define IOP0(ICODE, SUFF, PREF, RRM_CODE, MR_CODE, RMI8_CODE, RMI32_CODE) \
  {ICODE ## SUFF, "r 0 r",  #PREF " " RRM_CODE " r0 R2"},    /* op r0,r2*/ \
  {ICODE ## SUFF, "r 0 m3", #PREF " " RRM_CODE " r0 m2"},    /* op r0,m2*/ \
  {ICODE ## SUFF, "m3 0 r", #PREF " " MR_CODE " r2 m0"},     /* op m0,r2*/ \
  {ICODE ## SUFF, "r 0 i0", #PREF " " RMI8_CODE " R0 i2"},   /* op r0,i2*/ \
  {ICODE ## SUFF, "m3 0 i0", #PREF " " RMI8_CODE " m0 i2"},  /* op m0,i2*/ \
  {ICODE ## SUFF, "r 0 i2", #PREF " " RMI32_CODE " R0 I2"},  /* op r0,i2*/ \
  {ICODE ## SUFF, "m3 0 i2", #PREF " " RMI32_CODE " m0 I2"}, /* op m0,i2*/

#define IOP(ICODE, RRM_CODE, MR_CODE, RMI8_CODE, RMI32_CODE)  \
  IOP0 (ICODE, , X, RRM_CODE, MR_CODE, RMI8_CODE, RMI32_CODE) \
  IOP0 (ICODE, S, Y, RRM_CODE, MR_CODE, RMI8_CODE, RMI32_CODE)

#define FOP(ICODE, OP_CODE) \
  {ICODE, "r 0 r", OP_CODE " r0 R2"}, \
  {ICODE, "r 0 mf", OP_CODE " r0 m2"},

#define DOP(ICODE, OP_CODE) \
  {ICODE, "r 0 r", OP_CODE " r0 R2"}, \
  {ICODE, "r 0 md", OP_CODE " r0 m2"},

#define SHOP0(ICODE, SUFF, PREF, CL_OP_CODE, I8_OP_CODE)	                \
  {ICODE ## SUFF, "r 0 h2", #PREF " " CL_OP_CODE " R0 i2"},  /* sh r0,cl */ \
  {ICODE ## SUFF, "m3 0 h2", #PREF " " CL_OP_CODE " m0 i2"}, /* sh m0,cl */ \
  {ICODE ## SUFF, "r 0 i0", #PREF " " I8_OP_CODE " R0 i2"},  /* sh r0,i2 */ \
  {ICODE ## SUFF, "m3 0 i0", #PREF " " I8_OP_CODE " m0 i2"}, /* sh m0,i2 */

#define SHOP(ICODE, CL_OP_CODE, I8_OP_CODE)  \
  SHOP0(ICODE, , X, CL_OP_CODE, I8_OP_CODE)  \
  SHOP0(ICODE, S, Y, CL_OP_CODE, I8_OP_CODE)

#define CMP0(ICODE, SUFF, PREF, SETX) \
  {ICODE ## SUFF, "r r r", #PREF " 3B r1 R2;" SETX " R0;X 0F B6 r0 R0"},      /* cmp r1,r2;setx r0; movzbl r0,r0*/ \
  {ICODE ## SUFF, "r r m3", #PREF " 3B r1 m2;" SETX " R0;X 0F B6 r0 R0"},     /* cmp r1,m2;setx r0; movzbl r0,r0*/ \
  {ICODE ## SUFF, "r r i0", #PREF " 83 /7 R1 i2;" SETX " R0;X 0F B6 r0 R0"},  /* cmp r1,i2;setx r0; movzbl r0,r0*/ \
  {ICODE ## SUFF, "r r i2", #PREF " 81 /7 R1 I2;" SETX " R0;X 0F B6 r0 R0"},  /* cmp r1,i2;setx r0; movzbl r0,r0*/ \
  {ICODE ## SUFF, "r m3 i0", #PREF " 83 /7 m1 i2;" SETX " R0;X 0F B6 r0 R0"}, /* cmp m1,i2;setx r0; movzbl r0,r0*/ \
  {ICODE ## SUFF, "r m3 i2", #PREF " 81 /7 m1 I2;" SETX " R0;X 0F B6 r0 R0"}, /* cmp m1,i2;setx r0; movzbl r0,r0*/

#define CMP(ICODE, SET_OPCODE)   \
  CMP0(ICODE, , X, SET_OPCODE)   \
  CMP0(ICODE, S, Y, SET_OPCODE)

#define FCMP(ICODE, SET_OPCODE) \
  {ICODE, "r r r", "0F 2E r1 R2; " SET_OPCODE " R0;X 0F B6 r0 R0"},  /* ucomiss r1,r2;setx r0; movzbl r0,r0*/ \
  {ICODE, "r r mf", "0F 2E r1 m2; " SET_OPCODE " R0;X 0F B6 r0 R0"}, /* ucomiss r1,m2;setx r0; movzbl r0,r0*/

#define FEQ(ICODE, V, SET_OPCODE) \
  {ICODE, "r r r", "X C7 /0 R0 " V "; 0F 2E r1 R2; " SET_OPCODE " R0; X 0F 45 r0 H8"},  /* mov v,r0;ucomiss r1,r2;setnp r8;cmovne r0,r8 */  \
  {ICODE, "r r mf", "X C7 /0 R0 " V "; 0F 2E r1 m2; " SET_OPCODE " R0; X 0F 45 r0 H8"},  /* mov v,r0;ucomiss r1,m2;setnp r8;cmovne r0,r8 */ \

#define DEQ(ICODE, V, SET_OPCODE) \
  {ICODE, "r r r", "X C7 /0 R0 " V "; 66 0F 2E r1 R2; " SET_OPCODE " R0; X 0F 45 r0 H8"},  /* mov v,r0;ucomisd r1,r2;setnp r8;cmovne r0,r8 */ \
  {ICODE, "r r md", "X C7 /0 R0 " V ";66 0F 2E r1 m2; " SET_OPCODE " R0; X 0F 45 r0 H8"},  /* mov v,r0;ucomisd r1,m2;setnp r8;cmovne r0,r8 */ \

#define FCMP(ICODE, SET_OPCODE) \
  {ICODE, "r r r", "0F 2E r1 R2; " SET_OPCODE " R0;X 0F B6 r0 R0"},  /* ucomiss r1,r2;setx r0; movzbl r0,r0*/ \
  {ICODE, "r r mf", "0F 2E r1 m2; " SET_OPCODE " R0;X 0F B6 r0 R0"}, /* ucomiss r1,m2;setx r0; movzbl r0,r0*/

#define DCMP(ICODE, SET_OPCODE) \
  {ICODE, "r r r", "66 0F 2E r1 R2; " SET_OPCODE " R0;X 0F B6 r0 R0"},  /* ucomisd r1,r2;setx r0; movzbl r0,r0*/ \
  {ICODE, "r r md", "66 0F 2E r1 m2; " SET_OPCODE " R0;X 0F B6 r0 R0"}, /* ucomisd r1,m2;setx r0; movzbl r0,r0*/

#define BR0(ICODE, SUFF, PREF, LONG_JUMP_OPCODE)			\
  {ICODE ## SUFF, "l r", #PREF " 83 /7 R1 v0;"       LONG_JUMP_OPCODE " l0"},  /* cmp r0,$0;jxx rel32*/ \
  {ICODE ## SUFF, "l m3", #PREF " 83 /7 m1 v0;"      LONG_JUMP_OPCODE " l0"},  /* cmp m0,$0;jxx rel8*/

#define BR(ICODE, LONG_JUMP_OPCODE) \
  BR0(ICODE, , X, LONG_JUMP_OPCODE) \
  BR0(ICODE, S, Y, LONG_JUMP_OPCODE)

#define BCMP0(ICODE, SUFF, PREF, LONG_JUMP_OPCODE)			\
  {ICODE ## SUFF, "l r r", #PREF " 3B r1 R2;"       LONG_JUMP_OPCODE " l0"},  /* cmp r0,r1;jxx rel32*/ \
  {ICODE ## SUFF, "l r m3", #PREF " 3B r1 m2;"      LONG_JUMP_OPCODE " l0"},  /* cmp r0,m1;jxx rel8*/  \
  {ICODE ## SUFF, "l r i0", #PREF " 83 /7 R1 i2;"   LONG_JUMP_OPCODE " l0"},  /* cmp r0,i1;jxx rel32*/ \
  {ICODE ## SUFF, "l r i2", #PREF " 81 /7 R1 I2;"   LONG_JUMP_OPCODE " l0"},  /* cmp r0,i1;jxx rel32*/ \
  {ICODE ## SUFF, "l m3 i0", #PREF " 83 /7 m1 i2;"  LONG_JUMP_OPCODE " l0"},  /* cmp m0,i1;jxx rel32*/ \
  {ICODE ## SUFF, "l m3 i2", #PREF " 81 /7 m1 I2;"  LONG_JUMP_OPCODE " l0"},  /* cmp m0,i1;jxx rel32*/

#define BCMP(ICODE, LONG_JUMP_OPCODE) \
  BCMP0(ICODE, , X, LONG_JUMP_OPCODE) \
  BCMP0(ICODE, S, Y, LONG_JUMP_OPCODE)

#define FBCMP(ICODE, LONG_JUMP_OPCODE)					\
  {ICODE, "l r r", "0F 2E r1 R2;" LONG_JUMP_OPCODE " l0"},  /* ucomiss r0,r1;jxx rel8*/

#define DBCMP(ICODE, LONG_JUMP_OPCODE) \
  {ICODE, "l r r", "66 0F 2E r1 R2;" LONG_JUMP_OPCODE " l0"},  /* ucomisd r0,r1;jxx rel8*/

static struct pattern patterns[] = {
  {MIR_MOV, "r z",  "Y 33 r0 R0"},     /* xor r0,r0 -- 32 bit xor */
  {MIR_MOV, "r r",  "X 8B r0 R1"},     /* mov r0,r1 */
  {MIR_MOV, "r m3", "X 8B r0 m1"},     /* mov r0,m1 */
  {MIR_MOV, "m3 r", "X 89 r1 m0"},     /* mov m0,r1 */
  {MIR_MOV, "r i2", "Y B8 +0 I1"},     /* mov r0,i32 -- 32-bit move */
  {MIR_MOV, "m3 i2", "X C7 /0 m0 I1"}, /* mov m0,i32 */
  {MIR_MOV, "r i3", "X B8 +0 J1"},     /* mov r0,i64 */
  {MIR_MOV, "r p", "X B8 +0 P1"},      /* mov r0,a64 */

  {MIR_MOV, "m0 r", "88 r1 m0"},       /* mov m0, r1 */
  {MIR_MOV, "m1 r", "66 89 r1 m0"},    /* mov m0, r1 */
  {MIR_MOV, "m2 r", "89 r1 m0"},       /* mov m0, r1 */

  {MIR_MOV, "r ms0", "X 0F BE r0 m1"},  /* movsx r0, m1 */
  {MIR_MOV, "r ms1", "X 0F BF r0 m1"},  /* movsx r0, m1 */
  {MIR_MOV, "r ms2", "X 63 r0 m1"},     /* movsx r0, m1 */

  {MIR_MOV, "r mu0", "X 0F B6 r0 m1"},  /* movzx r0, m1 */
  {MIR_MOV, "r mu1", "X 0F B7 r0 m1"},  /* movzx r0, m1 */
  {MIR_MOV, "r mu2", "8B r0 m1"},       /* mov r0, m1 */

  {MIR_MOV, "m0 i0", "Y C6 /0 m0 i1"},    /* mov m0,i8 */
  {MIR_MOV, "m2 i2", "Y C7 /0 m0 I1"},    /* mov m0,i32 */
  
  {MIR_FMOV, "r r", "F3 Y 0F 10 r0 R1"},     /* movss r0,r1 */
  {MIR_FMOV, "r mf", "F3 Y 0F 10 r0 m1"},    /* movss r0,m32 */
  {MIR_FMOV, "mf r", "F3 Y 0F 11 r1 m0"},    /* movss r0,m32 */

  {MIR_DMOV, "r r", "F2 Y 0F 10 r0 R1"},     /* movsd r0,r1 */
  {MIR_DMOV, "r md", "F2 Y 0F 10 r0 m1"},    /* movsd r0,m64 */
  {MIR_DMOV, "md r", "F2 Y 0F 11 r1 m0"},    /* movsd r0,m64 */

  {MIR_EXT8, "r r",  "X 0F BE r0 R1"},     /* movsx r0,r1 */
  {MIR_EXT8, "r m0", "X 0F BE r0 m1"},     /* movsx r0,m1 */
  {MIR_EXT16, "r r",  "X 0F BF r0 R1"},    /* movsx r0,r1 */
  {MIR_EXT16, "r m1", "X 0F BF r0 m1"},    /* movsx r0,m1 */
  {MIR_EXT32, "r r",  "X 63 r0 R1"},       /* movsx r0,r1 */
  {MIR_EXT32, "r m2", "X 63 r0 m1"},       /* movsx r0,m1 */
  {MIR_UEXT8, "r r",  "X 0F B6 r0 R1"},    /* movzx r0,r1 */
  {MIR_UEXT8, "r m0",  "X 0F B6 r0 m1"},   /* movzx r0,m1 */
  {MIR_UEXT16, "r r",  "X 0F B7 r0 R1"},   /* movzx r0,r1 */
  {MIR_UEXT16, "r m1", "X 0F B7 r0 m1"},   /* movzx r0,m1 */
  {MIR_UEXT32, "r r",  "Y 8B r0 R1"},      /* mov r0,r1 */
  {MIR_UEXT32, "r m2",  "Y 8B r0 m1"},     /* mov r0,m1 */

  {MIR_I2F, "r r",  "F3 X 0F 2A r0 R1"},  /* cvtsi2ss r0,r1 */
  {MIR_I2F, "r mf", "F3 X 0F 2A r0 m1"},  /* cvtsi2ss r0,m1 */
  {MIR_I2D, "r r",  "F2 X 0F 2A r0 R1"},  /* cvtsi2sd r0,r1 */
  {MIR_I2D, "r md", "F2 X 0F 2A r0 m1"},  /* cvtsi2sd r0,m1 */

  {MIR_F2I, "r r",  "F3 X 0F 2D r0 R1"},  /* cvtss2si r0,r1 */
  {MIR_F2I, "r mf", "F3 X 0F 2D r0 m1"},  /* cvtss2si r0,m1 */
  {MIR_D2I, "r r",  "F2 X 0F 2D r0 R1"},  /* cvtsd2si r0,r1 */
  {MIR_D2I, "r md", "F2 X 0F 2D r0 m1"},  /* cvtsd2si r0,m1 */

  {MIR_F2D, "r r",  "F3 X 0F 5A r0 R1"},  /* cvtss2sd r0,r1 */
  {MIR_F2D, "r mf", "F3 X 0F 5A r0 m1"},  /* cvtss2sd r0,m1 */
  {MIR_D2F, "r r",  "F2 X 0F 5A r0 R1"},  /* cvtsd2ss r0,r1 */
  {MIR_D2F, "r md", "F2 X 0F 5A r0 m1"},  /* cvtsd2ss r0,m1 */

  /* lea r0, 7(r1); and r0, r0, -8; sub sp, r0; mov r0, sp */
  {MIR_ALLOCA, "r r",  "Y 8D r0 ad7; X 81 /4 R0 VFFFFFFF8; X 2B h04 R0; X 8B r0 H04"},
  {MIR_ALLOCA, "r i2",  "X 81 /5 H04 I1; X 8B r0 H04"},  /* sub sp, i2; mov r0, sp */
  
  {MIR_NEG, "r 0",  "X F7 /3 R1"},  /* neg r0 */
  {MIR_NEG, "m3 0", "X F7 /3 m1"},  /* neg m0 */
  {MIR_NEGS, "r 0",  "Y F7 /3 R1"}, /* neg r0 */
  {MIR_NEGS, "m2 0", "Y F7 /3 m1"}, /* neg m0 */

  {MIR_FNEG, "r 0",  "0F 57 r0 c0000000080000000"},  /* xorps r0,80000000 */
  {MIR_DNEG, "r 0",  "66 0F 57 r0 c8000000000000000"},  /* xorpd r0,0x8000000000000000 */

  IOP (MIR_ADD, "03", "01", "83 /0", "81 /0")
  {MIR_ADD, "r r r",  "X 8D r0 ap"},  /* lea r0,(r1,r2)*/
  {MIR_ADD, "r r i2", "X 8D r0 ap"},  /* lea r0,i2(r1)*/
  {MIR_ADDS, "r r r",  "Y 8D r0 ap"},  /* lea r0,(r1,r2)*/
  {MIR_ADDS, "r r i2", "Y 8D r0 ap"},  /* lea r0,i2(r1)*/

  IOP (MIR_SUB, "2B", "29", "83 /5", "81 /5")
  
  {MIR_MUL, "r 0 r", "X 0F AF r0 R2"},    /* imul r0,r1*/
  {MIR_MUL, "r 0 m3", "X 0F AF r0 m2"},   /* imul r0,m1*/
  {MIR_MUL, "r r i2", "X 69 r0 R1 I2"},   /* imul r0,r1,i32*/
  {MIR_MUL, "r m3 i2", "X 69 r0 m1 I2"},  /* imul r0,m1,i32*/
  {MIR_MUL, "r r s", "X 8D r0 ap"},       /* lea r0,(,r1,s2)*/
  {MIR_MULS, "r 0 r", "Y 0F AF r0 R2"},   /* imul r0,r1*/
  {MIR_MULS, "r 0 m2", "Y 0F AF r0 m2"},  /* imul r0,m1*/
  {MIR_MULS, "r r i2", "Y 69 r0 R1 I2"},  /* imul r0,r1,i32*/
  {MIR_MULS, "r m2 i2", "Y 69 r0 m1 I2"}, /* imul r0,m1,i32*/
  {MIR_MULS, "r r s", "Y 8D r0 ap"},      /* lea r0,(,r1,s2)*/

  {MIR_DIV, "h0 h0 r", "X 99; X F7 /7 R2"},   /* cqo; idiv r2*/
  {MIR_DIV, "h0 h0 m3", "X 99; X F7 /7 m2"},  /* cqo; idiv m2*/
  {MIR_DIVS, "h0 h0 r", "Y 99; Y F7 /7 R2"},  /* cqo; idiv r2*/
  {MIR_DIVS, "h0 h0 m2", "Y 99; Y F7 /7 m2"}, /* cqo; idiv m2*/

  {MIR_MOD, "h1 h0 r", "X 99; X F7 /7 R2"},   /* cqo; idiv r2*/
  {MIR_MOD, "h1 h0 m3", "X 99; X F7 /7 m2"},  /* cqo; idiv m2*/
  {MIR_MODS, "h1 h0 r", "Y 99; Y F7 /7 R2"},  /* cqo; idiv r2*/
  {MIR_MODS, "h1 h0 m2", "Y 99; Y F7 /7 m2"}, /* cqo; idiv m2*/
  
  IOP (MIR_AND, "23", "21", "83 /4", "81 /4")
  IOP (MIR_OR, "0B", "09", "83 /1", "81 /1")
  IOP (MIR_XOR, "33", "31", "83 /6", "81 /6")

  FOP (MIR_FADD, "F3 0F 58") DOP (MIR_DADD, "F2 0F 58") FOP (MIR_FSUB, "F3 0F 5C") DOP (MIR_DSUB, "F2 0F 5C")
  FOP (MIR_FMUL, "F3 0F 59") DOP (MIR_DMUL, "F2 0F 59") FOP (MIR_FDIV, "F3 0F 5E") DOP (MIR_DDIV, "F2 0F 5E")
  
  SHOP (MIR_LSH, "D3 /4", "C1 /4") SHOP (MIR_RSH, "D3 /7", "C1 /7") SHOP (MIR_URSH, "D3 /5", "C1 /5")
  
  CMP(MIR_EQ, "0F 94") CMP(MIR_NE, "0F 95") CMP(MIR_LT, "0F 9C")  CMP(MIR_ULT, "0F 92")
  CMP(MIR_LE, "0F 9E") CMP(MIR_ULE, "0F 96") CMP(MIR_GT, "0F 9F") CMP(MIR_UGT, "0F 97")
  CMP(MIR_GE, "0F 9D") CMP(MIR_UGE, "0F 93")

  FEQ (MIR_FEQ, "V0", "0F 9B") DEQ (MIR_DEQ, "V0", "0F 9B") FEQ (MIR_FNE, "V1", "0F 9A") DEQ (MIR_DNE, "V1", "0F 9A")
  
  FCMP (MIR_FLT, "0F 92") DCMP (MIR_DLT, "0F 92") FCMP (MIR_FLE, "0F 96") DCMP (MIR_DLE, "0F 96")
  FCMP (MIR_FGT, "0F 97") DCMP (MIR_DGT, "0F 97") FCMP (MIR_FGE, "0F 93") DCMP (MIR_DGE, "0F 93")

  {MIR_JMP, "l", "E9 l0"},
  
  BR (MIR_BT, "0F 85") BR (MIR_BF,  "0F 84")

  BCMP (MIR_BEQ, "0F 84") BCMP (MIR_BNE,  "0F 85")
  BCMP (MIR_BLT, "0F 8C") BCMP (MIR_UBLT, "0F 82") BCMP (MIR_BLE, "0F 8E") BCMP (MIR_UBLE, "0F 86")
  BCMP (MIR_BGT, "0F 8F") BCMP (MIR_UBGT, "0F 87") BCMP (MIR_BGE, "0F 8D") BCMP (MIR_UBGE, "0F 83")

  FBCMP (MIR_FBLT, "0F 82") DBCMP (MIR_DBLT, "0F 82") FBCMP (MIR_FBLE, "0F 86") DBCMP (MIR_DBLT, "0F 86")
  FBCMP (MIR_FBGT, "0F 87") DBCMP (MIR_DBGT, "0F 87") FBCMP (MIR_FBGE, "0F 83") DBCMP (MIR_DBGT, "0F 83")

  {MIR_FBEQ, "l r r", "0F 2E r1 R2; 7A v6; 0F 84 l0"},       /* ucomiss r0,r1;jp L;je rel32 L: */
  {MIR_DBEQ, "l r r", "66 0F 2E r1 R2; 7A v6; 0F 84 l0"},    /* ucomisd r0,r1;jp L;je rel32 L: */

  {MIR_FBNE, "l r r", "0F 2E r1 R2; 0F 8A l0; 0F 85 l0"},    /* ucomiss r0,r1;jp rel32;jne rel32*/
  {MIR_DBNE, "l r r", "66 0F 2E r1 R2; 0F 8A l0; 0F 85 l0"}, /* ucomisd r0,r1;jp rel32;jne rel32*/

  {MIR_CALL, "X r h0 $", "Y FF /2 R1"},  /* call *r1 -- function call */
  {MIR_CALL, "X r $", "Y FF /2 R1"},     /* call *r1 -- procedure call */

  /* ??? Returns */
  {MIR_RET, "h0", "C3"},  /* ret */
  {MIR_FRET, "h16", "C3"}, /* ret */
  {MIR_DRET, "h16", "C3"}, /* ret */
};

static MIR_reg_t get_clobbered_hard_reg (MIR_insn_t insn) {
  MIR_insn_code_t code = insn->code;

  if (code == MIR_DIV) return DX_HARD_REG;
  else if (code == MIR_MOD) return AX_HARD_REG;
  return MIR_NON_HARD_REG;
}
							    
// constraint: esp can not be index

static int int8_p (int64_t v) { return INT8_MIN <= v && v <= INT8_MAX; }
static int uint8_p (int64_t v) { return 0 <= v && v <= UINT8_MAX; }
static int int16_p (int64_t v) { return INT16_MIN <= v && v <= INT16_MAX; }
static int MIR_UNUSED uint16_p (int64_t v) { return 0 <= v && v <= UINT16_MAX; }
static int int32_p (int64_t v) { return INT32_MIN <= v && v <= INT32_MAX; }
static int uint32_p (int64_t v) { return 0 <= v && v <= UINT32_MAX; }

DEF_VARR (int);
static VARR (int) *pattern_indexes;

struct insn_pattern_info {
  int start, num;
};

typedef struct insn_pattern_info insn_pattern_info_t;

DEF_VARR (insn_pattern_info_t);
static VARR (insn_pattern_info_t) *insn_pattern_info;

static int pattern_index_cmp (const void *a1, const void *a2) {
  int i1 = *(const int *) a1, i2 = *(const int *) a2;
  int c1 = (int) patterns[i1].code, c2 = (int) patterns[i2].code;

  return c1 != c2 ? c1 - c2 : (long) i1 - (long) i2;
}

static void patterns_init (void) {
  int i, ind, n = sizeof (patterns) / sizeof (struct pattern);
  MIR_insn_code_t prev_code, code;
  insn_pattern_info_t *info_addr;
  static insn_pattern_info_t pinfo = {0, 0};
  
  VARR_CREATE (int, pattern_indexes, 0);
  for (i = 0; i < n; i++)
    VARR_PUSH (int, pattern_indexes, i);
  qsort (VARR_ADDR (int, pattern_indexes), n, sizeof (int), pattern_index_cmp);
  VARR_CREATE (insn_pattern_info_t, insn_pattern_info, 0);
  for (i = 0; i < MIR_INSN_BOUND; i++)
    VARR_PUSH (insn_pattern_info_t, insn_pattern_info, pinfo);
  info_addr = VARR_ADDR (insn_pattern_info_t, insn_pattern_info);
  for (prev_code = MIR_INSN_BOUND, i = 0; i < n; i++) {
    ind = VARR_GET (int, pattern_indexes, i);
    if ((code = patterns[ind].code) != prev_code) {
      if (i != 0)
	info_addr[prev_code].num = i - info_addr[prev_code].start;
      info_addr[code].start = i;
      prev_code = code;
    }
  }
  assert (prev_code != MIR_INSN_BOUND);
  info_addr[prev_code].num = n - info_addr[prev_code].start;
}

static int pattern_match_p (struct pattern *pat, MIR_insn_t insn) {
  int nop, n;
  size_t nops = MIR_insn_nops (insn);
  const char *p;
  char ch, start_ch;
  MIR_op_t op, original;
  MIR_reg_t hr;
  
  for (nop = 0, p = pat->pattern; *p != 0; p++, nop++) {
    while (*p == ' ' || *p == '\t')
      p++;
    if (*p == '$')
      return TRUE;
    if (insn->code == MIR_CALL && nop >= nops)
      return FALSE;
    gen_assert (nop < nops);
    op = insn->ops[nop];
    switch (start_ch = *p) {
    case 'X':
      break;
    case 'r':
      if (op.mode != MIR_OP_HARD_REG) return FALSE;
      break;
    case 'h':
      if (op.mode != MIR_OP_HARD_REG) return FALSE;
      ch = *++p;
      gen_assert ('0' <= ch && ch <= '9');
      hr = ch - '0';
      ch = *++p;
      if ('0' <= ch && ch <= '9') hr = hr * 10 + ch - '0';
      else --p;
      if (op.u.hard_reg != hr) return FALSE;
      break;
    case 'z':
      if (op.mode != MIR_OP_INT || op.u.i != 0) return FALSE;
      break;
    case 'i':
      if (op.mode != MIR_OP_INT) return FALSE;
      ch = *++p;
      if ((ch == '0' && ! int8_p (op.u.i)) || (ch == '1' && ! int16_p (op.u.i))
	  || (ch == '2' && ! int32_p (op.u.i)))
	return FALSE;
      else
	gen_assert ('0' <= ch && ch <= '3');
      break;
    case 'p':
      if (op.mode != MIR_OP_REF) return FALSE;
      break;
    case 's':
      if (op.mode != MIR_OP_INT || (op.u.i != 1 && op.u.i != 2 && op.u.i != 4 && op.u.i != 8)) return FALSE;
      break;
    case 'm': {
      MIR_type_t type, type2, type3 = MIR_T_BOUND;
      int u_p, s_p;
      
      if (op.mode != MIR_OP_HARD_REG_MEM) return FALSE;
      u_p = s_p = TRUE; ch = *++p;
      switch (ch) {
      case 'f': type = MIR_T_F; type2 = MIR_T_BOUND; break;
      case 'd': type = MIR_T_D; type2 = MIR_T_BOUND; break;
      case 'u': case 's':
	u_p = ch == 'u'; s_p = ch == 's'; ch = *++p;
	/* Fall through: */
      default:
	gen_assert ('0' <= ch && ch <= '3');
	if (ch == '0') {
	  type = u_p ? MIR_T_U8 : MIR_T_I8; type2 = u_p && s_p ? MIR_T_I8 : MIR_T_BOUND;
	} else if (ch == '1') {
	  type = u_p ? MIR_T_U16 : MIR_T_I16; type2 = u_p && s_p ? MIR_T_I16 : MIR_T_BOUND;
	} else if (ch == '2') {
	  type = u_p ? MIR_T_U32 : MIR_T_I32; type2 = u_p && s_p ? MIR_T_I32 : MIR_T_BOUND;
#ifdef MIR_PTR32
	  if (u_p)
	    type3 = MIR_T_P;
#endif
	} else {
	  type = MIR_T_I64; type2 = MIR_T_BOUND;
#ifdef MIR_PTR64
	  type3 = MIR_T_P;
#endif
	}
      }
      if (op.u.mem.type != type && op.u.mem.type != type2 && op.u.mem.type != type3) return FALSE;
      break;
    }
    case 'l':
      if (op.mode != MIR_OP_LABEL) return FALSE;
      break;
    case '0': case '1': case '2': case '3': case '4':
    case '5': case '6': case '7': case '8': case '9':
      n = start_ch - '0';
      gen_assert (n < nop);
      original = insn->ops[n];
      if (original.mode != op.mode) return FALSE;
      gen_assert (op.mode == MIR_OP_HARD_REG || op.mode == MIR_OP_INT
	      || op.mode == MIR_OP_FLOAT || op.mode == MIR_OP_DOUBLE
	      || op.mode == MIR_OP_HARD_REG_MEM || op.mode == MIR_OP_LABEL);
      if (op.mode == MIR_OP_HARD_REG && op.u.hard_reg != original.u.hard_reg) return FALSE;
      else if (op.mode == MIR_OP_INT && op.u.i != original.u.i) return FALSE;
      else if (op.mode == MIR_OP_FLOAT && op.u.f != original.u.f) return FALSE;
      else if (op.mode == MIR_OP_DOUBLE && op.u.d != original.u.d) return FALSE;
      else if (op.mode == MIR_OP_LABEL && op.u.label != original.u.label) return FALSE;
      else if (op.mode == MIR_OP_HARD_REG_MEM
	       && op.u.hard_reg_mem.type != original.u.hard_reg_mem.type
	       && op.u.hard_reg_mem.scale != original.u.hard_reg_mem.scale
	       && op.u.hard_reg_mem.base != original.u.hard_reg_mem.base
	       && op.u.hard_reg_mem.index != original.u.hard_reg_mem.index
	       && op.u.hard_reg_mem.disp != original.u.hard_reg_mem.disp) return FALSE;
      break;
    default:
      gen_assert (FALSE);
    }
  }
  gen_assert (nop == nops);
  return TRUE;
}

static const char *find_insn_pattern_replacement (MIR_insn_t insn) {
  int i;
  struct pattern *pat;
  insn_pattern_info_t info = VARR_GET (insn_pattern_info_t, insn_pattern_info, insn->code);
  
  for (i = 0; i < info.num; i++) {
    pat = &patterns[VARR_GET (int, pattern_indexes, info.start + i)];
    if (pattern_match_p (pat, insn))
      return pat->replacement;
  }
  return NULL;
}

static void patterns_finish (void) {
  VARR_DESTROY (int, pattern_indexes);
  VARR_DESTROY (insn_pattern_info_t, insn_pattern_info);
}

static int hex_value (int ch) {
  return '0' <= ch && ch <= '9' ? ch - '0' : 'A' <= ch && ch <= 'F' ? ch - 'A' + 10 : -1;
}

static uint64_t read_hex (const char **ptr) {
  int v;
  const char *p;
  uint64_t res = 0;
  
  for (p = *ptr; (v = hex_value (*p)) >= 0; p++) {
    gen_assert ((res >> 60) == 0);
    res = res * 16 + v;
  }
  gen_assert (p != *ptr);
  *ptr = p - 1;
  return res;
}

static void setup_r (int *rex, int *r, int v) {
  gen_assert ((rex == NULL || *rex < 0) && *r < 0 && v >= 0 && v <= MAX_HARD_REG);
  if (v >= 16) v -= 16;
  if (v >= 8) {
    if (rex != NULL) *rex = 1;
    v -= 8;
  }
  *r = v;
}

static void setup_reg (int *rex_reg, int *reg, int v) { setup_r (rex_reg, reg, v); }

static void setup_rm (int *rex_b, int *rm, int v) { setup_r (rex_b, rm, v); }

static void setup_mod (int *mod, int v) {
  gen_assert (*mod < 0 && v >= 0 && v <= 3);
  *mod = v;
}

static void setup_scale (int *scale, int v) {
  gen_assert (*scale < 0 && v >= 0 && v <= 3);
  *scale = v;
}

static void setup_base (int *rex_b, int *base, int v) { setup_r (rex_b, base, v); }

static void setup_index (int *rex_i, int *index, int v) { setup_r (rex_i, index, v); }

static void setup_rip_rel_addr (MIR_disp_t rip_disp, int *mod, int *rm, int64_t *disp32) {
  gen_assert (*mod < 0 && *rm < 0 && *disp32 < 0);
  setup_rm (NULL, rm, 5);
  gen_assert (int32_p (rip_disp));
  setup_mod (mod, 2); *disp32 = (uint32_t) rip_disp;
}

static void setup_mem (MIR_mem_t mem, int *mod, int *rm, int *scale, int *base, int *rex_b,
		       int *index, int *rex_x, int *disp8, int64_t *disp32) {
  MIR_disp_t disp = mem.disp;

  gen_assert (*disp8 < 0 && *disp32 < 0 && mem.index != SP_HARD_REG);
  if (mem.index == MIR_NON_HARD_REG && mem.base == MIR_NON_HARD_REG) { /* SIB: disp only */
    setup_rm (NULL, rm, 4); *disp32 = (uint32_t) disp;
    setup_base (NULL, base, BP_HARD_REG); setup_index (NULL, index, SP_HARD_REG);
  } else if (mem.index == MIR_NON_HARD_REG
	     && mem.base != SP_HARD_REG && mem.base != R12_HARD_REG) {
    setup_rm (rex_b, rm, mem.base);
    if (disp == 0 && mem.base != BP_HARD_REG && mem.base != R13_HARD_REG) {
      setup_mod (mod, 0);
    } else if (int8_p (disp)) {
      setup_mod (mod, 1); *disp8 = (uint8_t) disp;
    } else {
      setup_mod (mod, 2); *disp32 = (uint32_t) disp;
    }
  } else if (mem.index == MIR_NON_HARD_REG) { /* SIB: only base = sp or r12 */
    setup_rm (NULL, rm, 4);
    setup_index (NULL, index, SP_HARD_REG); setup_base (rex_b, base, mem.base);
    if (disp == 0) {
      setup_mod (mod, 0);
    } else if (int8_p (disp)) {
      setup_mod (mod, 1); *disp8 = (uint8_t) disp;
    } else {
      setup_mod (mod, 2); *disp32 = (uint32_t) disp;
    }
  } else if (mem.base == MIR_NON_HARD_REG) { /* SIB: index with scale only */
    setup_rm (NULL, rm, 4);
    setup_index (rex_x, index, mem.index); setup_base (NULL, base, BP_HARD_REG); 
    setup_mod (mod, 0); *disp32 = (uint32_t) disp;
    setup_scale (scale, mem.scale == 1 ? 0 : mem.scale == 2 ? 1 : mem.scale == 4 ? 2 : 3);
  } else { /* SIB: base and index */
    setup_rm (NULL, rm, 4);
    setup_base (rex_b, base, mem.base); setup_index (rex_x, index, mem.index);
    setup_scale (scale, mem.scale == 1 ? 0 : mem.scale == 2 ? 1 : mem.scale == 4 ? 2 : 3);
    if (disp == 0 && mem.base != BP_HARD_REG && mem.base != R13_HARD_REG) {
      setup_mod (mod, 0);
    } else if (int8_p (disp)) {
      setup_mod (mod, 1); *disp8 = (uint8_t) disp;
    } else {
      setup_mod (mod, 2); *disp32 = (uint32_t) disp;
    }
  }
}

DEF_VARR (uint8_t);
static VARR (uint8_t) *code;

static void put_byte (int byte) {
  VARR_PUSH (uint8_t, code, byte);
}

static void put_uint64 (uint64_t v, int nb) {
  for (; nb > 0; nb--) {
    put_byte (v & 0xff); v >>= 8;
  }
}

static void set_int64 (uint8_t *addr, int64_t v, int nb) {
  for (; nb > 0; nb--) {
    *addr++ = v & 0xff; v >>= 8;
  }
}

DEF_VARR (uint64_t);
static VARR (uint64_t) *const_pool;

static size_t add_to_const_pool (uint64_t v) {
  uint64_t *addr = VARR_ADDR (uint64_t, const_pool);
  size_t n, len = VARR_LENGTH (uint64_t, const_pool);

  for (n = 0; n < len; n++)
    if (addr[n] == v)
      return n;
  VARR_PUSH (uint64_t, const_pool, v);
  return len;
}

struct const_ref {
  size_t pc; /* where rel32 address should be in code */
  size_t const_num;
};

typedef struct const_ref const_ref_t;
DEF_VARR (const_ref_t);
static VARR (const_ref_t) *const_refs;

struct label_ref {
  size_t label_val_disp, next_insn_disp;
  MIR_label_t label;
};

typedef struct label_ref label_ref_t;
DEF_VARR (label_ref_t);
static VARR (label_ref_t) *label_refs;

static int setup_imm_addr (uint64_t v, int *mod, int *rm, int64_t *disp32) {
  const_ref_t cr;
  size_t n;
	
  n = add_to_const_pool (v);
  setup_rip_rel_addr (0, mod, rm, disp32);
  cr.pc = 0; cr.const_num = n;
  VARR_PUSH (const_ref_t, const_refs, cr);
  return VARR_LENGTH (const_ref_t, const_refs) - 1;
}

static void out_insn (MIR_insn_t insn, const char *replacement) {
  const char *p, *insn_str;
  
  if (insn->code == MIR_ALLOCA && insn->ops[1].mode == MIR_OP_INT)
    insn->ops[1].u.i = (insn->ops[1].u.i + 7) & -8;
  for (insn_str = replacement;; insn_str = p + 1) {
    char ch, start_ch, d1, d2;
    int opcode0 = -1, opcode1 = -1, opcode2 = -1;
    int rex_w = -1, rex_r = -1, rex_x = -1, rex_b = -1;
    int mod = -1, reg = -1, rm = -1;
    int scale = -1, index = -1, base = -1;
    int prefix = -1, disp8 = -1, imm8 = -1, lb = -1;
    int64_t disp32 = -1, imm32 = -1;
    int imm64_p = FALSE;
    uint64_t imm64, v;
    MIR_op_t op;
    int const_ref_num = -1, label_ref_num = -1;
    
    for (p = insn_str; (ch = *p) != '\0' && ch != ';'; p++) {
      if ((d1 = hex_value (ch = *p)) >= 0) {
	d2 = hex_value (ch = *++p);
	gen_assert (d2 >= 0);
	if (opcode0 == -1) opcode0 = d1 * 16 + d2;
	else if (opcode1 == -1) opcode1 = d1 * 16 + d2;
	else {
	  gen_assert (opcode2 == -1);
	  opcode2 = d1 * 16 + d2;
	}
	p++;
      }
      if ((ch = *p) == 0)
	break;
      switch ((start_ch = ch = *p)) {
      case ' ': case '\t': break;
      case 'X':
	if (opcode0 >= 0) {
	  gen_assert (opcode1 < 0);
	  prefix = opcode0; opcode0 = -1;
	}
	rex_w = 1;
	break;
      case 'Y':
	if (opcode0 >= 0) {
	  gen_assert (opcode1 < 0);
	  prefix = opcode0; opcode0 = -1;
	}
	rex_w = 0;
	break;
      case 'r':
      case 'R':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '2');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_HARD_REG);
	if (start_ch == 'r')
	  setup_reg (&rex_r, &reg, op.u.hard_reg);
	else {
	  setup_rm (&rex_b, &rm, op.u.hard_reg);
	  setup_mod (&mod, 3);
	}
	break;
      case 'm':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '2');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_HARD_REG_MEM);
	setup_mem (op.u.hard_reg_mem, &mod, &rm, &scale, &base, &rex_b, &index, &rex_x, &disp8, &disp32);
	break;
      case 'a': {
	MIR_mem_t mem;
	MIR_op_t op2;

	ch = *++p;
	op = insn->ops[1];
	gen_assert (op.mode == MIR_OP_HARD_REG);
	mem.type = MIR_T_I8;
	if (ch == 'p') {
	  op2 = insn->ops[2];
	  mem.base = op.u.hard_reg; mem.scale = 1;
	  if (op2.mode == MIR_OP_HARD_REG) {
	    mem.index = op2.u.hard_reg; mem.disp = 0;
	  } else {
	    gen_assert (op2.mode == MIR_OP_INT);
	    mem.index = MIR_NON_HARD_REG; mem.disp = op2.u.i;
	  }
	} else if (ch == 'd') {
	  mem.base = op.u.hard_reg; mem.index = MIR_NON_HARD_REG; mem.scale = 1;
	  ++p;
	  mem.disp = read_hex (&p);
	} else {
	  gen_assert (ch == 'm');
	  op2 = insn->ops[2];
	  mem.index = op.u.hard_reg; mem.base = MIR_NON_HARD_REG; mem.disp = 0;
	  gen_assert (op2.mode == MIR_OP_INT && (op2.u.i == 1 || op2.u.i == 2 || op2.u.i == 4 || op2.u.i == 8));
	  mem.scale = op2.u.i;
	}
	setup_mem (mem, &mod, &rm, &scale, &base, &rex_b, &index, &rex_x, &disp8, &disp32);
	break;
      }
      case 'i':
      case 'I':
      case 'J':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '7');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_INT);
	if (start_ch == 'i') {
	  gen_assert (int8_p (op.u.i)); imm8 = (uint8_t) op.u.i;
	} else if (start_ch == 'I' ) {
	  gen_assert (int32_p (op.u.i)); imm32 = (uint32_t) op.u.i;
	} else {
	  imm64_p = TRUE; imm64 = (uint64_t) op.u.i;
	}
	break;
      case 'P':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '7');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_REF);
	imm64_p = TRUE;
	if (op.u.ref->item_type == MIR_data_item
	    && op.u.ref->u.data->name != NULL && _MIR_reserved_name_p (op.u.ref->u.data->name))
	  imm64 = (uint64_t) op.u.ref->u.data->u.els;
	else
	  imm64 = (uint64_t) op.u.ref->addr;
	break;
      case 'l': {
	label_ref_t lr;

	ch = *++p;
	gen_assert ('0' <= ch && ch <= '2');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_LABEL);
	lr.label_val_disp = lr.next_insn_disp = 0; lr.label = op.u.label;
	gen_assert (label_ref_num < 0 && disp32 < 0);
	disp32 = 0; /* To reserve the space */
	label_ref_num = VARR_LENGTH (label_ref_t, label_refs);
	VARR_PUSH (label_ref_t, label_refs, lr);
	break;
      }
      case '/':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '7');
	setup_reg (NULL, &reg, ch - '0');
	break;
      case '+':
	ch = *++p;
	gen_assert ('0' <= ch && ch <= '2');
	op = insn->ops[ch - '0'];
	gen_assert (op.mode == MIR_OP_HARD_REG);
	setup_reg (&rex_b, &lb, op.u.hard_reg);
	break;
      case 'c':
	++p;
	v = read_hex (&p);
	gen_assert (const_ref_num < 0 && disp32 < 0);
	const_ref_num = setup_imm_addr (v, &mod, &rm, &disp32);
	break;
      case 'h':
	++p;
	v = read_hex (&p);
	gen_assert (v <= 31);
	setup_reg (&rex_r, &reg, v);
	break;
      case 'H':
	++p;
	v = read_hex (&p);
	gen_assert (v <= 31);
	setup_rm (&rex_b, &rm, v);
	setup_mod (&mod, 3);
	break;
      case 'v':
      case 'V':
	++p;
	v = read_hex (&p);
	if (start_ch == 'v') {
	  gen_assert (uint8_p (v)); imm8 = v;
	} else {
	  gen_assert (uint32_p (v)); imm32 = v;
	}
	break;
      default:
	gen_assert (FALSE);
      }
    }
    if (prefix >= 0) put_byte (prefix);
    
    if (rex_w > 0 || rex_r >= 0 || rex_x >= 0 || rex_b >= 0) {
      if (rex_w < 0) rex_w = 0;
      if (rex_r < 0) rex_r = 0;
      if (rex_x < 0) rex_x = 0;
      if (rex_b < 0) rex_b = 0;
      gen_assert (rex_w <= 1 && rex_r <= 1 && rex_x <= 1 && rex_b <= 1);
      put_byte (0x40 | (rex_w << 3) | (rex_r << 2) | (rex_x << 1) | rex_b);
    }
    
    gen_assert (opcode0 >= 0 && lb <= 7);
    if (lb >= 0)
      opcode0 |= lb;
    put_byte (opcode0);
    
    if (opcode1 >= 0)
      put_byte (opcode1);
    if (opcode2 >= 0)
      put_byte (opcode2);
    
    if (mod >= 0 || reg >= 0 || rm >= 0) {
      if (mod < 0)
	mod = 0;
      if (reg < 0)
	reg = 0;
      if (rm < 0)
	rm = 0;
      gen_assert (mod <= 3 && reg <= 7 && rm <= 7);
      put_byte ((mod << 6) | (reg << 3) | rm);
    }
    if (scale >= 0 || base >= 0 || index >= 0) {
      if (scale < 0)
	scale = 0;
      if (base < 0)
	base = 0;
      if (index < 0)
	index = 0;
      gen_assert (scale <= 3 && base <= 7 && index <= 7);
      put_byte ((scale << 6) | (index << 3) | base);
    }
    if (const_ref_num >= 0)
      VARR_ADDR (const_ref_t, const_refs)[const_ref_num].pc = VARR_LENGTH (uint8_t, code);
    if (label_ref_num >= 0)
      VARR_ADDR (label_ref_t, label_refs)[label_ref_num].label_val_disp = VARR_LENGTH (uint8_t, code);
    if (disp8 >= 0)
      put_byte (disp8);
    if (disp32 >= 0)
      put_uint64 (disp32, 4);
    if (imm8 >= 0)
      put_byte (imm8);
    if (imm32 >= 0)
      put_uint64 (imm32, 4);
    if (imm64_p)
      put_uint64 (imm64, 8);

    if (label_ref_num >= 0)
      VARR_ADDR (label_ref_t, label_refs)[label_ref_num].next_insn_disp = VARR_LENGTH (uint8_t, code);

    if (ch == '\0')
      break;
  }
  
}

static uint8_t MIR_UNUSED get_short_jump_opcode (uint8_t *long_jump_opcode) {
  gen_assert (long_jump_opcode[0] == 0x0F && long_jump_opcode[1] > 0x10);
  return long_jump_opcode[1] - 0x10;
}

static int insn_ok_p (MIR_insn_t insn) {
  return find_insn_pattern_replacement (insn) != NULL;
}

static uint8_t *target_translate (MIR_item_t func, size_t *len) {
  size_t i;
  MIR_insn_t insn;
  const char *replacement;
  
  gen_assert (func->item_type == MIR_func_item);
  VARR_TRUNC (uint8_t, code, 0);
  VARR_TRUNC (uint64_t, const_pool, 0);
  VARR_TRUNC (const_ref_t, const_refs, 0);
  VARR_TRUNC (label_ref_t, label_refs, 0);
  for (insn = DLIST_HEAD (MIR_insn_t, func->u.func->insns);
       insn != NULL;
       insn = DLIST_NEXT (MIR_insn_t, insn)) {
    if (insn->code == MIR_LABEL) {
      set_label_disp (insn, VARR_LENGTH (uint8_t, code));
    } else {
      replacement = find_insn_pattern_replacement (insn);
      if (replacement == NULL) {
	fprintf (stderr, "failure:"); MIR_output_insn (stderr, insn, func->u.func, TRUE);
      } else {
	gen_assert (replacement != NULL);
	out_insn (insn, replacement);
      }
    }
  }
  /* Setting up labels */
  for (i = 0; i < VARR_LENGTH (label_ref_t, label_refs); i++){
    label_ref_t lr = VARR_GET (label_ref_t, label_refs, i);
    
    set_int64 (&VARR_ADDR (uint8_t, code)[lr.label_val_disp],
	       (int64_t) get_label_disp (lr.label) - (int64_t) lr.next_insn_disp,
	       4);
  }
  // ??? pool
  *len = VARR_LENGTH (uint8_t, code);
  return VARR_ADDR (uint8_t, code);
}

static void target_init (void) {
  VARR_CREATE (uint8_t, code, 0);
  VARR_CREATE (uint64_t, const_pool, 0);
  VARR_CREATE (const_ref_t, const_refs, 0);
  VARR_CREATE (label_ref_t, label_refs, 0);
  patterns_init ();
}

static void target_finish (void) {
  patterns_finish ();
  VARR_DESTROY (uint8_t, code);
  VARR_DESTROY (uint64_t, const_pool);
  VARR_DESTROY (const_ref_t, const_refs);
  VARR_DESTROY (label_ref_t, label_refs);
}
