MIR_item_t create_mir_example2 (MIR_module_t *m) {
  MIR_item_t func;
  MIR_reg_t ARG1, ARG2;
  
  if (m != NULL)
    *m = MIR_new_module ("m");
  func = MIR_new_func ("memop", MIR_T_I64, 0, 2, MIR_T_I64, "arg1", MIR_T_I64, "arg2");
  ARG1 = MIR_reg ("arg1", func->u.func); ARG2 = MIR_reg ("arg2", func->u.func);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_mem_op (MIR_T_I64, 0, ARG1, ARG2, 8),
				       MIR_new_mem_op (MIR_T_I64, 64, ARG1, 0, 0), MIR_new_mem_op (MIR_T_I64, 0, 0, ARG1, 8)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_T_I64, 0, ARG1, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_T_I64, 0, 0, ARG2, 1)));
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_mem_op (MIR_T_I64, 1024, 0, 0, 0)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_mem_op (MIR_T_I64, 0, ARG1, ARG2, 8), MIR_new_mem_op (MIR_T_I64, 0, ARG1, 0, 8)));
  MIR_finish_func ();
  if (m != NULL)
    MIR_finish_module ();
  return func;
}
