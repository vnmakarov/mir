MIR_item_t create_mir_func_with_loop (MIR_module_t *m) {
  MIR_item_t func;
  MIR_label_t fin, cont;
  MIR_reg_t ARG1, R2;
  MIR_type_t res_type;
  
  if (m != NULL)
    *m = MIR_new_module ("m");
  res_type = MIR_T_I64;
  func = MIR_new_func ("loop", 1, &res_type, 1, MIR_T_I64, "arg1");
  R2 = MIR_new_func_reg (func->u.func, MIR_T_I64, "count");
  ARG1 = MIR_reg ("arg1", func->u.func);
  fin = MIR_new_label (); cont = MIR_new_label ();
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (R2), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, cont);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (R2), MIR_new_reg_op (R2), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_BLT, MIR_new_label_op (cont), MIR_new_reg_op (R2), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, fin);
  MIR_append_insn (func, MIR_new_ret_insn (1, MIR_new_reg_op (R2)));
  MIR_finish_func ();
  if (m != NULL)
    MIR_finish_module ();
  return func;
}
