static MIR_item_t create_mir_func_sieve_api (MIR_module_t *m_res) {
  MIR_item_t func;
  MIR_module_t m;
  MIR_reg_t iter, count, i, k, prime, temp, flags;
  MIR_label_t loop = MIR_new_label (), loop2 = MIR_new_label (), loop3 = MIR_new_label (), loop4 = MIR_new_label ();
  MIR_label_t fin = MIR_new_label (), fin2 = MIR_new_label (), fin3 = MIR_new_label (), fin4 = MIR_new_label ();
  MIR_label_t cont3 = MIR_new_label ();
  
  m = MIR_new_module ("m_sieve");
  if (m_res != NULL)
    *m_res = m;
  func = MIR_new_func ("sieve", MIR_T_I64, 0);
  iter = MIR_new_func_reg (func->u.func, MIR_T_I64, "iter"); count = MIR_new_func_reg (func->u.func, MIR_T_I64, "count");
  i = MIR_new_func_reg (func->u.func, MIR_T_I64, "i"); k = MIR_new_func_reg (func->u.func, MIR_T_I64, "k");
  prime = MIR_new_func_reg (func->u.func, MIR_T_I64, "prime"); temp = MIR_new_func_reg (func->u.func, MIR_T_I64, "temp");
  flags = MIR_new_func_reg (func->u.func, MIR_T_I64, "flags");
  MIR_append_insn (func, MIR_new_insn (MIR_ALLOCA, MIR_new_reg_op (flags), MIR_new_int_op (819000)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (iter), MIR_new_int_op (0)));
  MIR_append_insn (func, loop);
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin),
				       MIR_new_reg_op (iter), MIR_new_int_op (100)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (count), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (i), MIR_new_int_op (0)));
  MIR_append_insn (func, loop2);
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin2),
				       MIR_new_reg_op (i), MIR_new_int_op (819000)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_mem_op (MIR_T_U8, 0, flags, i, 1), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (i), MIR_new_reg_op (i), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_JMP, MIR_new_label_op (loop2)));
  MIR_append_insn (func, fin2);
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (i), MIR_new_int_op (0)));
  MIR_append_insn (func, loop3);
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin3),
				       MIR_new_reg_op (i), MIR_new_int_op (819000)));
  MIR_append_insn (func, MIR_new_insn (MIR_BEQ, MIR_new_label_op (cont3),
				       MIR_new_mem_op (MIR_T_U8, 0, flags, i, 1), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (temp), MIR_new_reg_op (i), MIR_new_reg_op (i)));
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (prime), MIR_new_reg_op (temp), MIR_new_int_op (3)));
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (k), MIR_new_reg_op (i), MIR_new_reg_op (prime)));
  MIR_append_insn (func, loop4);
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin4),
				       MIR_new_reg_op (k), MIR_new_int_op (819000)));
  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_mem_op (MIR_T_U8, 0, flags, k, 1), MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (k), MIR_new_reg_op (k), MIR_new_reg_op (prime)));
  MIR_append_insn (func, MIR_new_insn (MIR_JMP, MIR_new_label_op (loop4)));
  MIR_append_insn (func, fin4);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (count), MIR_new_reg_op (count), MIR_new_int_op (1)));
  MIR_append_insn (func, cont3);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (i), MIR_new_reg_op (i), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_JMP, MIR_new_label_op (loop3)));
  MIR_append_insn (func, fin3);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (iter), MIR_new_reg_op (iter), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_JMP, MIR_new_label_op (loop)));
  MIR_append_insn (func, fin);
  MIR_append_insn (func, MIR_new_ret_insn (1, MIR_new_reg_op (count)));
  MIR_finish_func ();
  MIR_finish_module ();
  return func;
}
