static const MIR_reg_t MAX_HARD_REG = 16 + 16 - 1; /* GP and XMM regs */

static const MIR_reg_t BP_HARD_REG = 6, SP_HARD_REG = 7;

static inline int hard_reg_mode_ok_p (MIR_reg_t hard_reg, MIR_op_mode_t mode) {
  assert (hard_reg <= MAX_HARD_REG);
  assert (mode == MIR_OP_INT || mode == MIR_OP_FLOAT || mode == MIR_OP_DOUBLE);
  return mode == MIR_OP_INT ? hard_reg < 16 : hard_reg >= 16;
}

static inline int fixed_hard_reg_p (MIR_reg_t hard_reg) {
  assert (hard_reg <= MAX_HARD_REG);
  return hard_reg == BP_HARD_REG || hard_reg == SP_HARD_REG;
}
