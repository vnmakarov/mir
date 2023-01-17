/* This file is a part of MIR project.
   Copyright (C) 2018-2023 Vladimir Makarov <vmakarov.gcc@gmail.com>.
   A common include file for mir-ppc64.c and mir-gen-ppc64.c
*/

#include "mir.h"

#define TARGET_NOP (24 << (32 - 6)) /* ori 0,0,0 */

#define HREG_EL(h) h##_HARD_REG
#define REP_SEP ,
enum {
  REP8 (HREG_EL, R0, R1, R2, R3, R4, R5, R6, R7),
  REP8 (HREG_EL, R8, R9, R10, R11, R12, R13, R14, R15),
  REP8 (HREG_EL, R16, R17, R18, R19, R20, R21, R22, R23),
  REP8 (HREG_EL, R24, R25, R26, R27, R28, R29, R30, R31),
  REP8 (HREG_EL, F0, F1, F2, F3, F4, F5, F6, F7),
  REP8 (HREG_EL, F8, F9, F10, F11, F12, F13, F14, F15),
  REP8 (HREG_EL, F16, F17, F18, F19, F20, F21, F22, F23),
  REP8 (HREG_EL, F24, F25, F26, F27, F28, F29, F30, F31),
  HREG_EL (LR),
};
#undef REP_SEP

static const char *const target_hard_reg_names[] = {
  "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
  "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
  "r16", "r17", "r18", "r19", "r20", "r21", "r22", "r23",
  "r24", "r25", "r26", "r27", "r28", "r29", "r30", "r31",
  "f0", "f1", "f2", "f3", "f4", "f5", "f6", "f7",
  "f8", "f9", "f10", "f11", "f12", "f13", "f14", "f15",
  "f16", "f17", "f18", "f19", "f20", "f21", "f22", "f23",
  "f24", "f25", "f26", "f27", "f28", "f29", "f30", "f31",
  "lr",
};

static const MIR_reg_t MAX_HARD_REG = LR_HARD_REG;
static const MIR_reg_t SP_HARD_REG = R1_HARD_REG;
static const MIR_reg_t FP_HARD_REG = R31_HARD_REG;

/* Hard regs not used in machinized code, preferably call used ones. */
static const MIR_reg_t TEMP_INT_HARD_REG1 = R11_HARD_REG, TEMP_INT_HARD_REG2 = R12_HARD_REG;
static const MIR_reg_t TEMP_FLOAT_HARD_REG1 = F11_HARD_REG, TEMP_FLOAT_HARD_REG2 = F12_HARD_REG;
static const MIR_reg_t TEMP_DOUBLE_HARD_REG1 = F11_HARD_REG, TEMP_DOUBLE_HARD_REG2 = F12_HARD_REG;
static const MIR_reg_t TEMP_LDOUBLE_HARD_REG1 = F11_HARD_REG;  //???
static const MIR_reg_t TEMP_LDOUBLE_HARD_REG2 = F12_HARD_REG;

static inline int target_hard_reg_type_ok_p (MIR_reg_t hard_reg, MIR_type_t type) {
  assert (hard_reg <= MAX_HARD_REG);
  if (type == MIR_T_LD) return FALSE;
  return MIR_fp_type_p (type) ? F0_HARD_REG <= hard_reg && hard_reg <= F31_HARD_REG
                              : hard_reg < F0_HARD_REG;
}

static inline int target_fixed_hard_reg_p (MIR_reg_t hard_reg) {
  assert (hard_reg <= MAX_HARD_REG);
  return (hard_reg == FP_HARD_REG || hard_reg == SP_HARD_REG
          || hard_reg == LR_HARD_REG
          /* don't bother to allocate R0 as it has special meaning for base reg and of addi: */
          || hard_reg == R0_HARD_REG || hard_reg == R2_HARD_REG || hard_reg == R13_HARD_REG
          || hard_reg == TEMP_INT_HARD_REG1 || hard_reg == TEMP_INT_HARD_REG2
          || hard_reg == TEMP_FLOAT_HARD_REG1 || hard_reg == TEMP_FLOAT_HARD_REG2
          || hard_reg == TEMP_DOUBLE_HARD_REG1 || hard_reg == TEMP_DOUBLE_HARD_REG2
          || hard_reg == TEMP_LDOUBLE_HARD_REG1 || hard_reg == TEMP_LDOUBLE_HARD_REG2);
}

static int target_locs_num (MIR_reg_t loc, MIR_type_t type) {
  return /*loc > MAX_HARD_REG && */ type == MIR_T_LD ? 2 : 1;
}

static const int PPC_JUMP_OPCODE = 18;
