/* This file is a part of MIR project.
   Copyright (C) 2019-2020 Vladimir Makarov <vmakarov.gcc@gmail.com>.
*/

/* See C11 7.16 and https://www.uclibc.org/docs/psABI-x86_64.pdf */
static char stdarg_str[]
  = "#ifndef __STDARG_H\n"
    "#define __STDARG_H\n"
    "\n"
    "#ifdef __APPLE__\n"
    "typedef __darwin_va_list va_list;\n"
    "#else\n"
    "typedef struct {\n"
    "  unsigned int gp_offset;\n"
    "  unsigned int fp_offset;\n"
    "  void *overflow_arg_area;\n"
    "  void *reg_save_area;\n"
    "} va_list[1];\n"
    "#endif\n"
    "\n"
    "#define va_start(ap, param) __builtin_va_start (ap)\n"
    "#define va_arg(ap, type) __builtin_va_arg(ap, (type *) 0)\n"
    "#define va_end(ap) 0\n"
    "#define va_copy(dest, src) ((dest)[0] = (src)[0])\n"
    "\n"
    "/* For standard headers of a GNU system: */\n"
    "#ifndef __GNUC_VA_LIST\n"
    "#define __GNUC_VA_LIST 1\n"
    "#endif\n"
    "typedef va_list __gnuc_va_list;\n"
    "#endif /* #ifndef __STDARG_H */\n";
