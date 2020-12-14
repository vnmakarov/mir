/* See C11 7.23 */
static char stdnoreturn_str[]
  = "#ifndef __STDNORETURN_H\n"
    "#define __STDNORETURN_H\n"
    "\n"
    "#define noreturn _Noreturn\n"
    "#endif /* #ifndef __STDNORETURN_H */\n";
