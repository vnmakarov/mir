# C to MIR compiler
  * Implemention of a small C11 (2011 ANSI C standard) to MIR compiler
    * no optional features: variable size arrays, complex, atomic
  * Minimal compiler code dependency.  No additional tools (like yacc/flex) are used
  * Simplicity of implementation over speed to make code easy to learn and maintain
    * Four passes to divide compilation on manageable sub-tasks:
      1. Preprocessor pass generating tokens
      2. Parsing pass generating AST (Abstract Syntax Tree). To be close ANSI standard grammar
         as soon as possible, [**PEG**](https://en.wikipedia.org/wiki/Parsing_expression_grammar)
         manual parser is used
      3. Context pass checking context constraints and augmenting AST
      4. Generation pass producing MIR

  ![C to MIR](c2mir.svg)

## Current state C to MIR compiler
  * **On Oct 25 we achieved a successful bootstrap**
    * `c2m` compiles own sources and generate binary MIR, this binary
      MIR compiles `c2m` sources again and generate another binary
      MIR, and the two binary MIR files are identical
    * The bootstrap test takes about CPU 10 sec (for comparison GCC minimal bootstrap takes about 2 CPU hours)    
  * Full x86-64 call ABI (multiple return regs, passing structures through regs) is not implemented yet
