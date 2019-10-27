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
  * In a state of fixing numerous bugs 
  * Full x86-64 call ABI (multiple return regs, passing structures through regs) is not implemented yet
