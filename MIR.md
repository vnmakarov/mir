# Medium Intermediate Representation (file mir.h)
  * This document describes MIR itself, API for its creation, and MIR textual representation
  * MIR textual representation is assembler like.  Each directive or insn should be put on a separate line
  * In MIR textual syntax we use
    * `[]` for optional construction
    * `{}` for repeation zero or more times
    * `<>` for some informal construction description or construction already described or will be described
  
## MIR program
   * MIR program consists of MIR **modules**
   * To start work with MIR program, you should first call API function `MIR_init`
   * API function `MIR_finish` should be called last.  It frees all internal data used to work with MIR program
   * API function `MIR_output (FILE *f)` outputs MIR textual representation of the program into given file
   * API function `MIR_scan_string (const char *str)` reads textual MIR representation given by a string
   * API functions `MIR_write (FILE *f)` and `MIR_read (FILE *f)` outputs and reads **binary MIR representation**
     to/from given file
     * Binary MIR representation much more compact and faster to read than textual one

## MIR data type
   * MIR program works with the following **data types**:
     * `MIR_T_I8` and `MIR_T_U8` -- signed and unsigned 8-bit integer values
     * `MIR_T_I16` and `MIR_T_U16` -- signed and unsigned 16-bit integer values
     * `MIR_T_I32` and `MIR_T_U32` -- signed and unsigned 32-bit integer values
     * `MIR_T_I64` and `MIR_T_U64` -- signed and unsigned 64-bit integer values
       * ??? signed and unsigned 64-bit integer types in most cases
         are interchangeable as insns themselves decide how to treat
         their value
     * `MIR_T_F` and `MIR_T_D` -- IEEE single and double precision floating point values
     * `MIR_T_P` -- pointer values.  Depending on the target pointer value is actually 32-bit or 64-bit integer value
     * `MIR_T_V` representing any value absence (void type)
   * MIR textual representation of the types are correpondinly `i8`,
     `u8`, `i16`, `u16`, `i32`, `u32`, `i64`, `u64`, `f`, `d`, `p`,
     and `v`
   
## MIR module
  * Module is a high level entity of MIR program
  * Module is created through API function `MIR_module_t MIR_new_module (const char *name)`
  * Module creation is finished by calling API function `MIR_finish_module`
  * You can create only one module at any given time
  * MIR module consists of **items**.  There are following **item types** (and function for their creation):
    * **Function**: `MIR_func_item`
    * **Import**: `MIR_import_item` (`MIR_item_t MIR_new_import (const char *name)`)
    * **Export**: `MIR_export_item` (`MIR_item_t MIR_new_export (const char *name)`)
    * **Forward declaration**: `MIR_forward_item` (`MIR_item_t MIR_new_forward (const char *name)`)
    * **Prototype**: `MIR_proto_item` (`MIR_new_proto_arr` and `MIR_new_proto`
      analogous to `MIR_new_func_arr` and `MIR_new_func` -- see below)
    * **Data**: `MIR_data_item` with optional name
      (`MIR_item_t MIR_new_data (const char *name, MIR_type_t el_type, size_t nel, const void *els)`
       or `MIR_item_t MIR_new_string_data (const char *name, const char *str)`)
    * **Memory segement**: `MIR_bss_item` with optional name (`MIR_item_t MIR_new_bss (const char *name, size_t len)`)
  * Names of MIR functions, imports, and prototypes should be unique in a module
  * MIR text module syntax looks the folowing:
```
    <module name>: module
                   {<module item>}
                   endmodule
```

## MIR function
  * Function is an module item
  * Function has a **frame**, a stack memory reserved for each function invocation
  * Function has **local variables** (sometimes called **registers**), a part of which are **arguments**
    * A variable should have an unique name in the function
    * A **predeclared variable** with name `fp` (type ???) contains address of the function frame
    * A variable is represented by a structure of type `MIR_var_t`
      * The structure contains variable name and its type
  * MIR function with its arguments is created through API function `MIR_item_t MIR_new_func (const
    char *name, MIR_type_t res_type, size_t frame_size, size_t nargs,
    ...)` or function `MIR_item_t MIR_new_func_arr (const char *name, MIR_type_t
    res_type, size_t frame_size, size_t nargs, MIR_var_t *arg_vars)`
    * Argument variables can be any type (except `MIR_T_V`)
      * This type only denotes how the argument value is passed
      * Any integer type argument variable has actually type `MIR_T_I64`
  * MIR function creation is finished by calling API function `MIR_finish_func (void)`
  * You can create only one MIR function at any given time
  * MIR text function syntax looks the folowing:
```
    <function name>: func <result type>, <frame size>, [ arg-var {, <arg-var> } ]
                     {<insn>}
                     endfun
```
  * Non-argument function variables are created through API function
    `MIR_reg_t MIR_new_func_reg (MIR_func_t func, MIR_type_t type, const char *name)`
    * The only permitted integer type for the variable is `MIR_T_I64` (or MIR_T_U64???)
    * Names in form `t<number>` can not be used as they are fixed for internal purposes
    * You can create function variables even after finishing the
      function creation.  This can be used to modify function insns,
      e.g. for optimizations
  * Non-argument variable declaration syntax in MIR textual representation looks the folowing:
```
    local [ <var type>:<var name> {, <var type>:<var name>} ]
```
  * In MIR textual representation variable should be defined through `local` before its use
    
## MIR insn operands
  * MIR insns work with operands
  * There are following operands:
    * Signed or unsigned **64-bit integer value operands** created through API functions
      `MIR_op_t MIR_new_int_op (int64_t v)` and `MIR_op_t MIR_new_uint_op (uint64_t v)`
      * In MIR text they are represented the same way as C integer numbers (e.g. octal, decimal, hexdecimal ones)
    * **Float or double value operands** created through API functions `MIR_op_t MIR_new_float_op (float v)`
      and `MIR_op_t MIR_new_double_op (double v)`
      * In MIR text they are represented the same way as C floating point numbers
    * **String operands** created through API functions `MIR_op_t MIR_new_str_op (const char *str)`
      * In MIR text they are represented the same way as C string
      * Strings for each operand are put into memory (which can be modified) and the memory address actually presents the string
    * **Label operand** created through API function `MIR_op_t MIR_new_label_op (MIR_label_t label)`
      * Here `label` is a special insn created by API function `MIR_insn_t MIR_new_label (void)`
      * In MIR text, they are represented by unique label name
    * **Reference operands** created through API function `MIR_op_t MIR_new_ref_op (MIR_item_t item)`
      * In MIR text, they are represented by the corresponding item name
    * **Register (variable) operands** created through API function `MIR_op_t MIR_new_reg_op (MIR_reg_t reg)`
      * In MIR text they are represented by the correspoding variable name
      * Value of type `MIR_reg_t` is returned by function `MIR_new_func_reg`
        or can be gotten by function `MIR_reg_t MIR_reg (const char *reg_name, MIR_func_t func)`, e.g. for argument-variables
    * **Memory operands** consists of type, displacement, base
      register, index register and index scale.  Memory operand is
      created through API function `MIR_op_t MIR_new_mem_op (MIR_type_t type,
      MIR_disp_t disp, MIR_reg_t base, MIR_reg_t index, MIR_scale_t
      scale)`
      * The arguments define address of memory as `disp + base + index * scale`
      * Integer type input memory is transformed to 64-bit integer value with sign or zero extension
        depending on signedness of the type
      * result 64-bit integer value is truncated to integer memory type
      * Memory operand has the following syntax in MIR text (absent displacement means zero one,
        absent scale means one, scale should be 1, 2, 4, or 8):
      
```
	  <type>: <disp>
	  <type>: [<disp>] (<base reg> [, <index reg> [, <scale> ]])
```
  * API function `MIR_output_op (FILE *f, MIR_op_t op, MIR_func_t func)` outputs the operand
    textual representation into given file
        

## MIR insns
  * All MIR insns (but call one) expects fixed number of operands
  * Most MIR insns are 3-operand insns: two inputs and one output
  * In majority cases **the first insn operand** describes where the insn result (if any) will be placed
  * Only register or memory operand can be insn output (result) operand
  * MIR insn can be created through API functions `MIR_insn_t MIR_new_insn (MIR_insn_code_t code, ...)`
    and `MIR_insn_t MIR_new_insn_arr (MIR_insn_code_t code, size_t nops, MIR_op_t *ops)`
    * Number of operands and their types should be what is expected by the insn being created
  * You can get insn name and number of insn operands through API functions
    `const char *MIR_insn_name (MIR_insn_code_t code)` and `size_t MIR_insn_nops (MIR_insn_t insn)`
  * You can add a created insn at the beginning or end of function insn list through API functions
    `MIR_prepend_insn (MIR_item_t func, MIR_insn_t insn)` and `MIR_append_insn (MIR_item_t func, MIR_insn_t insn)`
  * You can insert a created insn in the middle of function insn list through API functions
    `MIR_insert_insn_after (MIR_item_t func, MIR_insn_t after, MIR_insn_t insn)` and
    `MIR_insert_insn_before (MIR_item_t func, MIR_insn_t before, MIR_insn_t insn)`
    * The insn `after` and `before` should be alread in the list
  * You can remove insn from the function list through API function `MIR_remove_insn (MIR_item_t func, MIR_insn_t insn)`
  * The insn should be not inserted in the list if it is already there
  * The insn should be not removed form the list if it is not there
  * API function `MIR_output_insn (FILE *f, MIR_insn_t insn, MIR_func_t func, int newline_p)` output the insn
    textual representation into given file with a newline at the end depending on value of `newline_p`
  * Insn has the following syntax in MIR text:
```
	  {<label name>:} [<insn name> <operand> {, <operand>}]
```
  * More one insn can be put on the same line by separting the insns by `;`

### MIR move insns
  * There are following MIR move insns:

    | Insn Code               | Nops |   Description                                          |
    |-------------------------|-----:|--------------------------------------------------------|
    | `MIR_MOV`               | 2    | move 64-bit integer values                             |
    | `MIR_FMOV`              | 2    | move **single precision** floating point values        |
    | `MIR_DMOV`              | 2    | move **double precision** floating point values        |

### MIR integer insns
  * If insn has suffix `S` in insn name, the insn works with lower 32-bit part of 64-bit integer value
  * The higher part of 32-bit insn result is undefined
  * If insn has prefix `U` in insn name, the insn treats integer as unsigned integers
  * Some insns has no unsigned variant as MIR is oriented to CPUs with two complement integer arithmetic
    (the huge majority of all CPUs)
  
    | Insn Code               | Nops |   Description                                          |
    |-------------------------|-----:|--------------------------------------------------------|
    | `MIR_EXT8`              | 2    | **sign** extension of lower **8 bit** input part       |
    | `MIR_UEXT8`             | 2    | **zero** extension of lower **8 bit** input part       |
    | `MIR_EXT16`             | 2    | **sign** extension of lower **16 bit** input part      |
    | `MIR_UEXT16`            | 2    | **zero** extension of lower **16 bit** input part      |
    | `MIR_EXT32`             | 2    | **sign** extension of lower **32 bit** input part      |
    | `MIR_UEXT32`            | 2    | **zero** extension of lower **32 bit** input part      |
    |                         |      |                                                        |
    | `MIR_NEG`               | 2    | changing sign of **64-bit* integer value               |
    | `MIR_NEGS`              | 2    | changing sign of **32-bit* integer value               |
    |                         |      |                                                        |
    | `MIR_ADD`, `MIR_SUB`    | 3    | **64-bit** integer addition and subtraction            |
    | `MIR_ADDS`, `MIR_SUBS`  | 3    | **32-bit** integer addition and subtraction            |
    | `MIR_MUL`, `MIR_DIV`    | 3    | **64-bit signed**  multiplication and divison          |
    | `MIR_UMUL`, `MIR_UDIV`  | 3    | **64-bit unsigned** integer multiplication and divison |
    | `MIR_MULS`, `MIR_DIVS`  | 3    | **32-bit signed**  multiplication and divison          |
    | `MIR_UMULS`, `MIR_UDIVS`| 3    | **32-bit unsigned** integer multiplication and divison |
    | `MIR_MOD`               | 3    | **64-bit signed**  modulo operation                    |
    | `MIR_UMOD`              | 3    | **64-bit unsigned** integer modulo operation           |
    | `MIR_MODS`              | 3    | **32-bit signed**  modulo operation                    |
    | `MIR_UMODS`             | 3    | **32-bit unsigned** integer modulo operation           |
    |                         |      |                                                        |
    | `MIR_AND`, `MIR_OR`     | 3    | **64-bit** integer bitwise AND and OR                  |
    | `MIR_ANDS`, `MIR_ORS`   | 3    | **32-bit** integer bitwise AND and OR                  |
    | `MIR_XOR`               | 3    | **64-bit** integer bitwise XOR                         |
    | `MIR_XORS`              | 3    | **32-bit** integer bitwise XOR                         |
    |                         |      |                                                        |
    | `MIR_LSH`               | 3    | **64-bit** integer left shift                          |
    | `MIR_LSHS`              | 3    | **32-bit** integer left shift                          |
    | `MIR_RSH`               | 3    | **64-bit** integer right shift with **sign** extension |
    | `MIR_RSHS`              | 3    | **32-bit** integer right shift with **sign** extension |
    | `MIR_URSH`              | 3    | **64-bit** integer right shift with **zero** extension |
    | `MIR_URSHS`             | 3    | **32-bit** integer right shift with **zero** extension |
    |                         |      |                                                        |
    | `MIR_EQ`, `MIR_NE`      | 3    | equality/inequality of **64-bit** integers             |
    | `MIR_EQS`, `MIR_NES`    | 3    | equality/inequality of **32-bit** integers             |
    | `MIR_LT`, `MIR_LE`      | 3    | **64-bit signed** less than/less than or equal         |
    | `MIR_ULT`, `MIR_ULE`    | 3    | **64-bit unsigned** less than/less than or equal       |
    | `MIR_LTS`, `MIR_LES`    | 3    | **32-bit signed** less than/less than or equal         |
    | `MIR_ULTS`, `MIR_ULES`  | 3    | **32-bit unsigned** less than/less than or equal       |
    | `MIR_GT`, `MIR_GE`      | 3    | **64-bit signed** greater than/greater than or equal   |
    | `MIR_UGT`, `MIR_UGE`    | 3    | **64-bit unsigned** greater than/greater than or equal |
    | `MIR_GTS`, `MIR_GES`    | 3    | **32-bit signed** greater than/greater than or equal   |
    | `MIR_UGTS`, `MIR_UGES`  | 3    | **32-bit unsigned** greater than/greater than or equal |

### MIR floating point insns
  * If insn has prefix `F` in insn name, the insn is single precision float point insn.  Its operands should have `MIR_T_F` type
  * Otherwise, insn has prefix `D` in insn name and the insn is double precision float point insn.
    Its operands should have `MIR_T_D` type.
  * The result of comparison insn is a 64-bit integer value, so the result oeprand should be of integer type
  
    | Insn Code               | Nops |   Description                                                  |
    |-------------------------|-----:|----------------------------------------------------------------|
    | `MIR_F2I`, `MIR_D2I`    | 2    | transforming floating point value into 64-bit integer          |
    | `MIR_F2D`               | 2    | transforming single to double precision FP value               |
    | `MIR_D2F`               | 2    | transforming double to single precision FP value               |
    | `MIR_I2F`, `MIR_I2D`    | 2    | transforming floating point value into 64-bit integer          |
    | `MIR_UI2F`, `MIR_UI2D`  | 2    | transforming floating point value into unsigned 64-bit integer |
    | `MIR_FNEG`, `MIR_DNEG`  | 2    | changing sign of floating point value                          |
    | `MIR_FADD`, `MIR_FSUB`  | 3    | **single** precision addition and subtraction                  |
    | `MIR_DADD`, `MIR_DSUB`  | 3    | **double** precision addition and subtraction                  |
    | `MIR_FMUL`, `MIR_FDIV`  | 3    | **single** precision multiplication and divison                |
    | `MIR_DMUL`, `MIR_DDIV`  | 3    | **double** precision multiplication and divison                |
    | `MIR_FEQ`, `MIR_FNE`    | 3    | equality/inequality of **single** precision values             |
    | `MIR_DEQ`, `MIR_DNE`    | 3    | equality/inequality of **double** precision values             |
    | `MIR_FLT`, `MIR_FLE`    | 3    | **single** precision less than/less than or equal              |
    | `MIR_DLT`, `MIR_DLE`    | 3    | **double** precision less than/less than or equal              |
    | `MIR_FGT`, `MIR_FGE`    | 3    | **single** precision greater than/greater than or equal        |
    | `MIR_DGT`, `MIR_DGE`    | 3    | **double** precision greater than/greater than or equal        |

### MIR branch insns
  * The first operand of the insn should be label

    | Insn Code               | Nops |   Description                                                 |
    |-------------------------|-----:|---------------------------------------------------------------|
    | `MIR_JMP`               | 1    | uncontional jump to the label                                 |
    | `MIR_BT`                | 2    | jump to the label when 2nd **64-bit** operand is **nonzero**  |
    | `MIR_BTS`               | 2    | jump to the label when 2nd **32-bit** operand is **nonzero**  |
    | `MIR_BF`                | 2    | jump to the label when 2nd **64-bit** operand is **zero**     |
    | `MIR_BFS`               | 2    | jump to the label when 2nd **32-bit** operand is **zero**     |

### MIR integer comparison and branch insn
  * The first operand of the insn should be label.  Label will be the next executed insn if the result of comparison is non-zero

    | Insn Code               | Nops |   Description                                                 |
    |-------------------------|-----:|---------------------------------------------------------------|
    | `MIR_BEQ`, `MIR_BNE`    | 3    | jump on **64-bit** equality/inequality                        |
    | `MIR_BEQS`, `MIR_BNES`  | 3    | jump on **32-bit** equality/inequality                        |
    | `MIR_BLT`, `MIR_BLE`    | 3    | jump on **signed 64-bit** less than/less than or equal        |
    | `MIR_UBLT`, `MIR_UBLE`  | 3    | jump on **unsigned 64-bit** less than/less than or equal      |
    | `MIR_BLTS`, `MIR_BLES`  | 3    | jump on **signed 32-bit** less than/less than or equal        |
    | `MIR_UBLTS`, `MIR_UBLES`| 3    | jump on **unsigned 32-bit** less than/less than or equal      |
    | `MIR_BGT`, `MIR_BGE`    | 3    | jump on **signed 64-bit** greater than/greater than or equal  |
    | `MIR_UBGT`, `MIR_UBGE`  | 3    | jump on **unsigned 64-bit** greater than/greater than or equal|
    | `MIR_BGTS`, `MIR_BGES`  | 3    | jump on **signed 32-bit** greater than/greater than or equal  |
    | `MIR_UBGTS`, `MIR_UBLES`| 3    | jump on **unsigned 32-bit** greater than/greater than or equal|

### MIR floating point comparison and branch insn
  * The first operand of the insn should be label.  Label will be the next executed insn if the result of comparison is non-zero
  * See comparison semantics in the corresponding comparison insns

    | Insn Code               | Nops |   Description                                                  |
    |-------------------------|-----:|----------------------------------------------------------------|
    | `MIR_FEQ`, `MIR_FNE`    | 3    | jump on **single** precision equality/inequality               |
    | `MIR_DEQ`, `MIR_DNE`    | 3    | jump on **double** precision equality/inequality               |
    | `MIR_FLT`, `MIR_FLE`    | 3    | jump on **single** precision less than/less than or equal      |
    | `MIR_DLT`, `MIR_DLE`    | 3    | jump on **double** precision less than/less than or equal      |
    | `MIR_FGT`, `MIR_FGE`    | 3    | jump on **single** precision greater than/greater than or equal|
    | `MIR_DGT`, `MIR_DGE`    | 3    | jump on **double** precision greater than/less/ than or equal  |

### MIR return insns
  * Return insn should correspond to return type of the function
  * 64-bit integer value is truncated to the function return type first
  * The return value will be the function call value

    | Insn Code               | Nops |   Description                                                  |
    |-------------------------|-----:|----------------------------------------------------------------|
    | `MIR_RET`               | 1    | returning integer value                                        |
    | `MIR_FRET`              | 1    | returning **single** precision floating point value            |
    | `MIR_DRET`              | 1    | returning **double** precision floating point value            |

### MIR_CALL insn
  * The only insn which has variable number of operands
  * The first operand is a prototype reference operand
  * The second operand is a called function address
    * The prototype should correspond MIR function definition if function address represents a MIR function
    * The prototype should correspond C function definition if the address is C function address
  * If the prototype has non-void return type, the next operand is an
    output operand which will contain the result value of the function
    call
  * The subsequent operands are arguments.  Their types and number and should be the same as in the prototype
    * Integer arguments are truncated according to integer prototype argument type
  
### MIR_ALLOCA insn
  * Reserve memory on the stack whose size is given as the 2nd operand and assign the memory address to the 1st operand
  * The reserved memory will be aligned according target ABI

## MIR API example
  * The following code on C creates MIR analog of C code
    `int64_t loop (int64_t arg1) {int64_t count = 0; while (count < arg1) count++; return count;}`
```
  MIR_module_t m = MIR_new_module ("m");
  MIR_item_t func = MIR_new_func ("loop", MIR_T_I64, 0, 1, MIR_T_I64, "arg1");
  MIR_reg_t COUNT = MIR_new_func_reg (func->u.func, MIR_T_I64, "count");
  MIR_reg_t ARG1 = MIR_reg ("arg1", func->u.func);
  MIR_label_t fin = MIR_new_label (), cont = MIR_new_label ();

  MIR_append_insn (func, MIR_new_insn (MIR_MOV, MIR_new_reg_op (COUNT),
                                       MIR_new_int_op (0)));
  MIR_append_insn (func, MIR_new_insn (MIR_BGE, MIR_new_label_op (fin),
                                       MIR_new_reg_op (COUNT), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, cont);
  MIR_append_insn (func, MIR_new_insn (MIR_ADD, MIR_new_reg_op (COUNT),
                                       MIR_new_reg_op (COUNT), MIR_new_int_op (1)));
  MIR_append_insn (func, MIR_new_insn (MIR_BLT, MIR_new_label_op (cont),
                                       MIR_new_reg_op (COUNT), MIR_new_reg_op (ARG1)));
  MIR_append_insn (func, fin);
  MIR_append_insn (func, MIR_new_insn (MIR_RET, MIR_new_reg_op (COUNT)));
  MIR_finish_func ();
  MIR_finish_module ();
```

## MIR text example

```
m_sieve:  module
          export sieve
sieve:    func i32, 819000, i32:N
          local i64:iter, i64:count, i64:i, i64:k, i64:prime, i64:temp, i64:flags
          mov flags, fp
          mov iter, 0
loop:     bge fin, iter, N
          mov count, 0;  mov i, 0
loop2:    bge fin2, i, 819000
          mov u8:(flags, i), 1;  add i, i, 1
          jmp loop2
fin2:     mov i, 0
loop3:    bge fin3, i, 819000
          beq cont3, u8:(flags,i), 0
          add temp, i, i;  add prime, temp, 3;  add k, i, prime
loop4:    bge fin4, k, 819000
          mov u8:(flags, k), 0;  add k, k, prime
          jmp loop4
fin4:     add count, count, 1
cont3:    add i, i, 1
          jmp loop3
fin3:     add iter, iter, 1
          jmp loop
fin:      rets count
          endfunc
          endmodule
m_ex100:  module
format:   string "sieve (10) = %d\n"
p_printf: proto v, p, i32
p_seive:  proto i32, i32
          export ex100
          import sieve, printf
ex100:    func v
          local i64:r
          call p_sieve, sieve, r, 100
          call p_printf, printf, format, r
          endfunc
          endmodule
```

## Other MIR API functions
  * MIR API can find a lot of errors.  They are reported through a
    error function of type `void (*MIR_error_func_t) (MIR_error_type_t
    error_type, const char *message)`.  The function is considered to
    never return.  To see all error types, please look at the
    definition of error type `MIR_error_type_t` in file mir.h
  * You can get and set up the current error function through API
    functions `MIR_error_func_t MIR_get_error_func (void)` and `MIR_set_error_func
    (MIR_error_func_t func)`.
    * The default error function prints the message into stderr and call `exit (1)`
  * MIR is pretty flexible and can describe complex insns, e.g. insns
    whose all operands are memory.  Sometimes you need a very simple
    form of MIR representation.  API function `MIR_simplify_func
    (MIR_item_t func, int mem_float_p)` simplifies the function insns as much as
    possible by adding new insns and registers resulting in a form in which:
    * immediate, memory, reference operands can be used only in move insns
    * memory have only base register (no displacement and index register)
    * string and float immediate operands (if `mem_float_p`) are changed onto
      references for new string and data items
  * Before execution of MIR code (through interpreter or machine code generated by JIT),
    you need to load and link it
    * You can load MIR module through API function `MIR_load_module
      (MIR_module_t m)`.  The function allocates the module data/bss
      and makes visible the exported module items to other module
      during subsequent linking.  There is a guarantee that the
      different data/bss items will be in adjacent memory if the
      data/bss items go one after another and all the data/bss items
      except the first one are anonymous (it means they have no name).
      Such adjacent data/bss items are called a **section**.
      Alignment of the section is malloc alignment.  There are no any
      memory space between data/bss in the section.  If you need to
      provide necessary alignment of a data/bss in the section you
      should do it yourself by putting additional anonymous data/bss
      before given data/bss if it is necessary.  BSS memory is
      initialized by zero and data memory is initialized by the
      corresponding data.  If there is already an exported item with
      the same name, it will be not visible for linking anymore.  Such
      visibility mechanism permits usage of different versions of the
      same function
    * MIR permits to use imported items not implemented in MIR, for
      example to use C standard function `strcmp`.  You need to inform
      MIR about it.  API function `MIR_load_external (const char
      *name, void *addr)` informs that imported items with given name
      have given address (e.g. C function address or data)
    * Imports/exports of modules loaded since the last link can be
      linked through API function `MIR_link (void (*set_interface) (MIR_item_t item))`
    * `MIR_link` function also sets up call interface
      * If you pass `MIR_set_interp_interface` to `MIR_link`, then
        called functions from MIR code will be interpreted
      * If you pass `MIR_set_gen_interface` to `MIR_link`, then
        MIR-generator will generate machine code for all loaded MIR
        functions and called functions from MIR code will execute the
        machine code

# MIR code execution
  * Linked MIR code can be exectuted by an **interpreter** or machine code generated by **MIR generator**

# MIR code interpretation (file mir-interp.h)
  * Before use of the intepreter you should initialize it by API function `MIR_interp_init (void)`
  * API function `MIR_interp_finish (void)` should be called last after any interpreter usage.  It frees all internal interpreter data
  * The interpreter works with values represented by type `MIR_val_t` which is union `union {..., int64_t i; uint64_t u; float f; double d;}`
  * You can execute a MIR function code by API functions `MIR_val_t
    MIR_interp (MIR_item_t func_item, size_t nargs, ...)` and
    `MIR_val_t MIR_interp_arr (MIR_item_t func_item, size_t nargs,
    MIR_val_t *vals)`
    * Please remember that these functions simplify the MIR code function if it was not simplified yet
  * You can execute a MIR function code also through C function call
    mechanism.  First you need to setup the C function interface
    through API function `MIR_set_interp_interface (MIR_item_t
    func_item)`.  After that you can `func_item->addr` to call the
    MIR function as usual C function
    * C function interface is implemented by generation of machine
      code specialized for MIR function.  Therefore the interface
      works only on the same targets as MIR generator

# MIR generator (file mir-gen.h)
  * Before use of MIR generator you should initialize it by API function `MIR_gen_init (void)`
  * API function `MIR_gen_finish (void)` should be called last after any generator usage.
    It frees all internal generator data
  * API function `void *MIR_gen (MIR_item_t func_item)` generates machine code of given MIR function
    and returns an address to call it.  You can call the code as usual C function by using this address
    as the called function address
