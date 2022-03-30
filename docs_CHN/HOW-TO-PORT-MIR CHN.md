# 介绍
  将MIR移植到其它目标平台上需要实现许多平台相关的代码，
  在我看来大概有3千行C代码那么多，且对于一个有经验的人
  来说写完需要花费一个月的时间。

  这份文档列举了移植MIR所需要做的事情。首先我建议先移植MIR解释器和`c2mir`，
  并且你需要为其编写`mir-<target>.c`的文件，然后你可以通过添加`mir-gen-<target>.c`的文件来移植MIR生成器。更多细节你可以参考已有的
  实现：`mir-x86_64.c`, `mir-aarhc64.c`,`mir-gen-x86_64.c`,
  `mir-gen-aarhc64.c`
  
## 常见的平台相关函数 (`mir-<target.c>`文件中)
  这些函数可以在MIR解释器和生成器中使用，参考`mir-x86_64.c`或`mir-aarch64.c`
  然后在`mir-<target>.c`文件中实现。你可以使用MIR的内部函数
  `_MIR_publish_code`,
  `_MIR_get_new_code_addr`, `_MIR_publish_code_by_addr`,
  `_MIR_change_code`, `_MIR_update_code`, `_MIR_update_code_arr`
  来帮助你处理可执行代码。

  你需要实现的常见函数：
  * `void *_MIR_get_thunk (MIR_context_t ctx)`生成少量的代码(块)并返回
    指向代码的地址。代码会将控制流重定位到已存储在代码中的地址，地址可以通过以下函数来设置。
    该函数不定义地址。

  * `void _MIR_redirect_thunk (MIR_context_t ctx, void *thunk, void
    *to)` 将参数2`thunk`中存储的地址设置为参数3`to`。

  * `void *_MIR_get_wrapper (MIR_context_t ctx, MIR_item_t called_func, void *hook_address)`
    生成一个函数(`fun1`)并返回其地址。
    生成函数中将调用`hook_address`的函数并传递`ctx`和`called_func`两参，
    并获取函数末尾调用的另一个函数`fun2`的地址。函数`fun2`将会接收传递给
    前面生成的函数`fun1`的参数。

    * 函数`_MIR_get_wrapper`目前用于惰性代码生成，但在将来会有更多的用途。
      对于惰性代码生成来说，`hook_address`是一个给MIR函数`called_func`
      生成机器代码的函数，它将MIR函数代码块重定向到已生成的机器代码，并
      返回生成代码的地址。
    
## 解释器用平台相关函数 (`mir-<target>.c`文件中)
  这些函数用于实现MIR解释器，需要在`mir-<target>.c`文件中编写，
  且你也可以使用前面提到的MIR内部函数来实现MIR解释器。

  * `void *_MIR_get_bstart_builtin (MIR_context_t ctx)`生成一个
    函数并返回生成函数的地址。生成的函数没有参数，返回函数调用前的
    栈指针并用于实现解释器的`MIR_BSTART`指令。
    
  * `void *_MIR_get_bend_builtin (MIR_context_t ctx)`生成一个
    函数并返回生成函数的地址。生成函数有一个参数，将SP设置为该参数，
    并用于实现解释器的`MIR_BEND`指令。

  * `void *va_arg_builtin (void *p, uint64_t t)`返回可变参数表
    `p`的下一个在MIR中类型为`t`的参数地址。
  
  * `void va_block_arg_builtin (void *res, void *p, size_t s, uint64_tncase)`
    将`res`设置为基于下一个大小为`a`和`ncase`生成的内存块，`p`
    是可变参数列表。
    (例如：`MIR_T_BLK`case为0，`MIR_T_BLK + 1`case为1，
    `MIR_T_BLK + MIR_BLK_NUM -1`case为`MIR_BLK_NUM - 1`)
    译者注：可能`case`仅为用来跳转之类的值的代称？(doubt)
  
  * `void *_MIR_get_interp_shim (MIR_context_t ctx, MIR_item_t
    func_item, void *handler)`生成并返回一个与C函数行为一致的函数，
    其会调用函数`void handler (MIR_context_t ctx,
    MIR_item_t func_item, va_list va, MIR_val_t *results)`
    其中`va`用于访问生成的函数调用时的参数，`result`包含生成函数的返回值。
    MIR设计上默认无法识别外部的C和MIR函数调用，且我们应该能很轻松地在MIR
    生成的代码与MIR解释器之间切换。这意味着我们需要让MIR解释器的函数接口
    同普通的C函数保持一致。生成的函数提供以下接口：

  * `void *_MIR_get_ff_call (MIR_context_t ctx, size_t nres,
    MIR_type_t *res_types, size_t nargs, MIR_type_t *arg_types)`
    生成函数`void fun1 (void *func_addr, MIR_val_t
    *res_arg_addresses)`并返回其地址。生成的`fun1`像普通C函数那样
    调用`func_addr`并返回`nres`个结果。结果作为`res_arg_addresses`
    的头`nres`个元素，并将`nargs`个参数作为后续的元素。返回值和参数类型
    都由`res_types`和`arg_types`来描述。
    
## C2MIR平台相关代码
  写完`mir-<target>.c`且通过`interp-test`检查确保MIR解释器能跑后，
  你可以让`c2m`在解释器上跑。你需要新建一堆文件，但是大多数都只需要
  复制已有的。

  * 首先创建`c2mir/<target>`文件夹并在其中新建`c<target>.h`,`c<target>-code.c`,
    `c<target>-ABI-code.c`和`mirc_<target>_linux.h`。
    最简单的方式是复制已有的`x86_64`或`aarch64`文件夹，改个名并进行下一步修改。

    * `c<target>.h`文件中定义了C2MIR编译器使用的类型和宏，且在大多数64位
      目标平台不需要做任何修改。

    * `c<target>-code.c`文件中定义了C2MIR编译器所使用的平台相关的常量
      （如标准库目录）和需要注意数据对齐的函数。你只需将名字中有`<target>`
      的定义重命名。

    * `c<target>-ABI-code.c`定义了用于生成规范ABI调用的平台相关数据和函数。
      你可以使用一些在`c2mir.c`中的简易ABI函数，或是自己编写代码来生成规范
      的ABI调用。详见以下函数的注释：
      `target_init_arg_vars`, `target_return_by_addr_p`,
      `target_add_res_proto`, `target_add_call_res_op`,
      `target_gen_post_call_res_code`, `target_add_ret_ops`,
      `target_get_blk_type`, `target_add_arg_proto`,
      `target_add_call_arg_op`, `target_gen_gather_arg`

    * `mirc_<target>_linux.h`文件包括了C2MIR编译器的预定义宏，有些你需要重命名。
      你可以通过移植平台上的`cpp -dM < /dev/null`指令来查找需要重命名的宏。

  * 接下来在`c2mir.c`中include`c<target>.h`和`c<target>-code.c`，
    并将目标平台的标准库路径添加到`c2mir.c`和`c2mir-driver.c`中。

调试MIR解释器时，你可以在编译`mir.c`时使用`-DMIR_INTERP_TRACE`参数来追踪
MIR的指令执行。

由C2MIR编译器编译的C程序需要一些具体编译器的标准文件，通过将这些标准文件
存放在`c2m`程序自身中可以令其独立运行。对应平台的文件放在`c2mir/<target>`
文件夹中，分别是`mirc_<target>_float.h`,`mirc_<target>_limits.h`,
`mirc_<target>_stdarg.h`,`mirc_<target>_stddef.h`和`mirc_<target>_stdint.h`。

这些文件最方便的移植方式是从已有的目标相关的文件夹(如aarch64)中复制并修改。
大多数64位目标的情况下你不需要修改可能除了`long double`,`char`是否有符号，
`wchar`和`va_list`定义相关的宏外的文件。

通过MIR解释器运行C2MIR的C测试时你可以使用指令`make c2mir-interp-test`
  
## MIR生成器的平台相关代码(`mir-gen-<target>.c`文件)
移植MIR的最后一步是让MIR生成器生成你目标平台的代码。你需要提供MIR生成器用的以下平台相关的函数和定义：
 
  * `void target_init (MIR_context_t ctx)`和`void target_finish (MIR_context_t ctx)`
    可以用于内部初始化/析构这个文件使用的在特定上下文中贯穿MIR生成器执行所用的数据。

  * 寄存器定义
    * 当你想把MIR生成器当作C枚举器时，建议将你在MIR代码中所有用到的硬件寄存器都定义一遍。
      枚举器需要有用于寄存器分配，访问栈，传递参数等的硬件寄存器。所有生成机器代码时添加的硬件
      寄存器都需要在内。MIR生成器不使用枚举器的常量，但是你可以在`mir-gen-target.c`文件中
      使用。MIR生成器仅引用以下的目标硬件寄存器定义：

      * `MAX_HARD_REG` 可定义的硬件寄存器最大值
      * `SP_HARD_REG`和`HARD_REG_FRAME_POINTER` 用于目标ABI栈帧指针的硬件寄存器值
      * `TEMP_INT_HARD_REG1`, `TEMP_INT_HARD_REG2`, `TEMP_FLOAT_HARD_REG1`, `TEMP_FLOAT_HARD_REG2`,
        `TEMP_DOUBLE_HARD_REG1`, `TEMP_DOUBLE_HARD_REG2`, `TEMP_LDOUBLE_HARD_REG1`, 和 `TEMP_DOUBLE_HARD_REG2` 这些硬件寄存器不会用在生成机器代码时和寄存器分配时。
        更优的方案是使用被调用者暂存的硬件寄存器，这些寄存器仅在寄存器分配阶段后出现。
        前缀相同的标着`_REG1`和`_REG2`需要被区分开来，但是有着不同前缀的硬件寄存器可以相同。
        译者注：可能想表达的是程序中使用时需要做区分，但是这些定义可能指代相同的硬件寄存器？
    * `int target_hard_reg_type_ok_p (MIR_reg_t hard_reg, MIR_type_t type)` 仅在HARD_REG可以装下`type`
      类型的值时返回true。
    * `int target_fixed_hard_reg_p (MIR_reg_t hard_reg)`当`hard_reg`不被用于寄存器分配时返回true。
      对于栈帧指针来说，`hard_reg`为临时硬件寄存器（仅指代前面提到的前缀是`TEMP_`的）时总是返回true。
    * `int target_call_used_hard_reg_p (MIR_reg_t hard_reg)`当`hard_reg`可以在目标ABI下被被调用者暂存时
      返回true。
    
  * `int target_locs_num (MIR_reg_t loc, MIR_type_t type)`返回以标准64位(8字节)栈空间为单位，
    存储`type`类型所需要的个数。一般情况下是`1`，但是当类型为`long double`时可以是`2`。

  * 数组`const MIR_insn_code_t target_io_dup_op_insn_codes[]`包括了需要源操作数和
    一个目的操作数(输入输出)在该目标平台上相同的指令代码。`MIR_INSN_BOUND`作为枚举结束的标记。

  * `MIR_disp_t target_get_stack_slot_offset (MIR_context_t ctx, MIR_type_t type, MIR_reg_t slot)`
    返回相对于栈帧指针的栈槽位(slot)偏移量。没有指定硬件寄存器的MIR寄存器会将值存放在64位的栈槽位(slot)中。
    槽位数从`0`开始计数，到偏移的换算取决于你或是ABI的栈帧布局。你不需要关心栈槽位(slot)的对齐，这是MIR
    生成器的任务。

  * `void target_machinize (MIR_context_t ctx)`将MIR代码转为目标代码。通常其包括了根据ABI做的调用转换
    （通过添加将调用参数放到硬件寄存器或栈上的，从返回值寄存器取出被调用函数计算结果的，以及为当前函数设置好
    返回寄存器的MIR指令来实现）。该函数还可以完成以下工作：

    * 将一些MIR指令换成另一组对于目标平台来说更好的MIR指令，其中可能也包括了窥孔优化。
    * 当一个MIR指令需要一堆目标平台代码来实现时，将一些MIR指令换成调用内建函数。
    * 当目标平台指令仅在特定寄存器上工作时，将MIR指令操作数换成这些寄存器。在这种情况下你需要生成一些
      将原来操作数拷贝到硬件寄存器的代码。
    * 需要与C代码集成时，实现以特定方式传递数据块参数来满足目标调用ABI。
    
    你需要通过MIR生成器函数`gen_add_insn_before`, `gen_add_insn_after`和`gen_delete_insn`来添加和删除MIR指令。

  * `void target_make_prolog_epilog (MIR_context_t ctx, bitmap_t
    used_hard_regs, size_t stack_slots_num)` 添加生成函数的准备和收尾代码，
    一般来说包括暂存/恢复用过的被调用者暂存的硬件寄存器，分配栈空间，调整栈帧指针
    寄存器。

  * `int target_insn_ok_p (MIR_context_t ctx, MIR_insn_t insn)`
    MIR生成器大多数情况下在处理简化过的代码。对于任意化简过的指令（或机器指令）
    函数都应该返回true。总的来看简化过的指令是：

    * 所有针对寄存器的指令
    * 立即数相关的寄存器操作
    * 间接寄存器地址的赋值或取值

    MIR生成器会尝试将多个依赖数据的指令合并成一个。
    在你提供合并后指令翻译结果的情况下也返回true。
    你能提供越多的合并后指令的翻译结果，生成后的代码越好。
    
  * `uint8_t *target_translate (MIR_context_t ctx, size_t *len)`
    生成并返回当前MIR函数的机器代码地址。
    该接口函数应生成任意MIR指令在`target_insn_ok_p`返回true时的机器指令，
    同时将`len`设置为以字节为单位的生成指令的长度。

  * `void target_rebase (MIR_context_t ctx, uint8_t *base)`
    由MIR生成器在`target_translate`调用结束后调用。有时在`target_translate`
    调用后我们想要将生成的机器代码地址调整为仅在这个时间点知道的代码起始地址。
    一般情况下会处理`target_translate`执行中收集的数据。

建议从小的生成器测试开始（`make gen-test`）。通过测试代码生成后你可以继续
做由`c2m`生成的更大的测试（`make c2mir-gen-test`）。最后你可以执行指令
`make c2mir-bootstrap-test`，用MIR生成器做一个巨无霸测试——C-to-MIR compiler。