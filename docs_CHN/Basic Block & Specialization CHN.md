注意：翻译仅包括主要内容。
Note:Translation only includes main content of that article.

过去的三年里，我在MIR上花了我一半的工作时间，目标是创造一个通用的轻量级即时(JIT)编译器，而项目的基石是一个平台无关的中间表示(MIR)。有关项目更多的内容可以查阅我之前发在Red Hat Developer上的文章。

https://developers.redhat.com/blog/2020/01/20/mir-a-lightweight-jit-compiler-project
https://developers.redhat.com/blog/2021/04/27/the-mir-c-interpreter-and-just-in-time-jit-compiler

近期，我在MIR上的工作重点是做一个给主要的一些目标平台（x86-64 Linux和macOS, aarch64, s390x, riscv64 Linux, ppc64 big- 和 little-endian Linux）生成高质量机器代码的快速JIT编译器。

项目目前的版本是一个基于方法的JIT编译器，对于像C这样的静态语言可以有效地工作。我们已经开发了一个基于C到MIR编译器的C语言JIT编译器。

MIR最初的目标是实现一个更好的Ruby JIT编译器（尤其是我重点投入的由C编写的默认Ruby解释器——CRuby）Ruby是一个无比灵活的动态语言，你甚至可以重定义用于整数加法的方法。

为了让动态语言有更好的性能，你需要跟踪程序的执行，做许多的假设，并生成基于这些假设的代码。例如，你发现特定情况下加法计算时只有整数操作数参与，你可以假设这个情况不会改变，并生成针对整数特化的加法运算代码。

你需要用不同的方式来保证你的假设可靠，比如做一些假设检查，或是证明在特定执行路径下假设总是成立。如果检查发现假设出错，你需要切换到通用的代码上。这个切换过程在讨论JIT时一般称之为去优化。

这篇文章中，我将会介绍我怎么准备在MIR中实现生成特化和去优化的代码，和现阶段已经在MIR中实现的一些东西。

注意：大多数JIT编译器是针对特定语言的：JavaScript的V8，Lua的luajit，PHP的PHP JIT。我对在不同动态语言中支持JIT编译器的特化及去优化的实现更感兴趣。（看看OpenJDK的JIT编译器是怎么提高Java的性能的，可以了解更多JIT编译器中去优化的细节。）


# MIR中的特化及去优化
接下来我们可以具体看看MIR编译器中是怎么做代码特化和去优化的。
我会用以下简化后的代码来描述CRuby虚拟机(VM)中加法指令的实现：
```
    if (FIXNUM_2_P(recv, obj) &&
        BASIC_OP_UNREDEFINED_P(BOP_PLUS, INTEGER_REDEFINED_OP_FLAG)) {
        res = rb_fix_plus_fix(recv, obj);
    } else if (FLONUM_2_P(recv, obj) &&
               BASIC_OP_UNREDEFINED_P(BOP_PLUS, FLOAT_REDEFINED_OP_FLAG)) {
        res = DBL2NUM(RFLOAT_VALUE(recv) + RFLOAT_VALUE(obj));
    } else if (SPECIAL_CONST_P(recv) || SPECIAL_CONST_P(obj)) {
        ...  
    } else if (RBASIC_CLASS(recv) == rb_cFloat && RBASIC_CLASS(obj)  == rb_cFloat &&
               BASIC_OP_UNREDEFINED_P(BOP_PLUS, FLOAT_REDEFINED_OP_FLAG)) {
 ...
    } else if (RBASIC_CLASS(recv) == rb_cString && RBASIC_CLASS(obj) == rb_cString &&
               BASIC_OP_UNREDEFINED_P(BOP_PLUS, STRING_REDEFINED_OP_FLAG)) {
        ...
    } else if (RBASIC_CLASS(recv) == rb_cArray && RBASIC_CLASS(obj) == rb_cArray &&
               BASIC_OP_UNREDEFINED_P(BOP_PLUS, ARRAY_REDEFINED_OP_FLAG)) {
        ...
    } else {
        ... // call of method implemented + for object recv
    }
```

这些代码做了什么呢？首先，检查了操作数是定点数(整数)并且没有重定义整数加法的方法。如果成立，下面的代码将用于定点数的加法计算，否则将检查操作数类型是否是浮点数，字符串或数组。最后，代码调用了Ruby中对象recv实现的加法方法。

CRuby中的定点数都是能够被目标平台高效实现的整数子集，大数字则由GMP库以多精度数字的形式实现。

CRuby中的所有值都有特定的位标记它们的类型。例如，一个定点数总是有1个标志位，一个对象指针总是有3个(在32位平台上2个)（一般情况下为0的）标志位。以下代码是宏`FIXNUM_2_P`的实现：
```
  (recv & obj & 1) == 1
```

如果我们想在定点数加法中检查溢出则像这样：（译者注：表达存疑）
```
  (long) recv + (long) obj - 1
```

注意：为了表达简洁，下一节我将会忽略对加法运算重定义的检查，比如使用宏`BASIC_OP_UNREDEFINED_P`。

# 基于运行信息收集的代码特化
假设我们已经检查了一个特定加法中操作数的类型，并且发现近期执行的全是定点数加法，那么我们可以生成以下代码：
```
if (!FIXNUM_2_P(v1, v2)) goto general_case;
res = rb_fix_plus_fix(v1, v2)
```

乍一看，类型检查还在，我们并没有优化代码。那么，一系列的加法计算呢？
```
  //v1 + v2 + v3 + v4
  if (!FIXNUM_2_P(v1, v2)) goto general_case;
  res = rb_fix_plus_fix(v1, v2)
  if (!FIXNUM_2_P(res, v3)) goto general_case;
  res = rb_fix_plus_fix(res, v3)
  if (!FIXNUM_2_P(res, v4)) goto general_case;
  res = rb_fix_plus_fix(res, v4)
```

聪明的编译器可以去掉后两个检查，但不幸的是，GCC和Clang都不知道`res`有个标志位，所以它们不知道可以这样做。（GCC的Project Ranger完全实现后可能可以做到。）但如果值由一个两个成员(类型和值)组成的结构体表示，GCC/LLVM就会这么做。

# 扩展基础块上的优化
即便不移除多余的检查，编译器依然可以基于此做去掉多余的读写操作等的其它优化，
所以跑这样特化后的代码会更好。背后的原理是这些代码形成了一些特定的块（扩展基础快，EBBs），编译器可以很好地在这些块上做优化。像这样的代码还具备更好的局部性（可能涉及到多线程优化），以及在分支预测时命中率更高。

# 通用代码
那么我们怎么在定点数的例子中实现通用的部分呢？有三种可能：

* 切换到解释器执行。
* 让JIT编译器移除特化代码，并为VM指令生成通用代码。
* 跳转到一个有所有通用代码的位置上。

CRuby中切换到解释器执行开销很大，更优的方案是同时生成特化和通用的代码，并在特化代码假设不成立的情况下跳转到通用代码所在位置上。执行了一些跳转到通用代码的指令后，我们可以基于此重新生成整个方法的代码。

# 变量特性值
MIR JIT编译器不比GCC或Clang聪明，在做前面的那种检查时也会有同样的问题。为了解决这些问题，我计划以C内建函数的形式为变量和MIR指令添加一些特性值：
```
__builtin_prop_cond (cond, var1, property_const1, var2, property_const2, ...)
__builtin_prop_set (var, property_const)
```

注意：为了表达简洁，我将会跳过介绍MIR层上特性值的实现。

特性值都是整数常量。我们可以用`__builtin_prop_set`来为特定执行点上的变量设置特性值，并在变量赋值时传递。

当我们无法在特定执行点上获知一个变量的特性值时，将变量特性值设为0，意味着这是个未知的特性值。

接下来，我们可以对加法的代码用新的内建调用进行类型标注：
```
    enum prop { unknown = 0, inttype, flotype, ... };
    if (__builtin_prop_cond (FIXNUM_2_P(recv, obj), recv, intype, obj, intype)) {
        res = rb_fix_plus_fix(recv, obj);
        __builtin_prop_set (res, inttype)
    } else if (__builtin_prop_cond (FLONUM_2_P(recv, obj), recv, flotype, obj, flotype))
        res = DBL2NUM(RFLOAT_VALUE(recv) + RFLOAT_VALUE(obj));
        __builtin_prop_set (res, flotype);
    } else {
        ... // call of method implemented + for object recv
    }
```

下面的伪代码演示了怎么用`__builtin_prop_cond`和`__builtin_prop_set`：
```
 if (recv.prop == intype && obj.prop == inttype
        || (recv.prop == unknown && obj.prop == unknown) && FIXNUM_2_P(recv, obj)) {
        res = rb_fix_plus_fix(recv, obj);
        res.prop = intype;
    } else if (__builtin_prop_cond (FLONUM_2_P(recv, obj), recv, flotype, obj, flotype))
        res = DBL2NUM(RFLOAT_VALUE(recv) + RFLOAT_VALUE(obj));
        __builtin_prop_set (res, flotype);
    } else {
        ... // call of method implemented + for object recv
    }
```

因为我们在代码生成时知道这些特性值，所有特性值的赋值和比较操作最终都会被去掉。例如，如果我们知道`recv`和`obj`都是整数类型，最终可以生成：
```
  res = rb_fix_plus_fix(recv, obj);
```

如果我们在分析时知道`recv`和`obj`都是浮点类型，最终可以生成：
```
  res = DBL2NUM(RFLOAT_VALUE(recv) + RFLOAT_VALUE(obj));
```

如果`recv`和`obj`的特性值都为0，我们将得到和标注之前一样的原始实现。如果仅有一个为0，我们将得到最后`else`分支里的代码。

经过上述的运行信息收集和处理，我们生成的注解后代码大概会像这样：
```
if (!__builtin_prop_cond (FIXNUM_2_P(v1, v2), v1, intype, v2, intype)) goto general_case;
res = rb_fix_plus_fix(v1, v2);
__builtin_prop_set (res, inttype);
if (!__builtin_prop_cond (FIXNUM_2_P(res, v3), res, intype, v3, intype)) goto general_case;
res = rb_fix_plus_fix(res, v3);
__builtin_prop_set (res, inttype);
if (!__builtin_prop_cond (FIXNUM_2_P(res, v4), res, intype, v4, intype)) goto general_case;
res = rb_fix_plus_fix(res, v4);
__builtin_prop_set (res, inttype);
...
```

现在我们可以轻易地在这个扩展基础块中推算出和利用变量的特性值。在MIR寄存器中特性值分析并不重要，但是由MIR内存操作数表示的变量则需要做更为复杂的指向分析（指针指向？）。

最终结果：
```
if (FIXNUM_2_P(v1, v2)) goto general_case;
res = rb_fix_plus_fix(v1, v2);
res = rb_fix_plus_fix(res, v3);
res = rb_fix_plus_fix(res, v4);
...
```

注意：为了表达简洁，我只介绍了怎么做运行信息收集，尤其是当代码在多于一个线程上运行时。

# 基础块特化（BBV Basic Block Versioning）
在动态语言中（以Ruby为例），一个多态函数的常见情况是：一个所有变量都是定点数，另一个所有变量都是浮点数。（比如上文提到的`v1+v2+v3+v4`）

如果我们仅基于运行信息收集生成代码，那么只有一半的代码我们可以做特化，另一半则需要在假设不成立时做去优化。如果在一个具体的小函数调用中，绝大多数情况下值类型是某些特定类型，我们可以利用内联优化生成的代码，但这非常复杂。而基础块特化（BBV）则可以更好地解决这个问题。

那么基础块特化是怎么操作的呢？假设我们的代码中有几个不同的运行路径抵达特定的基础块（比如对同一个函数的不同调用点），而在这些路径上的变量有着一些具体的类型（特性值）。我们可以把基础块复制一份并基于此针对不同变量类型生成特化的代码。
```
路径1，路径2->res=v1+v2+v3+v4->...

路径1(v1,v2,v3,v4都为定点数)->特化基础块1->res为定点数
路径2(v1,v2,v3,v4都为浮点数)->特化基础块2->res为浮点数
```

在生成的特化基础块中我们可以推断出计算后的结果类型（如上例），并且我们可以不断基于这种方式去做更进一步的分代特化。

你可能会想如果我们不限制基础块特化的次数，那么在复杂情况下的排列组合会占用很多的资源。实践上来说，一个基础块只会针对一部分类型进行特化，其它情况下则会使用通用代码（特性值为0）。

# 激进特化 vs 保守特化
有两种方式来做基础块特化：激进或是保守。如果是激进，当我们为一个基础块做特化时，我们同时生成后续的基础块并为这些基础块生成代码，或者说直接一次为整个方法生成全部代码。

如果是保守，我们只在执行到特定情况时做特化生成，这意味着我们只对程序中会执行的基础块进行特化。显而易见地，这种方式会使生成的代码量更少而且通常编译时间更短。（如果我们对一个基础块做相同数量的特化，保守方案会因为需要为各个特化块做数据的初始化和后续处理而使得编译耗时更多）

# 保守方案的优点
相较于前面提到的基于运行信息收集的特化代码生成，保守基础块特化有以下优点：

* 特化前不用做信息收集
* 优化不依赖内联
* 当JIT驱动的程序仅有一小部分被执行时，我们不需要为所有基础块生成机器代码
* 我们不需要为去优化做额外的工作，因为这些已经在基础块特化的过程中完成了

许多基于方法的JIT编译器只会为执行特定次数后而不是超过某些阈值后的方法生成代码，执行模式只会在函数调用时切换。这种方式对于一个不常被调用却拥有大循环的函数来说效果并不好。在方法执行时做执行模式切换被称为栈上替换（OSR on-stack replacement），但保守基础块特化不需要为此做额外的工作，因为这个在特化过程中也一并做了。

有人可能会说在基础块特化的过程中代码体积会膨胀，但实践上来看，平均的特化个数非常少。在JavaScript的性能测试上，大约95%的基础块仅有一个特化。（数据来自Maxime Chevalier-Boisvert and Marc Feely文章中的see Simple and Effective Type Check Removal through Lazy Basic Block Versioning部分）

如图所示，在启动x86-64上的C-to-MIR编译器时（大概3万行C代码），在编译器所有函数的基础块中至少执行过一次的且特化了的只有51%（14737/29131），而编译器所有基础块中只有18%（14737/81799）。

原图数据：上述例子生成的基础块数量
* 81799（所有基础块）
* 29131（保守函数基础块数）
* 14737（保守基础块数）

所以我第一个为MIR实现保守基础块特化这点是没有任何疑问的。

# MIR中的保守基础块特化
所有MIR函数都是基于运行时生成代码块的间接调用，块中经常只有1到2条机器指令，而代码块能够让任意MIR函数更轻松地修改机器代码。例如，我们从特化代码切换到去优化代码时就需要用到。

MIR已经实现了一个保守方案，并且也是基于代码块的。在程序开始执行时，所有函数代码块都会重定向到机器代码的生成器。当一个函数被初次调用时，MIR代码生成器会为其生成优化后的代码；函数块接下来会重定向到生成的机器代码并往后执行。
```
执行路径：代码块(参数)
代码块：
{
    temp=函数
    goto 函数生成器
}
{
    goto 生成后函数
}
```

当我们使用保守基础块特化时，函数代码块在基础块开头切换到一个依赖变量特性值的特定地址上，并且可以由不同的方式来实现，比如哈希表。任何切换方式都比一条跳转指令更低效。不过，我们不能在一个函数中仅用几个简单的跳转块来替代切换过程，因为在MIR中一个函数是以其代码块的地址来表示的，且函数可以被赋值和比较，所以我们需要确保函数和其代码块是一对一的关系。

保守特化基础块的函数代码块重定向到为基础块生成特化机器代码的地址，或是一个已经生成的特化代码地址。一个函数调用的同时，会通过一些不被被调用函数暂存的寄存器（暂存的由ABI 应用程序二进制接口指定），传递调用参数的特性值。

一开始，一个函数代码块重定向到一个以特定方式运行的机器代码生成器，优化函数但不生成代码，而是为函数生成第一个特化基础块，使函数代码块重定向到特化基础块生成器并调用函数。后续代码则会在有必要做新的特化时修改函数代码块。

```
执行代码：
{
    temp2=特性值 id1
    代码块(参数)
}
{
    temp2=特性值 id2
    代码块(参数)
}
{
    temp2=特性值 id3
    代码块(参数)
}

代码块：
{
    temp=基础块
    jump 基础块生成器
}
{
    if(temp2==特性值 id1)jump 特化基础块1
    temp=基础块
    jump 基础块生成器
}
{
    if(temp2==特性值 id1)jump 特化基础块1
    if(temp2==特性值 id2)jump 特化基础块2
    temp=基础块
    jump 基础块生成器
}
{
    if(temp2==特性值 id1)jump 特化基础块1
    if(temp2==特性值 id2)jump 特化基础块2
    jump 通用基础块
}
```

特化基础块生成器处理MIR特性值指令，基于给定的特性值做代码优化，并为其生成机器代码。它会从当前基础块的末尾开始，查找后续具有相应特性值的基础块并在这些基础块的末尾添加跳转到生成的机器代码的指令。

如果特化基础块生成器找不到一个基础块的后续基础块，它会创建这些。生成器会在当前特化基础块的机器代码末尾添加跳转到新代码块的指令，并继续执行当前特化块的机器代码。当原来的特化基础块内有个间接跳转，或是多余一种情况的MIR切换指令有着相同的目标，基础块间的跳转仍然会由基础代码块来实现。