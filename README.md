# IRL

## Introduction

This project aims to build a complete intermediate representation language. It is designed so that IR can be directly and easily constructed by hand, without translation from higher level languages. The functionality is similar to [LLVM](https://www.llvm.org), but simplified and adjusted to meet the need of learning and research. This project is written in pure and safe Rust, except for the interpreter, where some `unsafe` code appears, but safe indeed. 

## Language

The language is a CFG-based register-transfer IR. Phi instruction is provided to build SSA form. The following is an example to show the structure of a simple program. The program is not very practical, but should suffice to show some characteristics of this language. This example can also be seen in [example.ir](test/example.ir).

```
type @Foo = { i16, { [2][4]i8 }, *@Bar }
type @Bar = { *i64, *@Foo }

@g: i64 <- 0

fn @main() {
%Begin:
    @g <- call i64 @max(1, 2)
    $b <- alloc [4]i64
    $p <- ptr *i64 $b [@g]
    $q <- ptr *i64 $p, 1
    st i64 @g -> $q
    $s <- ld i64 $q
    $t <- add i64 $s, 2
    @g <- mov i64 $t
    $a <- new [@g][2]i16
    $r <- ptr *i16 $a, 1 [1]
    st i16 3 -> $r
    ret
}

fn @max($a: i64, $b: i64) -> i64 {
%Begin:
    $c <- ge i64 $a, $b
    br $c ? %True : %False
%True:
    $x.0 <- mov i64 $a
    jmp %End
%False:
    $x.1 <- mov i64 $b
    jmp %End
%End:
    $x.2 <- phi i64 [%True: $x.0] [%False: $x.1]
    ret $x.2
}
```

It could be seen from the example that the syntax is a bit similar to [LLVM IR](https://www.llvm.org/docs/LangRef.html), but adopts some syntax features commonly seen in higher level programming languages. Programmers are saved from typing some type annotations, as long as they can be easily read from context. Also, some of the instructions are more informative, such as `st`, `br`, `phi` and `ptr`.

The type system and instruction set are all quite simple, but they are fairly enough support most of the following work. For type definition, see [`lang::value::Type`](src/lang/value.rs). For instruction set, see [`lang::inst`](src/lang/inst.rs).

## Compilation

This project supports reading a text source of the language and convert it to memory representation. It covers all the front-end procedures of a common compiler, including lexical, syntactical and semantical analysis.

### Parsing

The lexer and parser are all written by hand. The lexical and syntactical rules can be seen in [`irc::syntax`](src/irc/syntax.rs). The grammar is LL(2). The lexer creates a token one at a time. The recursive-descent parser keeps a buffer for the incoming token stream, either peeks to see which rule to use, or consumes token in the buffer to progress. The parsing is rather efficient.

### Construction

After parsing, the memory representation will be constructed, and the semantic correctness will be checked along the way. This process is divided into several passes: the first one deals with type aliases, global variable declarations and function signatures, and the second deal with basic blocks inside each function. 

If a function contains one or more phi instructions, it is assumed to be in SSA form, and another pass is required to verify this assumption. To be in SSA form, the following requirement should be satisfied: 

* Each local variable should be defined only once in the static program.

* Each local variable is defined before used.

* Each phi instruction has source operands for all predecessors.

## Optimization

Optimizations are implemented as different passes on the program. Most of the optimizations are based on the SSA form, so transformation to that form is mandatory. At present, the following optimizations are supported:

### Global Value Numbering

Detect fully redundant computations by finding congruent variables. See [`pass::gvn::GvnOpt`](src/pass/gvn.rs).

### Sparse Conditional Constant Propagation

Replace later uses of compile-time constants with their corresponding values. It applies this transformation by symbolic execution of the function using both control flow graph and SSA value graph. See [`pass::sccp:SccpOpt`](src/pass/sccp.rs).

### Partial Redundancy Elimination

Place each computation at its optimal position that avoids redundant computation on any path. [GVN-PRE](https://www.cs.purdue.edu/homes/hosking/papers/cc04.pdf) algorithm is adopted, which utilizes GVN as a subroutine to better handle expressions that may not be lexically equivalent. Algebraic simplification is also applied during optimization. See [`pass::pre::PreOpt`](src/pass/pre.rs).

### Loop-Invariant Code Motion

Recognize computations that produce the same value on every iteration of the loop and move them out of loop. See [`pass::licm::LicmOpt`](src/pass/licm.rs).

### Strength Reduction

Reformulate certain costly computations with less costly ones. [OSR](https://www.cs.rice.edu/~keith/EMBED/OSR.pdf) algorithm is adopted. See [`pass::osr::OsrOpt`](src/pass/osr.rs).

### Dead Code Elimination

Conventional mark-sweep algorithm to find instructions that define unused variables. Can serve as a subroutine for other optimizations. It is implemented as a method of [`lang::func::Fn`](src/lang/ssa.rs).

### Aggressive DCE

Take an aggressive approach to Dead Code Elimination. It only keep instructions that contribute to the returned result, and remove the rest. Note that this may alter the runtime behavior of a function. See [`pass::adce::AdceOpt`](src/pass/adce.rs).

### Copy Propagation

Replace later uses of copied values with their original ones. Can serve as a subroutine for other optimizations. See [`pass::copy::CopyProp`](src/pass/copy.rs).

Other optimizations will be added to this project successively.

## Execution

[`vm::exec::Machine`](src/vm/exec.rs) is an interpreter that could actually execute the program written in this language. It can be seen as a virtual machine that supports instructions defined in this language. The interpreter could check all of the *runtime* errors, including null pointer dereference, access to unallocated memory and stack overflow, stop immediately and report the error to the programmer. This makes sure that the interpreter will not panic itself at any time, as long as the program is correct in terms of its static semantics. For programs that have not gone through semantic analysis, especially those constructed directly by API, nonexistence of VM panic or unexpected behavior cannot be guaranteed.

The interpreter also counts the number of executed instructions and hypothetical execution time. The time is counted by computing weight of each instruction and summing all the weights up. The weights are based on the number of clock cycles required to do the corresponding computation in real-world processors. This could serve as a metric for evaluating the efficiency of certain optimizations.

If we run the example program, we can get the following feedback:

```
program terminated
instructions: 18  time: 39

global variables: 
@g = 4
``` 

Here we know that the final value of global variable `@g` is four. 18 instructions were executed, and it took 39 time units to run this program.

What if some runtime error occurs? We can see by modifying `$q <- ptr *i64 $p, 1` to `$q <- ptr *i64 $p, 2`.

```
runtime error: memory access out of bound
call stack: 
0 @main, %Begin, #4
```

The interpreter prints the error message and unwinds the call stack. We can know from the output that the error occurs at instruction number 4 (0-indexed) of block `%Begin` in function `@main`, when the program tries to store `@g` to pointer `$q`. Since the program only allocates four `i64`s, access to 2 + 2 = 4th element is not accepted.