# IRLab

## Introduction

This project is for experimenting some techniques of IR (intermediate representation) language, including compilation, analysis, optimization, execution, etc. The functionality is quite similar to [LLVM](https://www.llvm.org), but substantially simplified. Some of the implementation is ported from my previous project [GoCompiler](https://github.com/wzh99/GoCompiler). This project is also inspired by [LLIRInterpreter](https://github.com/abcdabcd987/LLIRInterpreter) and [ssa-anf](https://github.com/jacobstanley/ssa-anf)

## Language

The language involved is an CFG-based, register-to-register model IR. Phi instruction is provided to build SSA form, but is not mandatory. The following is an example to show the structure of a simple program. The program is not very practical, but should suffice to show some characteristics of this language. This example can also be seen in [example.ir](test/example.ir)

```assembly
type @Foo = { i64, { [2][4]i64 }, *@Bar }
type @Bar = { *i64, *@Foo }

@g <- 0: i64;

fn @main() {
%Begin:
    @g <- call i64 @max(1, 2);
    $b <- alloc [4]i64;
    $p <- ptr *i64 $b [@g];
    $v <- ld i64 $p;
    $q <- ptr *i64 $p, 1;
    st i64 $v -> $q;
    ret;
}

fn @max($a: i64, $b: i64) -> i64 {
%Begin:
    $c <- ge i64 $a, $b;
    br $c ? %True : %False;
%True:
    $x.0 <- mov i64 $a;
    jmp %End;
%False:
    $x.1 <- mov i64 $b;
    jmp %End;
%End:
    $x.2 <- phi i64 [%True: $x.0] [%False: $x.1];
    ret $x.2;
}
```

It could be seen from the example that the syntax is a bit similar to [LLVM IR](https://www.llvm.org/docs/LangRef.html), but adopts some syntax features commonly seen in higher level programming languages. It tries to reduce type annotation required in the language, as long as it can be inferred from context or expressions.

The type system and instruction set are all quite simple, but they are fairly enough support most of the following work. For type definition, see [`lang::val::Type`](src/lang/val.rs). For instruction set, see [`lang::instr`](src/lang/instr.rs).

## Compilation

This project support reading a text source of the language and convert it to memory representation. It covers all the front-end procedures of a common compiler, including lexical, syntactical and semantic analysis.

### Parsing

The lexer and parser are all written by hand. The lexical and syntactical rules can be seen in [`compile::syntax`](src/compile/syntax.rs). The grammar is an LL(1) one. The lexer creates a token one at a time. The recursive-descent parser keeps a buffer for the incoming token stream, either peeks to see which rule to use, or consumes token in the buffer to progress. The parsing is rather efficient.

### Construction and Verification

After parsing, the memory representation will be constructed, and the semantic correctness will be checked along the way. This process is divided into several passes: the first one deals with global variable declarations and function signatures, and the second deal with basic blocks inside each function. 

If a function contains one or more phi instruction, *or* if any versioned symbol appears in this function, it is assumed to be in SSA form, and another pass is required to verify this assumption. To be in SSA form, the following requirement should be satisfied: 

* Each local variable should be defined only once in the static program.

* Each local variable is defined before used.

* Each phi instruction has source operands for all predecessors.

## Design pattern

In this project, most of accesses to the program, including verification, analysis, optimization are all based on the listener design pattern. This derives from the insight that most of the algorithms related to these work follow the basic routine of dominator tree traversal. If we could factor out this routine, we could improve code reuse and make program less prone to bugs.

 Three listener traits with different granularity are provided in the program: `BlockListener` at block level, `InstrListener` at instruction level, and `ValueListener` at value level. Listener trait with finer granularity are extended trait of the listener with coarser one. They can be chosen on demand. Furthermore, different listeners can be combined to support more sophisticated work. 

## Optimization

Optimization on the program are implemented as passes, which is usually the case in modern compilers. Most of the global (function-level) optimizations depend on SSA form of the program, so a transformation to SSA form is a must. At present, the following optimizations are supported:

* Global Value Numbering

* Sparse Conditional Constant Propagation

* Dead Code Elimination
