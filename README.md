# IRLab

## Introduction

This project is for experimenting some techniques of IR (intermediate representation) language, including parsing, optimization, execution, etc. The organization is quite similar to [LLVM](https://www.llvm.org), with complexity greatly reduced. Some of the implementation are ported from my previous project [GoCompiler](https://github.com/wzh99/GoCompiler). This project is also inspired by [LLIRInterpreter](https://github.com/abcdabcd987/LLIRInterpreter) and [ssa-anf](https://github.com/jacobstanley/ssa-anf)

## Language

The language involved is an CFG-based, register-to-register model IR. Phi instruction is provided to build SSA form, but is not mandatory. The following is an example to show the structure of a simple program. The program is not very practical, but should suffice to show some characteristics of this language. This example can also be seen in [parse.ir](test/parse.ir)

```assembly
@g <- 0: i64;

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

fn @main() {
%Begin:
    @g <- call i64 @max(1, 2);
    ret;
}
```

It could be seen from the example that the syntax is similar to [LLVM IR](https://www.llvm.org/docs/LangRef.html), but adopts the type annotation style different from LLVM. Also, it tries to reduce type annotation required in the language, as long as it can be inferred from context or expressions.

The type system and instruction set are all quite simple, but they are fairly enough support most of the following work. For type definition, see [`lang::val::Type`](src/lang/val.rs). For instruction set, see [`lang::instr`](src/lang/instr.rs).

## Compilation

### Parsing

This project support reading a text source of the language and convert it to memory representation. It covers all the front-end procedures of a normal compiler, including lexical, syntactical and semantic analysis.

The lexer and parser are all written by hand. The lexical and syntactical rules can be seen in [`compile::syntax`](src/compile/syntax.rs). The grammar is an LL(2) one. The lexer creates a token one at a time. The recursive-descent parser keeps a buffer for the incoming token stream, either peeks to see which rule to use, or consumes token in the buffer to progress. The parsing is rather efficient.

### Construction and Validation

After parsing, the memory representation will be constructed, and the semantic correctness will be checked along the way. This process is divided into several passes: the first one deals with global variable declarations and function signatures, and the second deal with basic blocks inside each function. 

If a function contains one or more phi instruction, *or* if any versioned symbol appears in this function, it is assumed to be an SSA representation, and another pass is required to validate this assumption.
