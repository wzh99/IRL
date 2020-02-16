# IRLab

## Introduction

This project is for experimenting some techniques of IR (intermediate representation) language, including parsing, optimization, execution, etc. The organization is quite similar to [LLVM](https://www.llvm.org), with complexity greatly reduced. Some of the implementation are ported from my previous project [GoCompiler](https://github.com/wzh99/GoCompiler).

# Language

The language involved is an CFG-based, register-to-register model IR. Phi instruction is provided to build SSA form, but is not mandatory. The following is an example to show the structure of a simple program. The program is not very practical, but should suffice to show some characteristics of this language. This example can also be seen in [parse.ir](test/parse.ir)

```
@g <- 0 : i64;

fn @max(%a: i64, %b: i64) -> i64 {
%Begin:
    %c <- ge i64 %a, %b;
    br %c ? %True : %False;
%True:
    %x.0 <- @a;
    jmp %End;
%False:
    %x.1 <- @b;
    jmp %End;
%End:
    %x.2 <- phi i64 [%True: %x.0] [%False: %x.1];
    ret %x.2;
}

fn @main() {
%Begin:
    %g <- call i64 @max(1, 2);
    ret;
}
```

It could be seen from the example that the syntax is similar to [LLVM IR](https://www.llvm.org/docs/LangRef.html), but adopts the type annotation style different from LLVM. Also, it tries to reduce type annotation required in the language, as long as it can be inferred from context or expressions.

# Parsing

The lexer and parser are all written by hand. The lexical and syntactical rules can be seen in [syntax.rs](src/parse/syntax.rs) The grammar is an LL(2) one. The lexer creates a token one at a time. The recursive-descent parser keeps a buffer for the incoming token stream, either peeks to see which rule to use, or consumes token in the buffer to progress. The parsing is rather efficient.
