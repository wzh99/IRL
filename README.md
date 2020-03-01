# IRL

## Introduction

This project implement some technical aspects of IR (intermediate representation) language, including compilation, analysis, optimization, execution, etc. The functionality is quite similar to [LLVM](https://www.llvm.org), but substantially simplified. Some of the implementation is ported and improved from my previous project [GoCompiler](https://github.com/wzh99/GoCompiler). This project is also inspired by [LLIRInterpreter](https://github.com/abcdabcd987/LLIRInterpreter) and [ssa-anf](https://github.com/jacobstanley/ssa-anf).

## Language

The language involved is an CFG-based, register-to-register model IR. Phi instruction is provided to build SSA form, but is not mandatory. The following is an example to show the structure of a simple program. The program is not very practical, but should suffice to show some characteristics of this language. This example can also be seen in [example.ir](test/example.ir)

```
type @Foo = { i64, { [2][4]i64 }, *@Bar } // type alias is available
type @Bar = { *i64, *@Foo } // order of definition can be arbitrary

@g: i64 <- 0; // global variable definition, can be initialized

// Demonstrate the use of memory-related instructions
fn @main() {
%Begin:
    @g <- call i64 @max(1, 2); // no need to annotate type for arguments
    $b <- alloc [4]i64; // aggregate should be allocated before accessed
    $p <- ptr *i64 $b [@g]; // operands in the square bracket are indices INSIDE aggregates
    $v <- ld i64 $p;
    $q <- ptr *i64 $p, 1; // second operand is OFFSET of pointer
    st i64 $v -> $q; // use arrow to indicate data flow
    ret;
}

// Demonstrate SSA form of function
fn @max($a: i64, $b: i64) -> i64 { // post type annotation
%Begin:
    $c <- ge i64 $a, $b; // result type of comparing operator is always `i1`
    br $c ? %True : %False; // ternary expression for branch target, condition must be of type `i1`
%True:
    $x.0 <- mov i64 $a; // versioned variable can be used
    jmp %End;
%False:
    $x.1 <- mov i64 $b;
    jmp %End;
%End:
    $x.2 <- phi i64 [%True: $x.0] [%False: $x.1]; // one square bracket indicate one predecessor
    ret $x.2;
}
```

It could be seen from the example that the syntax is a bit similar to [LLVM IR](https://www.llvm.org/docs/LangRef.html), but adopts some syntax features commonly seen in higher level programming languages. It tries to reduce type annotation required in the language, as long as it can be inferred from context or expressions. Also, it tries to make some of the instructions more informative, such as `st`, `br`, `phi` and `ptr`.

The type system and instruction set are all quite simple, but they are fairly enough support most of the following work. For type definition, see [`lang::val::Type`](src/lang/value.rs). For instruction set, see [`lang::instr`](src/lang/instr.rs).

## Compilation

This project supports reading a text source of the language and convert it to memory representation. It covers all the front-end procedures of a common compiler, including lexical, syntactical and semantical analysis.

### Parsing

The lexer and parser are all written by hand. The lexical and syntactical rules can be seen in [`compile::syntax`](src/compile/syntax.rs). The grammar is an LL(1) one. The lexer creates a token one at a time. The recursive-descent parser keeps a buffer for the incoming token stream, either peeks to see which rule to use, or consumes token in the buffer to progress. The parsing is rather efficient.

### Construction and Verification

After parsing, the memory representation will be constructed, and the semantic correctness will be checked along the way. This process is divided into several passes: the first one deals with type aliases, global variable declarations and function signatures, and the second deal with basic blocks inside each function. 

If a function contains one or more phi instructions, *or* if any versioned symbol appears in this function, it is assumed to be in SSA form, and another pass is required to verify this assumption. To be in SSA form, the following requirement should be satisfied: 

* Each local variable should be defined only once in the static program.

* Each local variable is defined before used.

* Each phi instruction has source operands for all predecessors.

## Listener Pattern

In this project, most of the data flow analyses on SSA form, including construction, verification and several optimizations, are based on the listener design pattern. This derives from the insight that most of theses algorithms follow the basic routine of dominator tree traversal. If we could factor out this routine, we could improve code reuse and make program less prone to bugs.

 Three listener traits with different granularity are provided in the program: `BlockListener` at block level, `InstrListener` at instruction level, and `ValueListener` at value level. Listener trait with finer granularity are extended trait of the listener with coarser one. They can be chosen on demand. Furthermore, different listeners can be combined to support more sophisticated work. 

## Optimization

Optimizations are implemented as passes of transforms on the program, which is usually the case in modern compilers. Most of the optimizations are based on the SSA form, so transformation to that form is mandatory. At present, the following optimizations are supported:

### Global Value Numbering

Detect fully redundant computations by finding congruent variables. Implementation at [`opt::gvn::GvnOpt`](src/opt/gvn.rs), example at [gvn.ir](test/gvn.ir).

### Sparse Conditional Constant Propagation

Replace later uses of compile-time constants with their corresponding values. It applies this transformation by symbolic execution of the function using both control flow graph and SSA value graph. Implementation at [`opt::sccp:SccpOpt`](src/opt/sccp.rs), example at [sccp.ir](test/sccp.ir).

### Partial Redundancy Elimination

Place each (binary) computation at its optimal position. GVN-PRE algorithm is adopted, which utilizes GVN as a subroutine to better handle expressions that may not be lexically equivalent. Implementation at [`opt::pre::PreOpt`](src/opt/pre.rs), example at [pre.ir](test/pre.ir).

### Dead Code Elimination

Mark-sweep algorithm to find instructions that define unused variables. Can be used as a subroutine for other optimizations. It is implemented as a method of [`lang::func::Func`](src/lang/ssa.rs).

Other optimizations will be added to this project successively.

## Execution

To be done.
