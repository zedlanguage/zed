# MLIR study (step L1.35)

The record of DESIGN.md step L1.35 and the plan for L28. It answers four questions: how
ZIR-loop and the target dialects lower to MLIR's dialects; whether ZIR is also written as an
MLIR dialect; what MLIR's graph regions and LLVM's lowering provide and lack against ZIR's state
edges, content addresses and certificates; and whether the compact back end of L1.36 stays
Cranelift. The test `tests/steps/l01_35_mlir_study` reads the variants of `Op`, `Derived` and
`RegionKind` from the text of `crates/zedc-zir/src/zir/mod.rs` and checks that every ZIR operation
and region kind has a row in the tables below and every row an operation or region kind, so an
operation added later without a lowering fails it.

Sources, read 2026-10-30: the MLIR Language Reference (mlir.llvm.org/docs/LangRef), the `func`
dialect (mlir.llvm.org/docs/Dialects/Func), the `scf` dialect
(mlir.llvm.org/docs/Dialects/SCFDialect) and the `async` dialect
(mlir.llvm.org/docs/Dialects/AsyncDialect). Quotations are from those pages.

## Decisions

1. **ZIR is lowered into MLIR's existing dialects and is not written as an MLIR dialect.** The
   reasons:
   - What ZIR keeps above MLIR (the validator, the canonicalizer, content addresses, the
     certificates and the optimizer's algebra) is Zed's own code, in Rust now and in Zed after
     row S. An MLIR dialect would be a second, C++ implementation of the same structure that
     has to agree with the first, which is a source of miscompiles the differential oracle
     would have to find.
   - L29 writes MLIR's transformations in Zed, on Zed values; a dialect registered in MLIR's
     C++ context does not help a pass written in Zed.
   - Nothing in the lowering needs MLIR to see ZIR: every ZIR region maps to an operation of
     an upstream dialect (the tables below), and the information MLIR cannot hold is used
     before the lowering, not after it.
2. **The lowering starts at ZIR-loop, after scheduling.** ZIR-relational is lowered to ZIR-loop
   in Zed's own passes (fusion, the planner's choices, the memory plan of L1.34); only then is
   the graph given an order and handed to MLIR. So MLIR receives a program whose order is
   already chosen, and its regions are SSACFG regions emitted in a topological order of the
   ZIR region, the state edges' order included.
3. **Graph regions are not used.** They would fit ZIR's unordered regions ("the order of
   operations within a block … is not semantically meaningful and non-terminator operations
   may be freely reordered"), but they matter only to a dialect that keeps the graph inside
   MLIR, which decision 1 rules out. They also allow what ZIR forbids ("cycles can occur
   within a single block in a graph region") and "may only contain a single basic block", so a
   verifier would still have to restrict them.
4. **State edges become order, not values.** After the lowering, each `port` node is a call
   of a runtime function (`func.call`), which MLIR treats as having unknown effects and never
   reorders against another such call. The state edges have fixed that order before the
   lowering (decision 2), so no token type is needed in sequential code. Where L7.5's scheduler
   runs a wave's independent regions concurrently, each region becomes an `async.execute`
   whose dependencies are the state edges between regions as `!async.token`s: "starts
   execution of the attached body region only when all tokens and values become ready", and
   "All dependencies must be made explicit". A wave is therefore a set of `async.execute`
   operations, one per region, and each state edge between two of them is one token.
5. **Content addresses travel as locations.** MLIR has no content addresses. Each operation the
   lowering emits carries an MLIR location naming its ZIR node's address and path
   (`loc("zir/<address>":<line>:<col>)`, the line indexing the node path in a table the emitter writes; every `mlir-opt` runs with `--mlir-print-debuginfo`, and `--ensure-debug-info-scope-on-llvm-func` runs after the conversion to the llvm dialect; line tables are always on for this path), so a crash, a profile or a sanitizer report maps back
   to the node, and the build cache stays keyed by the ZIR address, above MLIR: an unchanged
   address skips the lowering entirely.
6. **Certificates stop at the lowering.** Every rewrite ZIR makes carries a certificate the
   checker revalidates; MLIR's and LLVM's passes carry none and are trusted the way Cranelift
   is, with the differential oracle (interpreter against native code, outputs byte-compared)
   as the check on them. L29 replaces them with passes written in Zed, each kept only when its
   output passes the oracle.
7. **Memory stays Zed's.** The plan of L1.34 is applied before the lowering: dups, drops and
   fused releases become explicit calls of the runtime's increment, decrement and free. MLIR's
   bufferization and ownership-based deallocation are not used for Zed values; `memref` is used
   only for flat numeric arrays inside a fused loop nest, whose buffers the loop's memory plan
   allocates and frees.
8. **The interface is MLIR's text form.** At L28 the code generator writes MLIR text and runs
   `mlir-opt` and `mlir-translate` to reach LLVM IR, then LLVM's code generator. The text form
   needs no C++ build in Zed's tree, and keeps the code generator testable by comparing text.
   MLIR's C API is adopted if measured compile time shows the process boundary matters.
9. **The Rust-hosted compiler keeps Cranelift; the Zed compiler emits MLIR text.** Cranelift is a
   Rust crate with a JIT and an object-file writer on one path, which is what L1.36 needs; it
   compiles fast; it needs no C++ toolchain, so CI builds it from a clean checkout. So `zedc run`,
   the tests, the differential oracle and the JIT stay on it. The compiler written in Zed reaches
   LLVM through the MLIR text port of step S.1a, under the author's order of 2026-11-05 that ZIR →
   MLIR → LLVM IR → x86-64 works before Zed₀. How run-time `compile` reaches a JIT from the Zed
   compiler is an open question to the author; the plan's answer is a retained Cranelift JIT port.
   What Cranelift lacks, loop optimization and vectorization, is what L28 adds, and the two back
   ends check each other under the differential oracle.

## Operations

| ZIR operation | MLIR lowering |
|---|---|
| `prim` | `arith` for scalars, and `math` only for what IEEE 754 fixes exactly, such as sqrt, with no contraction and no fast-math flags; each float result is canonicalized as the Cranelift path does (DESIGN.md sec:reduction); an elementary function calls the runtime's single implementation with `func.call`; an integer operation whose result the store's interval does not bound inside 64 bits is checked for overflow and takes the runtime's big-number path; strings and big numbers call the runtime with `func.call`. A `prim` with no inputs, a primitive as a value, is a `func.constant` of the runtime's function. |
| `lambda` | closure conversion: a `func.func` taking its captures as an extra argument (a runtime cell, decision 7), and a pair of the function and that cell. Upstream MLIR has no closure type, so the pair is an `llvm.struct`. |
| `apply` | `func.call` when the callee is known; `func.call_indirect` through the closure pair otherwise. A function that makes or receives a call in tail position is an `llvm.func` with the `tailcc` convention, and that call is `llvm.call tailcc musttail`, indirect calls included. |
| `if` | `scf.if`, its arms' results returned by `scf.yield`. An `if` or `match` in tail position is `llvm.cond_br` or `llvm.switch` blocks with a return in each arm, since `musttail` must come just before a return. |
| `match` | the decision tree on the scrutinee's tag and fields as `scf.index_switch` and nested `scf.if`, each arm yielding with `scf.yield`. |
| `rec` | a group of mutually recursive functions in one module, each an `llvm.func` with `tailcc` where a call among them is in tail position. |
| `wave` | one `async.execute` per region of the wave, with the wave's state edges as `!async.token` dependencies (decision 4); sequential code before L7.5 emits the regions in order. |
| `port read` | `func.call` of the runtime's read for the port. |
| `port push` | `func.call` of the runtime's push for the port. |
| `reindex` | inside a fused nest, index arithmetic in `arith`; otherwise a runtime call building the rekeyed family. |
| `discard` | the loop bound or guard that skips the dropped keys; a runtime call for a stored family. |
| `fold` | `scf.for` with the accumulator as an iteration argument; `scf.parallel` with `scf.reduce` when the operator's evidence states it associative and commutative; the exact float sum keeps its accumulator as the loop-carried value; any other float fold follows the canonical tree of DESIGN.md sec:reduction. |
| `fix` | `scf.while`, the before region testing whether the ascent changed. |
| `gen` | `scf.while`, the guard in the before region or the after region as the node's guard position says. A window keeps the rule of step L6.14a: generated code never loads below storage, and a read at a static distance has no compare. |
| `fam` | a runtime call building the family; in a fused nest, the loop that produces it. |
| `group` | the planner's chosen plan, lowered as the kernel definition its certificate holds; MLIR sees only the resulting loops and calls. |
| `orderedValues` | as `group`. |
| `scan` | `scf.for` with the running value as an iteration argument; a float scan other than `+` follows the canonical tree of DESIGN.md sec:reduction. |
| `join` | as `group`. |

## Region kinds

| ZIR region | MLIR form |
|---|---|
| `function` | the body of a `func.func`; ZIR regions are isolated, so captures are already explicit arguments, which fits a `func.func`, which is `IsolatedFromAbove` and so takes every outside value as an argument. |
| `match` | an arm region of `scf.if` or `scf.index_switch`, one block ending in `scf.yield`. |
| `loop` | the body of `scf.for`, `scf.while` or `scf.parallel`, one block ending in `scf.yield` or `scf.reduce`. |
| `rec` | a module of mutually recursive `func.func`s. |
| `port` | a `func.func` whose body calls the runtime's port functions in the order its state edges give. |

## Edges

| ZIR edge | MLIR form |
|---|---|
| `value` | an SSA value; its type from the edge's domain (an integer domain inside 64 bits is `i64`, a float `f64`, a boolean `i1`, other values a pointer to a runtime cell). |
| `state` | no value: the order of the runtime calls in sequential code, an `!async.token` between concurrent regions (decision 4). |

## Layout

Item LAYOUT-measure, 2026-11-05: the bytes each of the compiler's representations takes per
node, measured by the counting allocator of the test binaries on the step units
(`tests/steps/*/zed/*.zed`). The bytes of a structure are the bytes its drop frees, so a name
it shares with a structure that outlives it is not counted in it. The test
`l01_35_mlir_study::layout` holds the inline sizes below to the compiler's own, so a type that
grows fails it, and prints the measured figures.

Inline sizes, `size_of` on x86-64 (the heap cell as the tests build it, with feature `counts`):

| Type | Bytes |
|---|---|
| `ast::Expr` | 120 |
| `ast::ExprKind` | 104 |
| `ast::Stmt` | 272 |
| `ast::Type` | 72 |
| `ast::Pattern` | 88 |
| `kernel Term` | 88 |
| `kernel Value` | 56 |
| `zir::Node` | 112 |
| `zir::Op` | 40 |
| `zir::Src` | 56 |
| `zir::Edge` | 104 |
| `zir::Region` | 80 |
| `native Word` | 16 |
| `native heap cell` | 144 |

Measured on the 10 step units the front end accepts (4 more are refused by design and give no
record):

- Syntax tree: 496 expressions and statements in 126,752 bytes, 255 bytes per node, its
  types, patterns and names included.
- Kernel terms: 1,060 distinct terms (a shared term counted once) in 168,510 bytes for the
  elaborated units, 158 bytes per term.
- ZIR: 694 nodes in the 109 graphs of the closed terms the tables run, 649,448 bytes, 935
  bytes per node. A node's inline 112 bytes are a small part; its input, output and region
  vectors (56 bytes per input, 120 per output edge) and each region's vectors hold the rest.
  Since item INTERVAL-persistent (2026-11-10) an output edge takes 104 bytes: the interval set
  of its domain is one pointer to a shared tree instead of a 24-byte vector. The figures in this
  list are those of 2026-11-05.
- Native values: 109 runs allocated 195 heap cells, at most 8 live at once in one run. An
  unboxed value is one 16-byte word; a boxed one is a word and a 144-byte cell, plus its
  payload's own blocks. An atom with no payload is a word and takes no cell; one with a payload
  takes a cell. Each row also allocates one cell for the closure of the function it applies,
  so the `#leaf` row allocates 1 cell (the closure) and the six-field `#node(…)` row 3 (the
  closure, the result and the expected value), 2 live at once.
- A struct declaration (syntax tree only, since structs are compiled from step L2.4): 273
  bytes with no fields, 1,695 with six, about 237 bytes per field.
- Peak bytes of front end, lowering and native run together: 2,420,339 at 100 one-row
  definitions and 19,281,463 at 800, a ratio of 7.97 for 8 times the size.

For comparison, the Zig compiler's syntax-tree node is 13 bytes (zig-study); the figures here
are the base that items LAYOUT-soa and UNION-spare measure against.

## What this leaves for L28

- The integer domain decides when an `arith` operation can drop its overflow check; the
  check's absence must be proven by the store's interval, never assumed.
- The `match` decision tree is built in Zed before the lowering, so MLIR never sees patterns.
- The text form's version is pinned by one constant in the lowering crate, compared with `mlir-opt --version` by a test in `tests/full`, and the lowering's
  tests compare emitted text, so an MLIR upgrade that changes syntax fails a test rather than
  a build on a user's machine.
