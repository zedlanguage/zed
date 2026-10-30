# MLIR study (step L1.35)

The record of DESIGN.md step L1.35 and the plan for L28. It answers four questions: how
ZIR-loop and the target dialects lower to MLIR's dialects; whether ZIR is also written as an
MLIR dialect; what MLIR's graph regions and LLVM's lowering provide and lack against ZIR's state
edges, content addresses and certificates; and whether the compact back end of L1.36 stays
Cranelift. The test `tests/steps/l01_35_mlir_study` checks that every ZIR operation and region
kind has a row in the tables below, so an operation added later without a lowering fails it.

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
   lowering (decision 2), so no token type is needed in sequential code. Where L4's scheduler
   runs a wave's independent regions concurrently, each region becomes an `async.execute`
   whose dependencies are the state edges between regions as `!async.token`s: "starts
   execution of the attached body region only when all tokens and values become ready", and
   "All dependencies must be made explicit". A wave is therefore a set of `async.execute`
   operations, one per region, and each state edge between two of them is one token.
5. **Content addresses travel as locations.** MLIR has no content addresses. Each operation the
   lowering emits carries an MLIR location naming its ZIR node's address and path
   (`loc("zir:<address>" at "r.3/0.2")`), so a crash, a profile or a sanitizer report maps back
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
9. **The compact back end stays Cranelift.** Cranelift is a Rust crate with a JIT and an
   object-file writer on one path, which is what L1.36 needs (JIT first, AOT the same path); it
   compiles fast; it needs no C++ toolchain, so CI builds it from a clean checkout; and M0.8
   fixed that the Zed₀ compiler reaches Cranelift through built-in ports (step S.4), so changing
   the compact back end would change row S. What Cranelift lacks, loop optimization and
   vectorization, is what L28 adds, and the two back ends then check each other under the
   differential oracle.

## Operations

| ZIR operation | MLIR lowering |
|---|---|
| `prim` | `arith` and `math` for scalars; an integer operation whose result the store's interval does not bound inside 64 bits is checked for overflow and takes the runtime's big-number path; strings and big numbers call the runtime with `func.call`. A `prim` with no inputs, a primitive as a value, is a `func.constant` of the runtime's function. |
| `lambda` | closure conversion: a `func.func` taking its captures as an extra argument (a runtime cell, decision 7), and a pair of the function and that cell. Upstream MLIR has no closure type, so the pair is an `llvm.struct`. |
| `apply` | `func.call` when the callee is known; `func.call_indirect` through the closure pair otherwise. |
| `if` | `scf.if`, its arms' results returned by `scf.yield`. |
| `match` | the decision tree on the scrutinee's tag and fields as `scf.index_switch` and nested `scf.if`, each arm yielding with `scf.yield`. |
| `rec` | a group of mutually recursive `func.func`s in one module. |
| `wave` | one `async.execute` per region of the wave, with the wave's state edges as `!async.token` dependencies (decision 4); sequential code before L4 emits the regions in order. |
| `port read` | `func.call` of the runtime's read for the port. |
| `port push` | `func.call` of the runtime's push for the port. |
| `reindex` | inside a fused nest, index arithmetic in `arith` and `affine` where affine; otherwise a runtime call building the rekeyed family. |
| `discard` | the loop bound or guard that skips the dropped keys; a runtime call for a stored family. |
| `fold` | `scf.for` with the accumulator as an iteration argument; `scf.parallel` with `scf.reduce` when the operator's evidence states it associative and commutative; the exact float sum keeps its accumulator as the loop-carried value. |
| `fix` | `scf.while`, the before region testing whether the ascent changed. |
| `gen` | `scf.while`, the guard in the before region or the after region as the node's guard position says. |
| `fam` | a runtime call building the family; in a fused nest, the loop that produces it. |
| `group` | the planner's chosen plan, lowered as the kernel definition its certificate holds; MLIR sees only the resulting loops and calls. |
| `rank` | as `group`. |
| `scan` | `scf.for` with the running value as an iteration argument. |
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

## What this leaves for L28

- The integer domain decides when an `arith` operation can drop its overflow check; the
  check's absence must be proven by the store's interval, never assumed.
- The `match` decision tree is built in Zed before the lowering, so MLIR never sees patterns.
- The text form's version is pinned with the LLVM release CI installs, and the lowering's
  tests compare emitted text, so an MLIR upgrade that changes syntax fails a test rather than
  a build on a user's machine.
