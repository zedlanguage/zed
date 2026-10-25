<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a programming language in which the program *is* its value-dependency graph. Everything a modern language is expected to do for the programmer is done by reading that graph, rather than by a separate subsystem:

- **Automatic, deterministic parallelism.** Nothing in a Zed program says "in parallel" or "in sequence". The only ordering is data dependency, and the schedule is read off the graph. Outputs are bit-identical at any core count, floating-point reductions included.
- **No races, no deadlocks, no nulls, no traps.** There are no mutable places and no dependency cycles. Absence and failure are typed values that the program must handle or carry; null dereference, out-of-bounds indexing, division by zero, and unhandled failure cannot be written.
- **Queries and loops are one object.** Relational code (select / where / join / group) and loop code (for / filter / lookup / accumulate) elaborate to the same kernel term, and the compiler chooses how to execute either: a loop as a hash join, a join as a loop nest, a filter as an index probe.
- **Algebraic reasoning about data.** Collections are maps from tracked key domains to values. A program in which two values could land on one key does not type-check without an explicit reducer, and every join is one typed decision per region of the key overlap.
- **Pause-free memory management.** Lifetimes are read off the acyclic value graph: statically known releases are unconditional, and the rest is exact reference counting. There is no tracing garbage collector.
- **Incremental and reactive by default.** Every read of a varying quantity names the generation it reads, so reactive recomputation, time travel, and provenance are the same operation. Every incremental result equals a from-scratch recomputation.
- **A rich but simple type system.** One set-theoretic type algebra (union, intersection, negation) with occurrence narrowing and range-refined domains. Units, taint, order, cost, and operator algebra are facets carried with types.
- **Partial evaluation as the one staging mechanism.** Types, checks, serializers, reflection, metaprogramming, and the compiler-as-a-library are all compile-time evaluation of ordinary Zed.
- **Total provenance.** Every value can say where it came from, which supports debugging, information-flow security, and audit.
- **A familiar surface.** Dart-flavored assignments, loops, and method calls. Ordinary-looking code is correct, parallel, and incremental without any of those words appearing in it; written types, laws, proofs, and placement hints are optional layers that can never change what a program computes.

### Under construction -- coming soon
