> [!NOTE]
> **Zed is still under construction and is not yet ready for use, but it is coming soon.**
> Releases will be announced at [x.com/zedlang](https://x.com/zedlang). This page describes the language as it will be when finished.

<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a programming language in which a program is a graph of values and the dependencies between them. The compiler reads that graph to get parallel scheduling, memory management, safety checks, and incremental recomputation. You write ordinary-looking code, and none of those words appear in it.

## Why Zed exists

- **All computation is already a graph.** A value cannot be computed before its operands exist. Spreadsheets, SSA form, Spark, build systems, reactive UI frameworks and out-of-order CPUs all rely on this graph or work to recover it.
- **Mainstream languages throw the graph away.** They make you flatten it into a sequence of statements over mutable places. The usual problems follow from that step:
  - The compiler and CPU work to recover parallelism that the program text destroyed.
  - Threads and locks bring back concurrency by hand, along with races and deadlocks that the graph never contained.
  - Memory management guesses at lifetimes that the graph states exactly.
  - Incremental and reactive systems add dependency tracking that the language discarded.
- **Queries and loops should not be two worlds.** The same computation written as SQL or as a loop has different tools, different performance, and no check that the two agree.
- **Faults should be impossible to write, not merely caught.** A null, a bad index or a forgotten error case should be a compile error or an ordinary value, never a crash in production.
- **Power should not cost ceremony.** A program with no annotations should already be typed, parallel and memory-managed. Anything more you write should be optional.

## Core features

### One idea

- **Everything is a morphism**, a map from a tracked key domain to values: collections, functions, blocks, structs, loops, streams, variables, and the program itself.
- **One structural operation** (remap), **one way to merge values** (reduction with checked algebra), **one treatment of failure** (typed values), and **one model of state** (generations).
- **Familiar syntax.** The surface looks like Dart and fits on a short cheatsheet. A feature that adds a concept without removing one is not admitted.
- **Optional layers.** Types, units, laws, proofs and placement can be added in any combination. A layer can reject a program, accept one, or speed it up. It never changes a result unless the change shows in a type.

### Parallelism and determinism

- **Automatic parallelism.** Nothing in a program says "in parallel". Data dependency is the only sequencing, and the schedule is read from the graph.
- **Bit-identical results at any core count**, including floating-point reductions. A float sum is computed exactly and rounded once.
- **Declared nondeterminism only.** The sources are a short, fixed list: arrival order at ports, a declared interleaving at an output port, foreign-call results whose order the program leaves open, resource exhaustion, and reductions written `unordered`, which carry that fact in their type.
- **Algebra widens the schedule.** Associativity allows tree reduction and commutativity allows combining values as they arrive. Composing transition functions turns "inherently serial" loops into parallel scans.
- **No races or deadlocks.** Every value has one writer and can be read only once complete. The one remaining wait cycle comes from bounded queues, and it is a checked obligation on their declared bounds.

### Data, keys and queries

- **Loops and queries are one object.** Both forms compile to the same kernel term, so a loop can run as a hash join and a join as a loop nest.
- **Keys are tracked through every operation.** If two values could land on one key, the program does not compile until you say how to combine them.
- **Joins are one typed decision per region of the key overlap**: keep, drop or assert empty, for each side and for the intersection.
- **Data structures are plan choices.** An index exists only if keyed access demands it. A table that is only scanned compiles to a flat run.
- **Cost is part of the type.** Every function has a derived work and depth bound (`f::cost`), and `@cost`, `@fused` and `@noalloc` can assert one.

### Types and static checks

- **Set-theoretic types.** Union, intersection and negation, with occurrence narrowing and full inference.
- **Ranges are types.** `a[i]` either provably cannot miss, or its type says `T | #notFound`. An integer's machine representation is chosen from its domain, so it cannot overflow.
- **Facets carry everything else** on the same definitions: units, taint, order, uniqueness, cost and operator algebra, plus facets you define yourself.
- **No implicit conversions**, no implicit folds, and no last-write-wins at a collision.
- **The checker decides rather than guesses.** It gives a fixed answer for every program, independent of how clever an analysis could have been. No compiler algorithm takes exponential time, and none is cut short by a budget.
- **Diagnostics show their work.** A rejection shows each constraint, its site and the path it propagated along, and offers a repair you can write in the core language.

### Failure

- **No exceptions, no null, no traps.** Failures such as `#notFound`, `#divByZero` and `#ioError` are atoms in a union type.
- **Handle it or carry it.** A partial operation's result type carries its failures until code disposes of them with `else`, `?.` or `match`.
- **Exhaustive `match`.** An unhandled case does not compile.

### Memory

- **No garbage collector and no pauses.** Where the last use of a value is known statically, its release is unconditional and no count exists.
- **Exact reference counting for the rest**, exact because the value graph is acyclic. No tracing collector or cycle collector is needed.
- **Inferred storage.** Fusion removes most intermediates, and a recurrence keeps only the frames that are read.

### State, time and reactivity

- **Generations instead of mutation.** `x` is the value in this step, `x'` the next, `x[i-k]` a fixed distance back, and `x::frames` the whole history.
- **Loops are values.** `sim.pos` is the final state, and undo and time travel are field reads.
- **Incremental by default.** When an input changes, only the values that depend on it recompute, in waves that commit atomically, and the result matches a from-scratch run.
- **Total provenance.** Every value's address and immediate inputs can be queried, which supports debugging, audit and taint tracking.
- **Ports are the only outside world.** Files, sockets, stores and devices appear in a program's type. Timeouts, retries, hedging, circuit breakers and rate limits are declared on the port.

### Compile-time programming

- **Partial evaluation is the one staging mechanism.** Types, checks, serializers, reflection and metaprogramming all reduce to it, and any node whose inputs are static is evaluated at build with no annotation.
- **Introspection.** `f::source`, `f::ast`, `T::shape` and `T::fields` read code and types as ordinary values.
- **Formulas are values.** The syntax tree of a lambda can be expanded, differentiated, simplified and compiled back, with each rewrite checked by the kernel.
- **Grammars in structs.** One declaration gives a type, a parser and a printer, with the round trip guaranteed.

### Verification

- **Tests, laws and proofs are one scale.** A `law` is boolean Zed, graded by its evidence: checked over a whole finite domain, proved with a certificate an independent checker accepts, checked up to a bound, covered by a test, or assumed.
- **Model checking without a second language.** A loop is a state machine, `@invariant` is loop induction, and the reachable set is a value the compiler computes.
- **Algebraic claims carry graded evidence.** What `@associative` may license depends on the grade of its evidence. A false claim that gets through gives a wrong result that is still deterministic, blamed at its declaration.
- **Number algebras and matrices.** Exact `rat`, `complex`, `quat`, `oct`, and vectors and matrices with checked shapes.

### Compiler and targets

- **Self-hosted over a small core.** Type checking, decision procedures and optimizer rewrites are Zed source in the prelude, so you can read and extend them.
- **An e-graph optimizer with certificates.** A plan choice can never change a value.
- **One intermediate representation for every target**: native code through MLIR and LLVM, wasm, GPUs, distributed dataflow, hardware synthesis and microcontrollers.
- **C FFI in both directions**, with foreign calls typed as port operations.

## How the features work together

The features above are one graph read in different ways. Its edges are the schedule, its keys are the data algebra, its lifetimes are the memory plan, and its time keys are the reactive engine. Here is how that plays out.

**Keys, algebra and parallelism.** Reduction is the only place where values from different keys merge. The operator's tracked algebra decides how it may run: `+` on integers can combine as values arrive, while a float product takes one fixed tree, chosen so that the result is the same at any core count. Everything else moves values between distinct keys, so it needs no locks.

**Single assignment, memory and safety.** One writer and no mutable places mean there is nothing for a race to be about. The same acyclic graph makes reference counting exact, and static last-use analysis removes most of the counts. Eliminating data races and eliminating the garbage collector come from one fact about the program.

**Ranges, failures and partial evaluation.** A range in a type lets the checker delete a test, and a test it cannot delete shows up as a failure atom in the result type. So there is no hidden run-time check to reason about. A static input narrows the range to one value, and the whole call may then run at build. Checking and optimizing are one computation.

**Duality, demand and cost.** Loops and queries share a kernel term and every function has a derived cost, so the planner chooses by arithmetic. An index is an ordinary derived value that is removed when nothing reads it, the same way dead code is. A choice that depends on sizes known only at run time stays in the program and is made then. Two plans swap only when their outputs are identical.

**Generations, retention and reactivity.** Because a variable is its whole history, storage is a retention decision. If the program reads back two frames, the compiler keeps a two-slot ring. If it reads `::frames`, the history is kept and shared. Reactive recomputation is the same graph with its edges run in the push direction, which is why it needs no framework.

**Laws, optimizer and compiler.** A proved law licenses a rewrite, and the optimizer's rewrites are themselves Zed with proved laws. Partial evaluation specializes the checks and rewrites to their rule tables, so writing the compiler as a library costs no speed, and extending it takes the same language as using it.

## Zed in 24 examples

Names not defined in a snippet are assumed inputs. A `✗` marks a line the compiler rejects.

**1. A complete program.** The file port and the output are in the signature. There is no `void main`, no null check and no thread.

```zed
main(fs: Files) -> (stdout: Lines) {
  text   = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines  = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.rank;
}
```

**2. Integers that cannot overflow.** Integers have no width, and division states when it can fail.

```zed
big = 2 ** 100;                               // never overflows
third = 1r / 3r;                              // an exact rational
c: u8 = 256;                                  // ✗ a type error, not a wrap
half(n) = n div 2;                            // int: 2 is known not to be zero
ratio(positional a, positional b) = a div b;  // int | #divByZero: b might be zero
```

**3. Failures ride through a pipeline.** The type lists every way each entry can fail, and you choose what to do at the end.

```zed
amounts   = files.map(f -> int(read(f)));          // int | #invalid | #ioError | #notFound
sumKept   = amounts.where(a -> a is int) >< (+);   // skip the bad entries
sumZeroed = amounts.map(a -> a else 0) >< (+);     // or count them as zero
port      = parse(text)?.server?.port else 8080;
```

**4. A parallel float sum with one answer.** It gives the same bits on 1 core or 1,000, and giving that up for speed is visible.

```zed
total = readings >< (+);             // the exact sum, rounded once
quick = samples >< (+) unordered;    // faster, and the type says it may vary
```

**5. Your own parallel monoid.** The compiler derives the claim, because `combine` is a tuple of `+` monoids, so the fold can combine values as they arrive.

```zed
struct Moments { n: int, sum: rat, sumSq: rat }
moment(positional x: rat) = Moments(n: 1, sum: x, sumSq: x * x);
@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum, sumSq: a.sumSq + b.sumSq);
m = xs.map(moment) >< combine else Moments(n: 0, sum: 0r, sumSq: 0r);
```

**6. Lost data does not compile.** Rekeying by a non-unique field is an error, not a silent overwrite. Inverting a map groups, and the type says so.

```zed
byId  = users.rekey(u -> u.id);    // ✗ Collision, unless u.id is known to be injective
byId2 = users.group(u -> u.id);    // Id ->? (UserKey -> User)
whoTeaches = teacherOf as (teacher -> course) into (course -> teacher -> _);
```

**7. A pivot table in one line.** The result's shape is written directly, and `><` marks the level that is summed away.

```zed
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
// Region ->? Product ->? rat
```

**8. A join and a loop are the same program.** Both compile to one term, and the compiler picks the plan. Absence is a value, not a null row.

```zed
paid  = orders.join(payments, on: #orderId, kind: #left);
paid2 = for o in orders { payment = payments[o.orderId] else #none; (o, payment) };
```

**9. Matrix multiplication as a query.** It is a join on the inner dimension with that dimension reduced away.

```zed
ab = (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]);
at = a as (r -> c -> v) into (c -> r -> v);     // transpose
```

**10. Edit distance, with no choice of algorithm.** Sparse demand runs it as memoized recursion and dense demand as a wavefront table, from the same source.

```zed
d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

**11. Maximum subarray, parallelized.** The step is affine over `(max, +)`, so Kadane's serial loop becomes a parallel prefix scan.

```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;
```

**12. An "inherently serial" text scan, parallelized.** The state domain is finite, so the compiler turns `csvStep` into a transition table and runs a parallel scan.

```zed
state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

**13. Search that cancels itself.** Higher candidates run speculatively and stop as soon as a lower one hits, because the code is pure.

```zed
firstPrime = (for i in n.. { i }).where(isPrime).first;
```

**14. Binary search you don't write.** On a sorted view the plan is bisection in O(log n). Otherwise it is a scan with the same result. Here `i` is known to be in range, so `xs[i]` cannot miss.

```zed
lowerBound(positional xs: [int], positional t: int) =
  (0..<xs::len).where(i -> xs[i] >= t).first;
find(xs: [int], t: int) =
  match lowerBound(xs, t) { #none -> #none, i -> if xs[i] == t { i } else { #none } };
```

**15. Only what is asked for runs.** The record has two fields, each its own node in the graph, so a caller that reads one never pays for the other.

```zed
stats(positional data: [f64]) {
  n = f64(data::len);
  mean = data.sum / n;
  sd   = (data.map(x -> (x - mean) ** 2).sum / n).sqrt;
  return { mean:, sd: };
}
m = stats(xs).mean;      // sd's subgraph never runs
```

**16. History you declare, storage you don't.** The recurrence reads two frames back, so the compiler keeps a two-slot ring and no array exists.

```zed
pos[i in 0..<n] = 2*pos[i-1] - pos[i-2] + accel(pos[i-1]) * dt ** 2
  with pos[-1] = p0, pos[-2] = p0 - v0*dt;
last = pos[n-1] else p0;
```

**17. Undo is a field read.** Asking for `::frames` is what keeps the history, and the frames share their structure.

```zed
run  = loop t { while t < edits::len && !closed; doc' = doc.patch(edits[t]) with doc = empty; };
past = run::frames[run::len - 2].doc else empty;
```

**18. A spreadsheet in one line.** Edit one row of `sales` and only the values that depend on it recompute, with provenance for every cell.

```zed
@memoized report = sales.join(costs, on: #sku)
  .group(((s, c)) -> s.region)
  .map(rows -> rows.map(((s, c)) -> margin(s, c)).sum);
```

**19. Preconditions the compiler infers.** A field's range can name another field. `@ensure` moves a check back to the callers, and no test remains at run time.

```zed
struct Span { lo: int, hi: int[lo..] }
s = Span(lo: 2, hi: 5);
w = s.hi - s.lo;                                             // int[0..]
@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);    // inferred: x <= 49
a = odd(12);                                                 // 25
b = odd(60);                                                 // ✗ 60 is outside x <= 49
```

**20. Wrong physics and SQL injection don't build.** Units and taint are facets, checked and propagated with the type.

```zed
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                                  // f64 with units("m")
bad = v + t;                                // ✗ m/s + s
rows = exec(db, "SELECT * WHERE name = " ++ userName);  // ✗ taint #userInput reaches #clean sink
```

**21. A calculator: grammar, then meaning.** The structs are the parser, and the printer comes with them.

```zed
struct Sum   grammar { terms: Prod sep "+" }
struct Prod  grammar { factors: Atom sep "*" }
struct Paren grammar { "(" inner: Sum ")" }
type Number = Utf8String matching grammar { digit digit* };
type Atom   = Number | Paren;
Sum.eval    = terms.map(t -> t.eval).sum;
Prod.eval   = factors.map(f -> f.eval) >< (*);
Paren.eval  = inner.eval;
Number.eval = int(this) else 0;
value = Sum.parse("2*(3+4)")?.eval;         // 14, or #syntaxError
```

**22. A generic JSON decoder with no reflection and no code generator.** The type is known at build, so partial evaluation turns `decode` into a parser for just these two fields. On a literal input the whole call runs at build, and the program contains no parser at all.

```zed
struct User { id: int, name: Utf8String }
u: User | #parseError(pos: int, msg: Utf8String) = Json.decode(text);
ok: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
```

**23. Symbolic algebra on your own code.** A lambda's source is a value, the library is ordinary Zed, and each rewrite step is checked by the kernel.

```zed
p = ((x: rat) -> (x + 1r) ** 2)::source;
e = expand(p);         // the tree of (x: rat) -> x ** 2 + 2r * x + 1r
d = derivative(p);     // the tree of (x: rat) -> 2r * x + 2r
```

**24. Tests, proofs and a model check in the same language.** The first law is decided without running anything. The reachable set is computed at build, and a counterexample would come back as a trace.

```zed
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
law doubleIsSum(x: int) = double(x) == x + x;

type Lamp = #green | #yellow | #red;
type Cmd  = #tick | #fault;
advance(positional l: Lamp, positional c: Cmd) =
  if c == #fault { #red } else { match l { #green -> #yellow, #yellow -> #red, #red -> #green } };
reachable = loop { R' = R.union(R.flatMap(l -> [advance(l, #tick), advance(l, #fault)]).image) with R = { #red }; };
law faultStops(l: Lamp) = (l in reachable.R).implies(advance(l, #fault) == #red);
```
