# Thresholds, and what replaces them

The author's direction (2026-10-30): nothing in Zed may rest on an arbitrary threshold,
cap or budget whose crossing changes what the compiler does. Each one is to be replaced by
an algorithm with no parameter: a monotone propagation over the program's own dependency
graph, which stops because the lattice it climbs or descends has a height fixed by the
program, not by a constant; or a fragment chosen by the program's structure, decided
exactly and in low polynomial time.

This file lists every such constant in the specification and the implementation, what
crossing it changes, and the replacement, in the order the replacements are made. The
resource limits of the machine (memory, stack, the evaluator's largest integer) are not on
the list: running out of them is a build failure, never a different answer (DESIGN.md
"Budgets").

## The inventory

| Constant | Where | What crossing it changes |
|---|---|---|
| `RUNS` 20000 | check/mod.rs | a signature search gives `_` for its parameters and result |
| `CONTEXTS` 64 | check/mod.rs | a nested function gives `_` in further contexts |
| `open.len() > 5` | check/mod.rs `infer` | a function with more than 5 undeclared parameters gives `_` |
| `COMBOS` 256 | check/mod.rs `apply` | a call over unions with more combinations gives `_` |
| `SHOWN` 12 | check/mod.rs | the failed combinations after 12 are counted, not shown |
| `DEPTH` 16 | check/mod.rs | a derivation is cut after 16 steps |
| diagram budget 4096, walk 65536 | zed-kernel types/bdd.rs, empty.rs | a union or intersection keeps its operands; a part is not shown empty |
| `PIECE_LIMIT` 8 | store/interval.rs | a union of intervals loses pieces at a widening |
| `FINITE_SET_LIMIT` 64 | store/lattice.rs | a finite set becomes the top at a widening |
| `WIDENING_DELAY` 3 | store/iterate.rs | which changes of a loop head are joins and which widenings |
| `HEAD_ITERATIONS` 64 | store/iterate.rs | a component is set to the top |
| `NARROWING_ROUNDS` 64 | store/iterate.rs | phase 2 stops with the values it has |
| `REDUCTION_ROUNDS` 16 | store/product.rs | the reduction stops with the values it has |
| `VARIABLES` 16, `ATOMS` 64, `INTERMEDIATE` 4096, `KEPT_CONJUNCTIONS` 64 | store/presburger.rs | a relation is dropped and its written constraint kept |
| `CALL_DEPTH` 64, `TRANSFER_FUEL` 100000 | store/preimage.rs | the transfer through calls stops |
| `BUILD_FUEL` 10^6 | stage.rs | a build-stage term is left to run whole |
| `SPLIT_CAP` 1024 | stage.rs | the Trick does not split a parameter |
| `ENUMERATION_BUDGET` 4096, `ENUMERATION_FUEL` 10^4 | zed-kernel budgets.rs | an obligation is not enumerated; a binding removes nothing |
| `BMC_SEQ_LEN` 4, `BMC_GENERATIONS` 16, `BMC_BUDGET` 65536, the integer cut | zed-kernel budgets.rs | rung 6 checks a prefix |
| `SATURATION_ITERATIONS` 8, `SATURATION_NODES` 10^4 | zed-kernel budgets.rs | rung 3 stops saturating |
| `DEFAULT_FUEL` 10^8 | zed-kernel eval.rs | a compile-time evaluation stops |

Not thresholds: `TOP` 29 (the number of grammar layers), `POWER_FACTORS` 64 (the width of
`i64`), `MAX_BITS`, `MAX_DEPTH`, `MIN_STEPS`, `MIN_MEMORY`, `STACK_BYTES` (resources).

## The replacements

### 1. Signature search: carrier classes (replaces RUNS, CONTEXTS, open > 5, COMBOS, SHOWN)

Every operator and prelude word in L1 is homogeneous: its arrows range over a set of
carriers, every parameter takes the same carrier, and the result is that carrier or a type
fixed by the arrow (`op_sig`, `word_sig`). So the only relations the body of a function
can place on the carriers of its undeclared parameters are equality (two operands of one
operator, a value flowing to another) and membership (an operator accepts a set of
carriers; a literal adopts int, f64 or rat). A system of equalities and memberships is
solved exactly by union-find: each class of values that must share a carrier holds the set
of carriers still allowed. Merging two classes intersects their sets. Every step either
merges two classes or removes carriers from a set, so the state only descends, in at most
(number of values) merges and (number of classes × 5) removals: the wavefront the author
describes, and it stops by the height of that lattice, not by a constant.

- Each body is checked once. A nested function reads the outer binders' classes
  directly, as a let-bound function does in ML, so there are no contexts to multiply.
- A signature is the parameters' types over class variables with each class's set, not a
  list of arrows: `area(w, h) = w * h` is `(w: T, h: T) -> T` with `T` in int, f64, rat.
  The list of arrows is the product of the sets, and is printed only when asked for.
- A class that holds a literal takes the first carrier of its set in the order int, f64,
  rat, since the body elaborates once (this is what "the fewest adoptions" selects today).
- A call instantiates the classes. Where a class reaches one argument position, each part
  of a union argument is checked against its set separately; where it reaches several, the
  parts must all be one carrier. Both are linear in the parts, so no product is formed.
- A failure is an empty set. Its explanation is the chain of merges and memberships that
  emptied it, kept as a proof forest (each merge records the expression that caused it),
  which is as long as the derivation and needs no cut.
- Not Hindley–Milner with subtyping: the classes carry no variance. Unions stay as the
  checker builds them today; only carriers are solved for.

Cost: O(N α(N)) for a unit of size N, against exponential in the nesting depth and in the
number of undeclared parameters before.

### 2. Derivations (replaces DEPTH)

A derivation is a walk of a graph (a binder's origin, the expressions that continue it).
With a visited set each node is shown once and later uses refer to its number, so the
derivation is at most the size of that graph and needs no cut.

### 3. Widening and iteration (replaces PIECE_LIMIT, FINITE_SET_LIMIT, WIDENING_DELAY,
HEAD_ITERATIONS, NARROWING_ROUNDS, REDUCTION_ROUNDS)

Widening with landmarks: at a widening point a bound moves only to the next value written
in the program (its literals and declared bounds, each ±1) or to ±∞. The lattice seen at
widening points then has height 2(L + 1) per bound, L the number of landmarks, so
iteration ends by height with no delay and no cap on head changes; a union of intervals has
at most L + 1 pieces there; a finite set at a widening point keeps only written values and
otherwise becomes their interval hull. Narrowing refines only the bounds a widening set,
each at most once to each landmark, so it ends by the same height. Reduction rounds descend
the same way.

### 4. Presburger relations (replaces VARIABLES, ATOMS, INTERMEDIATE, KEPT_CONJUNCTIONS)

Eliminate a variable only when elimination does not increase the number of constraints
(lower bounds × upper bounds ≤ lower + upper, which holds when it has at most one bound on
one side or two on each). The system never grows, so elimination is polynomial with no cap;
a relation where no variable can be eliminated this way is kept as its written constraint,
a property of its shape the program can see.

### 5. Preimage through calls (replaces CALL_DEPTH, TRANSFER_FUEL)

A summary per function, computed once per strongly connected component of the call graph
in topological order, iterated to its fixpoint on the landmark lattice of 3. Each function
is summarized once.

### 6. Build-stage evaluation (replaces BUILD_FUEL)

A demanded term is evaluated at the build stage when its termination is shown (structural
or measured recursion, the evidence `total` mode already uses); otherwise it runs at run
time. The rule is about the term's form, not how far an evaluation got.

### 7. The Trick (replaces SPLIT_CAP)

Split a parameter on the values the program's static calls pass it, not on its whole
domain: at most one specialization per call site, so the code grows at most linearly.

### 8. Verification ladder (replaces the enumeration, BMC and saturation budgets, DEFAULT_FUEL)

- Rung 1 enumerates a domain whose members are listed in the source (bool, atom sets,
  literal sets, and tuples of these); a range is decided by interval reasoning instead.
- Rung 6 runs only to bounds the program writes; without them it does not run.
- Rung 3 saturates only with rewrites that do not grow terms (congruence closure and
  canonical forms), which terminate without a bound.

### 9. Type diagrams (replaces the 4096 and 65536 budgets)

Open. Emptiness of Boolean combinations of tuple types is coNP-hard, so an exact answer
cannot be polynomial in general. Candidates: decide exactly where the combination's tuple
parts share no component (a property of the types); keep operands otherwise. To be measured
on the corpus before choosing.

## Order

1 first (it is the one that grew exponentially), then 2, 3, 5, 4, 7, 6, 8, 9. Each is a
step with its own tests, the old threshold's tests rewritten to the new rule, and a
scaling test.
