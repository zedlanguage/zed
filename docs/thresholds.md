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
| `RUNS` 20000 | check/mod.rs | removed (1): a signature search gave `_` for its parameters and result |
| `CONTEXTS` 64 | check/mod.rs | removed (1): a nested function gave `_` in further contexts |
| `open.len() > 5` | check/mod.rs `infer` | removed (1): a function with more than 5 undeclared parameters gave `_` |
| `COMBOS` 256 | check/mod.rs `apply` | removed (1): a call over unions with more combinations gave `_` |
| `SHOWN` 12 | check/mod.rs | removed (1): the failed combinations after 12 were counted, not shown |
| `DEPTH` 16 | check/mod.rs | removed (2): a derivation was cut after 16 steps |
| diagram budget 4096, walk 65536 | zed-kernel types/bdd.rs, empty.rs | a union or intersection keeps its operands; a part is not shown empty |
| `PIECE_LIMIT` 8 | store/interval.rs | removed (3, 3c): an image or preimage with more pieces was merged and marked necessary |
| `FINITE_SET_LIMIT` 64 | store/lattice.rs | removed (3c): an interval or type with more members was not listed |
| `WIDENING_DELAY` 3 | store/iterate.rs | removed (3): which changes of a loop head were joins and which widenings |
| `HEAD_ITERATIONS` 64 | store/iterate.rs | removed (3): a component was set to the top |
| `NARROWING_ROUNDS` 64 | store/iterate.rs | removed (3): phase 2 stopped with the values it had |
| `REDUCTION_ROUNDS` 16 | store/product.rs | removed (3) |
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

**Done.** RUNS, CONTEXTS, `open > 5`, COMBOS and SHOWN are removed (`check::Class`,
`Ck::infer`, `Ck::apply_one`, `Ck::apply_many`). Where it differs from the plan above:

- A class holds the carriers and one more bit for other values (tuples, functions, atoms
  that are not carriers); a class left with that bit gives `_`.
- Union by rank without path compression, so a find is O(log N) and the whole O(N log N);
  path compression would need its writes logged for the repairs that are tried and undone.
- The explanation is the class's list of the uses that narrowed or merged it, shown in full,
  not a proof forest. The error is at the use that would empty the set, which is where the
  carriers ran out, not where the function is declared.
- There are no derived variables: an operator applied to a class gives the class when every
  arrow still possible returns its own carrier, with the atoms of all of them (so the
  result may hold an atom that only some of those arrows give), and otherwise the union of
  their results.
- A call of an operator over unions keeps one state per set of arrows still alive, not per
  combination of parts. Each state is a subset of the operator's arrows, so there are at
  most 2^(A+1) of them for an operator of A arrows (with the flag for an unknown part), a
  constant of the prelude, and the cost is
  linear in the parts.
- A function's own recursive call (not yet reachable, L6) flows its arguments into its
  classes.

Mutants of `check/mod.rs`, each caught by a step test: a class emptied without an error,
merged classes taking the union of their carriers, a literal not fixing its class's carrier,
a literal compared by `==` restricting its class, an `if` condition taking any carrier, and
a class dropping the arrows over non-carriers. The last was the code as first written: it
rejected `x < (1, 2)`, though `x` may be a tuple; `x` now gives `_`.

### 2. Derivations (replaces DEPTH)

A derivation is a walk of a graph (a binder's origin, the expressions that continue it).
With a visited set each node is shown once and later uses refer to its number, so the
derivation is at most the size of that graph and needs no cut.

**Done.** `Ck::derive_into` keeps a set of the expressions it has derived and a set of the
steps it has shown, and walks with its own stack, since a chain of definitions is as long as
the program (a recursive walk overflowed the stack at 400 bindings). A later use of a node is
not shown again rather than referring to its number; the renderer already shows a place once.
Before, a value read twice at each of k bindings was derived 2^k times up to the cut, and the
duplicate check scanned every step shown, O(n²); now 400, 800, 1,600 and 3,200 bindings take
0.15, 0.32, 0.63 and 1.20 s (debug build, whole `zedc run`). With the visited set disabled
the L1.29 tests do not finish in 300 s.

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

**Reduction rounds: done.** The plan above was wrong about them: they need no landmarks.
`REDUCTION_ROUNDS` hid an endless descent, not a slow one. The projection of the relation read
each name's interval but not its congruence, so `x == y` with `x` even and `y` odd moved the
two lower bounds up one step per round (after 16 rounds `x` was in `32..` and the arm was
still reachable). The projection now adds `x == m * k + r`, `k` a fresh variable, for each
name whose class has a modulus above 1, so its hulls end at members of every class and the
class moves no endpoint it gave. A projection of a box of several pieces can still narrow
again when it is run on its own output, since the narrowed pieces split the formula into
finer conjunctions, so it runs again only when another reduction has changed a product
since it last ran. The other reductions change only finitely often (a class only to one
value or none, a finite set and a type's literals only by losing members, enumeration once
per constraint), so the loop ends with no bound on its rounds. Test:
`l01_39_reduced_product::controls::an_equality_between_names_of_different_parity_is_unreachable`
(fails without the congruences in the projection).

**Widening and narrowing: done.** The landmarks are the program's integer literals k, each
as k − 1, k and k + 1, and its literal values for finite sets (`store::lattice::Landmarks`;
the equations give them, `Equations::landmarks`). The plan above changes in three places.

- *Interval widening.* Each finite endpoint of the new value that is not already one of the
  old value's endpoints moves outward to the nearest target: an endpoint of the old value,
  of either role, or a landmark; with none on that side it goes to ±∞. Pieces that then
  touch merge. Every finite endpoint of a chain lies in K, the first value's endpoints and
  the landmarks, and the chain has at most 2|K| + 2 elements. No piece cap is needed: the
  pieces are bounded by K. With no landmarks this is the old widening.
- *Interval narrowing* is not limited to landmarks. Each finite endpoint of the meet moves
  outward to the nearest of the old value's endpoints and the landmarks; with none on that
  side, it stays where it is, so an infinite end takes a finite bound once, as in classic
  narrowing. This recovers a bound the program computes (`0..99` from `i < 99` with no
  literal written) and still ends: each side changes at most once from infinite and then
  only to points of a finite set.
- *Finite sets* widen to the join when every added member is a landmark, else to the top
  (not to an interval hull: a finite set of values need not be integers). They narrow to
  the meet, which only loses members. A congruence narrows only from the top, or to one
  value or none; a cardinality as an interval, met with `0..`; a type as its parts.

`solve` widens at every change of a head, with no delay, and runs phase 2 until a round
changes nothing. The tests show the old constants were not needed: a counter stops at its
guard's landmark at any bound (2, 99, 10^6) in phase 1; with no landmark it goes to `0..`
and phase 2 brings it back to `0..=99`; a chain of six cells needs six narrowing rounds, run
to the end; `x = x + 1` from `0..`, where meets alone would descend forever, ends after no
change; and the stack-machine oracle agrees with and without landmarks. A head stops at
most once per landmark under its fixpoint: 3L + 1 evaluations for L landmarks
(`m0_05_widening_and_iteration::scaling::a_head_stops_at_most_once_per_landmark`, L = 1 to
128). Mutants: narrowing that takes the meet runs forever (the endless-descent test),
widening that ignores the landmarks fails 2 tests, and a congruence narrowing that takes the
meet fails 1. `PIECE_LIMIT` and `FINITE_SET_LIMIT` remained in arithmetic images, preimages
and the reduction's listing; 3c removed them.

**3c, pieces and listings: done.** No constant bounds the pieces of a set or the members a
reduction lists. Each former use is bounded by its own inputs instead.

- *Forward revision* (`revision::map2`). For operands of k ≥ m sign parts, the one with
  fewer is capped to ⌈(k + m)/k⌉ pieces, so at most k + m pairs are taken, and each sign
  region of the image (below 0, holding 0, above 0) is capped to the most pieces either
  operand has in one region. A chain of operators therefore never grows piece counts, and
  the work is linear in the operands. Candidates, measured on 2000 random pairs of 1 to 6
  pieces (mean members of the image; exact is the join of every pair's image) and on cost
  at k = 64 to 1024 pieces:

  | Rule | members of `+` | members of `*` | cost, 64 → 1024 pieces | score | reason |
  |---|---|---|---|---|---|
  | linear (chosen) | 52.0 | 782.9 | 52 µs → 856 µs, linear | 9 | no constant; chain never grows; within 4% / 8% of exact |
  | hull of each region | 53.4 | 826.9 | 20 µs → 386 µs | 7 | simpler, but loses holes the linear rule keeps |
  | every pair, region cap | 50.6 | 730.8 | 0.6 ms → 155 ms, quadratic | 3 | best precision, quadratic cost |
  | landmark holes | not run | | | 3 | needs landmarks in the arithmetic; loses holes a test observes (`{0, 10} · 2` against `== 14`) |
  | cap of 8 (old) | | | | 1 | a constant |
  | exact | 50.3 | 725.9 | grows as 8^k along a chain | 0 | a chain of k operators has up to 8^k pieces |

- *Preimages.* The cap on every input's box is gone; the forward check that a box meets the
  demand stays. `x mod c` lists the first and last periods its operand's interval meets
  exactly and the periods between as one piece: at most 2p + 1 pieces for p pieces of
  remainders, exact when there are at most two periods. A small domain is then enumerated
  as before.
- *Reduction listings* (`product.rs`). The type is narrowed to an interval's members only
  when they number at most two a piece, so the list is no longer than the interval; a type's
  own integer literals are filtered by the interval at any count, since the type already
  writes them; and `Type::listed` lists a type's values only where a tuple's rows are no
  more than its components' values (`Type::values` without a cap would multiply them).
  The enumeration's kept values are no longer capped, since they were already listed.

Tests: `l01_24_refinement_lattices::scaling` (every result of six operators is in the image,
each region keeps to the operands' largest region, a one-piece operand gives the join of
the pieces' images whenever that fits, a chain of `+` is linear in its length);
`l01_25_preimage_catalog::random::a_remainder_inverts_to_its_first_and_last_periods_and_one_piece_between`
(against every point, with 2p + 1 checked where the result stays necessary). Mutant: without
the region cap the chain test fails.

**Every rule that runs until nothing changes moves one way.** A loop with no bound on its
rounds ends only if each round moves the state in one direction of an order and that order
has no infinite chain in the states the loop can reach. Each such loop in the store:

| Loop | Direction | Why it cannot go the other way | Why its chains are finite |
|---|---|---|---|
| phase 1 (`iterate::Walk::stabilize`) | up | each cell is joined with its projection, then widened | widening moves endpoints only into K, the first value's endpoints and the landmarks |
| phase 2 (`iterate::narrow`) | down | each cell is narrowed by its meet with its projection, so a projection that is not monotone (the caps of forward revision) still cannot raise it | narrowing moves endpoints only to old endpoints or landmarks, and an infinite end takes a bound once |
| reduction (`Scope::reduce`, `Scope::bind`) | down | every write is `Entry::meet` | the class, finite set, literals and enumeration change finitely often; the projection runs again only after one of them changed, and its hulls end at members of every class |
| `callee` (`preimage.rs`) | to older scopes | each binding is looked up in the scope it was made in, built before it | scopes are finite `Rc` chains |

Phase 1, phase 2 and the reduction now assert their direction in test builds
(`debug_assert!` in `iterate.rs` and `product.rs`), so a future write that is not a join or
a meet fails in every test that reaches it.

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
