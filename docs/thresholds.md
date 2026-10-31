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
| `VARIABLES` 16, `ATOMS` 64, `INTERMEDIATE` 4096, `KEPT_CONJUNCTIONS` 64 | store/presburger.rs | removed (4): a relation was dropped and its written constraint kept |
| `CALL_DEPTH` 64, `TRANSFER_FUEL` 100000 | store/preimage.rs | removed (5): the transfer through calls stopped |
| `BUILD_FUEL` 10^6 | stage.rs | removed (6) |
| `SPLIT_CAP` 1024 | stage.rs | removed (7): the Trick did not split a parameter |
| `ENUMERATION_BUDGET` 4096, `ENUMERATION_FUEL` 10^4 | zed-kernel budgets.rs | removed (8): a set or box with more members was not enumerated; an evaluation that ran out removed nothing |
| `BMC_SEQ_LEN` 4, `BMC_GENERATIONS` 16, `BMC_BUDGET` 65536, the integer cut | zed-kernel budgets.rs | removed (8): never read by the compiler; the M0.10 harness keeps its own instance sizes in `tests/src/instances.rs` |
| `SATURATION_ITERATIONS` 8, `SATURATION_NODES` 10^4 | zed-kernel budgets.rs | removed (8): never read; rung 3 is not built |
| `DEFAULT_FUEL` 10^8 | zed-kernel eval.rs | removed (8): a compile-time evaluation stopped |

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

### 4. Presburger relations (replaces VARIABLES, ATOMS, INTERMEDIATE, KEPT_CONJUNCTIONS) — done

The plan above was to eliminate a variable only where elimination does not add rows. That
is what was built, with the input's row count as the bound, plus the dark shadow, and a
formula with disjunctions is no longer split into all its conjunctions:

- **Elimination** (replaces `INTERMEDIATE`, `VARIABLES`, the splinters). The Omega test
  eliminates, at each step, the variable that leaves the fewest rows, exact eliminations
  first, among those that leave no more rows than the problem was given. Each step removes
  a variable and the rows never pass the input's count, so the work is polynomial in the
  input. An inexact elimination decides the problem when the real shadow is empty (no
  point) or the dark shadow has a point (that point); between the two shadows, and when no
  variable qualifies, the question is undecided. The splinters, which solved one problem
  per value in a gap, are gone.
- **Disjunctions** (replaces `KEPT_CONJUNCTIONS`, `ATOMS`). The formula is put in negation
  normal form; its top-level constraints are the base. A disjunct whose own top-level
  constraints meet the base nowhere is removed, and a disjunction with one disjunct left
  joins the base, until nothing changes. A point is sought greedily, one disjunct per
  disjunction; where that fails, a disjunct is removed when the base with it is empty by
  the rule above (one level of lookahead), and the search runs again. A projection meets,
  over the disjunctions, the union of each disjunct's projection with the base, and with
  two disjunctions or more left, moves each finite bound inward by halving the step only
  where the value past it is shown empty.
- **Scope relations.** A scope keeps every conjunct of its relation (no 64-constraint
  limit). Its projection is computed per part (the base, and each other conjunct with the
  base), and a part is projected again only when the intervals or congruences of the names
  it mentions changed since it was last projected; a join keeps a part's record when both
  sides hold it. Two top-level constraints with the same terms are merged when the formula
  is built (the tighter bound; two different equalities give no point), and an exact test on
  one name adds nothing to the relation, since the interval holds it.

Termination: every loop removes a disjunct, a variable, or halves a step, and none of these
is undone, so each ends; the reduction rounds of the scope are meets (replacement 3).

An undecided question leaves the written constraint in place, which is sound; the error
reports it as "undecided: outside the fragment the Omega test decides". What is still
undecided: a problem between the shadows (Pugh's example, `l01_38_presburger::controls`),
and a disjunction where greedy search and one level of lookahead both fail.

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Elimination bounded by the input's rows, dark shadow, disjunctions pruned and searched greedily with one-level lookahead, scope parts projected again only when their names change | 40-symbol sum and 200 constraints decided (`controls.rs`); k nested tests 0.72 s at k = 64; k clauses of two disjunctions: solves 953 → 8917 for k = 8 → 64 (linear) | 8 | no constant; polynomial; undecided cases are named and keep the written constraint |
| The same, every part projected in every round | k clauses: 64–74× time for 8× k (COMPLEXITY.md S16) | 4 | correct but quadratic in the clauses |
| Split into all conjunctions, no cap | exponential in the disjunctions | 1 | exact on more problems but not polynomial |
| Keep the budgets | the old behavior | 0 | constants whose crossing changes the answer |

### 5. Preimage through calls (replaces CALL_DEPTH, TRANSFER_FUEL) — done

The plan above named a summary per strongly connected component of the call graph, iterated
to a fixpoint. The kernel terms the transfer reads have no `fix`: recursion reaches it only
as self-application (`w(w)`), so there is no call graph to order, and a call graph cycle is
the same lambda read inside its own call. What was built instead:

- **The recursion rule** (replaces `CALL_DEPTH`). The transfer keeps the stack of lambdas
  whose calls it is reading, by body. A call of a lambda already on the stack would make
  the same call again; it stops, with `StopKind::Recursion`, and the result is necessary,
  not exact. The stack holds distinct lambdas, so it is no higher than the number of
  lambdas in the term: a bound fixed by the program. A result is remembered for its term
  and scope only when no call it reads stopped at a lambda that was on the stack before it
  began, since only then it does not depend on where it was reached.
- **Summaries** (replaces `TRANSFER_FUEL`). A call is read once for each abstraction of its
  arguments. An argument that reads an input and is certainly an integer becomes a fresh
  input over its forward interval with its ends moved out to the landmarks: the term's
  literals and the ends of the input domains and the demand, each with its neighbors
  (`IntervalSet::snap`). A constant integer or boolean argument is bound as a literal, and
  any other argument that reads no input by the term and scope it resolves to. The summary
  is keyed by the lambda's body and scope, these arguments, and the demand, its ends moved
  out to the landmarks too. The call's preimage is the summary's box over the inputs met with
  each argument's preimage of the summary's interval for its parameter; it is exact when the
  summary is, the demand's ends were landmarks already, and each argument's preimage is
  exact. Landmarks are finite, so each lambda has finitely many summaries, each computed
  once: a chain of k functions each calling the one before twice takes time linear in k,
  where reading each call in place took 2^k.

Termination: no loop here runs until nothing changes. Every recursion of the transfer either
reads a strict subterm in a scope built before it, or enters a call, which pushes a lambda
not on the stack; the stack is bounded by the number of lambdas.

What is still read in place, and can still take time exponential in the nesting of calls:
a call with an argument that reads an input and may be a failure, a boolean or another
kind of value (a failure passed to a parameter the body does not read still meets the
demand, which a summary over integers does not see); and the translation into the
linear-relation domain, which reads every call in place (the caps of 4 that bounded it are gone; the relation it builds grows with the calls it reads).
A lambda passed as an argument is keyed by the scope it was made in, so summaries of
higher-order calls are shared only where those scopes are.

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Recursion stack plus summaries over landmark-snapped arguments | nested calls alike and apart, k = 6 and 48: linear (`scaling.rs`); exact for k = 1 … 48 | 9 | no constant; exact where the old transfer was; a structural bound on depth; leaves the cases named above |
| Recursion stack, calls read in place | the mutant with summaries off: see COMPLEXITY.md S15 | 4 | removes both constants but is exponential in the nesting of calls with different arguments |
| Summary per strongly connected component, iterated | not built | 2 | the kernel terms have no `fix`, so there is no call graph to order |
| Keep `CALL_DEPTH` and `TRANSFER_FUEL` | the old behavior | 0 | constants whose crossing changes the answer |

### 6. Build-stage evaluation (replaces BUILD_FUEL) — done

A demanded build-stage term is evaluated, with no fuel, only when its closed form (the
term with the build-stage bindings it reads put around it) shows that it ends
(`stage::ends`): it has no `fix` and no `gen`, and every function it calls or hands to
`reindex`, `discard` or `fold` is a primitive, a lambda whose body ends, or a name a `let`
binds to one of these. Otherwise it is left to run whole, with the reason "its form does
not show that it ends" in the report. The rule is about the term's form, not how far an
evaluation got. At L1 no measure is available: elaboration leaves `fix` as written until
L6, and the evidence records hold no termination fact, so `fix` and `gen` count as not
shown to end; a later layer that proves a measure can admit them.

Termination: a `let` binds its name only in its body, so a name refers to an earlier
binding, never to itself. Under the rule every call goes to a lambda written in the term or
to a primitive, never to a value passed in, so the calls nest no deeper than the term's
lambdas, and each primitive, including the family operations over a finite family, ends.
Self-application such as `w(w)` with `w(f) = f(f)` calls through a parameter and is left to
run; so is any higher-order call through a parameter (`h(f) = f(2)`), which is the price
of the rule. `ends` reads each subterm once, so it is linear in the term.

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Evaluate only terms whose form shows they end, with no fuel | `l01_28_staging::mix` (a nested chain built; `w(w)` left to run with the reason; the rule on calls through parameters, `let` names and shadowing) | 9 | no constant; a term whose ending is not shown runs at run time with the same result |
| Also admit calls through parameters when the checker gives the term a simple (non-recursive) type | not built | 6 | admits higher-order code, but the L1 checker does not reject self-application, so it is not yet sound |
| Keep `BUILD_FUEL` | the old behavior | 0 | a constant whose crossing changes the code |

### 7. The Trick (replaces SPLIT_CAP) — done

Split a parameter on the values the program's static calls pass it, not on its whole
domain. `stage::passed` mixes the unit and reads, in the residual definitions, each call of
the function by its kernel name whose argument there is a literal, and each test case of
the function whose argument there is a literal. `trick` keeps those values that lie in the
parameter's domain, and requires the domain to be finite: a bounded integer interval, or a
type that lists its values no longer than it is written (`Type::listed`, which has no cap).
The split has one arm per distinct value, so at most one per call site and test case, and
the general body stays last. A call whose arguments are all build-stage is computed by the
build and leaves no call, so it adds no arm.

Termination: `split` does not recurse into the arms it builds, and `passed` walks each term
once. What is no longer split: the values of a finite domain that no static call passes;
the old rule made an arm for each, and the general arm computes the same results.

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Values passed by residual calls and tests, within a finite domain | `l01_28_staging::trick` (a domain of 2^40 values split on the one value passed; one arm per value however many calls pass it) | 9 | no constant; code grows linearly in the call sites |
| Every value of a finite domain, no cap | not built | 2 | a domain like `int[0..=2^40]` is finite and would be split into 2^40 arms |
| Keep `SPLIT_CAP` | the old behavior | 0 | a constant whose crossing changes the code |

### 8. Enumeration and evaluation fuel (replaces the enumeration, BMC and saturation budgets, DEFAULT_FUEL) — done

Enumerate only a set whose members are listed, so the work is linear in what is written,
not in the size of the numbers. Two places enumerate:

- The reduced product (`store/product.rs`) enumerates a name whose finite set lists its
  integers. The finite set holds the literals the source writes, and an interval's members
  only where they are no more than its endpoints, so the list is no longer than its source.
  A range such as `int[0..=100]` is left to the interval, congruence and relation domains,
  however few members it has.
- The preimage catalog (`store/preimage.rs`) enumerates a box in which every piece of every
  input's set holds no more members than its two endpoints, and at most one input has more
  than one member, so the points number no more than the endpoints written. A product of
  two listed sets is not enumerated: its points grow as the product of the lists.

Each evaluation runs with no fuel and only when the term's form shows that it ends
(`stage::ends`, replacement 6); otherwise the constraint removes nothing. The evaluator's
default fuel is now unlimited (`Evaluator::new`); `Evaluator::with_fuel` remains for a
caller that wants a measured limit, and none in the compiler does. The BMC and saturation
constants were never read by the compiler, so they are deleted with the module; the M0.10
harness keeps its instance sizes as test fixtures (`zed_tests::instances`), which are not
a rule of Zed.

Termination: each enumeration visits each listed member once (or each point of a box with
one listed axis), and each visit evaluates a term that `ends` admits, which ends by the
argument of replacement 6.

What is lost: a range is no longer decided member by member. `x * 7 mod 10 == 3` over
`int[0..=30]` was `{9, 19, 29}`, exact; it is now `[9..=29]`, necessary. In the arm of
`n >= 0 && n <= 10 && n mod 4 == 1`, `n` was listed as `{1, 5, 9}`; it is now `int[1..=9]`
with the congruence `1 mod 4`, which still represents the set exactly, and the other arm
keeps 5. DESIGN L1.39's `isPrime(p)` example, which gave `{2}` over `int[0..=100]`, now
gives the interval only; a domain that represents primality, or a listed domain, is needed
to recover it; `@exact` (replacement 8a) gives the member-by-member answer on request.
Integer sets merge adjacent members, so a source list of three or more
consecutive values reaches the preimage catalog as a range and is not enumerated; the
reduced product reads the finite set, which does not merge them.

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Listed sets only, each evaluation admitted by `ends`, no fuel | `l01_39_reduced_product::controls` (a listed set enumerated and the same range not; a self-applying constraint removes nothing); `l01_25_preimage_catalog::entries`, `random` (listed boxes enumerated, checked against the interpreter) | 9 | no constant; cost linear in the source |
| Every finite interval, no cap | not built | 3 | ends, but `int32` ranges cost 2^32 evaluations each; the checker's cost would follow the numbers |
| A cap scaled to the source size | not built | 2 | still a threshold: adding a comment changes the precision |
| Keep the budgets | the old behavior | 0 | constants whose crossing changes the result |

### 8a. `@exact`: the precise preimage on request — done

Replacement 8 gives up the member-by-member answer on ranges. A few cases need it:

- a later obligation that excludes an interior point of the hull: after
  `isPrime(p) && p <= 10`, a division by `p - 4` is safe only if 4 is excluded; the hull
  `int[2..=10]` does not exclude it, and the exact set `{2, 3, 5, 7}` does;
- an index into a table with holes, where the hull reaches an index with no entry;
- an arm shown unreachable only by the exact set: `x * x mod 10 == 9 && x mod 10 == 5`;
- a `match` whose coverage depends on which members remain.

Listing the type is one way to ask for the exact set (replacement 8). `@exact`, a declaration
annotation like `@exhaustive`, is the other. In its scopes (`Scope::exact`), each written
constraint whose free names are in scope, whose open names are integers, and whose form
`ends`, narrows each open name to the projection of the points that meet it, over the
bounded box of their intervals within their congruence classes (`preimage::exact_preimage`).
Nothing is enabled by default.

The search is branch and prune. The exact domains run first (catalog, forward check,
linear relation); if their preimage is exact, the classes narrow it and the search stops.
Otherwise a stack of boxes starts from the narrowed box. For each box:

1. skip it if every axis is already within the projection found so far: each axis of the
   projection only grows, so the box can add nothing (residual supports, Bessière and
   Régin, IJCAI 2001);
2. at a box of several points, compute its preimage and meet; drop the box if empty; if the
   preimage is exact, every point meets the demand, so join the box into the projection;
3. at a single point, evaluate the term with no fuel and join the point if it meets the
   demand; a point whose evaluation fails stops the search, and the plain preimage is kept;
4. otherwise split the axis with the widest hull at its midpoint, narrow each half to its
   class, and push both.

When more than one axis keeps several values, the result is exact only if no point of the
box fails the demand: a second search, for the complement demand, stops at the first such
point. An input with no bound is not searched.

Termination: each box is strictly smaller than its parent and a box of one point is not
split, so the boxes form a binary tree whose leaves are disjoint parts of the root, with
fewer than twice as many nodes as points. In a scope, a constraint is projected again only
when the interval or class of one of its open names changed since its last projection
(`Scope::exactly`); those only shrink, so the rounds end.

Cost: at most twice as many boxes as points, each visit costing the size of the term. Where
the plain preimage is exact on sub-boxes, only the boxes that the boundary of the solution
set crosses are split. Measured in a release build:

| Term, domain | n | `@exact` | Every point evaluated |
|---|---|---|---|
| `x * x mod 10 == 9`, `0..=n` | 1,024 → 8,192 | 8.0 → 79 ms (linear in n) | — |
| `x * y mod 7 == 3`, `1..=n` squared | 64 → 256 | 49 → 731 ms (linear in n², the points) | — |
| `x * y <= n`, `1..=n` squared | 64 → 1,024 | 2.7 → 44 ms (linear in n) | 0.29 → 74.8 s (n²) |

`l01_25_preimage_catalog::scaling::the_exact_search_scales_with_the_number_of_points`
checks the three at doubling sizes. `l01_25_preimage_catalog::exact` and `random`
(`run_exact`, against every point of the box run on the interpreter, with and without a
class) check the result; a mutant that always claims exact and one that keeps the failing
points each fail both random tests. `l01_39_reduced_product::exact` checks the scope,
including a narrowing of one name that projects a constraint on another again
(`m * n mod 10 == 1` with `n * n mod 10 == 9` gives `m` in {3, 7, 13, 17}).

| Candidate | Measured | Score | Reasoning |
|---|---|---|---|
| Branch and prune: exact sub-boxes accepted whole, boxes within the projection skipped, classes applied, exactness by a search that stops at the first failing point | the table above | 9 | linear in the points at worst, far less where the domains are exact on parts; no constant |
| Branch and prune without skipping | not built | 6 | visits again boxes whose values are already known to have a supporting point |
| Listed types only (replacement 8) | in place | 5 | the author must write the list; ranges stay imprecise |
| Evaluate every point of the box | the last column above | 4 | always the worst case: 75 s against 44 ms at n = 1,024 |

The surface syntax reaches the store with the annotations (L15, beside `@exhaustive`); the
store mechanism and its tests are in place now.

### 9. Type diagrams (replaces the 4096 and 65536 budgets)

Open. Emptiness of Boolean combinations of tuple types is coNP-hard, so an exact answer
cannot be polynomial in general. Candidates: decide exactly where the combination's tuple
parts share no component (a property of the types); keep operands otherwise. To be measured
on the corpus before choosing.

## Order

1 first (it is the one that grew exponentially), then 2, 3, 5, 4, 7, 6, 8, 9. Each is a
step with its own tests, the old threshold's tests rewritten to the new rule, and a
scaling test.
