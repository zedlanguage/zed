# Complexity audit

DESIGN.md Part G, "Six standing rules", requires every algorithm to be of low complexity:
O(n log n) or better, O(n²) only with a recorded reason, nothing cubic or worse outside a
decision procedure that stops at a budget. This file lists every place an audit of
2026-10-30 found that breaks the rule, and the state of each. An item is closed when its
fix is in and a scaling test (size n against 8n, ratio at most 24) passes, or when the
reason it stays is recorded here.

Status: `open`, `fixed` (with the test that checks it), `kept` (with the reason).

## Store (`crates/zedc/src/store`)

| ID | Where | Class | Status |
|---|---|---|---|
| S1 | `preimage`: every use of a `let`-bound name transfers the bound term again (`mentions`, `close`, `fwd`, `back_at`, `lin`, `formula`, `scan`) | 2^k in `let` depth | fixed: one result per (term, scope), `TRANSFER_FUEL`; `l01_25_preimage_catalog::scaling` (k = 14: 296 ms → 0.37 ms) |
| S1b | `preimage`: `if` in guard position and equality of tests walk and copy the guard twice | 2^k in nesting | fixed: as S1, and translations past the M0.5 budget stop early; `l01_25_preimage_catalog::scaling` |
| S2 | `product::Scope::join` builds `Or(R∧A, R∧B)`, copying the common prefix | 2^k in connectives | fixed: `Formula::either` takes the shared conjuncts out, `Formula::bounded` keeps at most 64 constraints and 64 conjunctions; `l01_39_reduced_product::scaling` (about 3 ms per clause, linear) |
| S3 | `iterate::stabilize` restarts inner heads' counters on each outer round | 64^h in loop nesting | fixed: head changes counted over the phase, and a component whose outside inputs did not change since it stabilized is skipped (no value changes; the stack-machine oracle agrees); `m0_05_widening_and_iteration::scaling` (about 10 evaluations per loop at depths 1 to 48; the old code does not finish depth 48 in 600 s; phase-wide counts without the skip: 4,799 evaluations at depth 48, ratio 49) |
| S4 | `revision::forward` and `IntervalSet::lift2` multiply piece counts with no cap; `cap` is O(n²) | P^k pieces | fixed: `map2` and `lift2` cap operands and image to the piece limit; `cap` by a heap, O(n log n); `l01_24_refinement_lattices::scaling` (old `cap`: ratio 65; old chain: 64 pieces after one `+`) |
| S5 | Omega test: real and dark shadow both recursed with no step budget | 2^V per leaf | fixed: the dark shadow first, the real shadows alone (`relaxed_empty`) before both recurse, at most 4,096 problems solved; `l01_38_presburger::scaling` (15 variables: 1.03 s → 2 ms; the rising chain passes the budget without `relaxed_empty`). What remains is polynomial in at most 16 variables |
| S6 | `preimage::Cx::constant` walks the subtree at every node | O(n·depth) | fixed: bottom up from the parts' remembered values |
| S7 | `presburger::project` per name: DNF built once per name, hull by 128 bisection steps | O(V·C·128) | fixed (`project_each`, galloping hull) |
| S8 | `product::walk`/`reduce`: whole scope cloned per `let`, constraints printed per round; premise sets copied whole at each narrowing | O(n²) | fixed: a binding changes the scope in place and restores it (`Scope::bind`/`unbind`), written constraints keep their free names, premise sets share their parts (`cell::Premises`, constant-time union); `l01_39_reduced_product::scaling` (`let` chain linear, 42.6 ms → 3.4 ms at 200; `if` nest about 2.1 per doubling past 64 levels, old code ratio 24.8 and 45 at `let`s). The in-place binding also fixed a soundness error: a shadowing `let` kept the outer name's facts (`a_binding_forgets_what_held_of_the_name_it_shadows`) |
| S11 | `preimage`: the call depth counted every term, so past 64 nested terms the memo was skipped and a `let` chain of 22 took 0.8 s before the visit budget stopped it (the CI failure of `the_transfer_scales`) | 2^k past a threshold | fixed: the depth counts calls only (DESIGN L1.25); `l01_25_preimage_catalog::scaling::a_long_chain_of_lets_is_not_cut` (exact for every length 1 to 64; 0.4 ms at 22, 19.6 ms at 384) |
| S12 | `preimage::fwd_at` cut at the depth without reporting a stop | correctness | fixed: the stop is reported; `stops::a_call_that_never_returns_stops_at_the_call_depth` |
| S9 | `wto`: components revisited at each nesting level | O(d·(V+E)) | fixed: one depth-first traversal and the loop-nesting forest, each edge read once, O((V+E) log V); checked against the declarative order on 2×`RANDOM_INSTANCES` graphs of up to 40 vertices (two mutants caught); `m0_05_widening_and_iteration::scaling::the_order_of_nested_loops_takes_time_linear_in_the_depth` (depth 4,000: 79 ms → 4.8 ms; old ratio 64.3). Phase 1 on the same nests: 0.56 ms at 250 to 8.4 ms at 4,000, linear. `Element::vertices` copies each vertex once (was once per level) |
| S10 | `affine::Bounds::add`, `IntervalSet::join` re-sorts, `contains` linear | O(k²), small k | fixed: `join` (one merge), `contains` (binary search) and `widen`'s endpoint checks with S4; `Bounds::add`, `normal`, `joined` and `leq` compare only bounds with the same terms, a range of the set (`same_terms`), O(k log k); `l01_24_refinement_lattices::scaling::bounds_on_many_symbols_scale` (old ratio 60.8: 8 ms at 200, 484 ms at 1,600) |

## Kernel (`crates/zed-kernel`)

| ID | Where | Class | Status |
|---|---|---|---|
| K1 | `types.rs` `Dnf::not` (De Morgan by full product); also reached from `Display for Type` | 2^C | fixed: the tuple and morphism parts are reduced ordered decision diagrams with shared nodes (`types/bdd.rs`), so a complement is linear in the nodes; a union or intersection whose diagram would pass 4,096 pairs of nodes keeps its operands as an expression, built in constant time, and emptiness reads an upper bound of it within the budget (Kept). `l01_23_subtyping::scaling::the_parts_scale` (union of C differences `m(i) - m(i+1000)`, whose diagram has 2^C nodes: build about 48 ms at every C from 16 to 128 and complement about 1 µs; old DNF 18 s at C = 12; with the budget check removed the test does not finish in 300 s). Bounds are checked by `types::bdd::tests::bounds_enclose_the_part` (4 mutants caught) and the check's soundness under budgets of 1 to 16 by `l01_23_subtyping::oracle::a_small_budget_leaves_the_check_sound` (2 of 3 mutants caught; the third, an And lower bound, only by the unit test) |
| K2 | `types/empty.rs` `Search::product`: no pruning of disjoint negatives | n^k | fixed: the product is split outside each negated type in turn into disjoint pieces (outside it first in component `j`, inside it before `j`), and a negated type disjoint from a piece is passed over; past the budget of 4,096 splits in one query the piece is not shown covered, and the answers of that query that are not `true` are not kept (Kept). A union or intersection of many types is joined in pairs (`Type::union_all`, `Type::meet_all`, used in `rec.rs`, `store/product.rs` and `zir/text.rs`), since one at a time `k` tuple types, each ordered after the last, rebuild the diagram `k` times. `l01_23_subtyping::scaling::a_product_covered_by_its_cells_scales` (an `n × n` product less its `n²` cells: 4.3 s at `n = 5` before, 67 ms at 4,096 cells after; the cells built one at a time took 6 s at 1,024 cells, joined in pairs 45 ms), `negated_types_disjoint_from_the_product_are_passed_over` (13 decoys that would make `2^13` pieces, under a budget of 256 splits), `an_answer_past_the_budget_is_not_kept` and `a_cell_left_out_is_found`. Mutants caught: no passing over (decoy test), cut answers kept (memo test), overlapping pieces (grid tests), a wrong cover test (grid, oracle, `rec`), joining one at a time (grid). A check for a negated type containing the piece was dropped: with disjoint pieces it gives an empty component in every piece, and no test told the two apart |
| K3 | `Dnf::normal`: all pairs, restarted after each merge; unions folded pairwise | O(C³) | fixed with K1: the clause lists are gone; a diagram is canonical with no merging step |
| K4 | `print.rs` `Doc::render` calls `flat` at every node | O(n³) | open |
| K5 | `eval.rs` definedness `fix` in rounds: domain and map copied per attempt | O(D³) | open |
| K6 | values deep-copied on every variable, literal and read (`Family`, `Tuple`, `Path` own their contents) | O(n²) | open |
| K7 | family update and `Prim::Union` rebuild the whole family | O(n²) per loop | open |
| K8 | environment lookup is a linear walk of frames | O(n·depth) | open |
| K9 | provenance copies call and keypath stacks per fact | O(S·depth) | open |
| K10 | `Family::from_leaves` re-flattens built families; `discard` clones subtrees | O(L·d²) | open |
| K11 | `types/empty.rs` `done.retain` per non-empty result | O(T²) | open |
| K12 | `Type` compared by contents; `empty`/`top` rebuilt per call | O(s·depth) | open |
| K13 | `Atoms::zip`, `Lits::zip` rebuild both sides | O(N² log N) in folds | open |
| K14 | `define_on_demand`: `Vec::contains` on the demand stack; entries rerun from the start | O(D²), O(m²) | open |
| K15 | `fix_lattice`: two clones and a deep compare per round | O(R·n) | open |
| K16 | `Prim::Concat` copies both strings | O(n²) per loop | open |
| K17 | `rec.rs` flags recomputed per node; `contractive` DFS per definition; provenance `term`, `origins`, `holds`; `Type::values` product before cap; `Type::contains` payload copy; `Family::get` key copy | O(n·depth) | open |

## Front end (`crates/zedc/src`, not store or zir)

| ID | Where | Class | Status |
|---|---|---|---|
| F1 | `format.rs` `Formatter::block` renders a one-statement block twice | 2^depth | fixed: the statement is rendered once, at the inner indentation, and written on the block's line when its text has no line break (no indentation enters such a text, and the first attempt runs only when the block holds no comment, so the two renderings were the same text); output identical to the old at depths 1 to 10. `l01_13_formatter::scaling::nested_one_statement_blocks_scale` (old: 8 s at depth 20, ratio 454 between depths 2 and 16; new: 6 ms at depth 20) |
| F2 | `elab.rs`: a default argument is elaborated again at every call site | exponential (inferred) | open |
| F3 | `elab::topo`: linear scan for the next ready definition | O(n³) | open |
| F4 | `stage::Mixer::mix`: `free` and `effects` per node, bound names in a `Vec` | O(k³) | open |
| F5 | term canonicalizer: one binder renamed per step, whole term walked per step; facets bubble-sorted | O(B·t·d), O(F³) | open |
| F6 | `check`: `Info` cloned per signature-search run; `within` scans all adoptions | O(F·U) | open |
| F7 | `Tables::uses_in` visits nested scopes' uses once per enclosing scope | O(uses·depth) | open |
| F8 | `source::line_col` decodes from byte 0 per diagnostic, note and test | O(k·N) | open |
| F9 | `testing`: cone and `unit.close` per test over the whole unit | O(T·U) | open |
| F10 | `format.rs` comment scans over all comments per call | O(S·C) | open |
| F11 | formatter copies each level's string into its parent | O(N·depth) | open |
| F12 | checker's `else` pattern scans all binders | O(elses·binders) | open |
| F13 | `stage::free_in` with a `Vec` of bound names | O(t·depth) | open |
| F14 | lexer `"""` decoding: `cuts.iter().any` per character | O(chars·lines) | open |
| F15 | nested string holes rescanned per level | O(N·depth) | open |
| F16 | `resolve` scope chain walk; overload check by pairs | O(uses·depth), O(K²) | open |
| F17 | `Ty::union`/`meet` by deep equality; `derive_into`/`also` note dedup by scan; `ast::args` | O(T²), small | open |

## ZIR, native code and runtime

| ID | Where | Class | Status |
|---|---|---|---|
| Z1 | `zir/lower.rs`: an effectful `let`-bound lambda is inlined at every call, recursively | c^k nodes | fixed: a function that uses a port and whose name occurs more than once is one `lambda` node whose region takes and returns the ports' states, and each call is an `apply` that threads them (DESIGN L1.31, L1.33); a name used once is still inlined; `l01_33_lowering::scaling` (a chain of k functions each calling the one before twice: 3k+1 nodes, 25 ms at k = 800 in release; the old code runs out of memory at k = 16, and inlining every call gives 65,536 nodes there) |
| Z2 | `Lower::add` canonicalizes and encodes the whole subtree of each new node | O(n³) | fixed: a node's key is hashed from its normal-form operation, inputs and outputs and the keys of its regions (`canon::node_key`, `region_key`), so each node is hashed twice, when it is added and when its region closes; `l01_32_canonical_zir::fuzz::the_key_agrees_with_the_address` (catches region keys left out), `l01_33_lowering::scaling::lowering_a_deep_nest_scales` (`if` nest of 800: 28 s → 32 ms in release, old ratio about 8 per doubling) |
| Z3 | `zir/canon.rs` restarts from the top after every rewrite | O(k²) | fixed: every rule acts on one edge or one pattern alone and the binder rule's hint is removed by the hints rule, so `canonicalize` normalizes each edge and each pattern in one pass; `step` stays for the termination tests; `l01_32_canonical_zir::fuzz::the_one_pass_normal_form_is_the_one_the_steps_reach` (300 random graphs). The cost within one edge is F5's facet sort |
| Z4 | `memory.rs` planner: `consumes` and `Uses::of` recomputed down nested branches | O(k²·d²) | open |
| Z5 | planner finds an edge's node by `rposition` | O(n²) per region | open |
| Z6 | `lower.rs` `lookup` scans the whole scope | O(N·S) | open |
| Z7 | captures not deduplicated; merged by `contains`/`position` | O(raw·unique) | open |
| Z8 | `tables.rs` constants and call targets by linear search | O(C²), O(applies·lambdas) | open |
| Z9 | `tables.rs` `visit` clones each node with its regions | O(N·depth) | open |
| Z10 | `zir` validator matches state-edge uses by search | O(S²) | open |
| R1 | `hooks.rs` slow path deep-copies inputs into the kernel and back | O(n) per op | open |
| R2 | building an atom copies its whole payload through the kernel | O(n²) per list | open |
| R3 | `Heap::parts` on a VAL word deep-clones the constant and appends to `vals` | O(n²) time and memory | open |
| R4 | `Rope::chars` counts characters on every call | O(n) per `len` | open |
| R5 | rope flattened again after every append | O(n²) | open |
| R6 | heap never reuses a freed cell; `vals` only grows | O(allocations) memory | open |
| R7 | `matched` deep-copies a binder the arm does not use | O(unused) | open |

## Kept

| Where | Why |
|---|---|
| Fourier–Motzkin pairs, Omega `cost` scan, DNF split cloning | bounded by the Presburger budgets (16 atoms, 64 constraints, 4096 items) |
| signature search runs (check), `apply` combinations | exponential by design, capped at RUNS 20000 and COMBOS 256; only the per-run cost (F6) is a defect |
| `cost::frontier` Pareto filter | O(P²·devices) for a handful of plans |
| emptiness and subtyping of tuple and morphism parts (`types/bdd.rs`, `types/empty.rs`) | deciding emptiness of a Boolean combination of tuple or morphism types is coNP-hard, and any canonical form of some combinations is exponential in their atoms. A union or intersection stops at 4,096 pairs of nodes and keeps its operands; emptiness is decided through bounds within that budget and a walk of at most 65,536 nodes, a tuple clause is split at most 4,096 times in one query, and past these the type is not shown empty, so `is_empty` and `subtype` answer `false`, which every caller reads as "may have a value". Display prints at most the same walk, then `…` |
| memory test machine (`memory::Machine::check`) | test-only checking machine |
