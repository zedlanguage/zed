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
| S3 | `iterate::stabilize` restarts inner heads' counters on each outer round | 64^h in loop nesting | open |
| S4 | `revision::forward` and `IntervalSet::lift2` multiply piece counts with no cap; `cap` is O(n²) | P^k pieces | fixed: `map2` and `lift2` cap operands and image to the piece limit; `cap` by a heap, O(n log n); `l01_24_refinement_lattices::scaling` (old `cap`: ratio 65; old chain: 64 pieces after one `+`) |
| S5 | Omega test: real and dark shadow both recursed with no step budget | 2^V per leaf | fixed: the dark shadow first, the real shadows alone (`relaxed_empty`) before both recurse, at most 4,096 problems solved; `l01_38_presburger::scaling` (15 variables: 1.03 s → 2 ms; the rising chain passes the budget without `relaxed_empty`). What remains is polynomial in at most 16 variables |
| S6 | `preimage::Cx::constant` walks the subtree at every node | O(n·depth) | fixed: bottom up from the parts' remembered values |
| S7 | `presburger::project` per name: DNF built once per name, hull by 128 bisection steps | O(V·C·128) | fixed (`project_each`, galloping hull) |
| S8 | `product::walk`/`reduce`: whole scope cloned per `let`, constraints printed per round | O(n²) | open |
| S9 | `wto`: components revisited at each nesting level | O(V·E) | open |
| S10 | `affine::Bounds::add`, `IntervalSet::join` re-sorts, `contains` linear | O(k²), small k | `join` (one merge), `contains` (binary search) and `widen`'s endpoint checks fixed with S4; `Bounds::add` open |

## Kernel (`crates/zed-kernel`)

| ID | Where | Class | Status |
|---|---|---|---|
| K1 | `types.rs` `Dnf::not` (De Morgan by full product); also reached from `Display for Type` | 2^C | open |
| K2 | `types/empty.rs` `Search::product`: no pruning of disjoint negatives | n^k | open |
| K3 | `Dnf::normal`: all pairs, restarted after each merge; unions folded pairwise | O(C³) | open |
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
| F1 | `format.rs` `Formatter::block` renders a one-statement block twice | 2^depth | open |
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
| Z1 | `zir/lower.rs`: an effectful `let`-bound lambda is inlined at every call, recursively | c^k nodes | open |
| Z2 | `Lower::add` canonicalizes and encodes the whole subtree of each new node | O(n³) | open |
| Z3 | `zir/canon.rs` restarts from the top after every rewrite | O(k²) | open |
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
| memory test machine (`memory::Machine::check`) | test-only checking machine |
