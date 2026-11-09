# Review of `// Complexity tradeoff:` comments (CX-tradeoff-review)

Author's rule, 2026-11-09: wherever an algorithm below the complexity of the naive or standard
implementation is used, a `// Complexity tradeoff:` comment at the site names (1) the naive or
standard implementation, (2) its complexity, (3) the implementation used and its complexity,
(4) its tradeoffs (memory, constant factor, preconditions, refused cases and their error,
precision, timed crossovers).

Status before this review: `complete` (all four parts), `partial` (the missing parts named),
`missing` (no comment at a site that needs one), `stale` (the comment describes code that has
changed). Action: `none`, or what was added. Only comments were changed. Where the comment's
statement is inferred rather than measured or proved in the commit, the comment says so.

Commit: the commit that wrote the comment's first line (`git blame`), or the commit of the
change for a site that had no comment. Rows cite COMPLEXITY.md by ID; "cx" stands for
"Complexity tradeoff".

## crates/zed-kernel

### src/types/empty.rs

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| module doc | 44d370e7 | split of the box in every component (DPLL over tuple types), exponential | narrowing and one split per branch, polynomial in the types | parts only a multi-component split proves empty refused `TupleSplit` (K1, K2) | complete | none |
| `STORES` | eefe4060 | search of its own per reader, O(m·n) (K62) | kept values read by index, O(1) per read | memory O(all values built) until the unit ends | partial: no naive version or complexity | added naive (K62) and read cost |
| `group_verdicts` (`Some(false)` arm) | 97774885 | search per member, O(n²) (K56) | one shared search; own search only for a missed member | a missed member may read the whole group again | partial: no naive or complexities | added naive (K56) and used |
| `group_verdicts` (`Refusal::Group`) | 4af5c326 | game solver, quadratic in the component | linear decider, then the search | member refused `Group` | complete | none |
| `optimistic_values` | 0e312b27 | drop the closure and search again, quadratic | one more search, at most twice the cost | gives up whole when one closure has no value | complete | none |
| `Type::is_empty` (`refuse_forks`) | 8abbc466 | subset construction, exponential (NFA universality, PSPACE) | stop at the fork, polynomial | fork counted inhabited; answers not kept | partial: no used complexity | added used complexity |
| `Type::verdict_alone` (`NoWitness`) | 37148785 | complete value builder and search, exponential | the two searches run, polynomial | gives up the answer, never wrong | partial: no complexities | added both |
| `residues_meet` | 4be7a96a | joint split on several primes, NP-hard | one prime at a time, polynomial in classes | joint covers refused `Residues` | complete | none |
| `greedy_length` (residues modulo `q0·r`) | 3d98b6f2 | (cheaper) only the residues the negated classes name, one factor less | every residue, up to cubic in the type size | runs only when the rule refuses | complete | none |
| `residue_length` (`greedy_length`) | 4be7a96a | least length by sieve, up to the lcm, exponential in cycles (31 s at 9 primes) | greedy by conditional expectations, O(residues × classes × primes²) (K34) | may give no length, `Refused(NoWitness)` downstream | partial: no used complexity | added used (K34) |
| `Searching` (explicit stack) | 2e6bb252 | recursion on the thread stack | boxed futures on the heap, O(depth) heap | 1.2 to 2.5 times the time | complete | none |
| `Searching::decided` (`Refusal::Residues`) | 3d98b6f2 | backtracking split over primes, exponential | one-prime split, polynomial | refused `Residues` | complete | none |
| `Searching::settles` (`cuts`) | 2a8344c9 | content key, order n² (47.6 times 64→512); scan per call, 34.0 times | node-address key, one build per node pair | equal operands built apart miss | partial: no used complexity, no unkeyed naive | added both (K51) |
| `Searching::refuse_fork` (no `current`) | 2e6bb252 | search per open member, O(n²) (K61) | one search, all open members as roots | one such fork refuses every open root | partial: no naive or complexities | added naive and used (K61) |
| `Searching::narrow_tuples` (fork) | 72ec8650 | subset construction, exponential, PSPACE | refusal, polynomial | refused `Fork`, with hardness argument | complete | none |
| `Searching::tuples_on` (`open_forks`) | e1358008 | subset construction | no value sought in the part | part counted inhabited | partial: no complexities | added both |
| `Searching::tuples_on` (fork refusal) | 188fc1c3 | subset construction, exponential | refusal | refused `Fork`; split before it order n² | partial: no used complexity | added used |
| `Searching::tuples_on` (one pass placement) | 99e24c2f | pass in every piece, k walks (237 times bytes at 8d) | one pass per part, linear | piece the pass would decide left to search | partial: no used complexity | added used (K71) |
| `Searching::tuples_on` (`SharedCells`) | 99e24c2f | split into open tuple types, order c² (OV-hard) | one pass, then refusal | refused `SharedCells(j)` | partial: no used complexity | added used (K71) |
| `Searching::tuples_on` (`may_cover` split) | bcfd56bd | split of box in every component, coNP-hard | k pieces of n nodes | polynomial only | complete | none |
| `Searching::tuples_on` (`TupleSplit`) | 3d98b6f2 | DPLL/SAT, exponential | one split per branch, polynomial | refused `TupleSplit` | complete | none |
| `Searching::two_sat` | c22b2ec0 | SAT, exponential | 2-SAT linear, rest to the search | non-2-CNF left to the search | complete | none |
| `Searching::list_member` (two rest types) | 967100ac | set of types per link, lcm of cycles, exponential | gives up, O(1) | list not shown, `Refused(NoWitness)` | complete | none |
| `Searching::find_rep` (`past_fork`) | ac623170 | deep search past forks, order n² (63,634 cuts at 64) | one candidate per tuple type per path (1,578 cuts) | part counted as having no value | partial: no used measure | added used (K35 numbers) |
| `Searching::morphisms` (`MorphismSplit`) | 99e24c2f | split in every combination, exponential | one split per branch, polynomial | refused `MorphismSplit` | complete | none |
| `overlaps` (doc) | 5ea42bcd | pairwise meets, square of the types, a search each | key trie, size × log keys | coarse keys join disjoint types, order k² there | complete | none |
| `judge` (meets and differences) | 2e697ed0 | product of tree automata, exponential (EXPTIME) | decider, then the search per member | forks on the product refused `Fork` | complete | none |

### src/num.rs

Memory asks (`room(...)` before a wide computation) are a refusal tradeoff with no algorithm
choice: the time of the work is unchanged. They are judged on the complete solution named
(each allocation asked for its own memory), the bound used (a measured multiple of the width,
not a proved one), and the inputs refused (those whose real need lies between the two). All
of them in this file state those three and cite K30.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `Rat::decimal_parts` (memory ask) | 1d71099a | per-allocation asks | 64 bits a digit, measured 42.7 | refusal between the two | complete (memory ask) | none |
| `Rat::to_integer` (memory ask) | 1d71099a | per-allocation asks | 8 × width, measured 3.85 / 6.43 | refusal between the two | complete (memory ask) | none |
| `Rat::text_ask` (memory ask) | 1d71099a | digits by halves into memory reserved once | 8 × (width + text), measured 6.11 | refusal between the two | complete (memory ask) | none |
| `Rat::built_parts` (memory ask) | 8fc378cc | per-allocation asks | 8 × width (from `to_integer`) | refusal between the two; not measured alone | complete (memory ask) | none |
| `Rat::literal_text` | 79d9f6d6 | written power and quotient in type syntax, size of the source | `m` printed in full, O(digits of `m`) | nothing refused | complete | none |
| `Rat::sum` (memory ask, plain) | fc84ff8b | per-allocation asks, own reduction | 16 × width, measured 9.24 | refusal between the two | complete (memory ask) | none |
| `Rat::sum` (built coefficient) | 2bf39d29 | sum kept unbuilt | built, O(n log n) in the bits | cost grows with the value (A28) | complete | none |
| `Rat::sum` (memory ask, powers) | 1d71099a | per-allocation asks | 8 × width, measured 4.97 | refusal between the two | complete (memory ask) | none |
| `Rat::mul` (memory ask) | 26b4df16 | scratch allocated once | 8 × width, measured 5.00 | refusal between the two | complete (memory ask) | none |
| `Rat::scaled` (memory ask) | 26b4df16 | per-allocation asks | 16 × width, measured 10.9 | refusal between the two | complete (memory ask) | none |
| `Rat::pow` (memory ask) | 1d71099a | per-allocation asks | 8 × width, measured 6.43 | refusal between the two | complete (memory ask) | none |
| `Rat::pow` (wide base built) | 2bf39d29 | opaque base kept, coprime base | built, O(result size) | none refused | complete | none |
| `Rat::rem_built` (divisor built) | e3b51e94 | residue kept unbuilt | divisor built, O(size of `m`) | `TooLarge` when an ask fails | complete | none |
| `Rat::rem_built` (memory ask) | 56c364a9 | own modular power | 32 × width, measured 25.2 | refusal between the two | complete (memory ask) | none |
| `Rat::div_euclid` (memory ask) | 074a199a | division with known peak | by divisor kind, measured 14.5 / 25.5 | refusal between the two | complete (memory ask) | none |
| `Rat::div_euclid` (built remainder) | e3b51e94 | floor kept unbuilt | built, O(dividend size) | `TooLarge` when an ask fails | complete | none |
| `Rat::aligned` (memory ask) | 56c364a9 | in-place division of powers | 16 × width, measured 10.7 | refusal between the two | complete (memory ask) | none |
| `LEAF_DIGITS` | 4f52ced8 | num-bigint `parse`, O(n²) | halves, O(n log² n); crossover at 1024 | timed crossover, table given | complete | none |
| `read_decimal` (memory ask) | 841c584a | per-allocation asks | 48 bits a digit, measured 34.7 | refusal between the two | complete (memory ask) | none |
| `read_digits_by` | e78114fe | num-bigint, O(n²) | halves, O(n log² n) (A47, C31) | log factor above a product | complete | none |
| `valuation_upto` | de518f04 | build every `P_i` first, O(M(n)) per `v`, quadratic to 2000 words | tests on the way up, O(n log² n) | log factor for wide `v` | complete | none |
| `rem` (memory ask) | 57d39af3 | per-allocation asks | points × `POINT_WORDS` or `REM_STEP` × width | refusal between the two | complete (memory ask) | none |

### src/types.rs

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `Held` | 0bfb0cf1 | one growing `Vec`, O(1) amortized put, moves items | blocks of `2^k`, O(log n) put | borrows into parts stay valid | partial: standard form and its cost not named | added the `Vec` and last-block forms |
| `atom_names` | 07435961 | two held iterators, 208-byte steps, bytes >24x at 8n | resume by search, O(log n) a step | log factor per step | complete | none |
| `tuple_lens` | 07435961 | as `atom_names` | as `atom_names` | as `atom_names` | complete (by reference) | none |
| `Lits::cmp` | b47553d5 | ordered walk, order n | `==` first, order log n for equal sets made apart | unequal sets of equal sum pay both walks | complete | none |
| `Type::tuple` (empty component) | 3dae154f | memoized `is_empty` per component, up to the component's size | `lists_nothing`, O(1) | components empty only by search kept (C33) | complete | none |
| `Type::finite` | a61e2719 | full case split, exponential | one read of the parts | "not known finite" (C22) | complete | none |
| `Lits::union` | e0896f49 | walk of the smaller, O(s log l), quadratic on chains | twice the cheaper walk, O(min(s, d + log l) log l) | constant 2 | complete | none |
| `Atoms::zip` | d5798f8b | walk of the smaller, quadratic on chains | twice the cheaper walk | constant 2 | complete | none |
| `Numbers::tried` | 57b59496 | test against earlier boxes, order n per tuple | hash set, tuple length per lookup | memory: every tuple tried | complete | none |
| `merge_boxes` | e0896f49 | box by box, n² | merge passes, at most b ln b checks | other unions box by box | complete | none |
| `part_boxes` | bf9b9619 | meet of every pair, exponential along a chain | meet with the join, n log n chains | some finite meets not known finite (K69) | complete | none |
| `Graph::parities` | e0896f49 | chain left as built, order n per tuple, O(n²) | one pass, O(nodes) | unknown complements stay unions | partial: no naive version | added naive (K69 item 10) |
| `Graph::merged` | 57b59496 | chain not merged, order n per candidate (25 times at 8n) | smaller into larger, O(n log n) | none stated | partial: no naive version | added naive (K69) |
| `Graph::apply` | 57b59496 | whole part per tuple | changed nodes only | high-fan-out nodes pay per reader | complete | none |
| `Class::under` | e0896f49 | no memo, order n per value | once per recurring set, hash lookup | memory at most the repeated work | partial: no naive or used cost | added both (K69) |
| `Class::known` | e0896f49 | applied per tuple | once per set, hash lookup | memory at most the work | partial: no naive or used cost | added both (K69) |
| `RowIndex::new` (absorbed columns) | 7a8bc7d5 | filing by every column | absorb where classes cost no more | same verdicts either way | complete | none |
| `RowIndex::holds` | 7a8bc7d5 | one class per tuple (46 times 64→512) | one class per kinds or spine | up to k times one class's cost | complete | none |

### src/num/fast.rs and src/num/bound.rs

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `fast::mul` (Toom crossover) | 1d222ff3 | transforms, O(n log n) | Toom-3 about n^1.465 below `MUL_LEAF`/`TOOM_COST` | timed crossover, identical results | complete | none |
| `fast::mul` (sparse rows) | 841c584a | transforms, O(n log n) | rows over nonzero words, `nonzero(a)·words(b)` | dense factor O(n) more for the count | complete | none |
| `fast::pieces_mul` | 841c584a | whole product, one transform | pieces when `transform_plan` costs less | a cut square may cost a third more | complete | none |
| `fast::div_rem` (`DIV_LEAF`) | 57d39af3 | Newton reciprocal, O(M(n)) | num-bigint below the leaf, O(n) per leaf width | timed crossover, identical results | complete | none |
| `fast::div_rem` (sparse) | 841c584a | reciprocal, O(M(n)) | long division over nonzero words | chosen by computed costs | complete | none |
| `fast::approx_reciprocal` | 57d39af3 | Newton steps to the bottom | one division, O(RECIP_LEAF²) once | bounds unchanged | complete | none |
| `fast::gcd` | 841c584a | num-bigint Stein, O(n²) | half gcd, O(n log² n) (A47, C31) | log factor above a product | complete | none |
| `fast::reciprocal_points` | 57d39af3 | as `div_rem` | as `div_rem` | as `div_rem` | complete (by reference) | none |
| `fast::to_decimal` (`PRINT_WHOLE`) | 29ab1ba6 | split, about 2.3 per doubling plus fixed costs | num-bigint below 60,000 words | timed crossover, identical digits | complete | none |
| `fast::to_decimal` (`PRINT_HANDOFF`) | 29ab1ba6 | split | num-bigint at small powers | timed crossover, identical digits | complete | none |
| `fast::to_decimal` (halves) | 841c584a | num-bigint, O(n²) | halves, O(n log² n) (A47, C31) | log factor above a product | complete | none |
| `bound::cmp` | 2bf39d29 | build and compare, O(size) | doubling bounds, then built at size | Baker's bound would stop sooner | complete | none |
| `bound::round` (precision) | 2bf39d29 | build the parts | doubling, built at size | near-boundary quotients cost their size | complete | none |
| `bound::round` (memory ask) | 26b4df16 | scratch allocated once | 32k bits, measured 1.39 × 16k | refusal between the two | complete (memory ask) | none |

### Other zed-kernel files

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `types/bdd.rs` `Part::xor_at_once` | f13fb7c0 | `Connect` frames alone, complement made and freed per union | O(1) test first; both n log n (K90 (5)) | non-xor unions pay the test once | partial: no naive cost or measure | added naive and K90 numbers |
| `types/bdd.rs` `Connect` | a34629bf | plain recursion on the thread stack | heap frames, 1.3 to 1.9 times | constant factor only | complete | none |
| `types/bdd.rs` `Connect::zipped` (xor one form) | f2cd0724 | expression kept as made, O(1), two nodes for one set (K63) | one form, O(k log n); parity O(n log n) | later full comparisons inferred | partial: no naive version | added naive (K63), consequence marked inferred |
| `types/bdd.rs` `xor::inner` | f13fb7c0 | six expressions and a pair rebuilt | table lookup per two-child node | entry kept while the xor lives | complete | none |
| `types/bdd.rs` `Bdd` list cut | 07435961 | carry atoms over, the `m - p` dropped | split O(log m), remake O(min(p, m-p) log m) | count-keyed sequence would be O(log m) | complete | none |
| `types/bdd/set.rs` `same` | ab049007 | process-wide table, a lock per node made | O(k) walk across threads | per-comparison cost across threads | complete | none |
| `words.rs` `lower` | f4d937bf | block-by-block reading with Unicode tables | one more O(n) copy, asked first | refusal when memory is short | complete | none |
| `words.rs` `read_rat` (memory ask) | 841c584a | per-allocation asks | 48 bits a digit, measured 28.3 | refusal between the two | complete (memory ask) | none |
| `value.rs` `Value::int_text` (memory ask) | 1d71099a | digits packed with memory reserved once | 2 × (8 + per-digit) bits, measured half | refusal between the two | complete (memory ask) | none |
| `value.rs` `ReadSet::clear` | 8fd7e6a9 | free and regrow slots each comparison | keep slots unless 8 times the pairs | memory at most 8 times last pairs | complete | none |
| `types/print.rs` `Printer::canon` | 9ce72580 | the walk alone, O(t), order-dependent | rank by height, O(t log t) | log factor | complete | none |
| `types/print.rs` `Printer::list` | 9ce72580 | print nodes, linear in their union | each diagram its own list | text linear in the lists printed | complete | none |
| `text.rs` `LEAF` | bc0d2817 | share parts only, a node per character | copy up to `LEAF` bytes per join | up to `LEAF` bytes per prefix held | complete | none |
| `text.rs` `push_back`/`push_front` | 2de401ae | lazy middle (Hinze-Paterson) or Kaplan-Tarjan, O(1) worst case | strict pushes, O(1) amortized | reuse of full versions O(log n) | complete | none |
| `types/rec/unfold.rs` `Unit` | 07435961 | keep every group, or a cycle collector | free at unit end; remake O(body) | regrouping by later units | complete | none |
| `types/empty/refused.rs` `Why::recheck` | 28c78703 | whole walk per re-check, O(m n) | walk with cuts, O(nodes reached) | whole walk where a kept-refused member is met | partial: no naive version | added naive and used (K85) |
| `types/empty/names.rs` `absorb` | 92fdf6f2 | transitive reduction, O(n·m) or a matrix product | dominators, O(m log m) | some arms kept; group may be refused (K88) | complete | none |
| `term/walk.rs` `queued` | 08f7809e | walk by paths, exponential in depth | pairs hashed once, O(distinct pairs) | constant per comparison | complete | none |
| `provenance.rs` `Provenance::origins` | 40733fae | newest first, O(n²) on chains | oldest first, O(n log n) | reads values holding other failures, O(m log m) | complete | none |

## crates/zedc-preimage

Most sites here use the older form (given up, why, trigger, test, row, complete solution). A
site is complete when that text states the naive or standard version with its cost and the
used version with its cost; where one of the two costs was missing, a "Naive version: ...;
used: ..." sentence was added. `preimage_ref.rs` repeats eight comments of `preimage.rs`; each
fix was made in both.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `address.rs:418` (canonical address, smaller set into larger) | 241648eb | hashing modulo alpha (Maziarz et al.), O(n log² n) | small into large, n log n on a tree; n·F or k·m with shared parts | needs part-by-part comparison (C30) | complete | none |
| `holes.rs:467` (three holed names on two cycles) | 9322ec49 | snapping to a fixed point, a lap per value | refusal, from the count of holed names | exact ends refused (S25) | partial: no used cost | added naive/used |
| `holes.rs` `hull` | 9322ec49 | Dijkstra O(m log n) needs a potential | label correcting O(n m) without one | S25 | complete | none |
| `preimage.rs` `StopKind::Outside` | 5f387d63 | read through the loop, need not end | stop, O(1), whole box | necessary only (C15) | partial: no costs | added naive/used |
| `preimage.rs:358` (split after transfer) | 1f2e9e00 | split first, O(G n) | transfer first, O(n) | one class's run spent (S22e-quad) | complete | none |
| `preimage.rs:384` (split over found box) | ef791023 | no second split | one more split O(G n log n), may be spent for nothing | S22-order-chain | complete | none |
| `preimage.rs` `split_residues` (by-class terms) | 1f2e9e00 | one transfer per class, O(G n log n), up to O(n² log n) | shared summary, O(k log k) | listed terms (S22e) | complete | none |
| `preimage.rs` `split_residues` (many periods) | c5ae623c | a piece per period, width / m | first, last and one middle piece; projection linear in pieces | wider boxes (S22e-wide) | complete | none |
| `preimage.rs:736` (classes' sets) | 0130be38 | each class builds its set, O(H) each | shared set where equal | S22-split-holes | complete | none |
| `preimage.rs:2421` (`n * q` atom) | 0ef80f85 | arithmetic with products, undecidable | one atom, Presburger | facts needing the product (S39) | partial: no used version | added naive/used |
| `preimage.rs` `unite` | 1e4ead23 | (refusal scan) O(j m), up to n^1.5 | union by size O(n log n), refusals remembered | LOAD-affine-join | complete | none |
| `preimage.rs` `Tx::marks` | 6254ad0c | persistent multiset, O(log k) per input | O(k log k) per run | PA-letpre-linear | complete | none |
| `preimage.rs:4436` (recursion stop) | 44d370e7 | read at each depth, need not end | stop, O(1) | forward intervals kept (S12, S15) | partial: no costs | added naive/used |
| `preimage.rs` `Walk::union` | 44d370e7 | exact union, up to 2^k boxes | box hull, smaller box's names | not exact (C14) | complete | none |
| `preimage.rs:5588` (landmarks key) | 624ae2ac | exact key, up to 2^k summaries | landmark pairs | wider preimage (S13, S15) | complete | none |
| `preimage.rs` `Walk::project` (HC4) | 624ae2ac | exact preimage, points of the box | one narrowing per operand (cost inferred) | necessary only (C16) | partial: no used cost | added naive/used |
| `preimage.rs` `Walk::by_class` | 624ae2ac | each class's run, O(G n log n) | one summary, O(log G) per `if` | listed terms read per class | complete | none |
| `preimage.rs:6968` (arms differ) | ef791023 | slice once | O(L log n), L ≤ G | S22e-quad | complete | none |
| `preimage.rs` `Walk::back_by_class` | ca5957c8 | O(k²) demands | O(k log k) | inexact past two periods (S22-transfer-rem) | complete | none |
| `preimage.rs:7362` (case cuts) | d891b8de | cut at every start, L·S = O(k²) | neighbors, C + 2S = O(k) | measured wider boxes (S22-case-cuts) | complete | none |
| `preimage.rs` `Walk::defined_called` | 6a79d26f | callee's cone per call | condition at the arguments | RUNG2-definedness | complete | none |
| `preimage.rs` `Walk::formula_called` | ace60e16 | body read k times, O(k · cone) | projection, rows left | measured 0.051 s / 4.41 s (LOAD-call-relation) | complete | none |
| `preimage.rs` `Walk::lin_called` | 2fc841e1 | body per call, O(cone) | value projection | measured 0.239 s / 14.5 s | complete | none |
| `preimage.rs` `Walk::defined_chain` | 2907021c | nested `if`s, Θ(k²), solver k³ | O(k) nodes; O(m log n) per new divisor | PRES-mod-conjuncts | complete | none |
| `preimage.rs` `LetPa::sum` | 69c4cdd3 | (invert without forming) | O(d log d) per chain; Θ(d²) pieces when formed | measured (PA-let-block) | complete | none |
| `preimage.rs` `ByClass::clamp` | ef791023 | clamp base once | O(L) clamps | S22e-quad | complete | none |
| `preimage.rs` `in_range` | d4894aaa | per-arm transfer, about k^2.8 | i128 ends, O(1) per node | ends past i128 (S33) | complete | none |
| `preimage.rs` `invert_treap` | 76bb9d4c | hull per subtree, O(log p) | O((m + 1) log p), O(p) after a sloped sum | exact | complete | none |
| `preimage.rs` `mod_pre` | 44d370e7 | a piece per period, exponential in bits | 2p + 1 pieces | not exact (C17) | complete | none |
| `preimage.rs` `enumerate` | 623a07d2 | product of axes, exponential | listed boxes only | wider answer (C18) | complete | none |
| `preimage.rs` `witness` | 44d370e7 | unbounded search, undecidable | `None` on unbounded | S17 | complete | none |
| `preimage_ref.rs` `Outside` | 19b249aa | as `preimage.rs` | as `preimage.rs` | C15 | partial | added naive/used |
| `preimage_ref.rs` `POWER_FACTORS` | 19b249aa | k nested products, O(k) HC4 steps | power up to 64 factors | size switch, ledger CAP-power (C19) | partial: no costs | added naive/used |
| `preimage_ref.rs:1099` (recursion stop) | 19b249aa | as `preimage.rs` | as `preimage.rs` | S12, S15 | partial | added naive/used |
| `preimage_ref.rs:1134` (landmarks) | 19b249aa | as `preimage.rs` | | | complete | none |
| `preimage_ref.rs` `union` | 19b249aa | as `preimage.rs` | | | complete | none |
| `preimage_ref.rs` `project` (HC4) | 19b249aa | as `preimage.rs` | | | partial | added naive/used |
| `preimage_ref.rs` `mod_pre` | 19b249aa | as `preimage.rs` | | | complete | none |
| `preimage_ref.rs` `enumerate` | 623a07d2 | as `preimage.rs` | | | complete | none |
| `preimage_ref.rs` `witness` | 19b249aa | as `preimage.rs` | | | complete | none |
| `product.rs:328` (ints not listed) | 623a07d2 | list the interval, exponential in bits | not listed | C5 | complete | none |
| `product.rs:370` (finite type not listed) | a280f330 | 2^k or 2^(2^d) values | type kept | one value lost (S34) | complete | none |
| `product.rs` `Scope::refusals` | 44d370e7 | complete Presburger, exponential | refusal with a warning | S18, S28 | complete | none |
| `product.rs:3011` (stars projected again) | e22a4f8f | leaves ordered by bound, only those cut | k projections | C26 | complete | none |
| `product.rs:3263` (tree block by block) | 9322ec49 | no near-linear exact method known | block by block; O(k² log k) measured, open item O7 | S25 | complete | none |
| `product.rs` `Scope::reseed` | 68416f08 | partial potential via Bellman-Ford O(n m) | point of the whole tree | S25 | complete | none |
| `product.rs:4201` (threshold solve) | 37a8466a | kept state, O(N log N log W) | O(N · N log N log W) | case split 88% (S4-ti) | complete | none |
| `product.rs` `Scope::project_by_pendants` | 35b95486 | each disjunct combination, exponential | pendants eliminated; else whole, O(k³) | S43 | complete | none |
| `product.rs` `Scope::enumerate` | 44d370e7 | product of open names, exponential | one open name only | C6 | complete | none |
| `product.rs:4890` (group searched) | 63a6f9c4 | repair from part, many visits | whole group search per failure | S40 | complete | none |
| `threshold.rs:403` (hub search) | 37a8466a | one propagation, O(N log N) | O(log W) propagations | S4-ti | complete | none |

## crates/zedc-presburger

Line numbers are those before this review's edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `presburger.rs` `Formula::and_keeping` | eca1d8dc | merge, O(d k) copies | kept part, not merged | duplicate constraints kept (S31b) | complete | none |
| `presburger.rs` `Formula::or_keeping` | eca1d8dc | merge, O(d k) | kept part | later tests split (S31b) | complete | none |
| `presburger.rs` `complementary` | 4993072f | content hash per `or`, size × depth | constraint disjuncts only | compound `g \|\| !g` not found (S20) | complete | none |
| `presburger.rs` `satisfiable_inner` | f611a272 | one ask without implied rows | rows first, retry on refusal | at most two asks | partial: no naive version | added naive/used |
| `presburger.rs` `drop_jointly_empty` | c13b42a6 | (tree of halves, path remade) | O((m + k) log k) per pass, O(k) passes at worst | hub measured 9 to 31 passes (DISJ-incremental) | complete | none |
| `presburger.rs:1298` (rows of one hash) | acd91255 | all pairs, O(n²) | hash groups, O(n) expected | pairwise within a collision | partial: no naive or used cost | added naive/used |
| `presburger.rs` `or_old` | 01d71b2e | new path only | old path on refusal, O(n²) solves | DECIDE-disj-chain | complete | none |
| `presburger.rs` `decide_inner` | 01d71b2e | one ask without implied rows | rows first, retry on refusal | at most two asks | partial: no naive version | added naive/used |
| `presburger.rs` `Renamed` | eaa8e0c2 | canonical labeling, exponential | color refinement, refusal on ties | NAME-ties-or | complete | none |
| `presburger.rs` `settle_tied` | eaa8e0c2 | probe, cubic (22 ms to 10.8 s) | one solve after settling | refusal `Unordered` | complete | none |
| `presburger.rs` `pick` (no backtracking) | 44d370e7 | DPLL(T), exponential | first disjunct, never undone | `Refusal::Disjuncts` (S16, S18) | complete | none |
| `presburger.rs` `pick` (fast reading) | 0125606a | whole-group reading, O(n²) | by halves, fallback O(n²) | no answer lost | complete | none |
| `presburger.rs` `shadow` | 0125606a | Fourier-Motzkin, doubly exponential | exact eliminations that add no terms, O(m log m) | dense core kept | complete | none |
| `presburger.rs:3183` (`probe` propagations) | cf275a26 | conflict explanation | r propagations, O(r log m) settles | PRES-guarded-chain | complete | none |
| `presburger.rs:3343` (chain bounds) | cf275a26 | one pass along definitions | O(k²) passes, cubic | item PRES-settle-chain-rounds | complete | none |
| `presburger.rs` `bounds_refute` | 78e5f708 | propagate to fixed point, rounds grow with magnitudes | two readings, O(n log n) | proofs needing more carries | complete | none |
| `presburger.rs` `Parts::of` | eca1d8dc | shared chunk read once | O(d k) at separate branches; measured 50.7× | S31b | complete | none |
| `presburger.rs` `absorb` | 71a3442d | solve per disjunct, quadratic | unit-coefficient removal, linear × log | DECIDE-disj-chain | complete | none |
| `presburger.rs` `settle` | 01d71b2e | n solves of the group | by halves O(n log n); dense core quadratic | no answer lost | complete | none |
| `presburger.rs` `splinters` (depth) | b79d6715 | Pugh's enumeration, exponential in coefficients and depth | live-variable bound | `Refusal::Shadows` (S18) | complete | none |
| `presburger.rs` `splinters` (batches) | b79d6715 | every splinter, quadratic | stop at first refused batch | NAME-ties | complete | none |
| `presburger.rs` `System::dominated` | 97add2a2 | half-plane intersection, O(log p) | O(p) per row, p ≤ 10 measured | Q1-LOCAL | complete | none |
| `presburger.rs` `System::shrink` | fb9b82a6 | per-pair flags kept | O((r + z) t log n) | `Refusal::Growth` (Q1-LOCAL) | complete | none |
| `presburger.rs:7098` (box stage refusal) | 128668f1 | full Omega, doubly exponential | five box points, one pass | `Refusal::Growth` (S18, Q1-ROWBOX) | complete | none |
| `presburger.rs:7150` (tie refusal) | eaa8e0c2 | every order, exponential | refuse on tie | `Refusal::Tie` (NAME-ties) | complete | none |
| `presburger.rs` `Omega::cycles` | bbed2a02 | search after every step, O(m·n) | once, O(m log m + n) | zero-sum cycles missed (OMEGA-cycle-growth) | complete | none |
| `presburger.rs` `resolve` | 97add2a2 | resolve all first, O(n²) | O(w log w) per row, O(m n) on late cancellation | Q1-LOCAL | complete | none |
| `presburger.rs` `project` | 44d370e7 | every disjunct combination, exponential | meet of unions | wider set (S7, S16) | complete | none |
| `presburger.rs` `project_each` | acd91255 | both writings each time, 2× | second writing on refusal | PROJECT-each-canon | complete | none |
| `presburger.rs` `project_each_boxed` | 564bef57 | integer program | box stage bounds, one pass | wider (PROJECT-growth-box) | complete | none |
| `presburger.rs:8430` (hull bisection) | 01d71b2e | before: 41.6 s at 128 stages | O(n log n) on chains; O(n²) solves by cases | DISJ-incremental | complete | none |
| `presburger.rs` `summarize` | 873f1a86 | level's own formula, O(d²) measured 51.1× | this formula | wider hull (S31) | complete | none |
| `presburger.rs` `part_bounds` | 355e67f4 | integer program per hull, NP-hard | O(m log n) bounds | wider bounds (C2) | complete | none |
| `presburger.rs:9892` (tiers) | 355e67f4 | see `Tier` | O(sides × cluster), O(sides × part) | C2 | complete | none |
| `presburger.rs` `Tier` | 355e67f4 | integer program per side | Local O(sides × cluster), Whole O(sides × part) | measured 52 ms to 3.86 s (C2-local-tier) | complete | none |
| `presburger.rs` `products` | 44d370e7 | CAD, doubly exponential; integers undecidable | products of premise pairs | `NotProved` (C2) | complete | none |
| `deep.rs` `Flat` | eca1d8dc | (no shorter printed form) | written out, exponential in a chain | compare and hash linear | complete | none |
| `deep.rs` `Formula::cmp` | 9e80c1c5 | read through, N | visited set, linear; O(e log N) with `Canon` | S31b | complete | none |
| `deep/canon.rs` module | 9e80c1c5 | hash, linear but not deciding | parse O(k log N), O(n²) when N exponential | author accepted 2026-11-04 | complete | none |
| `extend.rs` `Extending::defined` | 5a4987d5 | decide whole | extend kept part's answers | measured LOAD-holes-mod, LOAD-mod-chain | complete | none |
| `extend.rs:311` (each part tried) | 3aa6326c | largest part only, decided whole twice | O(kept parts × whole) before whole | LOAD-chain-affine | complete | none |
| `extend.rs:341` (faces) | 36279a9f | implication between clauses, co-NP-hard | merge equal, holes, bounds; O(n²) otherwise | LOAD-disj-residue | complete | none |
| `extend.rs` `project` | 7d23ca0c | product of disjunctions, exponential | O(r d) per group | shared atom kept | complete | none |
| `extend.rs` `decided` | a7032e3f | one shape asked | second shape on refusal | measured 42/34 refusals | complete | none |
| `extend.rs` `Summaries::summary` | 4e48ee57 | every definition per test, O(n²) | summary per definition, O(n) | LOAD-chain-sep | complete | none |

## crates/zedc-int

17 sites, all in `int.rs`. Most are the fallbacks where a kept value (a sum of powers) has no kept form for an operation, so the value is written out "at the cost of its digits". These state both versions: the kept form that is missing (named as the complete solution) and the written-out value used, with its cost; they are counted complete. Line numbers are those before the edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `int.rs:1067` (`strip` remainder tests) | 3d29a0df | squares only, O(M(n)) whatever `k` | test by remainder, about `n log d`, only where `d <= sqrt(n)` | measured 13.9 vs 11.1 instruction growth | complete | none |
| `int.rs:1198` `Core::same` | d4894aaa | `value_cmp` at the bits of the value | form comparison over a coprime base | roots of different radicands only by `value_cmp` | partial | added naive/used sentence |
| `int.rs:1418` `fold` | d4894aaa | written out, bits of the value | one sort plus a power per term (doc comment) | only powers of one integer folded | complete | none |
| `int.rs:1488` root bisection | d4894aaa | Newton, O(log bits) steps | bisection, O(bits · bits of k) products | interval Newton needs a containment proof | complete | none |
| `int.rs:1699` root of a root | d4894aaa | kept nested-root atom | written out, its digits plus a root | needs radicand residues | complete | none |
| `int.rs:1864` perfect-power test | d4894aaa | closed-form root, not known | precision to the bits of `x`, one residue test per 64 bits | no closed form for a root of a sum | complete | none |
| `int.rs:2012` written-out memory ask | 0e524771 | one ask per allocation | one ask, a byte per bit of the widest bound | refusal window up to 5.49 times; memory-ask rule | complete | none |
| `int.rs:2058` value inside `i128` | d4894aaa | cancelled by `fold` | written out, digits of the cores | as `fold` | complete | none |
| `int.rs:2244` trailing zeros of a root | 9fd9e552 | 2-adic residue in the memo | written out, its digits | root needs unit precision | complete | none |
| `int.rs:2261` kept exponent | 9fd9e552 | kept-exponent atom | exponent written out, its digits | no atom with kept exponent | complete | none |
| `int.rs:2320` power of a sum | d4894aaa | kept `s ^ k` atom | expansion, up to `C(n + k - 1, k)` terms | new atom needs its own approximation and residues | complete | none |
| `int.rs:2364` power past `u32` | 7498c2e7 | expansion, past any memory | `None`, O(1), caller bounds outward | loses exactness | complete | none |
| `int.rs:2524` `div_floor` | d4894aaa | kept `floor(a / b)` atom | written out, their digits; by a power of 2 in form | new form needed | complete | none |
| `int.rs:2566` `mod_floor` | d4894aaa | from a kept quotient | written out, their digits | as `div_floor` | complete | none |
| `int.rs:2599` `gcd` | d4894aaa | coprime-base factoring plus residues | written out, their digits | no form for gcd of unrelated powers | complete | none |
| `int.rs:2851` `Hash` | d4894aaa | value hash, O(1) expected, at a root's digits | one bucket per sign, O(n) comparisons per lookup | hash must agree with equality across forms | partial | added standard/used sentence |
| `int.rs:2907` decimal display | d4894aaa | own form as Zed text | written out, digits plus decimal conversion | printed value must parse back | complete | none |
