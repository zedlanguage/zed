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
| `group_verdicts` (refused member, reference) | 188fc1c3 | as `Type::verdict_alone` | as `Type::verdict_alone` | member refused, its message names definitions, cycles and tuple | complete (reference to `Type::verdict_alone`, completed in this review) | none |
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
| `fast::to_decimal` (`PRINT_WHOLE`) | 29ab1ba6 | split, about 2.3 per doubling plus fixed costs | num-bigint below 7845 words | crossover set by the benchmark `crossover print-whole` (PRINT-below-whole, 2026-11-12), identical digits | complete | none |
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
| `presburger.rs:9892` (tiers) | 355e67f4 | see `Tier` | O(Σ_B (cuts(B) + sides(B)) × size(B)), O(sides × part) | C2 | complete | none |
| `presburger.rs` `Tier` | 355e67f4 | integer program per side | Local O(Σ_B (cuts(B) + sides(B)) × size(B)) over the block-cut tree, Whole O(sides × part) | quadratic in one large block; 9.7× at 8 → 64 links (C2-local-tier) | complete | none |
| `presburger/local.rs` `cluster_sides` | C2-local-tier | integer program per side over the cluster, O(sides × cluster) | one pass over the block-cut tree, each side asked over its block | quadratic in one large block; wider than the hull where a projection has gaps (C2) | complete | none |
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

## crates/zedc-types

15 sites, all in `ty.rs`. Line numbers are those before the edits. Four doc comments named the bound on the hard case (orthogonal vectors, a quadratic refusal) and the cost used, but not the naive version beside it; each gains one sentence.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `ty.rs:176` (void tuple row) | 3dae154f | kernel search, up to the component's size per row | O(1) per component | rows empty only by search kept | complete | none |
| `ty.rs:506` `PartialEq` | 2d09ac32 | recursion, linear | recursion switching to an explicit stack, linear | none given up; stack bound by recursion depth | complete | none |
| `ty.rs:1659` (hidden-variable memo) | 889d3e94 | memo keyed by set hidden, O(rows) plus hashing the set | O(rows × signatures) worst | hashing a set per signature avoided | complete | none |
| `ty.rs:3032` explicit-stack comparison | 493ff031 | recursive, 59.0 ms | boxed futures, 60.8 ms, O(depth) heap | constant factor for unbounded depth | complete | none |
| `ty.rs:3589` `Near` | a65698ee | every pair, O(l·r·w) | filed groups, O((l·G + r·H)·w + l·G·log G) | worst n² (orthogonal vectors under SETH) | partial | added naive/used sentence |
| `ty.rs:3701` `Holders` | 5b8d1da1 | every tuple per value, O(l·r·w) | O(l·w + G·log G) to file, O(g·w + p) per value | worst l·r (orthogonal vectors) | partial | added naive/used sentence |
| `ty.rs:4217` (shape search) | faa267cb | members × shapes, n² | n log n × groups, refusal past a first shape | 6 refusals in 20,000 random | complete | none |
| `ty.rs:4672` `tied` | 241f0b9d | every pair of functions, n² | refused at the place | each pair could be compared | partial | added naive/used sentence |
| `ty.rs:4764` `cut` | 241f0b9d | kernel part for marks, O(k) (inferred) | each set by each mark, O(k·m) | no kernel part for marks | partial | added sentence; complete cost marked inferred |
| `ty.rs:5775` (pairwise below `l·r ≤ 1`) | b0648dc0 | pairs, measured instructions | filing, measured instructions | crossover measured; same answers | complete | none |
| `ty.rs:5865` (scan then file) | 5b8d1da1 | scan per value | file at `l·v > 16·(l + v)` | constant measured; same answers | complete | none |
| `ty.rs:6218` `every_arrow_fits` | ce7b9082 | n·m comparisons | candidates by key, n²/2 worst, n for shared parameter | Hitting Set lower bound (conjecture) | complete | none |
| `ty.rs:6466` covering (refusals) | 585e7f18 | DNF tautology, exponential; all subsets | linear in the width | three refused classes | complete | none |
| `ty.rs:6491` covering (candidates) | 53d0c317 | each arrow with each slot arrow, n·m | candidates, n·m worst | measured 63.3 times bytes | complete | none |
| `ty.rs:6659` `result_within` | 9b740605 | value by value, product of bounds; quadratic in shapes | linear in the results | some fits refused | complete | none |

## tests

18 markers in `tests/`. Twelve are references: a test comment that names a tradeoff comment in a crate and states the case it exercises. A reference is counted complete when the site it names exists and is complete; its costs are those of that site. One reference named a function that no longer holds the comment (stale) and was corrected. Line numbers are those before the edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `tests/src/oracle.rs:229` (walk ends after a stop) | ac2be137 | going on, O((n + s·F) log n) | ended walk, O(n log n) | bindings left unrun, reported with the reason | complete | none |
| `grammar_read.rs:72` | aac84859 | reference: `Reader::within` (`zedc-syntax` grammar.rs) | | | complete (reference) | none |
| `in_place.rs:351` | 56c364a9 | reference: `Rat::rem_built` (num.rs) | | | complete (reference) | none |
| `in_place.rs:369` | 26b4df16 | reference: `Rat::scaled` (num.rs) | | | complete (reference) | none |
| `memory_check.rs:312` | 1d71099a | reference: `bound::round` (num/bound.rs) | | | complete (reference) | none |
| `products.rs:57` | 26b4df16 | reference: `Rat::mul`, `Rat::scaled` | | | complete (reference) | none |
| `kinds.rs:1194` | a65698ee | reference: `Near` (ty.rs), F127 | | | complete (reference) | none |
| `kinds.rs:1332` | b0648dc0 | reference: `Near` (ty.rs), F132 | | | complete (reference) | none |
| `kinds.rs:1524` | 5b8d1da1 | reference: `Holders` (ty.rs), F133 | | | complete (reference) | none |
| `admission_sweep.rs:306` | b57ac34a | exact monotonicity for any k, exponential in k (coNP-complete) | 2^k reads, groups of k ≤ 4 | larger groups not swept | complete | none |
| `cycle_dup.rs:397` | 92fdf6f2 | reference: `names::absorb` (empty/names.rs) | | | complete (reference) | none |
| `group_oracle.rs:446` `Machine` | 1c44eba7 | hash map, measured 35 s on one system | table quadratic in the pool, some megabytes | memory for time | complete | none |
| `group_oracle.rs:918` (pool rounds) | 1c44eba7 | every value per component, product of pool sizes | 36 tuples and 6 constants per type per round, up to 6^w combinations built | `E` proves only the pool | partial | added naive/used sentence |
| `l01_38_presburger/extend.rs:129` | 5a4987d5 | reference: named `Extending::answers`, which only calls `Extending::defined`, where the comment is | | | stale | reference changed to `Extending::defined` |
| `ladder.rs:925` | 355e67f4 | reference: `part_bounds` (presburger.rs) | | | complete (reference) | none |
| `ladder.rs:1405` | 355e67f4 | reference: `products` (presburger.rs) | | | complete (reference) | none |
| `trivial.rs:357` (CNF) | b1c9b0de | CNF written out, product of clause counts | charged against the work budget, refused at it | budget is A54's stand-in (MIX-budget) | complete | none |
| `trivial.rs:682` (shared-field atom) | b1c9b0de | split by end symbol, wrong (loses agreement) | O(p log p) plus pairs, cubic in the atom | time and space cubic | complete | none |

Observation, not changed (outside a comment-only item): in `group_oracle.rs` the tuple rounds build every combination of up to 6 values per component (6^w) before keeping the first 36; taking 36 while building would bound the work by 36 per tuple type.

## crates/zedc-lattice

15 sites. Most are widenings and narrowings: the naive version is the plain join or meet, whose chains need not end, and the used version bounds the chain length; the tradeoff is precision. Line numbers are those before the edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `affine.rs:489` `widen` | 44d370e7 | join, chains need not end | bounds only shrink: at most one change per first bound, plus O(\|K\|) | new symbolic bounds dropped | partial | added naive/used sentence |
| `affine.rs:511` `narrow` | e86e485d | meet, chains need not end | each side changes at most once | tighter symbolic bound not taken | complete | none |
| `affine.rs:533` `leq` | 44d370e7 | Presburger entailment | linear in the bounds | false where below with other terms | complete | none |
| `interval.rs:324` `widen` | 44d370e7 | no widening, need not end | O(\|K\|) evaluations of a head | bound not named by a literal lost | complete | none |
| `interval.rs:393` `narrow` | e86e485d | meet, need not end | O(\|K\|) elements | tighter bound between landmarks lost | complete | none |
| `interval.rs:587` bit-word transfer | bc75c161 | exact image, search over the pieces' digits | hull, O(1) per word; shifts O(pieces) | holes not carried | complete | none |
| `interval.rs:628` single kept operands | 9fd9e552 | kept-form rules | written out, its digits | exact | complete | none |
| `lattice.rs:213` congruence narrow | 44d370e7 | meet, need not end | at most three changes | larger modulus not taken | complete | none |
| `lattice.rs:273` finite-set widen | 44d370e7 | join, need not end | once per landmark | all members lost at the top | complete | none |
| `lattice.rs:383` type widen | 6f016efe | join, need not end | each part at most once | members of a base type lost | complete | none |
| `lattice.rs:406` type narrow | 6f016efe | meet, need not end | each part at most once | smaller `next` not taken | complete | none |
| `revision.rs:327` image of pairs | 44d370e7 | k·m pieces, k^n over a chain | at most 4(k + 2) pairs, linear | merged pieces fill gaps | complete | none |
| `revision.rs:488` | 007abbf8 | reference: `pow_end` | | root exact or bounded | complete (reference) | none |
| `revision.rs:503` | 9e139638 | reference: `pow_end` | | | complete (reference) | none |
| `revision.rs:538` `pow_end` | 9e139638 | kept-exponent atom, comparisons not specified; expansion squares terms 32 times | bound `2 ^ u32::MAX` or infinite, O(1) | end not exact | complete | none |

## crates/zedc-check

14 sites. Line numbers are those before the edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `arms.rs:20` (module) | 308f2f4e | structural comparison of subterms, O(size) per pair; hash-consing O(1) expected per node (inferred) | one pass per root, memoized by span, O(1) per node | equal calls are different atoms | partial | added naive/used sentence (`//!`) |
| `mod.rs:1567` (`loose` vs empty) | ebbfd948 | `is_empty`, O(n) per lookup, O(n²) per chain | digest order, O(1) | unreduced empty payloads count as atoms | complete | none |
| `mod.rs:2377` (settled message type) | a934e9cf | memo across messages | O(size of the type) per message | same order as printing | complete | none |
| `mod.rs:4188` (decimal repair) | f45ecae1 | read as `rat`, O(n^1.47) | typed `rat`, O(n) | repairs needing the value not offered | complete | none |
| `mod.rs:5260` (`Known` from text) | 308f2f4e | store fixpoint per call | O(1) per node | parameters read as any int | complete | none |
| `mod.rs:5313` (`codePoint`) | 8d24cbde | each body per call site; memo linear | O(1) per node | results through functions read as any int | complete | none |
| `mod.rs:5499` (handled atoms) | 55045d49 | own walk per binder, O(B + R + E) unions each (inferred) | Tarjan, O(B + R + E) unions | union cost grows with distinct atoms | partial | added naive/used sentence |
| `mod.rs:6061` (explicit stack) | 81f3d848 | recursive, 52.8 G instructions | 54.1 G, same order | +2.6% | complete | none |
| `mod.rs:6401` (joined tuple shapes) | bb07f93b | union of shapes, O(n²), 53.4 times | joined, linear | which components went together | complete | none |
| `walk.rs:3072` (`lists_nothing`) | 3dae154f | kernel search, up to the type's size per test | O(1) | types empty by search stay reachable | complete | none |
| `walk.rs:3216` (`Scope::reaches`) | 142c3aa0 | every arm asked, 19.8 times | arms that add a type, 16.6 times bytes per 8 times size | `Never` missed in one case; NARROW-negated-star | complete | none |
| `walk.rs:3623` (lazy stars) | 961b304c | `k²` projections | O(k), measured | time only | complete | none |
| `walk.rs:3925` (class replacement) | ff24610b | lazy read, O(size of `sig`) once (inferred) | every depth, O(size of `sig`) per level, n² worst | sites would follow class links | partial | added naive/used sentence |
| `widen.rs:503` (word warnings) | c79fb5b4 | relational Presburger domain, exponential worst | O(1) per node, O(N) | no narrowing, operands independent | complete | none |

## Other crates

26 sites in zedc-stage, zedc, zed-tools, zedc-solvers, zedc-zir, zedc-base, zedc-syntax, zed-native, zed-rt and the corpus runtime. Line numbers are those before the edits.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `zedc-stage stage.rs:211` `ends` | 269ff6ee | size-change termination, PSPACE-complete; run with a step count (a size switch) | form check, near the distinct parts | terms that end but do not show it left to run time | complete | none |
| `zedc-stage stage.rs:541` `Sets` | 269ff6ee | union by the sets' sizes | hash-consed tries with a pair memo, a path in the common case; no proved bound | worst near the product of sizes | complete | none |
| `zedc-stage stage.rs:1048` maps | 269ff6ee | restriction by the sizes of map and set | hash-consed restriction with a pair memo; no proved bound | worst near the product of sizes | complete | none |
| `zedc-stage stage.rs:2401` `eval` | 269ff6ee | keyed by each function, once per distinct function, O(part × functions) (inferred) | keyed by answers taken; m new answers run m + 1 times | sharing given up, not exactness | partial | added naive/used sentence |
| `zedc front.rs:264` underlines | d16ca5c4 | every nest in full, O(d·L), quadratic | ends of heavy chains, O((s + L) log s) | marks drawn by ends | complete | none |
| `zedc front.rs:630` linear questions | 3e67fdd0 | complete Presburger, exponential worst | solver fragment, refusals costed at their raise sites | correct programs may be rejected | partial | added naive/used sentence |
| `zedc front.rs:708` chained relations | 5a4987d5 | each link decided whole, O(n²) | extended from the callee, O(n) | links that exclude the callee's point stay O(n²) | complete | none |
| `zedc front.rs:747` refused question restated | b273d0f6 | answer from the callee's | decided whole, O(the relation) | paid only on refusal | complete | none |
| `zedc mutate.rs:342` mutant rows | e2474205 | every row run, need not end | `stage::ends` form check, near the distinct parts | rows not shown to end are not run | partial | added naive/used sentence |
| `zedc pin.rs:299` | f3d10776 | hash map, O(1) | ordered map, O(log p) | no sort at each write | complete | none |
| `zedc suppress/addresses.rs:104` | 3e67fdd0 | each node's text hashed, O(n·depth); BLAKE3 at that cost | prefix hashes, O(n) once, O(1) per node | collisions mod 2^61 - 1 resolved by the rest of the address | complete | none |
| `zed-tools catalog.rs:781` | 637fdcd1 | walk up the ancestors per name | linear in the text, one lookup per name | none | complete | none |
| `zed-tools imports.rs:1339` | e18da1f4 | merged table, size of the modules per glob | one lookup per glob import | none | complete | none |
| `zed-tools imports.rs:1784` | e9e91392 | reachability per calling file, O(files × imports); Rust type inference | scan typing; join O(p √p) (AGM bound) | two cases not reported; IMPORTS-untyped-join | complete | none |
| `zed-tools imports.rs:2097` `ty_in` | e18da1f4 | read at every call, O(calls × type length) | once per text, O(type length) plus a lookup per call | memory for the kept types | partial | added naive/used sentence |
| `zedc-solvers negsssp.rs:542` | abf5c32f | a unit per edge (24.9 times) or none (+5%) | a unit per vertex and negative edge, O(m) | measured | complete | none |
| `zedc-solvers negsssp.rs:564` | abf5c32f | Duong's recursion alone | BF-Dijkstra first until it runs out, at most one pass extra | measured | complete | none |
| `zedc-solvers utvpi.rs:278` race | 094a40b5 | Goldberg–Radzik alone O(V·E); BF-Dijkstra O((E + V log V)·r) | race with Duong's bound, measured constants | race constant about 2 | complete | none |
| `zedc-zir canon.rs:220` | 208a874e | constants rewritten at each comparison | numbered regions, bytes of the operation per comparison | regions held until the lowering ends | complete | none |
| `zedc-zir legalize.rs:169` | 05d22662 | hash-consed, O(distinct regions) (inferred) | each use, O(graph as a tree) | memo by address banned | partial | added naive/used sentence |
| `zedc-zir lower.rs:182` occurrence ids | 9843712e | hash-consed ids, distinct subterms | tree size, `2^d` for shared parts | lowering already pays tree size | complete | none |
| `zedc-base cost.rs:129` peak | e5a0a719 | freed at the last reader, O(r) | counted to the schedule's end, O(r) | upper bound may reject a feasible plan | complete | none |
| `zedc-syntax grammar.rs:481` `within` | aac84859 | explicit stack, any depth | recursion, linear, stack per level | deep nests would overflow | complete | none |
| `zed-native lib.rs:65` | fc4686da | Cranelift e-graph and backtracking allocator, n^1.6 and n^1.4 | `OptLevel::None`, linear | slower code | complete | none |
| `zed-rt stack.rs:65` | d8fb27b5 | segmented stack, a compare per call | one reservation | refused under `RLIMIT_AS` | complete | none |
| `zed/corpus/ref zedrt.rs:226` | 4f52ced8 | num-bigint `parse`, O(n²) | halves above `LEAF_DIGITS` | timed crossover, same results | complete | none |

## Sites outside the 302 Rust markers

The 302 markers counted by the item are in `.rs` files. Eleven more `// Complexity tradeoff:` comments are in the Zed prelude (`zed/prelude/*.zed`, copies of Rust comments) and in the TypeScript chart tool (`tools/dagview`). They were reviewed by the same rule.

| Site | Commit | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| `tools/dagview/layout.ts:35` placement | 10a5b9c1 | network simplex, about O(n²), 240 s | Brandes-Koepf, O(n), under 1 s | wider chart, narrowed later | complete | none |
| `tools/dagview/layout.ts:60` starts | 10a5b9c1 | 7 random starts | 2, measured | best of fewer tries | complete | none |
| `tools/dagview/layout.ts:103` second pass | 71c7ac5b | first pass alone | added O(m log m) pass, measured | more bends | complete | none |
| `tools/dagview/narrow.ts:15` sweeps | 71c7ac5b | 0 sweeps | 8 sweeps, O(m log m) each | measured | complete | none |
| `tools/dagview/state.ts:491` ancestors | c0fef4e4 | transitive closure, no near-linear method known | O(n·a) | memory | complete | none |
| `zed/prelude/iteration.zed:24` | e6b30c2e | edges inverted once, O(V + E log E) (Rust copy) | O(V · E) | no flattening word yet; PRELUDE-depgraph | complete | none |
| `zed/prelude/lattice.zed:110` | 44d370e7 | as `interval.rs:324` | | | complete | none |
| `zed/prelude/lattice.zed:129` | e86e485d | as `interval.rs:393` | | | complete | none |
| `zed/prelude/lattice.zed:209` | e86e485d | as `lattice.rs:213` | | | complete | none |
| `zed/prelude/lattice.zed:228` | 44d370e7 | as `lattice.rs:273` | | | complete | none |
| `zed/prelude/revision.zed:17` | 44d370e7 | k·m pairs | stated "at most k + m pairs"; the code (Rust copy `map2`) and COMPLEXITY.md S4, S14 take at most 4(k + 2) once both operands are split at 0 | | stale | corrected to 4(k + 2), here and in the description above it |

The doc comment above `revision.rs` `map2` said the same "at most `k + m`" pairs, against the `4(k + 2)` of its own tradeoff paragraph and of the code (`shrink` caps the smaller operand to at most 2 pieces, `sign_parts` then splits both at 0); it is corrected too.

## COMPLEXITY.md rows checked at their sites (CX-tradeoff-krows)

Every row of COMPLEXITY.md (477 rows, all prefixes, not only the K rows the summary below
listed) was looked up at its code site. Where a row records an algorithm faster than the
naive one and the site had no `// Complexity tradeoff:` comment, or one that lacked the naive
cost, the used cost or the tradeoffs, the comment was added or completed. Only comments and
COMPLEXITY.md changed. "complete (review)" means a table above already cites a full comment
at that site. "not needed" means the code is the standard implementation (a map lookup, a
visited set, the removal of a copy, a correctness fix), or the row is open or kept with no
faster algorithm. Paths in parts B and C are relative to `crates/zed-kernel/src` unless they
name a crate; `store/x.rs` in parts A and G is the module path `zedc::store::x`.

### Part A: Store rows (S, LOAD, PROJECT, PRES, RUNG, NAME and other store rows)

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| S1 | zedc-preimage/preimage.rs:`struct Memo` | no memo, let depth 2^k; one memo per summary about n^1.8 | one memo per transfer keyed by (term number, scope number), about n^1.2 | memory until the transfer ends; keys are numbers | missing | added (one comment for S1, S1b, S6, S11, S19, S21) |
| S1b | preimage.rs:`struct Memo` (`Tx::lin`, `Tx::formula`) | translation repeated per path | remembered per (term, scope) | as S1 | missing | covered by the S1 comment; row pointer `preimage.rs:1668 and 1816` stale, fixed to `preimage.rs` |
| S2 | zedc-preimage/product.rs:`Scope::join` | `Or(R∧A, R∧B)`, 2^k connectives | persistent-set difference, one `Formula::either` of the remainders; cost of the differing conjuncts | no cap; greedy disjunct choice with one-level lookahead; projected per disjunction | partial: the doc gave the cost, no naive version or tradeoffs | added; row pointers `product.rs:987`, `presburger.rs:512` stale, fixed to file names |
| S3 | zedc-lattice/iterate.rs:`struct Walk` | re-stabilize inner components at each head change, exponential | dirty-flag skip, linear in the loops | O(d) marking per edge | missing | added |
| S4 | zedc-lattice/revision.rs:`map2` doc | exact image k·m pieces, k^n over a chain | at most 4(k + 2) pairs, O(k) | merged pieces fill gaps | complete (checked revision.rs:328) | row pointers `revision.rs:192`, `:284`, `interval.rs:276` stale, fixed to file names |
| S5 | zedc-presburger/presburger.rs:`Omega::run` | real and dark shadow both recursed, 2^V per leaf | one loop, no recursion into the shadows, splinters one level deep; polynomial in the rows | `Refusal::Shadows`, `Refusal::Growth`; residue above n log n is S18 | missing | added; row pointers `presburger.rs:2166/1907/2235/1369` stale, fixed to names |
| S6 | preimage.rs:`struct Memo` | O(n·depth) for constant | memo per transfer | as S1 | missing | covered by the S1 comment |
| S7 | (review-cited site) | — | — | — | complete (review) | none |
| S8 | product.rs:`Scope::bind`; zedc-lattice/cell.rs:`struct Premises` | scope copied per `let`, O(n²); premise sets copied, O(n²) | in-place bind + `unbind`, O(log s) per binding; union as a shared node, O(1) | copy when shadowing or `p` empty; LIFO undo; `Arc` node + `u64` id per union | missing | added at both sites |
| S11 | preimage.rs:`struct Memo` | as S1 | as S1 | as S1 | missing | covered by the S1 comment |
| S12 | (review-cited site) | — | — | — | complete (review) | row pointer `Tx::through, preimage.rs:1062` stale (now `Tx::enter`; `through` is in the test-only preimage_ref.rs), fixed |
| S9 | zedc-lattice/wto.rs:`weak_topological_order` | Bourdoncle recursive, O(d·(V+E)), O(V·(V+E)) on a nest | one DFS + loop-nesting forest, O((V+E) log V) | V log V words for binary lifting; nothing refused | missing | added (plain text, no link to private `Traversal`) |
| S23 | product.rs:`ranks`, `ordered_by` | — | standard sort | — | not needed: standard sort | none |
| S10 | zedc-lattice/affine.rs:`same_terms` | scan, O(k²) | BTreeSet range, O(log n + k) a call | relies on Bound's derived Ord comparing terms first; probe copies terms | missing | added |
| S14 | (review-cited) | — | — | — | complete (review) | none |
| S15 | (review-cited) | — | — | — | complete (review) | none |
| S16 | (review-cited) | — | — | — | complete (review) | none |
| S13 | iterate.rs:`struct Scopes` | every literal to every cell, 3L+1 evaluations per head | innermost component's landmarks | memory up to L × depth; widening may pass a literal that would have stopped it (inferred) | missing | added |
| S17 | (review-cited) | — | — | — | complete (review) | none |
| S18 | (review-cited) | — | — | — | complete (review) | none |
| Q1-ROWBOX | (review-cited) | — | — | — | complete (review) | none |
| Q1-LOCAL | (review-cited) | — | — | — | complete (review) | none |
| S19 | preimage.rs:`struct Memo` | as S1 | as S1 | as S1 | missing | covered by the S1 comment; see suspected code below |
| S20 | (review-cited) | — | — | — | complete (review) | none |
| S22 | preimage.rs:`enum Pa` | k² demands on a shared term | treap of affine pieces, inversion by descent, O(k log k) | one input; hull may narrow a box the `map2` cap widened (sound subset) | missing | added; stale claim "`stage::ends` (`stage.rs:165`) still walks a shared term as a tree" corrected in the row (fixed by row ENDS; stage.rs:203 doc confirms reading distinct parts once) |
| S22e | (review-cited) | — | — | — | complete (review) | none |
| S22e-quad | (review-cited) | — | — | — | complete (review) | none |
| S22e-wide | (review-cited) | — | — | — | complete (review) | none |
| S22-order | preimage.rs `Walk::by_class_at` | — | — | — | not needed: a non-termination fix (no summary for a test `if`), no faster algorithm; site comment already names the case | none |
| S22-order-chain | (review-cited) | — | — | — | complete (review) | none |
| S22-transfer-rem | (review-cited) | — | — | — | complete (review) | none |
| S22-linear-rem | preimage.rs:`Walk::lin_by_class` | k nested disjunctions, superlinear (24.6 s at k = 120) | one variable by cases, summary O(k log k) | one input, constant modulus; cases kept per scope | partial: doc had naive and used, no marker or tradeoffs | added |
| S22-case-cuts | (review-cited) | — | — | — | complete (review) | none |
| S22-hole-summaries | preimage.rs:`Pa::to_treap` | cut at every hole, O(k²) pieces | summary over the hull, `2k + 1 + 3T` cases | sound only while every reader meets with the domain | partial: doc had naive, no marker or tradeoffs | added |
| S22-fwd-holes | zedc-preimage/shared_ints.rs:`struct Ints` | new `IntervalSet` per level, O(k·H) | shared lazy node, O(1) join/monotone op | `Rc` per op; operand-address keys valid only because entries keep operands alive | partial: module doc had naive and used, no marker or tradeoffs | added (row appears twice in COMPLEXITY.md, lines 62 and 64: duplicate row, not removed under the freeze) |
| S22-split-holes | (review-cited) | — | — | — | complete (review) | none |
| S22-shapes-linear | zedc-presburger/presburger.rs:`has_point` | probe every disjunct, O(h²) | stop at first point, linear | a failing probe still runs to the end | partial: doc had naive, no marker or tradeoffs | added |
| S21 | preimage.rs:`Terms::add` | tree walk, exponential with sharing | explicit stack + id visited set, linear in distinct parts | — | missing | added |
| S24 | product.rs:`Scope::close` | every call path, exponential | visited set, O(functions reached + sizes) | closed test counted per arm; depth recursion (T2-mid) | partial: doc gave cost, no naive or tradeoffs | added |
| S25 | (review-cited) | — | — | — | complete (review) | none |
| S4-ti | (review-cited) | — | — | — | complete (review) | none |
| S26 | zedc-presburger/hull.rs:`Hull::and`, `used` | — | in-place persistent-map edits; `contains_key` before `remove`/`get_mut` | constant factor (21%) | not needed: copy removal, no algorithm below naive; the `contains_key` reason is already commented at hull.rs:130 | none |
| S27 | zedc-presburger/presburger/deep.rs (module) | derived recursive walks, O(depth) stack | heap work lists/fold, O(distinct parts) | heap memory, larger constant | missing | added |
| S28 | (review-cited) | — | — | — | complete (review) | none |
| S29 | zedc-presburger/conjuncts.rs:`Blocks::remove` | split per conjunct + repeated lookups, O(k³) | one split per block, `unite` returns the block, near linear | a `BTreeMap` per call; failed split rebuilds linked blocks | partial: doc gave the cost, no naive or tradeoffs | added |
| S30 | preimage.rs:`read_powers` | O(n·depth) | each product read once into `Tx::powers`, linear | exact `Count`, O(d²) bits (S30b) | missing | added |
| S30b | zedc-lattice/revision.rs `Exponent`; preimage.rs `Count` | — | — | — | not needed: removes a size switch, no faster algorithm; covered in the S30 comment and revision.rs:537 doc | none |
| S31 | (review-cited) | — | — | — | complete (review) | none |
| S31b | (review-cited) | — | — | — | complete (review) | none |
| S31c | preimage.rs:`Walk::and_if` | `if` per level copying the prefix, O(k²) | read as `&&` into one `Joining`, linear | shared subterms recorded (`Terms::shared`) | missing | added |
| S32 | presburger.rs:`stable_colors` | hashed rounds until stable, O(n²) on a pipeline | Berkholz–Bonsma–Grohe refinement, O((n+m+t) log(n+m+t)) | graph in memory; stable partition, not canonical labeling | partial: doc gave used version, no naive or tradeoffs | added |
| S34 | (review-cited) | — | — | — | complete (review) | none |
| S33 | (review-cited) | — | — | — | complete (review) | none |
| S35 | cell.rs:`struct Premises` (`Premises::set`) | tree walk, n²/2 paths or exponential | id visited set, O(m log m) | `u64` id per node; ids not addresses | partial: `set` doc gave the cost, no naive or tradeoffs | added (with S8) |
| S36 | lattice::Congruence, revision.rs, int.rs | — | — | — | not needed: exactness change (`Num` past `i64`), cost of the arithmetic (S33); existing comments at revision.rs:549, int.rs:2370 cover the kept-power limit | none |
| NAME-ties | (review-cited) | — | — | — | complete (review) | none |
| NAME-ties-or | (review-cited) | — | — | — | complete (review) | none |
| NAME-ties-orient | presburger.rs:`struct Ties` | — | union by rank, O(log n) | — | not needed: standard union-find | none |
| DECIDE-disj-chain | (review-cited) | — | — | — | complete (review) | none |
| DISJ-incremental | (review-cited) | — | — | — | complete (review) | none |
| S37 | product.rs:`Tree::of` | — | sort per level, O(n log n) | — | not needed: standard sorting, replaces a hash for determinism | none |
| S38 | zedc-solvers/utvpi.rs:`integer_point` | elimination with fill (18.8 then 31.1 times per 8 times) | point from the potential + 2-SAT over tight edges, linear after the potential | unit two-variable rows only | missing | added |
| S39 | (review-cited) | — | — | — | complete (review) | none |
| RUNG2-definedness | (review-cited) | — | — | — | complete (review) | none |
| RUNG2-carrier | zedc-types `Sig::int_params`, elab, front | — | linear scan per arrow | — | not needed: correctness fix (D6), standard linear scan | none |
| PRES-mod-conjuncts | (review-cited) | — | — | — | complete (review) | none |
| PRES-guarded-chain | (review-cited) | — | — | — | complete (review) | none |
| LOAD-chain | preimage.rs:`struct Scoped` | fresh transfer per body, O(n²) | one numbering per scope, body-dependent entries dropped, O(n) | scope holds O(n) entries | partial: doc gave the cost, no marker or tradeoffs | added (one comment for LOAD-chain, -share, -aux, -args) |
| LOAD-chain-share | preimage.rs:`struct Scoped`; extend.rs | copied callee constraints, O(n²) | callee kept whole as one shared part | non-extending links decided whole (open, commented at extend.rs:208) | partial | covered by the Scoped comment |
| LOAD-chain-aux | preimage.rs:`struct Scoped` | renumbered auxiliaries per body, O(n²) | one translation state per scope | — | partial | covered by the Scoped comment |
| LOAD-chain-args | preimage.rs:`struct Scoped` (`Frame`) | kept translation dropped on moved arguments, O(n²) | read in callee's coordinates | refused question in moved coordinates decided again (front.rs) | missing | covered by the Scoped comment |
| LOAD-chain-defs | zedc-presburger/presburger/extend.rs:`reached_past` | whole chain of definitions per link, O(n²) | definitions reached past the point's values | fallback decides the whole | partial: doc gave the cost, no naive | added |
| LOAD-chain-sep | (review-cited) | — | — | — | complete (review) | none |
| LOAD-chain-affine | (review-cited) | — | — | — | complete (review) | none |
| LOAD-affine-cone | preimage.rs:`projected` | callee body re-read per call, O(n²) | projection once per callee and key, O(rows left) a call | memory per projection; falls back where the relation chooses | missing | added |
| LOAD-affine-join | (review-cited) | — | — | — | complete (review) | none |
| LOAD-call-summary | extend.rs:`struct Faces` | rest of the chain read per link, O(n²) | lazy face per conjunction, O(faces' rows) | face valid only where no other reader needs a projected atom | missing | added |
| LOAD-disj-residue | (review-cited) | — | — | — | complete (review) | none |
| LOAD-bound-holes | presburger/extend/holes.rs:`struct Holes` | holes as disjunctions, O(n²) | persistent treap of intervals, O(log n) a cut | `Faces::free` may answer where the whole is refused | missing | added |
| LOAD-call-relation | (review-cited) | — | — | — | complete (review) | none |
| LOAD-holes-mod | (review-cited) | — | — | — | complete (review) | none |
| LOAD-mod-chain | (review-cited) | — | — | — | complete (review) | none |
| LOAD-extend-refuses | extend.rs:`decided` | — | — | — | complete (checked extend.rs:1976) | none |
| S40 | (review-cited) | — | — | — | complete (review) | none |
| S41 | — | — | — | — | not needed: audit, no change | none |
| S42 | product.rs `Scope::projected` (`PartKey`, `PartWith`) | — | key by conjunct | — | not needed: a memory-retention fix by key choice, no faster algorithm | none |
| S43 | (review-cited) | — | — | — | complete (review) | none |
| PROJECT-each-canon | (review-cited) | — | — | — | complete (review) | none |
| PROJECT-canon-gcd | presburger.rs `signed`/`Con::reduced` | — | — | — | not needed: the row says "not a cost item"; site doc at presburger.rs:1200 | none |
| PROJECT-canon-decide | — | — | — | — | not needed: test only, no change | none |
| PROJECT-canon-precision | presburger.rs `project_parts` | — | — | — | not needed: open precision item, no algorithm changed | none |
| PROJECT-dead2-quadratic | presburger.rs:`settle_as_sets` | whole union-find group per disjunct, O(n²) | projection by halves, O((m + k) log k) | refused projection asks the whole group | partial: doc gave naive, no marker or tradeoffs | added |
| PROJECT-canon-272 | — | — | — | — | not needed: fixed by PROJECT-growth-box (cited complete) | none |
| PROJECT-growth-box | (review-cited) | — | — | — | complete (review) | none |
| S44 | presburger.rs:`satisfiable_inner` | one ask without implied rows | implied rows first, at most two asks | refused formula asked twice | partial: complete comment, no row ID | added "COMPLEXITY.md row S44." |
| NARROW-hub-seed-edges | product.rs:`Scope::bound_pass` | every seed reads all edges, O(k²) | only added and changed edges, O((s + a + m) log n) | relies on `Seeds::changed` recording every change | partial: doc gave the cost, no naive or tradeoffs | added |
| S45 | zedc-preimage/address.rs:`struct Address` | printed-text key, 2^d | canonical term by binder height, digest then structure, linear in distinct parts | canonical term kept; equal digests cost a structural compare | missing | added |
| S46 | zedc-int/int.rs:`least_root` | full Newton root per index, allocated | word roots; residue filter; carried inverse | remainder tree per base; filter necessary only | partial: doc gave the cost, no naive or tradeoffs | added |
| S47 | preimage.rs `split_at`; `Int`/`Num` `Arc<BigInt>`; `fit_lambda` | — | standard treap split, shared digits, one map | — | not needed: restores the treap invariant and removes copies; standard | none (see suspected code) |

### Part B: Kernel rows K1 to K46

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| K1 | zed-kernel/src/types/bdd.rs (module doc), `Part`, `list` | DNF complement by De Morgan's product, 2^C; ROBDD meet of a and b, up to \|a\|·\|b\| nodes | decision list in one form, O(1) complement, O(log n) expected per added literal; any other union or meet kept as an O(1) expression | the work moves to `empty`, exponential in the worst case, which refuses the classes it names | missing | module paragraph added (K1, K3); row K1 was stale (it said ROBDDs with a linear complement) and is fixed |
| K2 | `Type::union_all`, `Type::meet_all` | one operand at a time, O(n²) | joined in pairs, O(n log n) | none | complete (review table) | none; the row says `rec.rs`, which is now `types.rs` `mod rec` and `types/rec/group.rs` (left as is, see below) |
| K3 | types/bdd.rs (module doc) | merging DNF clauses after each change, O(C³) | no merging step; expressions kept | as K1 | missing | covered by the K1/K3 module paragraph |
| K4 | the printer's `fits` | — | Wadler's `fits`, the standard method | — | not needed: standard algorithm | none |
| K5 | zed-kernel/src/eval.rs:`round` | copy the `Defined` map each round, O(R·n) | one shared map with round stamps plus wait lists | memory for stamps and wait lists | missing | comment added |
| K6 | `Value` clones | deep copy, O(size) | `Arc` sharing, O(1) | — | not needed: covered by the K7 and K21 comments | none |
| K7 | value.rs:`union`, `from_leaves` | rebuild the family, O(n) per insert | persistent imbl maps; `Levels::place` keeps a family whole | O(log n) per access in place of O(1) | missing | comments added at `union` and `from_leaves` (K7, K10) |
| K8 | eval.rs:`type Env` | cloned `HashMap` per call, O(n) | persistent map, O(log n) per access | log factor per lookup | missing | comment added |
| K9 | provenance.rs:`NodeAddress` | `Vec` copied per step, O(depth) | `imbl::Vector`, shared prefix | log factor per index | missing | comment added |
| K10 | value.rs:`from_leaves` | as K7 | as K7 | as K7 | missing | covered by the K7/K10 comment |
| K11 | zed-kernel/src/types/empty.rs:`Searching::solve` | `done.retain` per non-empty result, O(T²) | phases; an answer read by another decision undone at the end of a phase | — | stale: the `done` stack in the row no longer exists | row K11 fixed (sentence added naming the phases); no code comment needed, test `many_negated_types_passed_over_scale` still holds it |
| K12 | types.rs:`impl Ord for Type` | structural comparison, O(size) | digest first, contents only on equal digests | a hash per node | missing | comment added |
| K13 | (review table) | — | — | — | complete (review table) | none |
| K14 | eval.rs:`pull` | Jacobi rounds, O(R·n) | memoized demand; busy and stalled sets, O(log D) per step | memo memory | missing | comment added |
| K15 | value.rs:`items_eq` | `cmp == Equal`, reads both families in full, O(n) per round | sizes first, then imbl `diff` skipping shared nodes, pair table keyed by id | table bounded at 8 times the pairs by `clear` | missing | comment added (K15, K21, K40); row K15 was stale (it named `OrdMap`'s test) and is fixed |
| K16 | zed-kernel/src/text.rs:`join` | `String` concatenation, O(n) per join | finger tree, O(log n) | log factor per index | partial: no naive version | another fork's `join` comment (R4/R5/C29) now ends "C29, K16."; my duplicate sentence at `push_back` removed |
| K17 | `types.rs` `mod rec`, `contractive` (`first_on_cycle`) | — | Tarjan's components, one-pass translation | — | not needed: standard algorithms | none; row's `rec.rs` is history and left as is |
| K18 | value.rs:`merge_failures` | copy the largest set, O(n) per merge | extend the largest set in place, smaller into larger | — | missing (prose only) | prose replaced by the standing form |
| K19 | types.rs:`rope` | recursive text building, O(depth) stack | explicit stack, each type at most twice | map of texts for the run | missing | comment added (K19, K39) |
| K20 | eval.rs (module doc) | native recursion, 10 µs per call, stack overflow on depth | explicit-stack machine, frames on the heap, 1.2 µs per call | heap allocation of frames | missing | module paragraph added |
| K21 | value.rs:`items_eq`, `copy` | deep compare and deep copy | id pair table; `copy` shares nodes | memory for the table | missing | covered by the K15 and `copy` comments |
| K22 | zed-kernel/src/deep.rs (module doc); value.rs `walk_with`, `copy`, `all_leaves` | recursive walks and drops, O(depth) stack | explicit stacks; drop queue | heap memory O(depth) | missing | deep.rs module paragraph (K22, K39) and value.rs `copy` comment added; row K22 was stale (walks moved to value.rs) and is fixed |
| K23 | standard lookup | — | — | — | not needed: no growth, a standard lookup | none |
| K24 | empty.rs:`struct Region` | per-tuple-type copy of the box | change log, about 3.4 times fewer instructions at c = 128 to 512 columns; a prefix trie measured c^2.93 | O(N) log memory | missing | comment added |
| K25 | zed-kernel/src/provenance.rs:`origins` | one search per member, O(M·E), O(n²) on a chain of sets | one backward pass, O(n log n) | reads values of reached facts, O(m log m) | complete | none |
| K26 | zed-kernel/src/types/bes.rs:`refusal` | rescan per verdict | stamp counting (control `exring:6:1`, 36.80) | — | missing | comment added; points to the `group_verdicts` `Refusal::Group` comment |
| K27 | types.rs `mod rec`:`same`; group.rs `Node::of` | structural comparison of bounds, O(n log n) on equal bounds nested log n deep | class per node from `Numbering::first`, expected O(1) per node; the test O(1) | the table lives while trees are built, O(nodes) | partial: `same` said O(1) only | comment added at `same`; group.rs `monotone` comment cites K27 for the admission check; row's file pointer fixed (`judge` is in empty.rs, `refs` in group.rs) |
| GROUP-admit-msg | zed-kernel/src/types/rec/group.rs:`monotone`, `flipped`, `path` | — | message built only on rejection, linear in its text | — | missing | covered by the new `monotone` comment; row's `types/rec.rs` fixed to `types/rec/group.rs` |
| GROUP-admit | tests/steps/l01_23_subtyping/admission_sweep.rs:`Flat::monotone`; group.rs:`monotone` | exact monotonicity test, coNP-complete; the evaluator O(2^k·k·m) | sufficient syntactic check: one walk (`refs`), one `via` propagation on a stack, one `flipped` search per body, O(size of the bodies) | monotone groups that may narrow a domain through a named definition are rejected, with site and path | partial: test evaluator complete, kernel site missing | comment added before group.rs `monotone` |
| SURFACE-cycle | zed-kernel/src/types/print.rs:`heights`, `same_names` | — | one pass each over the type's graph | — | not needed: standard walks with visited sets | none |
| K28 | types.rs:`Type::finite`, `each_value` | — | visited set; box looked up once | — | not needed: standard DFS with a visited set | none |
| K29 | print.rs:`Type::surface` | — | one visit per node with a visited set, O(N log N) | — | not needed: standard | none |
| K30 | num.rs (review table) | — | — | — | complete (review table) | none |
| K31 | empty.rs:`find_cycle` | walk from each type, O(k) each, Θ(n²) for `nth_from_end(n)` | answer of every type on a walk recorded (`cycles`), each chain once, O(n log n) | O(n) map memory | missing (prose doc only) | comment added |
| K32 | bdd.rs:`Part::forced` | one evaluation per atom, O(atoms × nodes), 11.5 s at d = 46 | one post-order pass over persistent sets, O(N log N) while sets stay small | worst case nodes × atoms when sharing defeats smaller-into-larger | missing | comment added; module doc sentence corrected to "one pass over the nodes of an expression" |
| K33 | group.rs:`Group::instance` | — | one Tarjan pass and one DFS | — | not needed: standard algorithms | none; row's file pointer fixed to `types/rec/group.rs` |
| K34 | empty.rs `greedy_length` (review table) | — | — | — | complete (review table) | none |
| K35 | empty.rs:`find_rep` (candidate skip) | narrow every candidate, O(n²) types | one test per candidate skips those inside an excluded tuple type, O(n) on `fork_by` (8.5 times from n 8 to 64) | none, same answer | partial: naive given, no label or used complexity | standing form prepended (K35, K80); `refine` itself is the plain method and needs none |
| K36 | empty.rs:`overlaps`, `split_classes` | pairwise meets, O(k²) searches | union-find over keys in a trie, size × log keys | coarse keys join disjoint types; a joined class of k pinwheels costs order k² | complete | none |
| K37 | empty.rs:`struct Simulation` | greatest fixed point by rounds, O(pairs × rounds); pre-T6: 4n² pairs, 0.5 s at n = 128 | counting of open choices, failures spread once (Horn satisfiability), O(needs) | sufficient only; other pairs go to `Search` | missing (prose doc only) | comment added |
| K38 | zedc-types/src/ty.rs:`Ty::kernel` | each shape tried in turn, O(shapes × components), n² | shapes joined in pairs, O(n log n); kernel decides | a piece the kernel cannot decide is refused | partial: no complexities | inline comment completed; row cites `check/ty.rs`, now `zedc-types/src/ty.rs` (left, see below) |
| K39 | deep.rs drop queue; types.rs `rope` | recursive drop and text, O(depth) stack | thread-local drop queue; explicit stack | heap O(depth) | missing | covered by the deep.rs (K22, K39) and `rope` (K19, K39) comments; row's `types/rec.rs` fixed to `types.rs` `mod rec` |
| K40 | types.rs `contains`; words.rs `room_to_print`; provenance `origins`; zedc-zir lower.rs `body_uses` | — | memo keyed by `fresh_id` ids | — | not needed: standard memo keys | none (the `items_eq` comment cites K40) |
| K41 | num.rs:`LEAF_DIGITS`, `valuation_upto`, `over_ten_to` | num-bigint parse and Stein gcd, O(n²) | halves joined by NTT products, O(n log² n); valuations of 2 and 5 | timed crossover at the leaf | complete | none; row K41 was stale ("O(n^1.47) with num-bigint's Toom-3") and is fixed to O(n log² n) with `num/fast.rs` |
| K42 | zedc-zir/src/zir/memory.rs:`Machine::alone` | — | `Vec` indexed by occurrence id, O(1) | — | not needed: standard indexing | none |
| K43 | zedc-preimage `Terms::add` | — | visited set keyed by `Shared` id | — | not needed: standard visited set | none |
| K44 | zedc-stage stage.rs:`Reader::ids` | — | `HashMap<u64, usize>` by `Shared::id` | — | not needed: standard memo | none |
| K45 | `resolve`, `Tables::collect_stmt` | — | O(1) per port | — | not needed: no faster algorithm | none |
| K46 | bdd.rs digests, `reaching` | — | correctness fix | — | not needed: a correctness fix, not a faster algorithm | none |

### Part C: Kernel rows K47 to K95

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| K47 | `types/print.rs` `Printer::canon`; `types/bdd.rs` module `list` | the walk in node order, O(t), text depends on atom order | rank by height (AHU), O(t log t); list printing O(nodes) | log factor | complete (review row 142) | none |
| K48 | `types.rs` `order` | recursion with no memo, one step per path, exponential in the depth of sharing; a native frame per tied level | `equal` set of node-id pairs for the whole comparison, one step per pair, heap stack | memory O(pairs found equal), a hash insert per pair | missing | added marker in `order`; fixed stale `bdd::order` in the K48 row and in 5 doc comments of `types.rs` (now `order`) |
| K49 | `types/rec/group.rs` `Group::new`, `Group::instance`, `GROUPS`, `INSTANCES` | Debug-text key plus scan of instances, O(n²) on nests | hash table by digest, O(1) expected | (standard hash interning) | not needed: hash-table interning is the standard implementation | COMPLEXITY.md pointer `types/rec.rs` → `types/rec/group.rs` |
| K50 | `tests/steps/l01_23_subtyping/rec.rs`, `x13.rs` | — | — | — | not needed: tests only, cost is K40's | none |
| K51 | `tests/steps/l01_23_subtyping/judgments.rs` | — | — | — | not needed: tests only (the `cuts` memo has its marker, review row 37) | none |
| K52 | `types/empty.rs` `find_rep` closure branch | — | O(1) known-empty test | — | not needed: O(1) check, tests | none |
| K53 | `types.rs` `Rec`, `types`, module `rec` `Key`, `Key::order`; `types/print.rs` | — | digest, place, then definitions; O(1) when digests differ | — | not needed: standard comparison by key | COMPLEXITY.md: `types/rec.rs` `Key` → `types.rs` module `rec`; `Checked::order` (no longer exists) → `Key::order`; `types/bdd.rs` `types` → `types.rs` `types` |
| K54 | `types/empty.rs` `Searching::two_sat`, `TwoSat::solve` | per-length search, n^3 to n^3.5 on parity cycles | 2-SAT by structure, linear | pigeonhole and 3-literal clauses left to the search | complete (marker at the 2-SAT site, K54) | none |
| K55 | `tests/steps/l01_23_subtyping/group_oracle.rs` `Machine`, pool | hash map by pair plus path set per application | u32 table over all pool pairs | quadratic memory in the deduplicated pool | complete (review rows 329-330) | none |
| K56 | `types/empty.rs` `group_verdicts`; `types/rec/unfold.rs` `Type::group_members`, `Key::members` | a search per member, O(n²) | one shared search, O(group) | a missed member may read the group again | complete (review row 26) | COMPLEXITY.md: `types.rs` `Type::group_members`, `types/rec.rs` `Key::members` → `types/rec/unfold.rs` |
| K57 | `types/bdd.rs` `Part::choose`, `empty.rs` `split_classes` | — | — | — | not needed: rejected, no code added | none |
| K58 | `print::written`, `Formula::written`, `elab::written_name` | — | one pass, linear | none | not needed: linear printing | none |
| K59 | `types/empty.rs` `Searching::rep`, `returnable`, `find_rep` | — | no cost added | — | not needed: correctness fix, no faster algorithm | none |
| K60 | `types/empty.rs` `Searching::no_key`, `no_keys` | a search per key type, O(d²) on a nest of d (inferred) | key types decided in the one search, each once, O(d) | proved only at phase end when it reads a type being decided; none while seeding; member may be `Refused(NoWitness)` | missing | added marker in `no_key` |
| K61 | `types/empty.rs` `group_verdicts`, `refuse_fork`, `Search::solve_all` | a search per open member, O(n²) | one search with all open members as roots | a fork outside any decided type refuses every open root | complete (marker at `refuse_fork`, review row 38; `group_verdicts` doc) | none |
| K62 | `types/empty.rs` `STORES`, `decide_groups_read`; module `rec` `Key::group` | a search of its own per reader, O(m·n) | kept values read by index, O(1) per read | memory of all values until the unit ends | complete (review row 25) | COMPLEXITY.md: `types/rec.rs` `Key::group` → `types.rs` module `rec` |
| K63 | `types/bdd.rs` module `list` (treap cells), `Connect::zipped`, `zip_chain` | `Bdd::zip` apply, O(m²) for a list built a literal at a time | hash-consed treap cells, O(log m) expected per literal | balance in expectation only; per-cell weak table entry and caches; constant factor | partial: `Connect::zipped` had its marker (review row 134), the list treap had none | added marker at module `list`; COMPLEXITY.md `types/bdd/list.rs` → `types/bdd.rs` module `list` |
| K64 | `types/empty.rs` `Searching::drain`, `Search::round`, `deciding` | — | O(log n) per drain step (was O(1) amortized) | — | not needed: soundness fix, no faster algorithm | none |
| K65 | `types/empty.rs` `decide_groups_read`; `types.rs` `Type::judged_known`, module `rec` `Key::judged_known`; `group_oracle.rs` `kernel()` | — | deciders only of groups read, skip judged; Tarjan in the test helper | — | not needed: constant factor; Tarjan SCC is the standard algorithm | COMPLEXITY.md: `types/rec.rs` `Key::judged_known` → `types.rs` module `rec` |
| K66 | `types/bdd/set.rs` `make`, `types/bdd.rs` module `list` `cell`, module `xor` `node`, `Expr::link`, `Row::new`, `types/rec/group.rs` `GROUPS`, `INSTANCES` | — | weak tables, entry removed on drop | — | not needed: memory fix; weak hash-consing tables are standard | COMPLEXITY.md: `types/bdd/list.rs` → module `list`; `types/rec.rs` → `types/rec/group.rs` |
| K67 | `types/bdd.rs` module `list` `restrict`; `choice_of` (chain-chain); `set::same`; list cut | (1) memo per list, O(m²); (2) both chains listed per join, O(m²) | (1) memo by cell id, each cell once per memo; (2) shorter chain looked up in the longer, O(k log n); (3) `set::same` O(k) across threads; (4) cut O(log m) | memo memory; log factor per lookup; cross-thread O(k) | partial: (3) at `set::same` and (4) at the cut had markers; (1) and (2) had none | added markers at list `restrict` (1) and `choice_of` (2); COMPLEXITY.md `types/bdd/list.rs` → module `list` |
| K68 | `types/rec/unfold.rs` `Unit`, `end_unit`, `Env::member`, `Env::forget`; `types.rs` `Held` | keep every group, or a cycle collector | free at unit end, remake O(body) | regrouping by later units | complete (marker in `unfold.rs`, review row 146) | COMPLEXITY.md: `types/rec.rs` split into `types.rs` module `rec`, `types/rec/unfold.rs`, `types/rec/group.rs` |
| K69 | `types.rs` `part_boxes`, `Graph`, `Class::under`, `Class::known`, `RowIndex::holds` | meet of every pair of boxes, exponential along a chain | meet with the join, n log n | some finite meets not known finite | complete (review rows 100-105) | none |
| K70 | `types.rs` `Shared`, `ARROWS`, `ROWS`; `order` `Step::Morphisms` | — | interning, pointer compare; KeyHasher | — | not needed: constant factor; hash-consing is standard | none |
| K71 | `types/empty.rs` `tuples_on`, `one_pass`; `bdd.rs` `same_as_not` | split into open tuple types, order c² | one pass, linear, then `SharedCells` refusal | refusal of covers | complete (review rows 42-43) | none |
| K72 | `types.rs` module `rec` `canon`, `Canon::order`; `refine.rs` | per-member walk, O(N²) on one SCC; naive refinement rounds O(N(N+M)) | color refinement with Hopcroft's rule, O((N+M) log N) | graph memory; log factor over written-order numbering; bisimilar members merge | missing | added markers in `canon` and at the top of `refine.rs`; COMPLEXITY.md `types/rec.rs` → `types.rs` module `rec` |
| K73 | `value.rs` `items_eq` (the tradeoff block before it), `Comparisons`, `Scope`, `walk` | read as trees, 2^d for shared levels; one part in n places read n times, O(n²) | pairs kept per relation until the outermost comparison ends, O(distinct pairs · log width) | table memory; +18 to 24% on families with no sharing | partial: marker cited K15, K21, K40 without K73, the n² surface case or the constant cost | completed the marker (K73 citation, surface case, `Scope`, constant cost) |
| K74 | `zedc-presburger` `formula.rs` `Id`, `is_shared`; `presburger.rs` `BelowKey`; `conjuncts.rs` `and_held` | — | ids in place of addresses, cost unchanged | +8 bytes per node, one atomic add | not needed: determinism fix, the memo is K40's | none |
| K76 | `types/bdd/set.rs` `SetTable`; `types.rs` `Morphism::cmp`, `Type::zip_at_once` | BTreeMap search | HashMap, O(1) expected; O(1) simple cases | — | not needed: standard hashing and simple-case fast paths | none |
| K77 | `types/empty.rs` `Search` maps, `Searching::cut` | BTreeMap<Type> searches | HashMap by digest; `cut` memo by node address | equal operands built apart miss (K51 marker) | not needed: standard hashing; the `cuts` memo has its K51 marker | none |
| K78 | `eval.rs` `Machine::fold`; `value.rs` `Levels` | — | one loop, constant stack, O(n log n) | — | not needed: standard loop in place of mutual recursion | none |
| K79 | `text.rs` `compare`, `Text::chunks` | — | one-block texts compared as `str`, no stack | +2 to 4% on trees | not needed: constant-factor fast path for a simple case | none |
| K80 | `types/empty.rs` `find_rep` (disjoint disjuncts, `inside_excluded`, all-inside proof); `bdd.rs` `disjoint_disjuncts` | n candidates by n cells, then refine, O(n²) | split and skips, O(n) for these forms | forked parts not so proved are refined at the old cost | partial: plain comments gave both costs, no marker or tradeoff | added marker before `disjoint_disjuncts` in `find_rep` |
| K81 | `num/fast.rs` `to_decimal`; `zedc-int` `Display` | num-bigint, about n^1.5 measured (O(n²) asymptotic) | halves, O(n log² n) from 7845 words | crossovers `PRINT_WHOLE`, `PRINT_HANDOFF` set by the benchmark `crossover` (PRINT-below-whole) | complete (three markers in `to_decimal`) | none (note: the code says num-bigint is O(n²), the row says about n^1.5 measured; both hold) |
| K82 | `num/fast.rs` `mul` | num-bigint schoolbook / Karatsuba / Toom-3, n^1.465 | NTT over three primes, O(n log n) above `MUL_LEAF` | timed crossovers | complete (marker in `mul`) | none |
| K83 | `types/bucket.rs` `Bucket`, `find` | list read whole per lookup, scanned per drop, O(b) | treap by contents, O(log b) expected | expectation only; slot memory; restarts; short-addresses chain still about n² log n | missing | added marker at the top of `bucket.rs` |
| K84 | `types/empty.rs` `judge`/`group_verdicts` (marker after `runs`) | decider gives up the whole group, every member searched (23 times at 8k) | `a & b` as `And`, `a \ b` as `a`, linear, exact `Empty` | members inhabited through a meet go to the search; exponential product forks refused | partial: no naive version | added naive and used to the existing marker |
| K85 | `types/empty/refused.rs` `Why::recheck`, `refused_site`; `empty.rs` `group_verdicts` | whole walk per re-check, O(m n) | walk with cuts, O(nodes reached) | whole walk where a kept-refused member is met | complete (review row 147) | none |
| K86 | `types/bdd/set.rs` `retain`; `types/bdd.rs` list `restrict` (stage `Block`); cell and xor tables | (1) `set::remove` per literal, O(r log m), c log² c split; (2) BTreeMap tables; (3) chains joined a literal at a time | (1) one walk, O(m) per block, c log c; (2) HashMap; (3) `union_if_agree`, O(k log(n/k+1)) | (1) O(m) even when few literals go | partial: `retain` doc gave both costs, no marker or tradeoff | added marker before `retain` |
| K87 | `types/bdd.rs` module `xor` `half`, `meet` | `zip` with `Connect::zipped`'s search per meet | meet expression made directly, proved equal | none (results identical) | not needed: constant factor; doc of `xor::meet` gives the proof | none |
| K88 | `types/empty/names.rs` `absorb`; `empty.rs` `system` | transitive reduction, O(n·m) | dominators, O(m log m) | some arms kept; group may be refused | complete (review row 148) | none |
| K89 | `types/empty/refused.rs` `Why::recheck`, `refused_site` | re-check per member, O(m n) | shared re-check with kept members as leaves | O(m n) kept where a kept-refused member is met | complete (marker in `Why::recheck`) | none |
| K90 | `types/bdd.rs` `Part::xor_at_once`, `xor::inner`, `InnerTable`, `Owned::release` | frames first; six expressions per node | O(1) xor test first; inner table | entry kept while the xor lives | complete (review rows 132, 135) | none |
| K91 | `types/print.rs` `surfaces_by_name`, `named`; `unfold.rs` `Show`; `zedc-types` `write_parts` | — | linear, each node written once | none | not needed: linear, no tradeoff | none |
| K92 | `types/print/defs.rs`; `Printer::collect`; `check/mod.rs` `lay_out` | — | linear, visited set | none | not needed: linear, no tradeoff | none |
| K93 | `types/empty.rs` `Searching::morphisms`, `rep` | no bound (did not end) | linear in the group | — | not needed: termination fix, standard bound | none |
| K94 | `types/empty.rs` `holds_known`, `optimistic_values` | — | three-valued test, same cost; one more search only before a refusal | refusal costs up to twice the search | complete (marker at `optimistic_values`) | none |
| K95 | `types/empty/refused.rs` `refused_site` | every repair re-checked, O(m n) | skip the repair holding the member once an earlier one left it to the search, O(m + n) | none | partial: comment gave the naive cost, no marker or used cost | added marker before the repair loop |

### Part D: Front end rows F1 to PA-let-block

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| F1 | zedc diagnostics rendering | render per use, repeated | render once | none | not needed: standard implementation | none |
| F2 | zedc-elab elab/walk.rs StmtKind::Function | each default copied into every call, exponential | one definition `f$x` per default | one more definition per default | missing | comment added (with F23) |
| F3 | resolve/stage topological order | — | Kahn's algorithm, O(V+E) | none | not needed: standard algorithm | none |
| F4 | zedc-stage stage.rs `Frees`, `Scope` | free/effects per node, Vec of bound names, O(k³) | one summary per shared node, `by_name` O(log k) | summary memory per node | stale (row named `Index`, `Mins`) | comments added at `Frees`, `Scope`; row note added |
| F5 | zedc-zir canon/mod.rs `canonicalize`, `inversions` | stepwise rules O(B·t·d); bubble sort O(F³); pairwise inversions O(F²) | one-walk rename O(t log t); sort/dedup O(F log F); merge sort O(F log F) | test checks equality with the stepwise rules | missing | comments added |
| F6 | zedc-check check/mod.rs `Ck.log` | clone `Info` per try, O(F·U) | undo log, cost = writes | log memory | stale (signature search removed) | comment added; row note added |
| F7 | zedc-resolve resolve/tables.rs `order` | `uses_in` over nested scopes, O(uses·depth) | grouped uses + binary search, O(uses log n) | — | missing | comment added |
| F8 | zedc-base source.rs `Lines` | decode from byte 0 per offset, O(k·N) | line starts + binary search, O(log lines) + line length | column still O(line length) (F30) | partial: no marker, naive or row ID | comment added |
| F9 | zedc-stage stage.rs `Cones` | `Unit::close` per row, O(rows·unit) | index built once, worklist + visited set | index memory | missing | comment added (with F41) |
| F10 | zedc-syntax format.rs `Formatter.comments` | scan of comments per node | BTreeMap by offset, O(log c) | — | missing | comment added |
| F11 | zedc-syntax format.rs `Formatter.pieces` | string copy per level, O(N·depth) | pieces joined once, O(N) | — | missing | comment added |
| F12 | zedc-resolve resolve.rs `Resolution.patterns` | scan, O(elses·binders) | range map | — | missing | comment added |
| F13 | zedc-stage stage.rs `Frees` | `free_in` with Vec, O(t·depth) | per-node summary with hash-consed `Sets` | — | stale (`free_in` gone) | comment at `Frees`; row note added |
| F14 | zedc-syntax lex/string.rs `decode` | linear scan of cuts | sorted cuts + binary search | precondition: cuts sorted, disjoint | missing | comment added |
| F15 | zedc-syntax lex/string.rs `Holes` | scan per hole | `Holes` index | — | missing | comment added (with F63) |
| F16 | zedc-resolve resolve.rs `visible`, `Bound.signatures` | scope chain walk O(depth); pairwise O(K²) | stack per name O(1); hash set | — | stale (kept O(K·U) fixed by F46/F49) | comments added; row note added |
| F17 | zedc-types ty.rs `Ty::union`, `meet_rest` | pairwise compare | hash sets | kept Θ(n²) from type size in if-chains | missing | comments added |
| F18 | (removed) check signature search | 2^depth | — | — | stale (code removed in a494377b) | row note added |
| F19 | — | — | — | — | not needed: standard implementation | none |
| F20 | zedc-base cost.rs `frontier` | all pairs, O(P²·devices) | lexicographic sort + frontier compare, O(P log P + P·F·devices) | quadratic when F = P | partial: doc explained it, no marker or row ID | comment added |
| F21 | zedc-types ty.rs `Ty::without_loose` | complement of all atoms, O(n) per step | `(set − atoms) ∪ (set ∩ family)`, O(f log n) | — | missing | comment added |
| F22 | zedc-types ty.rs `Ty::union_all` | fold one at a time, O(n²) | one pass with one hash set | — | missing | comment added |
| F23 | zedc-elab elab/walk.rs map `at` | position scan, O(args·params) | name→index map | — | missing | comment added (with F2) |
| F24 | zedc-syntax ast Display | String per part | write into formatter | — | not needed: standard implementation | none |
| F25 | zedc-stage stage.rs `mix_keeping` | list scan of roots, O(defs·roots) | hash set | — | missing | comment added |
| F26 | zedc-stage stage.rs `ends`/`Reader` | list search, O(n·depth) | `Reader` numbering parts by `Shared::id` (row ENDS) | — | stale (no name→stack map) | row note added; comment owned by row ENDS |
| F27 | zedc testing (port writes) | O(ports·writes) | map of first write | — | not needed: site not found in crates/zedc/src/testing.rs or zed-rt; row unverified | none; flagged |
| F28 | zedc-types ty.rs `Vars` | search of list, O(v²) | set beside order | — | missing | comment added |
| F29 | zedc-check check/mod.rs `reasons`, `derive_into` | scan of shown notes, O(R²) | hash set | one copy per note | missing | comments added |
| F30 | source.rs column count | — | O(line length) per offset | — | not needed: not a fault | none (named in F8 comment) |
| F31 | — | — | — | — | not needed: not a fault | none |
| F32 | zedc-check check/walk.rs `check_with` | per-call recompute | results shared per unit | — | missing | comment added |
| F44 | tests/src/scaling.rs harness; types/bdd.rs `Part::forced` | — | harness fix | — | not needed: test harness; `Part::forced` belongs to kernel parts B/C | none |
| F34 | check `+` | — | superseded by F77 | — | not needed: superseded | none |
| F33 | zedc-preimage product.rs Scope projection | Vec + structural compare, O(P²) | `HashSet<&Formula>` | — | stale? no `HashSet<&Formula>` in product.rs now | none; flagged, not resolved |
| F35 | zedc-syntax parse/engine.rs `Entry.reads_seed` | every rule stale at each growth, quadratic | only seed-reading entries go stale, linear | flag per entry; 1.2-1.7x parse time; loop-before-fail and growing lookahead still quadratic | missing | comment added |
| F36 | same as F35 | — | linear | — | missing | covered by F35 comment |
| F37 | parse, builder, formatter, Drop | recursion | explicit stacks, same order | none | not needed: same complexity | none |
| F38 | zed-tools | — | O(n) per item | — | not needed: standard | none |
| F39 | zed/corpus/ref p14 | — | O(n log n) Delaunay MST | — | not needed: reference program, standard algorithm | none |
| F40 | — | — | checked | — | not needed: checked row | none |
| F41 | zedc-stage stage.rs `Cones` | copies + key printing, O(rows·reached) | `Arc` terms | — | missing | comment added (with F9) |
| F42 | zedc-stage stage.rs `Specializer` | O(splits·unit) | one mix + per-split body mixes | — | missing | comment added |
| F43 | — | copy | copy removed | — | not needed: copy removal | none |
| F45 | — | — | checked | — | not needed: checked row | none |
| F46 | zedc-resolve resolve.rs `Ref::Bound` | Vec copy per use | `imbl::Vector` sharing | — | missing | comment added |
| F47 | — | copy | copy removed | — | not needed: copy removal | none |
| F48 | — | — | checked | — | not needed: checked row | none |
| F49 | zedc-resolve resolve/tables.rs `ListKey` | O(U·K) | U + K grouped by shared list | colliding unshared lists compared by content | missing | comment added |
| F50-F54 | — | — | checked | — | not needed: checked rows | none |
| F55 | check::read::parse_type | — | O(n), by design | — | not needed: standard single pass | none |
| F56 | — | — | checked | — | not needed: checked row | none |
| F57 | zedc-types ty.rs atom printer (payloads) | whole set per payload atom, O(p·n) | one difference, O(p log n) | — | missing | comment added |
| F58 | zedc mutate.rs `apply` | `with_child` rebuild, O(size·depth) | one copy + `child_mut`, O(size) | — | partial: existing comment at mutate.rs:342 covered only the "not run" precision tradeoff | comment added at `apply` |
| F59 | — | — | checked | — | not needed: checked row | none |
| F60 | zedc-syntax ast/builder.rs `Bare` | names listed per rejection, O(chains·source) | `OnceCell` set once per source | one set held | missing | comment added |
| F61 | — | — | checked | — | not needed: checked row | none |
| F62 | many passes | recursion | explicit stacks | — | not needed: same complexity | none |
| F63 | zedc-syntax lex/string.rs `Holes` | scan of line breaks | binary search, O(log B) | — | missing | comment added (with F15) |
| WIDEN | zedc-check check/widen.rs | — | O(N) DFS with explicit stack | existing comment at :503 is a precision tradeoff | not needed: standard DFS | none |
| WIDEN-test | zedc run.rs `write_warnings` | — | one loop | — | not needed: standard loop | none |
| F64 | — | — | checked | — | not needed: checked row | none |
| F65 | zedc-check check/walk.rs `apply_one` | scan per variable, O(v·a) | grouping in one pass, O(a + v) | — | partial: plain comment, no marker or row ID | comment added |
| F66 | Ty::write printer | String per level | one String | — | not needed: standard implementation | none |
| F67 | Sig::write, parse_type | — | O(n) | — | not needed: standard | none |
| F68 | zedc-types ty.rs `Scope` (printer) | fresh names from `T` again per rename, O(renames²) | map of stacks, set, one counter | skipped name never reused | partial: field docs, no marker or row ID | comment added |
| F69 | check `adopted`, `equal` | — | own stacks, O(n) | — | not needed: standard walk | none |
| F70 | preimage `Pa::plus` | — | precision fix (summary of `n + n`) | — | not needed: precision fix, not a faster algorithm | none |
| PA-let-block | zedc-preimage product.rs `seen_fresh` | caches left stale, Θ(d²) | caches rebased, O(differing entries · log n) | precondition: `x` fresh | partial: doc explained it, no marker or row ID | comment added |

### Part E: Front end rows from PA-let-check to the end of the section

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| PA-let-check | zedc-check check/walk.rs:`Ck::summarized` | a summary per test, O(d) each, O(d²) (0.23 to 19.4 G instr.) | one summary per binder in `Arms::summaries`, O(d) (0.16 to 2.54 G) | memory until the walk ends; summary keeps the input types where first read | missing | added doc paragraph |
| PA-let-stack | zedc-preimage product.rs:`struct Run` | recursion, overflow at about 670 bindings on 2 MiB | boxed futures on a heap stack, O(d) heap | within 1.4x in time (3.18 vs 2.27 s; 4.51 vs 4.52 s) | missing | added comment |
| PA-bind-cost | zedc-preimage product.rs:`struct Product` | deep copy per path insert, O(s log n), about 70 KB a binding | `Arc` sharing, copy on write, O(log n) (1,201M to 733M instr.) | an indirection; `Arc::make_mut` copies on write | missing | added comment |
| PA-let-narrow | product.rs:`Scope::bind_summarized`, walk.rs:`Ck::summarize_value` | — | — | precision fix; its one tradeoff (`Scope::summarize`) is covered at `Scope::atom_names` and by PA-walk-multi | not needed: precision, no cost | none |
| PA-let-multi | zedc-preimage preimage.rs:`struct Sep` | `pa_bounds` of every input per read, O(k), Θ(d²) | `Sep::tot` plus `Shift`, O(log k) | a `Tb` per term; `tot` None binds without narrowing (precision); a scaled sum reads fresh, O(h log h) | missing | added comment |
| PA-let-narrow-many | zedc-check walk.rs:`Ck::read_image` (and `Sep`) | O(k) per read, Θ(d²) (2,275 / 132,867 term bounds) | persistent treap updated at the differences, O(m log k) (323 / 2,563) | one read kept per binder; fresh read at naive cost when differences reach the inputs | missing | added doc paragraph |
| PA-walk-multi | zedc-preimage product.rs:`Scope::holds` | each input checked per read, O(k), Θ(k²) (1,680 / 103,040) | read from last read, O(m log k) (158 / 1,278) | `Reads` never freed during a walk; a lock; fresh read at naive cost | missing | added comment |
| PA-letpre-linear | zedc-preimage product.rs:`Scope::term_read` | every input bounded per test, Θ(k²) (3,200 / 204,800) | tree of term bounds plus `Sums::wants`, O(log k) per inverted term | a tree per summary id; terms not read whole always inverted; identical on 800 random sums | missing | added comment (residual `Tx::marks` already had one) |
| F71 | zed-tools spec.rs:`sections` | — | one pass, hash map of counts | — | not needed: standard O(n) pass | none |
| F72 | zedc order.rs:`items`, `Items::keep_names` | — | one hash map of queues per name, O(i) | — | not needed: standard O(i) | none |
| F73 | zedc elab:`cycles` | — | Tarjan on an explicit stack, O(n + e + c log c) | — | not needed: standard algorithm | none |
| F80 | zedc-check check/mod.rs:`struct Origin` | origins, reasons, notes put into words when recorded, O(type printed) each | data in O(1), words only when a reported derivation reaches it | data keeps types alive until the check ends | partial: doc said lazy, no naive/used costs | added comment |
| F81 | tests l01_29 `stable` | — | O(u) checks | — | not needed: standard, test code | none |
| F84 | zedc unit.rs / resolve | — | hash-map index, O(U + (E + N) log N) | — | not needed: standard maps | none |
| F85 | zedc-check `join` | — | union-find, O(L·α(N)) | — | not needed: standard union-find | none |
| F83 | zedc-stage stage.rs:`Frees` and `Mixer::mix` | the term read as a tree, O(2^d) for d levels of shared parts | each part summarized once by node id, O(P log P); mix memo by (node id, map), O(Q log Q), heap stacks | one summary per node and a mixed part per (part, map) until the mix ends | partial: `Frees` comment cited F4/F13 only; `Mixer::mix` doc had no naive cost | added F83 and naive cost to `Frees`; added comment at `Mixer::mix` |
| WORDS-minmax | zedc resolve `WORDS` | — | constant tables | — | not needed: O(1) | none |
| ENDS | zedc-stage stage.rs:`ends` | read as a tree, O(2^k) for k levels of shared arms | each distinct part once by id on an explicit stack | one entry per distinct part | partial: doc had used cost, no naive cost (the existing tradeoff comment covers the refusal, row C20) | added naive cost to doc |
| F74 | zedc-check check/mod.rs:`handled` | — | union-find (gone) | — | stale: code replaced by F117's Tarjan | COMPLEXITY.md row F74 fixed (marked superseded by F117); F74 cited at `handled` |
| F75 | zedc-check check/mod.rs:`outside_of`, walk.rs:`first_taking` | — | one union per part in post-order | — | not needed: the standard walk | none |
| F76 | zedc-check `refused`, `pass_at` | — | O(A) set differences, map lookups | — | not needed: standard | none |
| F117 | zedc-check check/mod.rs:`handled`; zedc-resolve `Resolver::flow` | each binder's own walk, O(B + R + E) unions per binder | Tarjan once, O(B + R + E) unions | union cost grows with distinct atoms named | partial: row ID missing | added row IDs F117, F74 |
| F119 | zedc-check walk.rs:`Ck::join_narrowed` | passes until no change, O(n²) (inferred) | sort once, two passes, O(n log n) | precondition: links run older to newer | partial: doc had used cost only | added comment |
| BODY-display | zedc ast/body.rs:`body_block` | — | O(1) per brace | — | not needed: O(1) | none |
| KINDS | lexer, parser, `Denote` | — | O(n) per type | — | not needed: standard | none |
| BINDER-type | zedc-resolve `bind`, `names_type` | — | constant table | — | not needed: O(1) | none |
| CMDLINE | zedc run.rs:`words`, `arguments` | — | O(n log n) sort once | — | not needed: standard | none |
| RECORD-address | zedc `Ports::address` | — | one canonicalizer pass | — | not needed: standard | none |
| ENV-port | zedc run.rs:`Environment::new` | — | `BTreeMap`, O(n log n) | — | not needed: standard | none |
| F77 | zedc-types ty.rs:`struct Facts` | variables worked out at each depth, O(n³) nested tuples, O(n²) lambdas | `OnceLock` memo per signature, linear | three `OnceLock`s; clone starts empty; `Eq`/`Hash` ignore it | partial: doc only, no costs | added comment |
| F78 | zedc query.rs keys | — | full encoded keys in place of hashes | slower lookup, for correctness | not needed: precision fix, no faster algorithm | none |
| F79 | zedc cost.rs:`frontier`, `pick` | — | lexicographic order | — | not needed: precision fix | none |
| F82 | zedc-syntax ast/node.rs:`Type::and_operands` | nested intersection copied at each depth, O(n²) bytes, on thread stack | operands gathered once on a heap stack, O(n) | none | missing (candidate part covered at ty.rs `every_arrow_fits`) | added comment |
| F86 | zedc-syntax parse/engine.rs:`Parser::call` | hash map, O(1) with SipHash | scanned `Vec` list per position, O(2R) worst, 4.6 to 13.6 average | cost bounded by the grammar | partial: explanation present, no tradeoff label or naive/used form | added comment |
| F87 | zedc-types ty.rs:`mask_text` | — | O(1) | — | not needed: O(1) | none |
| F88 | zedc-syntax grammar.rs:`Reader::within` | — | — | — | complete | none |
| F89 | zedc-types ty.rs:`struct Row` | row by value walked each level, O(n²) | shared node with facts kept, O(1) copy and read | facts made with every row; a reference count | missing | added comment |
| F90 | zedc-check check/mod.rs:`Class::known` | scan of `uses` per use, O(n²) | hash map by kind, O(1); merged small into large | an entry per distinct use | partial: doc only, no costs | added comment |
| F91 | zedc-check `narrowed` | — | O(1) per test | — | not needed: O(1) | none |
| F92 | zed-tools cite.rs | — | hash sets, O(n) | — | not needed: standard | none |
| F93 | zedc-types ty.rs:`merge` | insertions alone, O(n² log n) | insertions and diff interleaved | factor two; disjoint-set family still O(n² log n) (open, A8) | partial: doc only, no row ID | added comment |
| F94 | zedc elab `row_call` | — | hash map, O(a) per row | — | not needed: standard | none |
| F95 | zedc-types `held_function`, `unchecked_function` | — | row memo (covered at `Row`, ty.rs memo at hidden-variable comment) | — | not needed: uses the F89 memo | none |
| F96 | zed-kernel print.rs | — | O(n) | — | not needed: standard | none |
| F97 | zedc-types ty.rs:`rebuild_tys` | row entered once per path, O(2^n) | memo per row, shape and function, O(distinct parts) | memo held until the walk ends | missing (hidden-variable memo had its own) | added comment |
| F98 | zedc-check `tuple_at` | — | O((n + m) log m) | — | not needed: standard | none |
| INCR-script | tests l01_30 reuse.rs | — | hash maps | — | not needed: standard, test code | none |
| F99 | tests oracle predictions | — | O(1) per program | — | not needed: nothing to fix | none |
| F100 | zedc-check `payload`, `Ty::shapes` | — | clone removed | — | not needed: a copy removed, the standard form now | none |
| F109 | zedc-types ty.rs:`Row::kernel` | walk into components per call, O(2^n) | made once with the row, O(1) read | every row pays and keeps it | partial: doc had naive cost, no used cost or row ID | added comment |
| F103 | zed-tools imports.rs | — | — | — | complete | none |
| F102 | zedc-check `repairs` | — | at most 4 trials per argument | — | not needed: O(1) | none |
| F105 | zedc work.rs | — | O(1) per mark | — | not needed: O(1) | none |
| F106 | zedc-types ty.rs:`struct Shape` | payload by value, O(n²) | shared node, O(1) copy | a reference count; change builds a new node | partial: doc only, no costs | added comment |
| F107 | tests/src/oracle.rs:`counterexamples` (and `bindings`) | each row searching every failure; `Unit::get` and a new `Cones` per binding, O(n²) | one `Cones` per unit, ordered map, O(n log n) | map of references | partial: the stop-walk comment cites F107, the map had none | added comment |
| F108 | tests l01_07 readme | — | O(n) | — | not needed: standard | none |
| F112 | tests l01_07 mathlib.rs | — | O(n) | — | not needed: standard | none |
| STEPS-split | zed-tools step_targets.rs | — | sorted set, hash set | — | not needed: standard | none |
| DIAG-suppress | zedc suppress/addresses.rs:`Content` | — | — | — | complete | none |
| DIAG-suppress-rest | zedc suppress `InFile` | — | O(p) per file | — | not needed: standard | none |
| DIAG-addr-rest | zedc `Package::report_on_disk` | — | as DIAG-suppress | — | not needed: standard | none |
| DIAG-addr-root | zedc place.rs:`Place::of` | — | O(q) per file | — | not needed: standard | none |
| ISSUE1-tvar-else | zedc-check walk.rs:`Ck::apply_many` | a state per combination of pieces, O(p^a) | states merged by (arrows, `ClassAt`), O(a p s A) | s can double the count by arrows alone | partial: doc said "a state per pair", no costs | added comment |
| F101 | zedc-types `merges` | — | digest comparison | — | not needed: standard | none |
| ATOM-payload-open | zedc-types ty.rs:`Ty::closed`, `Shape` | walk with no visited set, O(2^n) | flags kept in each row and shape | as F89, F106 | missing | row ID and naive cost added to the `Shape` comment |
| IS-chain-quad | zedc-check check/mod.rs:`joined` | copy at each join and re-narrowing, O(k²) | small onto large, O(k log k) | `VecDeque` in place of `Vec` | partial: doc had used cost only | added comment |
| TY-subst-stacks | zedc-types ty.rs:`rebuild_tys` | recursion per level | explicit heap stack | constant factor | missing | added comment (with F97) |
| TY-sub-stack | zedc-types ty.rs:`struct Comparing` | — | — | — | complete | none |
| TY-refuse-exp | zedc-types ty.rs:`Comparing::fitted` | each comparison run again, O(2^depth) | verdict per pair of names, linear | an entry per pair until the comparison ends | partial: doc had naive cost only | added comment |
| TY-write-stack | zedc-check check/mod.rs:`Denote::ty`; zedc-types ty.rs:`drop_types`, `Sig::facts`, `Sig::digest` | recursion, overflow at 8,000 nested lambdas | heap stacks, O(n) | constant factor (+2.6%) | partial: `Denote::ty` complete; drop, facts and digest had none | added comment at `drop_types` |
| MSG-never-collapse | zedc-check `emptied` | — | O(t), printed messages only | — | not needed: standard | none |
| MSG-never-expect | zedc-check `explain_empty` | — | O(t) | — | not needed: standard | none |

### Part F: ZIR, lowering and run-time rows (Z, R, HEAP, PRE-stack and others)

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| Z1 | `zedc-zir zir/lower.rs` `Job::Closure` branch of the `let` case (two-owner closure) | inline the lambda at every call, c^k nodes | one `lambda` node, an `apply` per call threading port states, O(1) nodes per call | calls not specialized; a name used once is still inlined | missing | added cx comment |
| Z2 | `zedc-zir zir/lower.rs` `Lower::add` (with `canon::node_key`, `region_key`) | encode the whole subtree per new node, O(n) per node, O(n²)–O(n³) | key hashed from the shell and the regions' keys, each node hashed twice | shells compared on a key hit; shapes held to the end | partial: doc gave the used cost only, no naive | added cx comment (with Z19) |
| Z3 | `zedc-zir zir/canon.rs` `canonicalize` | one rule step at a time, restart from the top, O(k²) | one pass, each edge and pattern once, O(k) + O(F log F) per edge | precondition: every rule reads one edge or pattern | missing | added cx comment |
| Z4 | `zedc-zir zir/memory.rs` `plan` | questions re-asked per region, O(k·d²), paths O(d²) bytes | occurrence numbers, answers kept, preorder links, O(occurrences + edges) | answers held until planning ends | partial: doc gave the used cost only | added cx comment |
| Z5 | `zedc-zir zir/memory.rs:741` `partition_point` | `rposition`, O(n) per lookup | binary search over sorted bases, O(log n) | none | not needed: binary search over a sorted array is the standard form | none |
| Z6 | `zedc-zir zir/lower.rs` `Scope` | scope searched linearly, O(S) per lookup | superseded by Z12: persistent map | see Z12 | missing (as Z12) | covered by the Z12 comment at `Scope` |
| Z7 | `zedc-zir zir/lower.rs` `node` capture merge | `contains`/`position`, O(raw·unique) | map from source edge to position, O(1) per capture | none | not needed: a hash map index is the standard form | none |
| Z8 | `zed-native tables.rs` `const_at`, `lambda_at` | linear search, O(C²), O(applies·lambdas) | `BTreeMap` of constants, `Vec` by plan index | none | not needed: standard index | none |
| Z9 | `zed-native tables.rs` `Tables::visit`, `codegen.rs` `Gen::walk` | node clones with paths, O(N·depth); recursion | `Arc` regions, numbers, explicit stacks | stack O(d) for running a term d deep | not needed: a copy removed and the required explicit-stack form | none |
| Z9b | `zedc-zir zir/lower.rs` `Lower::bring` | edge carried through every region per read, O(d²) | `Frame::brought`, stop at the nearest holder, O(1) amortized | one map entry per region per edge | partial: plain comment, no naive cost, not in cx form | rewrote as cx comment |
| Z10 | `zedc-zir zir/validate.rs` state-use count | search, O(S²) | count map | none | not needed: standard hash count | none |
| Z11 | `zedc-zir zir/lower.rs` `body_uses` | read each body with nested lambdas, O(n·depth) | uses kept per body by occurrence id, nested bodies' uses added | uses of every body held | missing | added cx comment; COMPLEXITY.md Z11 said "kept by the body's address", code keys by occurrence id: row fixed |
| Z12 | `zedc-zir zir/lower.rs` `Scope` | vector scope copied per in-place call, O(n·S) | `imbl::HashMap`, O(log S) lookup, O(1) keep and swap | slower lookup constant, allocation per binding | partial: doc said "at no cost", no naive or complexities | added cx comment (Z6, Z12) |
| Z13 | `zedc-zir zir/lower.rs` `Frame::states` | search of ports used, O(n·P) | map per frame | none | not needed: standard map | none |
| Z14 | `zed-native codegen.rs` `Loc`; `zedc-zir zir/memory.rs` `Machine::check` | words in registers live across calls, O(n²) allocation; full audit per step, O(steps·heap) | stack slot per word, load per use, linear; check of touched cells, audit only on a fault | a store and load per word, 16-byte slot per word; every count write must record its cell | partial: `Loc` doc named the cost only; `check` none | added cx comments at both; field and port maps and the `Lets` port set are standard, none |
| Z15 | `zed-native lib.rs:65` `isa` | Cranelift e-graph and backtracking allocator, n^1.6 and n^1.4 | `OptLevel::None`, single pass, linear | slower code | complete (in review table) | none |
| R1 | `zed-rt heap.rs` `Cell::value` | copy each input into the kernel and back per call, O(n²) for n calls | value kept per cell until freed | memory of one kernel value per cell; relies on live cells never changing | partial: doc cited R1, no naive or complexities | added cx comment at `Cell` |
| R2 | `zed-native hooks.rs` `shape` (with `node`) | payload through the kernel per atom, O(n²) per list | atom built from words, shape kept per node | kernel's atom rules written twice | missing | added cx comment |
| R3 | `zed-rt heap.rs` `Entry::parts` | parts pushed per match, O(matches·size) memory | parts entered once, read in place | entries never freed | missing | added cx comment at `Entry` |
| R4 | `zed-kernel text.rs` `Size` | count characters per `len`, O(n) per call | counts kept per node, O(1) | two words per node | partial: module doc only | added cx comment at `Size` |
| R5 | `zed-kernel text.rs` `Text::join` | flatten on each append, O(n²) for n appends with reads | persistent finger tree, O(1) amortized / O(log m), never written out | `flat` copies per call; up to `LEAF` bytes copied per join; `TooLong` refusal | partial: doc and module doc gave used cost only | added cx comment (cites C29; the C-row fork may also touch this file) |
| R6 | `zed-rt heap.rs` free list, `release_one`, `value` | no reuse, O(allocations) memory; filter per part; DAG read per path | free list with generations; one pass; value kept per cell | table entries never freed | not needed for the free list and `release_one` (standard forms); DAG read covered by the R1 comment at `Cell` | none |
| R7 | `zedc-zir zir/memory.rs` arm modes | deep copy of an unused binder | no copy | none | not needed: a gratuitous copy removed | none |
| R8 | `zed-rt heap.rs:720` `Heap::dec` | allocate a stack per call | early return, reused stack | constant factor only | not needed: constant factor, same order | none |
| R9 | `zed-native hooks.rs` `Lets::closures`; `zedc-zir zir/memory.rs` `Lets::closures`, `Machine::tree`; `zed-rt heap.rs` `Heap::fresh` | closure walked per path, 2^d; a cell per occurrence, 2^d | term per closure kept by cell; cell per shared sequence by identity | one map entry each; equal sequences built apart stay apart | partial: docs cited R9, no naive or complexities | added cx comments at all four sites; explicit stacks need none |
| R10 | `zed-rt stack.rs:65` `Stack::new` | segmented stack, a compare per call | one reservation | refused under `RLIMIT_AS` | complete (in review table) | none |
| PRE-stack | `zed-kernel frames.rs` `Stack` | plain recursion on the thread stack, overflow at depth 1,000–3,000 | boxed frames on a heap `Vec`, O(1) per call | 11% time, more peak memory | missing | added cx comment; COMPLEXITY.md row pointed at `store/preimage.rs`, now `zedc-preimage/src/preimage.rs`: row fixed; module doc `store::preimage` fixed |
| R11 | `zed-native lib.rs` `Jit` guard | leak on failed compile | guard frees | none | not needed: a leak fix, no algorithm | none |
| R12 | `zed-rt heap.rs` table | — | measured, no free list | — | not needed: measurement only | none |
| MATCH-fn-binder | `zed-native hooks.rs` `matched`; `zedc-zir memory.rs` `Machine::matched` | — | O(1) per binder, correctness fix | — | not needed: correctness fix | none |
| R13 | `zed-rt heap.rs` `Heap::is_in` | make the whole value, O(size) per test | meet with the kind, answer with no read when all or none | partial `t` pays the meet and the read | partial: doc described it, no complexities | added cx comment |
| Z16 | `zed-native codegen.rs` `dispatch` | a test per block, O(k) | Cranelift `Switch` | none | not needed: standard jump table | none |
| Z17 | `zedc-zir zir/validate.rs` path buffer | path string per node, O(n·depth) bytes | one buffer, `truncate` | none | not needed: standard form | none; COMPLEXITY.md row named `zir/mod.rs`, code is in `zir/validate.rs`: row fixed |
| Z18 | `zedc-zir zir/canon.rs` `normal_edge` | swap rule step by step, O(F²) steps | `sort_unstable` + `dedup`, O(F log F) | none | not needed: sort is the standard form; doc states the cost | none |
| R14 | `zed-rt heap.rs` `survivors` (feature `counts`) | — | O(c log g) listing, by design | — | not needed: new code at standard cost | none |
| Z19 | `zedc-zir zir/lower.rs` `Lower::add`, `Frame::seen` | chain of nodes per key, O(k) confirmations | `BTreeMap` by `canon::Shape`, O(log k) | key never trusted alone; shapes held | partial: doc gave used cost, no naive | covered by the cx comment added at `add` (with Z2) |
| Z20 | `zedc-zir zir/text.rs:1480` `family` | pairwise key check | sort, refuse least repeated key, O(n log n) | none | not needed: sorting to find duplicates is standard | none |
| Z21 | `zed-native exe.rs`, `link.rs` | — | linear decode and plan | — | not needed: new linear code | none |
| Z22 | `zedc-zir zir/binary.rs` name checks | — | O(length) per name | — | not needed: new linear code | none |
| Z23 | `zed-native link.rs` `runtime_of`, `build_id` | — | linear reads | — | not needed: new linear code | none |
| Z24 | `zedc-zir zir/text.rs` generated binders | — | O(length) per binder | — | not needed: new linear code | none |
| Z25 | `zedc-zir zir/legalize.rs:169` | hash-consed, O(distinct regions) | each use, O(graph as a tree) | memo by address banned | complete (completed in review) | none; the preorder numbering and bit set are standard |
| Z26 | `zedc-zir zir/binary.rs` `W::magnitude`; `canon/serial.rs` `magnitude` | decimal digits, about n^1.5 in bits | 64-bit limbs, O(n) | bytes not readable as a number; content addresses changed (VERSION 4) | partial: doc said "decimal digits cost more than linear", no naive measure, not cx form | added cx comments at both |
| Z27 | `tests/steps/l01_35_mlir_study/mod.rs` `variants` | — | one pass | — | not needed: new linear code | none |
| Z28 | `zed-native link.rs` `Identity` | — | linear hashing | — | not needed: new linear code | none |
| Z29 | `zed-native link.rs` `sweep` | — | O(e) | — | not needed: new linear code | none |
| RUNTIME-build-src | `zed-native sources.rs` `of` | — | visited sets, O(B + M + F log F) | — | not needed: standard visited set and sort | none |
| Z30 | `zed-native link.rs` `dependencies`, `Inputs::of` | — | hash set by (device, inode), linear | — | not needed: standard hash set | none |
| R15 | `zed-alloc-count` `live`; `tests/src/layout.rs` counts | — | O(1) per allocation, visited set | — | not needed: standard forms | none |
| HEAP-binder-paths | `zed-kernel paths.rs` `Paths`, `Kept` (used by `zed-rt heap.rs` `matches`, `release`) | path copy per binder, O(d²) | parent-linked nodes, kept tree built once, O(nodes + kept) | reading a path back O(depth), messages only | partial: doc named the d²/2 avoided, no used cost, not cx form | added cx comment at `Paths` |
| HEAP-binder-memory | `zed-kernel paths.rs` `Paths`, `Kept` (used by `zedc-zir memory.rs` `binder_paths`, `Machine::release`) | as HEAP-binder-paths | as HEAP-binder-paths | as HEAP-binder-paths | partial (same site) | covered by the comment at `Paths` |

### Part G: Tradeoffs, Crossovers and Kept sections (C, F and other rows)

| Row | Site (file:fn) | Naive version, complexity | Used version, complexity | Tradeoffs | Before | Action |
|---|---|---|---|---|---|---|
| C1 | presburger.rs (row records a precision limit) | — | — | — | not needed: precision loss, no faster algorithm | none |
| C2 | presburger.rs `products`, `Tier` | exact products of variables | opaque atom bounded by intervals | products not related | complete (reviewed) | none |
| C3 | zedc-lattice/src/lattice.rs `impl Lattice for Type::widen` | no widening, infinite ascending chain | widen to whole base type, each part changes once | loop types lose gained members | complete (reviewed) | COMPLEXITY.md row pointer fixed: `store/product.rs` → `store/lattice.rs` `Lattice for Type` |
| C4 | zedc-lattice/src/lattice.rs `impl Lattice for Type::narrow` | narrow to any smaller part, infinite descending chain | each part changes at most once | `1 \| 2` narrowed by `1` stays | complete (reviewed) | COMPLEXITY.md row pointer fixed as C3 |
| C5 | zedc-preimage/src/product.rs `reduce_domains` | fixpoint to exhaustion | bounded rounds | less precision | complete (reviewed) | none |
| C6 | product.rs `enumerate` | full enumeration | bounded split | refusals | complete (reviewed) | none |
| C7 | (row) | — | — | — | not needed: precision rule, no algorithm below naive | none |
| C8 | zedc-lattice/src/interval.rs `narrow`; lattice.zed:129 | as row | as row | as row | complete (reviewed) | none |
| C9 | lattice.rs Congruence `widen` ~213; lattice.zed:209 | as row | as row | as row | complete (reviewed) | none |
| C10 | interval ends (TD-ends) | — | unbounded ints | — | not needed: no faster algorithm | none |
| C11 | affine.rs ~535 | as row | as row | as row | complete (reviewed) | none |
| C12 | affine.rs ~489 | as row | as row | as row | complete (reviewed) | none |
| C13 | affine.rs ~513 | as row | as row | as row | complete (reviewed) | none |
| C14 | preimage.rs union ~4625 | as row | as row | as row | complete (reviewed) | none |
| C15 | preimage.rs ~136 | as row | as row | as row | complete (reviewed) | none |
| C16 | preimage.rs `project` (HC4) ~6546 | joint narrowing | each operand alone | precision | complete (reviewed) | none |
| C17 | preimage.rs `mod_pre` ~11118 | as row | as row | as row | complete (reviewed) | none |
| C18 | preimage.rs `enumerate` ~11192 | as row | as row | as row | complete (reviewed) | none |
| C19 | `POWER_FACTORS` (removed by CAP-power) | — | — | — | not needed: code removed | none |
| C20 | stage.rs `ends` ~211 | as row | as row | as row | complete (reviewed) | none |
| C21 | (row) | — | — | — | not needed: nothing given up | none |
| C22 | (row site) | as row | as row | as row | complete (reviewed) | none |
| C23 | (removed) | — | — | — | not needed: code removed | none |
| C24 | zedc-solvers utvpi.rs race ~278 | as row | as row | as row | complete (reviewed) | none |
| C-WIDEN | zedc-check check/mod.rs ~503 | as row | as row | as row | complete (reviewed) | none |
| C25 | interval.rs `bit_word` 587, 628 | as row | as row | as row | complete (reviewed) | none |
| C26 | check/mod.rs `known` ~5260, check/arms.rs | as row | as row | as row | complete (reviewed) | none |
| C27 | zedc-base cost.rs 129 | as row | as row | as row | complete (reviewed) | none |
| C28 | check/mod.rs ~5313 | as row | as row | as row | complete (reviewed) | none |
| C29 | zed-kernel text.rs 100, 378 | as row | as row | as row | complete (reviewed) | none |
| C30 | zedc-preimage address.rs 418 | as row | as row | as row | complete (reviewed) | none |
| C31 | zed-kernel num.rs `read_digits_by`, num/fast.rs `to_decimal`, `gcd` | O(n²) schoolbook | subquadratic | crossovers timed | complete (reviewed) | none |
| C32 | trivial.rs 357, 682 | as row | as row | as row | complete (reviewed) | none |
| C33 | types.rs 1408 | as row | as row | as row | complete (reviewed) | none |
| C34 | ty.rs 176; walk.rs 3072, 3216 | as row | as row | as row | complete (reviewed) | none |
| MSG-line-quote-cost | zedc/src/front.rs `rows` | each item against every row, O(i·r) up to O(i²); a line quoted per step O(s·L) | min-heap, O(i log i) | heap memory O(r) | missing | added `Complexity tradeoff:` at `rows` |
| MSG-line-quote-nested | front.rs `layout` ~264 | as row | as row | as row | complete (reviewed) | none |
| C35 | (row) | — | O(size) | — | not needed: nothing given up, O(size) | none |
| C36 | zedc-check check/walk.rs `apply_demanding` | demand analysis per body and arrow with a fixpoint | `Demand::All`/`First` only, O(arguments) | an argument of no value is not told apart when the body would not read it | missing | added `// Complexity tradeoff:` before `let unneeded` |
| C37 | zedc-presburger conjuncts.rs `StarIndex::place`; zedc-preimage product.rs `Scope::settle` | (place) each hub near y needs all m names, k·m needs, O(d²); (settle) each stale leaf projected alone, O(leaves × core) | (place) anchor, k−1+m needs, O((k+m) log n) per move; (settle) one projection per class, O(classes × core + leaves × log classes) | memory for anchor/hits; per-class memory until the call ends; refused leaves projected alone | missing | added comments at both sites |
| OMEGA-cycle-growth | presburger.rs `cycles` ~7462 | as row | as row | as row | complete (reviewed) | none |
| NUM-subquad (4 rows) | zed-kernel num/fast.rs `MUL_LEAF`, `DIV_LEAF`, `GCD_LEAF`, `PRINT_LEAF` | schoolbook O(n²) | Toom/transform, Newton, half gcd, divide-and-conquer printing | timed crossovers, identical results | complete (reviewed; fast.rs 593, 646, 834, 1093, 1375) | none |
| KERNEL-leaf-digits (4 rows) | zed-kernel num.rs `LEAF_DIGITS` | num-bigint parse O(n²) | split by powers of ten, O(n log² n) | timed crossover | complete (reviewed; num.rs 1074) | none |
| BIGINT-fast-mul (2 rows) | num/fast.rs `mul` | num-bigint product | `MUL_LEAF` handoff | timed crossover | complete (reviewed; fast.rs 593) | none |
| SCALE-fix-crossover | num/fast.rs `MUL_LEAF` | as above | as above | as above | complete (reviewed) | none |
| Fourier–Motzkin pairs | presburger.rs elimination ~2716 | eliminate every variable, pairs grow | eliminate only when no terms are added | atoms kept, refusals | complete (reviewed) | none |
| undeclared parameters (check), `apply` | zedc-check check/mod.rs `struct Class`, walk.rs `Ck::merge` | search over signatures, contexts, carrier combinations (F6, F18), exponential, capped | union-find by rank, smaller list into larger, O(N log N) | no path compression (finds O(log N)); repairs undo from a log of touched roots | missing | added `Complexity tradeoff:` on `Class` |
| emptiness and subtyping | zed-kernel types/empty.rs, ty.rs `verdict` | complete decision, coNP-hard | sound, not complete; named refusals | refusals | complete (reviewed; 31 markers each file) | none |
| `axioms::of`, AXIOMS-order | zedc axioms | — | constant table | — | not needed: O(1) in the program | none |
| BIT-axioms harness | `check_word`, `check_shift` | — | fixed instance set | — | not needed: test of a table | none |
| `ieee_min_max` | zed-kernel value | — | O(1) | — | not needed: constant work | none |
| scaling `Meter`, `os` | zed_tests::scaling, zed_alloc_count::os | — | fixed work | — | not needed: no program-size dependence | none |
| `zed_alloc_count` `count` | zed-alloc-count/src/lib.rs `count` (Linux) | one count per thread, sum at read: O(1) per allocation, O(threads) per read | walk of the thread chain, O(d) per allocation, O(1) read | allocation cost grows with d (about 3, tests only) | missing | added `Complexity tradeoff:` at `count` |
| `words` `utf8` etc. | zed-kernel words | array | persistent map, O(n log n) | L1 has no arrays | not needed: standard for the data structure available | none |
| `bits` `mulHi` etc. | zed-kernel bits | — | O(1) per word | — | not needed: constant work | none |
| F104 | (row) | — | — | — | not needed: standard | none |
| XMARK `mark_failure`, `no_arrow_at_carrier` | zedc testing, check | — | linear | — | not needed: standard | none |
| F110 | (row) | — | — | — | not needed: standard keyed lookup | none |
| F111 | (row) | — | — | — | not needed: standard | none |
| MSG-words `said` | l01_21 test `rows` | — | linear | — | not needed: test helper, standard | none |
| K75 | zed-kernel value.rs `Value::selects` | compare by paths, O(paths), 2^d | `items_eq` with pair table keyed by ids, O(distinct pairs) | table memory | missing | added `// Complexity tradeoff:` (may overlap fork C, which covers K rows) |
| F113 | check/mod.rs `one_shape_per_length` ~6407 | as row | as row | as row | complete (reviewed) | none |
| F114 | (row) | — | — | — | not needed: standard | none |
| F116 | as F113 | as row | as row | as row | complete (reviewed) | none |
| T11-unit-share (`run::program` etc.) | run.rs | — | `Arc` sharing | — | not needed: sharing, standard | none |
| F126 | (row) | — | — | — | not needed: standard | none |
| F115 | (row) | — | — | — | not needed: standard | none |
| F118 | zedc-types ty.rs `struct Same` | derived `==`, O(paths), 2^n; stack overflow at 100,000 levels | union-find, O((n+m) α) | table memory; address keys sound only while operands are borrowed | missing | added `Complexity tradeoff:` |
| F120 | (row) | — | keyed dedup | — | not needed: standard hash lookup | none |
| F121 | (row) | — | — | — | not needed: standard | none |
| F122 | (row) | — | — | — | not needed: standard | none |
| F123 | zedc-types ty.rs `struct Via`; walk.rs `floor`, `floor_on`, `floors_at` | each need holds its own chain and notes, O(n) per wrapper, O(n²) (control: 28.4 times bytes) | shared links, O(1) per wrapper, notes only on error | chain lives as long as any need holds a link | missing (doc said O(1) hashing only) | added `Complexity tradeoff:` on `Via` |
| F124 | ty.rs | as row | as row | as row | complete (reviewed) | none |
| F125 | (row) | — | — | — | not needed: standard | none |
| F127 | ty.rs | as row | as row | as row | complete (reviewed) | none |
| F128 | zedc-types ty.rs `struct Pairs` | recursion, O(paths), 2^n, overflow | heap frames + memo by pair addresses, O(distinct pairs) | memo memory; boxed-future constant factor | missing | added `Complexity tradeoff:` |
| F129 | zedc pin.rs `Pins` (~299); zedc unit.rs `unit_address` | (Pins) hash map + sort at write; (address) each unit addressed per import, O(i × t) | (Pins) ordered map O(log p); (address) memo by unit index, O(t log t) | memory of one address per unit | partial: `Pins` had it, the memo by unit did not | added `Complexity tradeoff:` at `unit_address` |
| F130 | (row) | — | — | — | not needed: standard | none |
| F131 | trivial.rs (as C32) | as C32 | as C32 | as C32 | complete (reviewed, C32 comments) | none |
| F132 | ty.rs | as row | as row | as row | complete (reviewed) | none |
| F133 | ty.rs | as row | as row | as row | complete (reviewed) | none |
| F134 | (row) | — | explicit stack | — | not needed: project rule, standard | none |
| F135 | zedc-check check/mod.rs `adopted` | read a decimal at `rat` per tried repair, O(n^1.47) each | `rough`: type `rat` without reading digits, O(n) | a repair needing the exact value not offered | complete (reviewed) | none |
| F136 | (row) | — | — | — | not needed: standard | none |
| F137 | (row) | — | topological order / SCC | — | not needed: standard | none |
| F138 | zedc-presburger presburger.rs `decide_kept` (1385), `tighten` (8616, 8448), `learn` `none` (3349) | each bisection question re-runs the whole search | kept points answer questions; backward disjunct order | learning still O(k³) in chain length | complete (reviewed) | none; worse than n log n recorded below |
| F139 | (row) | — | — | — | not needed: standard | none |
| F140 | zedc-check check/walk.rs `Ck::components` | every pair of tuples, recursively: O(n²) pairs, O(n³), 2^n on shared rows (39.9 s at 800 shapes) | union per position + visited set of type pairs, O(n) | set memory; failures reported per union, each piece once | partial: doc explained naive and used, no marker or tradeoffs | added `Complexity tradeoff:` paragraph |
| F141 | (row) | — | — | — | not needed: standard | none |

## Summary

| Status before | Rust markers (302) | Outside (11) | After this review |
|---|---|---|---|
| complete (references counted when their target is complete) | 253 | 10 | complete |
| partial | 48 | 0 | complete: the missing costs added |
| missing | 0 found | 0 | |
| stale | 1 (`tests/.../extend.rs:129` named `Extending::answers`) | 1 (`revision.zed` pair bound) | complete: pointer and bound fixed |

Among the sites this review read, COMPLEXITY.md rows that disagree with the code: none. S4 and S14 give the `map2` pair
bound as 4(k + 2), as the code does; the comments in `revision.zed` and above `revision.rs`
`map2` said k + m and were fixed.

The search by COMPLEXITY.md row (CX-tradeoff-krows, section above) checked all 477 rows,
the K rows this review left open among them. "missing: 0" in the table above counted only
the sites this review read; the search by row found more:

| Status before, by row (477) | Rows | After |
|---|---|---|
| complete | 120 | complete |
| partial (no naive cost, no used cost, or no tradeoffs) | 67 | complete: the missing parts added |
| missing (a faster algorithm with no comment at its site) | 101 | complete: comment added |
| stale (the comment or the row named code that moved) | 9 | complete: pointer fixed |
| not needed (standard code, open or kept rows, no faster algorithm) | 178 | none |
| other (two rows whose status cell holds an escaped `\|`) | 2 | as their rows say |

COMPLEXITY.md rows that disagreed with the code, found by the search by row. In every case
the code was right and the row was fixed:

- A wrong cost, algorithm or site: K1 (decision lists, O(1) complement), K11, K15, K22,
  K41 (NTT, O(n log² n)), F4, F6, F13, F16, F18, F26, S22 (ENDS), PRE-stack, Z11, Z17.
- Stale pointers to moved code: K2, K48 (`bdd::order`, now `order`), K17, K27, K33, K38, K39, K49, K53 (`Key::order`), K56,
  K62, K63, K65–K68, K72, GROUP-admit-msg, F27 (`rows.rs` `wave`, the `written` map), F101
  (`zedc-types/src/ty.rs` `merges`), C3, C4 (`store/lattice.rs` `Lattice for Type`), S12
  (`Tx::enter`); line numbers removed from S1b, S2, S4, S5.
- Superseded: F33 (by L1.39: the conjuncts now sit in the persistent set `Conjuncts::set`),
  F74 (by F117); a fragment of F70 split off as its own line was joined back.
- A duplicate, older S22-fwd-holes row was removed; S19 gained a new measurement (`preimage`
  of `i != 1 && … && i != k` under `true`, k = 384 against 3072: 8.0 times the instructions
  and the bytes, limit 11.88), so the `!=` chain it records is now linear.

Cases still above O(n log n) met by the search are all recorded already: F138
(PRES-settle-chain-rounds), F93 (question A8), F97 (question A20), K36, K83, S47, Z26,
`Part::settle` (L1.23) and `zed_alloc_count` `count` (O(d) per allocation for a thread chain
of length d). Some costs in the new comments are inferred from the code, not measured, and
say so: K37 naive, K60 O(d²), F119 naive O(n²), F68 naive, F57, the `Class` union-find without
path compression, S13 widening precision, S8 undo order and S38's point.
