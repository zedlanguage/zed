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
