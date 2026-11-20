# Proofs in code comments: audit of proofdoc1a (DOC-proofs-in-comments-audit)

Crates swept: zed-kernel, zed-numtheory, zed-collections, zed-graph, zed-native, zed-rt,
zed-alloc-count, zed-clif, zed-tools, zedc-zir, and the shell tools under tools/. Sources, in
order: the commit messages since 2026-11-01 that touch these crates (`git log --since=2026-11-01
-- <crate>`, 1096 commits; those whose messages hold proof, prove, lemma, invariant or
derivation, 181 commits, were read first), then the sites those commits name, then a grep of
each small crate for `proof`, `unreachable`, `expect(`, `SAFETY` and `unsafe` (`command grep -a
-n -i -E`). Each argument was checked at its site on the branch base a4895f607 (origin/main).
Counts per crate (rows below, looked at / edited): zed-kernel 14 / 2, zed-numtheory 12 / 2,
zed-graph 4 / 1, zed-collections 4 / 1, zed-rt 2 / 1, zed-tools 1 / 1, zedc-zir 3 / 0,
zed-native 2 / 0, tools/ 1 / 0, zed-alloc-count 1 / 0, zed-clif 1 / 0. The running log, the ledger and
the reports under wt/ were not swept, and of the 181 commits only those named in the rows were
followed to their sites: the sweep is not complete.

| Source | Claim | Code site | Status |
|---|---|---|---|
| d9a6fc9a6 | `split` finds a factor of every odd composite: `c = p - 2` splits all but 25 | zed-numtheory factor.rs `split` | completed (the cases `p = 3` and `p = 5`, the batch gcd, what the tests cannot catch) |
| d9a6fc9a6 | `rem_big_u64`'s `expect`: the remainder is below the modulus | zed-numtheory lib.rs `rem_big_u64` | already there |
| zed-numtheory commits | the search of `next_prime` ends | zed-numtheory lib.rs `next_prime` | already there |
| zed-numtheory commits | the sieve's least prime factors, fewer than 3 `top` writes | zed-numtheory lib.rs `least_prime_factors` | already there |
| zed-numtheory commits | the primes of a block fit a u16 | zed-numtheory lib.rs `least_prime_factors_in_blocks` | already there |
| zed-numtheory commits | the marker table tells a shared factor | zed-numtheory lib.rs `shares_a_factor_by_table` | already there |
| e94c5eac6 | factor refinement gives the coprime base, at most 15 elements per input | zed-numtheory lib.rs `coprime_base_u64` | already there |
| zed-numtheory commits | the striking of `odd_primes_below` stops in time | zed-numtheory lib.rs `odd_primes_below` | already there |
| 63bea08ff | one subtraction reduces a product modulo 2^61 - 1 | zed-numtheory lib.rs `m61::mul` | already there |
| 63bea08ff | `fold8` reduces a sum of eight residues with one subtraction | zed-numtheory lib.rs `m61::fold8` | completed (the callers' premise, what the test cannot catch) |
| 63bea08ff | the eight-byte table hash equals Horner's rule | zed-numtheory lib.rs `m61::PolyBytes` | already there |
| zed-numtheory commits | the inverse modulo 2^61 - 1 | zed-numtheory lib.rs `m61::inv` | already there |
| 9a2b7a2a1 | `take` gives no number twice without a panic | zed-graph ids.rs `IdSource::take` | completed (the proof, the one-draw-early case, the test) |
| zed-graph commits | the edge that reached a node is open until its block is given | zed-graph biconnected.rs `biconnected` | already there (in the `expect` message; not checked step by step) |
| zed-graph commits | the cut-node oracle of blocks (tests) | zed-graph biconnected.rs `same_block_by_cuts` | already there |
| 9a2b7a2a1 | a rank stays an upper bound on the height, saturating only when roots are chosen | zed-graph union_find.rs `UnionFind::link` | already there |
| d79b3d56d | `refine` reads at most `2 m k` pairs, `8 m k` searches over both passes; its box is checked by `row_rep` | zed-kernel types/empty.rs `Searching::refine` | already there (the loop checked: one undo, from the pair after it) |
| a676e87d7 | the passes of `tuples_on` are at most 1 + the cells | zed-kernel types/empty.rs `tuples_on` | completed ("No test checks the bound") |
| PERF-residue-length-cost | `meeting_pair` costs O(n · max d(p)) | zed-kernel types/empty.rs `meeting_pair` | completed (where the premise is checked by the callers, the early-return case, the tests) |
| 9a60e38ed | `Atoms::minus` equals `self & !other`, by the four cases | zed-kernel types.rs `Atoms::minus` | already there |
| 9a60e38ed | `Type::minus` equals `self & !other` | zed-kernel types.rs `Type::minus` | already there |
| a056e0808 | a second sum of an unchanged map reads no entry | zed-kernel btree.rs `Map::sum` | already there |
| 7028f23a2 | `rename_apart`'s passes and its names equal the naive version's | zed-kernel types/print/names.rs `rename_apart` | already there (read, not checked step by step) |
| 2cf50d91a | the bit test is exactly "is a NaN" | zed-kernel value.rs `F64::new` | already there |
| d9a6fc9a6 | `gcd_using`'s `expect`s: `y` nonzero, `x` odd | zed-kernel num/fast.rs `gcd_using` | already there |
| e94c5eac6 | `one_wide` may stop once more than 63 bits lie outside the widest | zed-kernel num/coprime.rs `one_wide` | already there (checked) |
| 1faf391fd | the elements of a coprime base are bounded by the input bits, not 2^32 | zed-kernel num/coprime.rs `index` | already there |
| 7d0d766ad | no kernel name is `$k@j` | zed-kernel text/ident.rs `written_name` | already there (read, not checked step by step) |
| 319c6e1b4 | the split by code point ranks, (P1) and (P2) | zed-kernel text/split.rs `split_tree` | already there (read, not checked step by step) |
| 22b7172f5, 0abccafd1 | the work of `difference_if_agree` over the fixed sets | zed-kernel types/bdd/set.rs `difference_if_agree` | already there (read, not checked step by step) |
| zed-collections grep | the `n`th value's slot exists and is empty | zed-collections held.rs `Held::put` | added |
| c4937d86c | a key that holds its `Arc` keeps its address from reuse | zed-collections by_address.rs `ByAddress` | already there |
| zed-collections grep | `pred` and `succ` exist where the `expect`s call them | zed-collections intervals.rs, search.rs `above`, `below` | already there (in the `expect` messages) |
| 1faf391fd | no count is proved to fit a u32 | zed-collections index.rs `to_u32` | already there |
| zed-rt grep | the libc calls of the run's limits and stacks are sound | zed-rt limits.rs, stack.rs (`SAFETY:` comments) | already there |
| zed-rt grep | each call of the fault handler is async-signal-safe | zed-rt stack.rs `on_fault` | corrected (`mprotect` is not in signal-safety(7); marked "Not proved") |
| 3a9752389 | the join of the untyped calls costs O(p √p) | zed-tools imports.rs `untyped_imports` | added (the proof was only in COMPLEXITY.md F103) |
| a94a3d54c, 593468853 | a port read placed outside the bodies keeps the value, given the premise | zedc-zir zir/lower.rs `Lower::read_frame` | already there |
| 300cf1e58, 9b7a17570 | the facet sort's dedup drops exactly the repeats | zedc-zir canon/mod.rs `sorted_facets` | already there |
| zedc-zir grep | every string an address writes is a literal | zedc-zir canon/serial.rs (module comment) | already there |
| 0588b18b0 | no hook runs between `rt_direct` and `rt_direct_read` | zed-native codegen.rs `Gen::named_direct`, hooks.rs | already there |
| 714b348c1, 59ca62448 | making a held value early cannot fail or run code | zed-native hooks.rs | already there |
| zed-alloc-count grep | each `unsafe` block and `unsafe fn` of the counting allocator states its premise | zed-alloc-count lib.rs, meter.rs, os.rs (`SAFETY:` comments, `# Safety` sections) | already there (each `unsafe` block has a `SAFETY:` comment within six lines; of the `unsafe fn`s, `free`, `release` and `malloc` were read; not checked step by step) |
| zed-clif grep | each `unsafe` block and `unsafe fn` of the C interface states its premise | zed-clif lib.rs (`SAFETY:` comments, `# Safety` sections of `read`, `text`, `give`, `function`) | already there |
| 7792ab098, 8a2dbb805 | skipping a recorded group after a rebase is sound | tools/merge_check.sh (header) | already there (the narrowing marked "not proved") |
