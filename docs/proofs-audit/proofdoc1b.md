# Proofs in comments: audit of proofdoc1b (DOC-proofs-in-comments-audit)

This audit covers the crates zedc-check, zedc-elab, zedc-resolve, zedc-stage, zedc, zedc-syntax,
zedc-base and zedc-lattice. The sources are the commit messages since 2026-11-01 that touch these
crates (`git log --since=2026-11-01 -- <crate paths>`, 1228 commits, ranked by how often a
message names a proof, bound, invariant or argument; the highest-ranked were read first). Each
argument was checked against the code on origin/main as it is now, and the proof, the facts it
uses and the tests that check it were written as `//` comments at the code. Comments only: no
behavior, test or identifier changed. The sites of `RunMark` and of the `fwd_memo` and
`finished_with` memos in zedc-check `check/mod.rs` are left to proofdoc1. Counts (rows below):
zedc-check 28 rows (13 already there, 14 added or completed, 0 marked unproved, 0 corrected, 1
no site found, covering two commits); zedc-base 5 (2 already there, 3 added or completed);
zedc-elab 2 (completed); zedc-resolve, zedc-stage, zedc, zedc-syntax and zedc-lattice 0 so far
(zedc-lattice and zedc-syntax share the 161eba557 row); 13 rows name arguments whose code is in
another crate. No argument in the code was found wrong. One stale pointer: the test comment in
tests/steps/l08_02_remaps/empty.rs
`a_function_a_call_returns_and_runs_at_another_carrier_is_not_compiled_yet` says the proof is
at `Ck::finish`; it is at zedc-elab `Elab::check_instances` (test files were not edited).

| Source | Claim | Code site | Status |
| --- | --- | --- | --- |
| 1acea31e7 | A product of reduced fractions cancels only by gcd(p, s)·gcd(r, q); a product of coprime parts of L1 and L2 bits has at least L1 + L2 - 1 bits | zedc-check check/walk.rs `product_built` | completed |
| d0b785f06 | A power x^k with \|x\| of L >= 2 bits has at least k(L - 1) + 1 bits, so a power past the address space is refused exactly | zedc-check check/walk.rs `too_large_power` | completed |
| d0b785f06 | The product bound of `too_large_product` | zedc-check check/walk.rs `too_large_product` | already there (points to `product_built`) |
| 4c4a9aab4, 4c7dac8b4 | A read of exact keys at a key the type lists has no miss | zedc-check check/walk.rs `exact_key_read` | completed (tests) |
| 4c7dac8b4 | `KType::ints_listed` lists exactly the ints the type holds | zed-kernel | other crate: zed-kernel |
| e5b5ea82e | The remap recovers the key from its div and mod parts | zedc-check check/walk/remap.rs `recovered` | completed (tests) |
| 998cee67d, de80f3ca6 | f64 holds every int of magnitude at most 2^53, and 2^53 + 1 is the least positive int it does not | zedc-check check/walk.rs `exact_in_f64` | added |
| de80f3ca6 | `beyond_float` | zed-kernel | other crate: zed-kernel |
| c4937d86c | Address-keyed visited sets are safe: keys stay alive for the call, empty rows share one address harmlessly, the set is never iterated | zedc-check check/walk.rs `holds_fn` | added |
| c4937d86c | The same for the map of rebuilt signatures | zedc-check check/walk.rs `without_needs` | added |
| c4937d86c, ad0193034 | Address keys of compared signatures | zedc-check check/walk.rs `compared_alone`; check/read.rs `Seen::sigs` | already there |
| c4937d86c | `Approx::done` address keys | zedc-types | other crate: zedc-types |
| (walk.rs) | Two rebuildings of one place join where their tests agree; the `false` case is reached by no program | zedc-check check/walk.rs `join_coercions` | completed (tests) |
| 53ce3cfda | A memory limit is accepted exactly for 1..=2^64; the two `expect`s hold | zedc-check check/limits.rs `bytes_limit` | added |
| b4d2da96c | A class a use asked for takes its whole carrier, since the literal's own value is not enough | zedc-check check/walk.rs `resolve_top_parts` | completed (tests) |
| 3ceb4d7ab, 0a60d5977 | Family values | zedc-check check/mod.rs `family_values` | already there |
| 0a60d5977 | `Comparing::payloads_by_rest` | zedc-types | other crate: zedc-types |
| 2468c99e5 | `put_read` | zedc-check check/mod.rs `put_read` | already there |
| 0529d1886 | `coerce_forwarded` | zedc-check check/walk.rs `coerce_forwarded` | already there |
| (walk.rs) | The remap search ends | zedc-check check/walk.rs `remap_of` | already there |
| e359078b9 | Fates are judged conservatively | zedc-check check/fate.rs (module comment) | already there |
| 831f1ec0a | Lambdas in functions: rule and cost | zedc-check check/walk.rs `lambda_in_fns` | already there |
| 831f1ec0a | `Bound` trie; `Searching::empty` | zedc-types; zed-kernel | other crate: zedc-types, zed-kernel |
| d4d229225 | `met`, `Domains::meet` | zedc-types | other crate: zedc-types |
| 1679fe8c6 | log2 comparison | zed-kernel num/bound.rs | other crate: zed-kernel |
| 46897f128 | `rename_apart` | zed-kernel | other crate: zed-kernel |
| 7f18aade0 | preimage arguments | zedc-preimage | other crate: zedc-preimage |
| ab9f94b9b | Refusals placed in O(d log k); the same question at one place keeps the meet in any order | zedc-check check/walk.rs `place_refusals` | already there (order rests on zedc-preimage `product::kept_meet`) |
| 6f0f43d2f, 15657d994 | Loop class of S4; remainders read class by class | zedc-preimage | other crate: zedc-preimage |
| acc4f3aed, 1dd869737 | Arguments at old crates/zedc/src/check paths | (code moved) | no site found |
| 3871b9a96 | Brent's bound: the sum of ceil(s_i / p) is at most t + (q - t) / p | zedc-base cost.rs `brent` | already there |
| 6c82ca26a | The frontier keeps a dominated plan that ties and comes first, so the pick over the frontier is the pick over every plan | zedc-base cost.rs `frontier` | completed (two steps, tests) |
| 6aa0e1d6e | The static footprint sweep never subtracts before it adds | zedc-base cost.rs `sweep` | added |
| 6aa0e1d6e | On a device of one core the footprint of two parts at once is the larger of each peak plus the other's kept bytes, and is reached | zedc-base cost.rs `Load::interleaved` | added |
| ecf23c120 | Exact keys fix a list's count: `L = U` and the set `[0, n - 1]` give n | zedc-check check/walk/fp_ops.rs `ranks_count` | completed (step, tests) |
| ecf23c120 | The `zip` and `++` recursions over variables end | zedc-check check/walk/fp_ops.rs `zip_end`, `list_concat_end` | already there |
| bcaafb217 | A call through a partial slot outside an exact function's domain is guarded; no guard where every key is covered | zedc-check check/walk.rs `domain_guard`, `domain_test` | completed (tests at `domain_guard`; proofs already there) |
| 6bedbaa1a | Constant folds give the same verdict on every machine, since every ask is compared with a fixed bound | zedc-check check/mod.rs `FOLD_ASK_BITS` | added (rests on zed-kernel `room`, other crate) |
| 2f16e91e0 | The value of a part is the part the steps name of the caller's argument | zedc-check check/walk.rs `open_place` | completed (tests) |
| b8178145a | A cast of integer literals alone is taken at `int` | zedc-check check/walk.rs `cast_takes_int` | already there |
| 5985ac958 | A lambda in a union slot is fitted to the one function type it holds | zedc-check check/walk.rs `one_fn` | already there |
| 5985ac958 | Arrows paired in written order choose only the instance tried, never a yes | zedc-types `Cx::through_fn` | other crate: zedc-types |
| d3ae39af9, 9b45ed03a | A kept forward is named as E names it (point b); `#4-outer` refuses what the proof would need a premise for | zedc-check check/walk/r10_forward.rs (leaf-need loop) | already there |
| d3ae39af9 | Point a, the B1 skip | zedc-types `Sig::first_seen` | other crate: zedc-types |
| a934e9cf8, c390deb51, 38a7a62e6 | Signature digests, row variables and `holds_needs` memoed once per signature | zedc-types | other crate: zedc-types |
| be011d566 | A function a call returns, run later at another identity, cannot be compiled with one body per closure | zedc-elab elab/bodies.rs `check_instances` | completed (tests) |
| 161eba557 | `line_bounds` precondition; `write_sum` past i64 | zedc-base source.rs, zedc-lattice affine.rs | already there (tests and doc, no proof claimed) |
| f24b492bf | A stream over `a ..` read one entry at a time gives what the whole stream gives, since `map` and `where` act on each entry alone and keep its key | zedc-elab elab/walk/fp_ops.rs `stream_term` | completed (tests) |
