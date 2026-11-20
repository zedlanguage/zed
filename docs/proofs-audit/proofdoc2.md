# Proofs in code comments: audit of proofdoc2 (DOC-proofs-in-comments-audit-rest)

This table covers the rest of proofdoc1a's crates (zed-kernel, zed-numtheory, zed-collections,
zed-graph, zed-native, zed-rt, zed-alloc-count, zed-clif, zed-tools, zedc-zir, tools/), and the
two rows the first pass filed and this agent closed: FAIL-rt-fault-mprotect-signal-safety
(zed-rt `on_fault`) and TYPES-run-marks-move-safe (zedc-types `RunMark`). The checker crates are
in [proofdoc2b](proofdoc2b.md), and the front-end crates, zed-cert and zed-meter-settings are in
[proofdoc2a](proofdoc2a.md).

Sources, in order. (1) The commits since 2026-11-01 that touch these crates and whose messages
name a proof, lemma, invariant or derivation: `git log --since=2026-11-01 --format='%h %s' -i -E
--grep='proof|prove|lemma|invariant|derivation' -- <crates>`, 187 commits. Of these, 26 are
already rows of proofdoc1a.md. Thirteen messages were read in full and their sites checked (rows
below). (2) The ledger and the running log, searched with `command grep -a -i` for proof, proved,
not proved, bound and invariant together with these crates' names. This found CANON-confluence
and the sum and roots code of zed-kernel `poly`. (3) A grep of these crates' src for `not proved`,
`Assumption, not proved` and `measured, not proved` (25 lines). Each hit was read at its site and
matched to a plan row, or to an argument at the site that no answer rests on the claim. Sites
were checked on main at cf4648fff, and the poly and canon sites again after the rebase on
beeb2b261.

Counts per crate (found / already there / added or completed / marked unproved / corrected):

| Crate | Found | Already there | Added | Not proved | Corrected |
|---|---|---|---|---|---|
| zed-kernel | 25 | 20 | 1 | 2 (row named at the site) | 0 |
| zedc-zir | 3 | 1 | 2 | 0 | 1 |
| zed-rt | 1 | 0 | 0 | 0 | 1 |
| zedc-types | 1 | 0 | 1 | 0 | 1 (Not proved replaced by a proof) |
| zed-alloc-count | 1 | 1 | 0 | 0 | 0 |
| zed-clif | 1 | 1 | 0 | 0 | 0 |

One fault was found and fixed. zedc-zir canon/domain.rs `Domain::normal` kept a class given as
`Congruence::Class { modulus, residue }` as written, with no `Congruence::new`. So `4 mod 9` and
`1 mod 4`, the same class of integers, had two normal forms and two addresses when the domain
had no finite set. The fix normalizes the class, and the test is
`m0_07_canonicalization::domains::a_class_built_with_its_fields_has_the_normal_form_of_the_same_class`:
the pairs (4, 9), (4, -3), (-4, 1) and (-4, 9) against `Congruence::new(4, 1)`. It fails with
the old line (residue 9 against 1) and passes with the fix. No address made today changes. The
only class built from its fields outside `new` is zedc-preimage product.rs `framed_class`, `0 mod
1`, which is already normal.

Not swept: 156 of the 187 commits, neither rows of proofdoc1a nor read here. The vendored imbl
patch cdc2c76e1 was read as a message only; its diff was not checked. The commits not read:

e204348f4 8e3867d18 09287a709 0797f08e9 19311b3fe 86150ff67 9ad003d0c f91eac49c 8596f59ce
f075a1c0b fad56b903 002cb0cce be476c3a4 929e7e04a 3dbee8ea8 570acb0a8 cb68d7fec e3ee7d064
8878228af 7cd0c9e58 0a3429bfa f2329fde4 c9205d30b 1a78001da 2ab9f29af fe770de11 5484ed5fc
c5168f1b3 46897f128 fed6e73e4 90117acd2 432f2d455 c53a7410d a1704042b b8802ec53 3256dd649
ac8f22b35 00171c62b e5b5ea82e 6bb9bb93f ba41f402c d67def0d2 35cbbb966 71100fdf0 fe5968d36
60f594a97 a74161bb4 465fc2167 6567a6bfe 1ba844398 f31c2310a 6017477df 1eaf7b0bb 1a51ce141
7740e3ac7 b5643d1b2 d4541f819 f48ec1bf4 28541d398 ddc1ec274 0b1008760 5e7dc557b 8b55fc92c
8183b743b 7b7a83c4b 0e8168cc1 87553695b f86104e1d 3204ef377 e62be00e0 34a583731 de439fba5
2ba5d8788 56e9e1fc6 3ac71c151 9bc1e50d4 26e179519 9379f755c d81f448e5 a02d270c5 3189a1922
197c7de2b 25c813fcd 4c7dac8b4 1a9277873 0ae743c85 badba0482 222adf91b d2bc324d2 fa271b3f2
f24b492bf 10cc98a38 32acdc5eb 80870e234 9e3cc1480 63eccf955 a52bd454f 1b18cee1c 5ec318c98
3ffbadf75 475e582ff 0b3c8f079 e60e73504 9778881e0 18ebecd2f 5a5276a82 f0bde0d35 5dcfdad0a
fc7cfde43 b8b284a09 83e0f8843 521de84af d9d8729bb 26f8d7d35 3a7b10812 86322e10b 6b87a1c3a
7d0cc8d9f f8b286311 5e95a07dc 6ae1d9048 1679fe8c6 59a32b29b 81a60d522 8c2710fc5 e7b12dd2e
e4f209295 b602e0cde afbdffe42 d18e52a0a b037a40ba d694e2a26 51ae6534c 5d72f0689 299e38768
6ebe63b42 7d9e078c0 8abbc466e 9f8961b3b b691d27f5 40733faeb 94b14f925 5970a932f 00a508032
bea44d4a5 37148785d 2de401ae4 86b17eae2 6ff237028 bc75c1615 877fc8603 1f50505a3 8c5ccccb9
1fcf49287 181885f72 967100aca

| Source | Claim | Code site | Status |
|---|---|---|---|
| proofdoc1a, row FAIL-rt-fault-mprotect-signal-safety | the stack fault handler is safe in a signal handler | zed-rt stack.rs `on_fault` | corrected (cf4648fff): `mprotect` is now made as the system call itself (inline `syscall`, x86_64 number 10; `svc 0` with number 226 on aarch64, which was not compiled here) and `errno` is saved and restored, with the argument at the site |
| proofdoc1, row TYPES-run-marks-move-safe | a mark's signature is found at the address it names after a move | zedc-types ty.rs `RunMark` | corrected (ea2e24555): a root's own marks carry `RunMark::ROOT` (0, which no `Arc` address is), a held function's marks the address of its `Arc`; the field is private and read through `RunMark::holder(&Arc<Sig>)`; the Not proved paragraph is replaced by the proof; test `run_marks_name_a_new_signature_at_the_address_of_one_dropped` and its control |
| ledger, CANON-confluence (zed 0c093f6) | the rules give one normal form in any order | zedc-zir canon, DESIGN M0.7 | already there (row CANON-confluence Done; tests `rules::the_normal_form_does_not_depend_on_the_order_of_the_rules`) |
| ledger, CANON-confluence | the one walk of `canonicalize` gives the rules' normal form | zedc-zir canon/mod.rs `canonicalize` | added: part by part (domain by `Domain::normal`, facets sorted and deduplicated, body by nameless forms, which each rule step keeps, per the argument in the binders module comment); a free name written as a level is refused by `refuse_free_level` |
| ledger, CANON-confluence | the domain normal form is a function of the admitted set, so idempotent | zedc-zir canon/domain.rs `Domain::normal` | added (three steps) and corrected: a class built from its fields was kept as written (fault above) |
| a60a0ab47 | a written sum chain is read as one sum in O(T log k) | zed-kernel poly.rs `Poly::sum` | added: the bound with cancellation, by induction on the merges, from the monotonicity of the optimal merge cost and Huffman's theorem (Huffman 1952, "the two least probable messages") |
| running log, poly/roots | the branch and bound keeps few intervals | zed-kernel poly/roots.rs module comment and `positive_roots` | Not proved; both sites now name plan row ROOTS-interval-bound (open, in the needs of L1.41-join-zed-kernel-numeric) |
| 0cc69f311 | a list that implies another absorbs it | zed-kernel types/bdd.rs `absorbed`, `implies_by_blocks` | already there (the lemma and both cases at `implies_by_blocks`) |
| 10c13b7c7 | the kept height bounds are never stale | zed-kernel types/empty.rs, the doc at line 211 | already there |
| 6a42df78d | a class piece may keep the wide component box | zed-kernel types/empty.rs, the cut by classes | already there (proof that the answer is the same, at the tradeoff comment) |
| ca431e71b | the `expect` in `Rat::pow` cannot fire | zed-kernel num.rs `Rat::pow` | already there |
| bc76a4833, adeb362b3, 030a2d36d | treap priorities from a 5-wise independent family; the expected bounds | zed-kernel priority.rs, types/bdd/set.rs | already there (Seidel and Aragon, Wegman and Carter, quoted); "the OS random bytes are uniform" is Not proved, row PROOF-sweep-zed-kernel |
| 2f4e801e2 | plan and COMPLEXITY.md only | none | no code claim |
| grep | equal rows hash alike while `hash::blind` runs | zed-kernel types.rs `impl Hash for Row` | Not proved at the site; row PROOF-sweep-zed-kernel (in the needs of L1.41-join-zed-kernel-correct) |
| grep | no caller depends on a meet now "not known finite" | zed-kernel types.rs `Finiteness` | Not proved at the site; row PROOF-sweep-zed-kernel |
| grep | the box walk of `meet_rows` ends | zed-kernel types.rs `Finiteness::meet_rows` | Not proved at the site; rows PROOF-meet-rows-finite and PROOF-sweep-zed-kernel (both in the needs of L1.41-join-zed-kernel-correct) |
| grep | `digest` agrees with `==` in every form | zed-kernel value.rs `impl Hash for Value` | Not proved at the site (ASSUME-documented); row PROOF-sweep-zed-kernel |
| grep | a map read as a list by `may_be_list` has the keys `0 ..< n` | zed-kernel value.rs `may_be_list` | Not proved at the site; row PROOF-sweep-zed-kernel. A map with keys 0, 0.5 and 2 passes, and `Prim::ListConcat` (eval.rs) then joins it as a list, a wrong value; only the checker's typing of `++` keeps such a map out |
| grep | the memory limit in the repair is reached before the machine runs out | zed-kernel value.rs, the memory repair | Not proved at the site; cost and message only; row PROOF-sweep-zed-kernel |
| grep | `held` is the run's bytes | zed-kernel limits.rs `held` | Not proved exact at the site; rows MAIN-limits-count and PROOF-sweep-zed-kernel |
| grep | the memory asked for before a wide division | zed-kernel num.rs `Rat::div_euclid` | already there: measured, and the site says why no quotient rests on it (a figure too low turns a refusal into the allocator's abort) |
| grep | absorbing on equal digests costs little | zed-kernel types/bdd.rs, line 4234 | already there: measured, cost only |
| grep | a bench's mean at m = 2048 | zed-kernel types/bdd/bench.rs line 603 | already there: no bound rests on it |
| grep | `is_empty` is a function of the type alone | zed-kernel types/empty.rs, the fork search | Not proved at the site (ASSUME-documented); row PROOF-sweep-zed-kernel |
| grep | a value `Filer` files as listed is in the column type | zed-kernel types/empty.rs line 4996 | Not proved at the site; row PROOF-sweep-zed-kernel |
| grep | every cycle of the texts passes through a definition | zed-kernel types/print.rs line 725 | Not proved at the site (ASSUME-documented); row PROOF-sweep-zed-kernel |
| grep | the 64 TiB reservation is enough | zed-alloc-count meter.rs `RESERVED` | already there: the site says why no answer rests on it |
| grep | Cranelift's cost per function | zed-clif lib.rs `generate` | already there: time only, and the site says why |
