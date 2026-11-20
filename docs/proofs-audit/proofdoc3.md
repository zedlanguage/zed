# Proofs in code comments: audit of proofdoc3 (DOC-proofs-in-comments-audit-rest-2)

Author, STANDING, 2026-11-20: "also you must add proofs and reasoning in the code comments too".
This third pass reads what the second pass listed as not read (row
DOC-proofs-in-comments-audit-rest-2):

- the 156 commits of [proofdoc2](proofdoc2.md) "Not swept" (142 of them touch zed-kernel);
- the entries of [proofdoc2b](proofdoc2b.md) not read: its 28 at score 4 or more and the 382
  below. Its scoring cannot be rebuilt from its description, so this pass reads a superset:
  every entry (one commit in one crate, `git log --since=2026-11-01 6b9edf7fb -- crates/<crate>`
  for zedc-check, zedc-base, zedc-elab, zedc-types, zedc-presburger, zedc-preimage,
  zedc-solvers and zedc-int, less the commits named in proofdoc1.md and proofdoc1b.md) whose
  message matches `proof|prove|bound|invariant|derivation|derive|lemma|argument` at least once,
  less the commits in proofdoc2b's table: 820 entries, which hold the 28 and the elab parts of
  e5ff7920a and 7931d6ed6;
- [proofdoc2a](proofdoc2a.md)'s high-ranked zedc and zedc-syntax commits whose code moved out
  of those crates: the 39 commits since 2026-11-01 (to 6b9edf7fb) that changed a file of
  crates/zedc or crates/zedc-syntax that no longer exists, at score 3 or more on proofdoc2a's
  keywords (`proof|prove|bound|invariant|derivation|lemma|cannot|never|exact|argument`);
- the sites proofdoc2a names as not traced: zedc unit.rs `pinned` and `write_pins`, zedc-syntax
  builder.rs the hole taken once, and the grammar-shape `unreachable!`s and `expect`s;
- 80870e234 (PROOF-treap-digest-priorities), which proofdoc2b did not follow.

Commits after 6b9edf7fb are outside this pass. The work is split over three helpers, each with
its own section below: proofdoc3a (zed-kernel, read only, as kernel24 and kernel25 own it; the
lower crates; the front-end crates' part of the 156; zedc-preimage; 80870e234; the untraced
sites), proofdoc3b (zedc-check, zedc-elab, zedc-base; the moved commits), proofdoc3c
(zedc-types, zedc-presburger, zedc-solvers, zedc-int). Each claim a verdict rests on is proved
at its site, every step in a comment; or broken by a program, fixed with a test red first; or
marked Not proved at the site with the open sub-case.

## proofdoc3a: zed-kernel (read only), lower crates, front-end crates, zedc-preimage, untraced sites

Not yet written.

## proofdoc3b: zedc-check, zedc-elab, zedc-base, and the moved commits

Not yet written.

## proofdoc3c: zedc-types, zedc-presburger, zedc-solvers, zedc-int

The list holds 373 entries (one commit in one crate): 140 in zedc-types, 198 in
zedc-presburger, 18 in zedc-solvers and 17 in zedc-int, ordered by score. This pass read 12
of them, 11 in zedc-types and 1 in zedc-int, in order of score, each message and each site it
names. It also completed one zedc-solvers site that no entry read here names. The sites were
read on 46b9d5d88 and checked again after a rebase onto origin/main of 2026-11-20 (9ffbe5a4d).
The pass then stopped, for lack of room: it started no new entry, and the rest are listed
under "Not read:". A first triage of more entries, done by helpers that were stopped on
order, is not used here, as its verdicts were not checked against the code.

| Crate | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|
| zedc-types | 11 | 1 | 10 | 0 (2 sub-steps of 1 entry, under PROOF-sweep-zedc-types) | 0 |
| zedc-presburger | 0 | 0 | 0 | 0 | 0 |
| zedc-solvers | 0 (1 site outside the list) | 0 | 1 | 0 | 0 |
| zedc-int | 1 | 0 | 1 | 0 | 0 |

| Source | Claim | Code site | Status |
|---|---|---|---|
| 4a5668e7d | A bounded variable beside another variable is bound only to a piece its bound holds; the binding branch through a mask never names one carrier | zedc-types ty.rs `accepts` | Added: the claim, facts F1 to F4 with where each holds, the proof by branch, and a new test `l01_26_type_resolution::bounds::a_bounded_variable_beside_a_variable_of_one_carrier_takes_each_carrier_of_its_bound`. Two facts stay Not proved at the site: F2, that nothing shrinks a binding, and F3, that no outer binding holds a name a nested `fits_in` forgot; both under the existing row PROOF-sweep-zedc-types, named at the site |
| 988743bce | A bounded variable only a function parameter holds fits under any name | ty.rs `Cx::through_fn` | Completed: the tests named, and what they cannot catch |
| 4345e1690 | An arrow of `q` with a parameter type proved empty asks for no cover, so `Never -> v` and `Never ->? v` are each within the other | ty.rs `covers` | Completed: the test named; a type empty but not proved so gives only a wrong no |
| 9d5317f7c | A meet of functions is empty by the kind of a value; `inhabited_fn` cases | ty.rs `Domains::kinds_apart`, `Domains::inhabited_fn` | Completed: the tests named |
| 4497c4c31, 38a070dad | Functions over function domains that differ, or over functions whose results share no value, meet empty | ty.rs `Domains::fns_apart` | Completed: the tests named |
| bdc3a1160 | A bounded variable of a partial arrow's value type narrows at each carrier | ty.rs `Narrowing` | Completed: the test named |
| e7f92635c | An arrow of a variable of several carriers is permitted at each carrier | ty.rs `instances` | Completed: the tests named; only a wrong no is given up |
| aa40b6049 | Members pinned by the ceilings are matched as the rule of one shape matches them | ty.rs `Pins::lists` | Completed: the randomized test named, and what it cannot catch |
| ef56f8c84 | The index of a binding's variables is kept as the binding changes and answers as one made anew | ty.rs `Binds` | Completed: the test named; it checks answers, not cost |
| 84e65bf61 | Two chains of calls compare link by link; only the first call is hashed | ty.rs test `two_chains_of_calls_are_equal_link_by_link`, `impl Hash for Via` | Already there: the doc, the `Hash` impl and the test's assertions agree |
| 843ceb28f | No prime below `FILTER_BOUND` is 1 modulo an index above `FILTER_BOUND / 2`, so such an index needs its own prime | zedc-int int.rs `FILTER_BOUND` | Added: the proof (the indices are odd primes, so `q = k * p + 1` odd needs `k` even, `q >= 2p + 1 > 1025`) and the test named |
| (none; site met in reading negsssp) | One edge relaxed per call is Dijkstra's relaxation, exact as `ell` is at least 0 | zedc-solvers negsssp.rs `Search::relax_one` | Added: the argument, the citation (Dijkstra 1959, doi:10.1007/BF01386390), and where `ell >= 0` is made |

No code claim: none found among the 12 entries read.

Not read:

- zedc-types (129): 2143bead4, 1233ccd22, f3970ac46, f2297a652, 13e376cb7, 5d9bad32b, bbae90d38, 09f77b6f3, 37dad5731, ced805157, 08e6206a4, 18cc11692, 475e582ff, 62c5ace4b, 64eede4ce, 76705768a, 7da6fc4a6, e7180d4db, 69844cb07, 7fc4ac500, 922be74e7, afbdffe42, d4ce3868b, e70d43315, f26b8a8e5, 2981d4645, 83920e1d6, 83a509ae3, a98079c36, b59ca2ae8, bcb0fcb93, c38724eb5, d20413aae, f0bde0d35, fed6e73e4, feeafc10c, 0d87a73ca, 0e50ec37c, 25ef78dd1, 2b3e706f1, 2ec6b9418, 3189a1922, 405650a5b, 444cdb15b, 4ef43bf6c, 7028f23a2, 7d9e078c0, 995200322, 9d877b65c, a3cee3606, b623e6fe0, c1e5a82e3, d493d34a3, e5a605a6e, e82d77ca9, 1c2b6a270, 305ad0293, 400b14585, 65f995fee, 6945f496b, 6e2e39396, 6ebe63b42, 701def5c6, 875e58597, 9778881e0, a034e80cd, a619cb307, a670bd1cb, a9443c314, af8174807, d20f8009e, ee79685e4, 01063a0ca, 03e64b6da, 148a42eb4, 1d9291f72, 22dd31a36, 27e8e2464, 2e3a7b0a4, 2f99f5283, 47be53825, 493ff031b, 6704ae0ff, 67dd99e3a, 69526a75a, 718e9ecda, 7a54c17f9, 807260a3b, 811505cca, 8412a61b4, 92a76ed89, 9b35c8ab0, 9e8f139f1, b5317f47c, b991293a4, c289ffeca, cbc003938, d2a97b1f9, e6dfb6877, eb6e0ad7f, 06d1dc49c, 08d2feda8, 0de5b565c, 205591658, 29bf6b297, 2d09ac322, 3248fbce2, 3e597380e, 3fd923c4a, 453066558, 47681f229, 47b73bd8f, 4abfd2ae1, 620307b4c, 65a9230a8, 78f2ca158, 81f3d8487, 929e7e04a, 9b5729b46, a16eb1e6e, bd7d5aa55, c1dfb00f7, d18e52a0a, d6a84bc7c, dd8b42f68, df3fa8308, e2ef08f39, ea2effe91, fb5f2416f
- zedc-presburger (198): 6ff7e1be7, 2143bead4, 42273225f, 3527c0a74, 030972c93, 80870e234, d59fb9c44, e5b5ea82e, 151c323ff, 24981fcda, 7dd6559a9, 5213e08d6, a803272fb, 09287a709, 36e8b20a6, 4033def30, 48dde176a, 6130a038d, 842e295c5, 9992e3560, 015f88415, 300df7ed3, 383cb5b66, 7bfd6bba8, 9abde2cea, ad40b4107, b467e298d, b77467075, d6fa0ddbd, d80e81d08, e22a4f8fa, 0fe50a2fc, 1ad3da05c, 1faf391fd, 1ffeb360d, 355e67f4e, 3e3db6907, 4a8d78984, 4e9bb0d27, 5c102b331, 78fdd83c1, 8ee7ea8dd, 90b8f2b61, a6562e094, e8fea7860, ea431f549, f0bde0d35, ff395d583, 181ac91dd, 1dc603590, 1ff9a3b61, 252abbb51, 25ef78dd1, 2b3e706f1, 2d1365800, 34989b330, 36279a9f9, 40bb19caa, 4b1ccff17, 53b114449, 564bef57c, 5bde6551f, 65446a377, 66e347e86, 7bdf8c1f1, 8e3867d18, 94f38f6d3, 96a4e186b, 9758548e8, 9e786fe17, a1a2a3c63, aa8366a07, ec537c0b1, ed1f1be11, f0186c022, f0ce6ac5e, f4c033ccd, f548497ad, fb9b82a6a, 030a2d36d, 136017dd7, 28a3d9acb, 32acdc5eb, 384b173ac, 4e48ee579, 54ddb1f80, 5dfd87a78, 6e72af6bd, 711b27b81, 72d5f383f, 7d23ca0c7, 7dda7ea0d, 7f771ec77, 83ebfff6e, 8575c70cc, 8590c4d2b, 889492a23, 9f8961b3b, a3273dbda, a54f1b103, aabf487cc, ac67403b3, ace60e16b, b2ba71b22, c4964f39a, d73f3c8e1, f060dbed1, f835ff861, fe770de11, 04ebcda96, 0f5f38d66, 134e107ca, 16490c8d2, 26e45260d, 295d02151, 2df2801ba, 30732fe05, 364dd4a15, 374a5823a, 3bd1b249d, 3fb4bb8e4, 47dbe05b9, 4e52a49fc, 5a5c167cf, 5eba9712b, 68416f089, 6b87a1c3a, 6d5a815dd, 7a7417966, 8780d212c, 8ecea2e9f, 9312fea5a, 9e25afa99, b991293a4, bf0be61bc, c8cac82fa, cc9e97345, cd403f3b0, d3f5e50c3, d77a6be8e, dc637c0d3, e8981310f, f17dead5b, f9936c4fe, fafbc69a5, fdb5fda2a, 0d4b0170a, 104c0e177, 11e2c2786, 12c58bd41, 141a411e3, 1a19cae20, 23ae5cdd3, 23c5a37c0, 23ce8727a, 2dfb9e87f, 2f837d6da, 34e5a4454, 3aa6326c3, 3f2a92b63, 4a9b79d02, 4c17c8e8f, 5168f5a37, 5202d9698, 5a5084526, 5ccb21f3f, 62e774ae6, 6da69df6f, 729325cd6, 81878e7cb, 8980815f3, 8bf067d56, 96dae93e0, 9b756f7ea, 9c56b1189, 9eaff655d, a7032e3f4, b3ff809f1, b87677be2, bbe8ee73e, c2f253250, c74ad4124, c80855b33, cb6445059, cc5576aea, cdc669612, cf2546144, cf65370dd, d5ae3f504, d8026ecb5, da7810c72, ecfbd2bd0, ed3971714, eea76fee4, efe9dcf29, f02739989, f3778742d, f66d9b0b1
- zedc-solvers (18): e5b5ea82e, 475e582ff, d80e81d08, 1ffeb360d, 3e4f866b5, 25ef78dd1, 2b3e706f1, 10a4e923a, b991293a4, f9936c4fe, 4c17c8e8f, 5168f5a37, 6da69df6f, 87bab4327, c6969ca91, d3608d87b, d5ae3f504, e275c5f0b
- zedc-int (16): 76bb9d4cf, 29ab1ba6e, d80e81d08, 25ef78dd1, 2b3e706f1, 878a1bf1b, fe770de11, 22e348bb9, 47dbe05b9, b991293a4, d7e7d86d0, e843dda31, fffe13699, 6cc6d3efd, 6da69df6f, cc5576aea
