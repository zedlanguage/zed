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

Read on main at 46b9d5d88: 66 of the 243 zedc-check entries, highest score first (every entry
at score 5 or more, and the first 15 at score 4), each message in full, then the code that relies on each claim as it is on
that base. The zedc-elab, zedc-base and moved entries come after the rest of zedc-check and
are listed under "Not read" until they are read. A claim whose code lies in a crate another
helper or agent owns (zed-kernel, read only; zedc-zir; zedc-types; zedc-preimage) is recorded
as "other crate" and left to that owner. The read-only sites (`push_vars`, `vars_order`,
`Ck::fit_needs`, `Ck::bind_never`, `must_decode`) were read and their status recorded only.

| Crate | Found | Already there | Added or completed | Marked unproved | Corrected |
|---|---|---|---|---|---|
| zedc-check | 66 claims in 54 entries (7 in other crates) | 50 | 9 | 0 | 0 |

| Source | Claim | Code site | Status |
|---|---|---|---|
| 2143bead4 | `RunMark`: marks name a signature by its `Arc`'s address; a new one at a dropped one's address reads its own | zedc-check check/r10_tests.rs `run_marks_name_a_new_signature_at_the_address_of_one_dropped` (proof at zedc-types `RunMark`) | already there: the test's comment was updated by TYPES-run-marks-move-safe (ea2e24555) |
| 759ca91d4 | `in_parens`: the answer `false` is at worst a pair of parentheses more | zedc-syntax lex/mod.rs `in_parens` (moved from zedc-check fp_ops.rs) | already there (argument and unit tests in the same file) |
| 759ca91d4 | `sig_text`: a variable whose every use is a pass at a closed type takes exactly the meet of those types | zedc-check check/mod.rs `sig_text` | completed: the three steps, where the need is checked, the tests and what they cannot catch |
| bbae90d38 | An `else` whose pattern is not a plain atom passes the atom on and never meets `Boundary::Other`; the other forms are refused before the checker | zedc-check check/fate.rs `Walk::expr`, the `ExprKind::Else` arm | added: why passing on keeps every rejection, that the claim rests on the refusal of a binding pattern (and what the arm would need without it), the test and which arm it reaches |
| bbae90d38 | `scrutinee`: the arms of a `match` read in order, conservative where an arm cannot be read | zedc-check check/fate.rs `scrutinee` | already there |
| bbae90d38 | `push_vars` (b) cannot happen; (a1) reached; (a2) not proved absent, the verdict rests on no claim about it | zedc-check check/walk.rs `push_vars` (chk3's, read only) | already there |
| e5b5ea82e | `recovered`: a row left with one nonzero entry is exactly an atom whose unit vector lies in the rows' span | zedc-check check/walk/remap.rs `recovered` | already there (five steps, tests and their limit) |
| e5b5ea82e | the facet dedup compares by `Value::cmp` | zedc-zir canon/mod.rs | other crate (zedc-zir, proofdoc3a) |
| 0203fd7aa | `call_arg_ops`: the ranges still index the errors at the end of the binding | zedc-check check/walk.rs `call_arg_ops`, `group_arg_ops` | already there (the open sub-case argued harmless: a range is used only where its errors lie inside its argument) |
| 044da9bab | A bounded variable's binding widened to its carrier holds every value the call gives | zedc-check check/walk.rs `apply_one`, the widening loop | completed: why the widened result holds every value, the tests and their limit |
| 4c7dac8b4 | `ints_listed` lists exactly the ints a type holds (PROOF-ints-listed-complete) | zed-kernel types.rs `ints_listed` (read only); zedc-check check/walk.rs `exact_key_read` | already there at both |
| 7bd52fc4e | `f64(n)` is exact for an int proved within ±2^53 | zedc-check check/walk.rs `exact_in_f64` and the sites pointing to it | already there |
| a030f8984 | The O(n·k) case of `read_part` is reached by no input | zedc-check check/read.rs `read_part` | already there (three steps, tests) |
| cff28820b | A `rat` power of a nonzero base with a non-literal exponent is nonzero | zedc-check check/mod.rs `rat_step` | completed: the proof (no zero divisors in Q, both signs of the exponent), the test and its limit |
| cff28820b | `bound::cmp` asks for memory | zed-kernel num/bound.rs | other crate (zed-kernel, read only) |
| f1b8f668e | `emptied`: time and text linear in the size of the type | zedc-check check/mod.rs `emptied` | completed: the tests named, with their limit |
| 0e736f771 | A fix carried through a bound name costs O(fixes) per use, against O(program) per fix | zedc-check check/walk.rs `carried_bound`, `carried_use`, `shared_settled` | already there |
| 1679fe8c6 | Comparing kept powers with a proved `log2` error bound (Higham 2002); printing a power from its exponents | zed-kernel num/bound.rs, num.rs `integer_text` | other crate (zed-kernel, read only); the citation is at bound.rs |
| 1679fe8c6 | `kept`: folding an operation on integer literals in an `if` is O(its size) | zedc-check check/walk.rs `kept`; check/mod.rs `folded` | completed: the cost was stated in operations only; an operation that adds to a kept power builds its digits, O(b log² b) for b bits (open row LIT-power-expression); `folded`'s doc still said folding any power costs its size, which the kept powers made stale |
| 1679fe8c6 | `power_product`: reading a literal type's power costs the text | zedc-check check/read.rs `power_product` | already there |
| 0d0cca54a | The later refused literals cost one more pass, O(a) | zedc-check check/walk.rs `apply_one`, after the argument loop | already there |
| 76705768a | A list type inside `L .. U -> V` is refused, never passed unchecked | zedc-types kernel_type.rs (the bound check) | already there |
| 76705768a | `carried_lent`: at most one more check per fix that failed alone | zedc-check check/walk.rs `carried_lent` | already there (argument, the naive exponential way, rows) |
| 8164a8ea9 | A decimal literal without a suffix is exactly a `rat` | zedc-check check/mod.rs `menu` | already there (DESIGN row cited) |
| 8164a8ea9 | `f64(n)` offered where n is within ±2^53 | zedc-check check/walk.rs `exact_in_f64` | already there (see 7bd52fc4e) |
| 827095bce | Rebuilding the argument is enough: a generic body gives a value of a bare variable only from its arguments (PROOF-generic-body-values-from-args) | zedc-check check/walk.rs `coerce_forwarded` | already there (case-by-case proof, tests, cost) |
| e8266a053 | `keyspace` memo by binder in place of union-find, same O(n) | zedc-check check/walk/fp_ops.rs `Ck::keyspace` | already there |
| 06e2ab7fe | One summary per callee for all its tests, O(k) for k tests (Sharir and Pnueli 1981) | zedc-check check/walk.rs `term_for` | already there (citation with "no DOI, not found on Crossref") |
| 3b8668458 | A cast of a literal runs on at most 3 values; a power-form `rat` decided from its exponents | zedc-check check/walk.rs `word_atoms` | already there |
| 46897f128 | `rename_apart`: at most V + 2·Σ(1 + s) runs | zed-kernel types/print/names.rs (read only); zedc-check check/mod.rs points to it | already there (the zedc-check site is a pointer; the kernel comment proves the bound and a test shows the old conjecture false) |
| 80b432724 | An operand beside `Never` is still checked; a row shared by many paths visited once, linear | zedc-check check/walk.rs `compared_alone` and `apply_many` | already there |
| 83373e144 | An interval key inside the exact keys is in range; a key that is an operation on literals is that `int` at run time; exact keys in a parameter's range | zedc-check check/walk.rs `exact_key_read` and the parameter-keys branch | already there (each with its proof) |
| d80e81d08 | `bits + 7` cannot overflow in `whole_byte_width` | zedc-check check/walk.rs `whole_byte_width` | already there |
| dba724818 | `fix_bound`: one `Vars` per body, each row entered once, O(size of the types) | zedc-check check/walk.rs `fix_bound` | already there |
| e22a4f8fa | A longer path search over k tests costs k² | zedc-check check/arms.rs `Carried::longer` | already there: since made O(log s) prefixes, stated in the doc |
| e22a4f8fa | A class's stars projected again only when its leaf bound is not shown to stay | zedc-preimage product.rs `same_leaf_bound` | other crate (zedc-preimage, another helper's) |
| e70d43315 | `permitted`: exact for one parameter, sound for more | zedc-types ty.rs `permitted` | other crate (zedc-types, another helper's); the zedc-check part holds no claim |
| fc7a7365f | The argument of a forwarded need found by one lookup per variable | zedc-check check/mod.rs `CallFrame::by_var` | already there ("built once for the call in O(v)") |
| 17e5c4252 | A cast's literal repair costs O(d^1.47) once, as `word_atoms` | zedc-check check/walk.rs `literal_repair` | already there |
| 1faf391fd | No site can prove a count below 2^32; `to_u32` panics with the count | zed-collections index.rs (module doc); zedc-check coprime.rs and widen.rs call it | already there (the argument is at the shared routine; the zedc-check sites rely on no bound) |
| 2646fc090 | `read_part` O(n), O(n·k) case open | zedc-check check/read.rs | already there (see a030f8984) |
| 447df80cb | A `Read` fit at a span has one writer (PROOF-read-fit-single-writer), resting on unique spans | zedc-check check/mod.rs `put_read` | already there (four steps, the span test, the debug assertion) |
| 633705d20 | One trial call per arrow of the slot, on the error path only | zedc-check check/walk.rs `lambda_repair` | already there |
| 7940088be | Carried fixes checked in rounds, places sorted and found by binary search | zedc-check check/walk.rs `carried_*`, `arg_holding` | already there |
| 83a509ae3 | A read of a family of one interval with every key present misses with `#outOfBounds`, whatever its low end | zedc-check check/walk.rs `dense_read` | already there |
| bcb0fcb93 | Soundness: an int base under an exponent that may be negative takes no int at all | zedc-check check/walk.rs `power_on` | added: why every int base can fail (not only those below 0), where the need is made, the old counterexample and the tests |
| cb4136d17 | `powers_bound`: one pass over the class's uses, O(u); the end gives the same answer | zedc-check check/walk.rs `powers_bound` | already there |
| f0bde0d35 | Assumptions stated at their sites (term_for implicit calls, carriers_only; the coprime base's bit bound) | zedc-check check/walk.rs `term_for`, `carriers_only`; check/coprime.rs `base_of` | already there (the coprime bound now at the kernel's shared routine) |
| f83194447 | `#4-outer` is reached, each time also refused by another rule | zedc-check check/walk/r10_forward.rs, the `#4-outer` tests | already there |
| fed6e73e4 | `finished_with`: one pass with one `rename_apart`, linear | zedc-check check/mod.rs `finished_with` | already there |
| 0e329a46e | A curried call through a value calls a function right only when every parameter has one name and place in both and the left-out ones one default; else the function held places it | zedc-check check/walk.rs `unaligned` | already there (the conditions, why they make the first function enough, O(p + a)) |
| 0e50ec37c | A need alike to an earlier one may be left out of the signature: one type at every call, printed bounds unchanged, O(n + c) | zedc-check check/walk.rs `Ck::share_alike` | already there (the conditions, two proofs, the replay on failure, the cost) |
| 1286f4779 | A call that leaves out a default reading a name is placed by the callee; O(p + a) | zedc-check check/walk.rs `callee_places`, `open_left_out` | already there |
| 1614015dc | Edits matched to arguments by binary search over sorted spans; a pad not written as a format width, which takes at most 2^16 - 1 | zedc-check check/walk.rs `in_text_order`, `edits_in`, `lies_in`; check/mod.rs the fixes menu | already there |
| 1dc603590 | Meeting a name a join holds of no type with its parameter's type keeps every value | zedc-check check/walk.rs the `Item::Bound` arm (`meet_type`) | already there (a parameter the scope has no product of is any value of its type, stated above the loop) |
| 1dc603590 | The join of the sides of `\|\|` keeps the looser end of two; the lazy settling of leaves | zedc-preimage product.rs | other crate (zedc-preimage) |
| 251d01b97 | `read_image` reads each input by `NameProducts::read`, the changes from the paths a test writes, in place of the whole exact map per scope version | zedc-check check/walk.rs `read_image` | already there |
| 25ef78dd1 | The byte count of the limit repair fits, and its `ceil_log2` is defined | zedc-check check/walk.rs `main_limit_fix` | added: why the `expect` holds (every caller's size is within the address space, at most 2^67 bits), that `need >= 2`, that `ceil_log2` is total, and the test |
| 25ef78dd1 | `whole_byte_width`'s `bits + 7`; the shared midpoint in arms.rs | zedc-check check/walk.rs `whole_byte_width`; check/arms.rs | already there (see d80e81d08) |
| 2b3e706f1 | The narrowing in `Carried::longer` by the shared `first_true` | zedc-check check/arms.rs `Carried::longer` | completed: `first_true` documents a predicate false on a prefix and true on the rest, which `explains` is not shown to be; why the answer still explains `x` (the loop moves `hi` only to a `mid` found true), what a predicate that is not monotone costs (longer notes, not wrong ones), the test and its limit |
| 2cc4082d7 | The watcher counts, the key index and the closed-range map make each step O(1) or O(log k); the M31 memo expands one child at a time; the callee finish runs on an explicit stack | zedc-check check/probe.rs `R10State`; check/walk/r10_forward.rs `r10_on_need`; check/mod.rs the M31 walk, `r10_finish_fwd_callee` | already there |
| 50db0e281 | A prelude word called by name needs every argument (`Demand::All`) | zedc-check check/walk.rs `apply`, `apply_demanding` | already there (the soundness proof and what its test cannot catch) |
| 52e3a5315 | `shown` decodes a type holding a forward with held names, O(flat form); proof (i) of `r10_decode_fwd_needs`; step (iii) in `finished_with` | zedc-check check/mod.rs `shown`, `r10_decode_fwd_needs`, `finished_with` | already there |
| 5400e8605 | The rebuildings of a lambda called in a generic body sit at the arguments there; a second, different fit at one span is refused | zedc-check check/walk.rs `coerce_at`; check/mod.rs `Ck::put` | already there (the route step by step, the counterexample, the tests) |
| 7028f23a2 | `#4-own-vars` is an O(1) test on the facts | zedc-check check/walk/r10_forward.rs, the admission walk | already there |
| 7028f23a2 | `cached_fwd_summary` reuses a body only at unchanged ranks; the `rename_apart` bound | zedc-types ty.rs; zed-kernel types/print/names.rs | other crates (zedc-types, another helper's; zed-kernel, read only) |

No code claim:

- zedc-check: 6254ad0c2 (its claims are in zedc-preimage), 922be74e7, afbdffe42, b7fda077c,
  d6fa0ddbd, 3958b1767, daf5a87f2, b59ca2ae8, 555863e23, c38724eb5 (the claims are zedc-types
  `must_decode`, proof5's, read only; zedc-check holds only its tests), 7433e3145 (a crate
  move), 7d9e078c0 (message texts).

Not read:

- zedc-check (177): 84ed8e51d, 995200322, 9d877b65c, a02d270c5, a444b1e1d, acc07210e, b9fcd73c3, c4ad09e8a, d493d34a3, e0d680d9f, e50f2e026, eb9d470b5, 068d62e2f, 0e1e5468d, 18ea94666, 26f8d7d35, 2ab9f29af, 305ad0293, 3798539bc, 3cdd34f55, 400b14585, 4c75d8f88, 4e6c5bfaa, 4fc432347, 516e1324a, 549d0d033, 5767fe37a, 59fe136e7, 5decb7fcc, 61be98168, 628d33f6d, 635687ff7, 65f995fee, 6e2e39396, 701def5c6, 7d0cc8d9f, 809f95c53, 84f080d6b, 86322e10b, 924583b1b, 9aff48777, 9e3cc1480, 9e4acde1f, a034e80cd, a55b75fd8, a670bd1cb, a9443c314, af6a5a696, af8174807, b18332dd5, b2ba71b22, b3469579a, b7edc27fd, bfe7e7956, c50a8965b, d20f8009e, e7b12dd2e, ee79685e4, fe770de11, 01063a0ca, 03a4f95f2, 0f6b67903, 148a42eb4, 1cdb4bf0e, 275d434e7, 2cccffee8, 47be53825, 4d3221711, 55045d490, 57434d47b, 578bbc92d, 5af4b2f2a, 5db8eb317, 5ff79522f, 60ce2dad4, 61299315a, 64d244789, 6704ae0ff, 67dd99e3a, 6817d8ebc, 69526a75a, 718e9ecda, 727dae146, 74d26e990, 7a7417966, 7d0d766ad, 7dc27aa9e, 81e1bb50f, 84e65bf61, 8d9f4f9d2, 97beabefa, 981ec6c8a, 9ad186cfe, 9b35c8ab0, 9e8f139f1, b3de801c3, b48d21bcd, b991293a4, ba11fed9c, bad0d2e86, bd3c630e0, bea44d4a5, c289ffeca, d11373afd, d59b4756e, d83518eb5, d9d8729bb, da0895a4f, df8cea00b, e2e0e0612, e6dfb6877, ebd6faee5, ef56f8c84, f240a5462, f38d90beb, f6c6b1f99, f79ee52bf, f8f4ddabb, f923d44b9, fffe13699, 009e52933, 00a508032, 019b3519b, 06d1dc49c, 0b05cc8cf, 0cbb40ab4, 131d7f7fd, 19514ef8c, 1a19cae20, 205591658, 2059d260b, 256d0fc5d, 29bf6b297, 30b46ffdb, 35f48821c, 3b7276f38, 3e597380e, 3fd923c4a, 47681f229, 47f742016, 480291d0e, 4abfd2ae1, 4ce8104bb, 4e55a11ba, 51ae6534c, 5a5ef9670, 5ccb21f3f, 61590f5c5, 620307b4c, 650ec1e0a, 65fe79c41, 695a25e74, 6a1038700, 788205304, 7b5ff433f, 7efc39992, 807ba2009, 81f3d8487, 8824fb555, 893f60ac7, 929e7e04a, a16eb1e6e, a7dba5382, aea083d67, af7540d08, b3c21a87e, b5444f558, b6b810dec, c8fa18353, d18e52a0a, dd8b42f68, e2ef08f39, e36d97342, e8755d8a1, eaef33ced, eb156f28d, fbb2b68aa
- zedc-elab (44): 7fb0c6594, 7931d6ed6, 8164a8ea9, 9b7a17570, e5ff7920a, f24b492bf, 555863e23, f0bde0d35, 0e329a46e, 1286f4779, 2b3e706f1, 995200322, 9d877b65c, 068d62e2f, 18ea94666, 4c75d8f88, 5767fe37a, 7d0cc8d9f, 86322e10b, 875e58597, c50a8965b, cf099fcf2, 03a4f95f2, 0e8df04e7, 64d244789, ac7cafdd0, ac9176a94, cb0137143, d11373afd, f240a5462, 131d7f7fd, 14b96090a, 29bf6b297, 47d87108b, 480291d0e, 4ce8104bb, 51ae6534c, 650ec1e0a, a7dba5382, af7540d08, b6b810dec, ea2effe91, eb156f28d, fbb2b68aa
- zedc-base (39): 30ad62cc4, 7fb0c6594, 13237878e, ba41f402c, d6fa0ddbd, 25ef78dd1, 7d9e078c0, a02d270c5, eb9d470b5, 007a9ebb0, 24a43c819, 4e6c5bfaa, 50b8eea24, 5767fe37a, c5ed79580, 331f39ab5, 726008ee7, 8a14a296f, 981ec6c8a, 995a598b2, bea44d4a5, bfc106d61, d11373afd, e6dfb6877, ebd6faee5, 168d440d9, 259a46243, 3ef2d671a, 4ce8104bb, 50a4b3789, 6a1038700, 7634e8afc, 835596645, a1740c637, b6fab1610, c80981f4b, cac8265b5, f64572af8, fde51511a
- moved from zedc and zedc-syntax (39): 6c2c05101, 1dd869737, fd98fb235, 15657d994, 174c0f20b, 585e7f18b, 63a6f9c4d, 78e5f708f, acc4f3aed, 0513b158e, 26b4df164, 2bf39d29e, 64781908f, 745bf800f, 7498c2e7e, b6d0a2eef, 16d8ce615, 1b531cd56, 52e4b51fc, 5354b56d7, 7433e3145, 79885f50d, 889d3e94d, 9111fb39d, 961b304c9, a934e9cf8, e3b9b5c6b, 01d71b2ea, 53d0c3177, 63fa169e7, 8f23b02b7, 9147744bd, 9b7406051, c22a191c9, c3044ee83, ce1450451, cf099fcf2, d9495abf6, fec575742

## proofdoc3c: zedc-types, zedc-presburger, zedc-solvers, zedc-int

The list holds 373 entries (one commit in one crate): 140 in zedc-types, 198 in
zedc-presburger, 18 in zedc-solvers and 17 in zedc-int, ordered by score. This pass read 12
of them, 11 in zedc-types and 1 in zedc-int, in order of score, each message and each site it
names. It also completed one zedc-solvers site that no entry read here names. The sites were
read on 46b9d5d88 and checked again after a rebase onto origin/main of 2026-11-20 (bd4504e9b).
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
