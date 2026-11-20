# Proofs in comments: audit of proofdoc2b (DOC-proofs-in-comments-audit-rest)

This audit covers the crates zedc-check, zedc-base, zedc-elab, zedc-types, zedc-presburger,
zedc-preimage, zedc-solvers and zedc-int. The sources are the commit messages since 2026-11-01
that touch these crates (`git log --since=2026-11-01 -- <crate paths>`), less the commits already
in proofdoc1.md and proofdoc1b.md, and the lines of wt/running-log.md and wt/ledger.jsonl that
name them: 457 crate-commit entries, ranked by how often a message names a proof, bound,
invariant, derivation, lemma or argument (scores 1 to 14; an entry is one commit in one crate).
The 75 entries at score 4 or more, 55 distinct commits, were taken in order, zedc-check first.
Each claim was checked against the code on origin/main as it is now; where the comment lacked
the claim, a step, the facts used and where each is established, or the test and what it cannot
catch, that was written at the code. One bug was found and fixed with a test (P377); one false
bound and two false sentences were corrected; one claim was proved in part and marked "Not
proved" for the rest, with a row. The sites of zedc-types ty.rs `RunMark`,
`vars_order_and_marks` and the r10 test
`run_marks_name_a_new_signature_at_the_address_of_one_dropped` were left out, as the brief says.

Counts (rows below; one row can count in two columns):

| Crate | Found | Already there | Added or completed | Marked unproved | Corrected |
| --- | --- | --- | --- | --- | --- |
| zedc-check | 12 | 0 | 9 | 1 | 3 (one a bug) |
| zedc-types | 7 | 2 | 5 | 0 | 1 |
| zedc-presburger | 6 | 6 (one already marked "Not proved", with its row) | 0 | 0 | 0 |
| zedc-preimage | 5 (LOAD-chain-affine, which touches zedc-presburger too, counted here) | 5 | 0 | 0 | 0 |
| zedc-base | 2 | 2 (no argument to prove) | 0 | 0 | 0 |
| zedc-elab | 0 | 0 | 0 | 0 | 0 |
| zedc-solvers | 0 | 0 | 0 | 0 | 0 |
| zedc-int | 0 | 0 | 0 | 0 | 0 |

One entry at score 4 or more names an argument whose code is in another crate: 80870e234
(PROOF-treap-digest-priorities, zed-kernel). It was not followed.

Not swept. Of the 55 commits at score 4 or more, these were not read: zedc-check 0203fd7aa,
0d0cca54a, 555863e23, 7bd52fc4e, 827095bce, acc07210e, 5400e8605, 447df80cb, 76705768a,
7940088be, daf5a87f2, e8266a053, 52e3a5315, f83194447, e0d680d9f, fc7a7365f, 0e329a46e,
1286f4779, 759ca91d4, 995200322, c4ad09e8a; zedc-elab e5ff7920a (its elab part; the zedc-check
part, `entries_alike`, was read), 7931d6ed6 (its elab part), 555863e23, 9b7a17570, 0e329a46e,
1286f4779, 995200322; zedc-base 30ad62cc4. (7fb0c6594, "proofs and reasoning in comments, batch
1 (DOC-proofs-in-comments-audit)", is this audit's own earlier work and was left out.) None of
the 382 entries at score 3 or less were read; they hold every zedc-solvers and zedc-int entry (6
and 3).

| Source | Claim | Code site | Status |
| --- | --- | --- | --- |
| 82a961bbb | Every key of a map or set display is a guaranteed key | zedc-check check/walk.rs `display_ty` | corrected: false where a key's type holds more than one value (`f(n: int) = { n -> 10 }[n + 1]` typed `(n: int) -> 10`, `#notFound` at run time); fixed to `(L) -> V` and `U ->? V`, proof at the code; test l03_02_map_run::types::a_key_of_many_values_is_permitted_not_guaranteed (red before); row FAIL-display-computed-key-sure, Done (2f0500f53, 8344fba6a) |
| 82a961bbb | `key_ints`: a key set read from a data signature is exact or the signature is partial ("Not proved" for the message case) | zedc-check check/walk/fp_ops.rs `key_ints` | completed: proved by the list of every site that makes a signature data; the display was the one exception, fixed above |
| 82a961bbb | `Ck::known`: a range end's value is the run's in every case, and the memo is read alike in either order | zedc-check check/mod.rs `known` | completed: two nodes never share a span, so the order does not matter; the test named, with what it cannot catch |
| 7931d6ed6 | `lit_spares`: a literal spared in an argument that takes its call's carrier is checked later | zedc-check check/walk.rs `lit_spares` | added: every span spared is taken out again by `lit_takes` before the walk ends, five steps; two tests added in l01_26a_generic_literals call_arguments |
| 41739da61 | The lending table reads each carried fix when it joins or moves | zedc-check check/walk.rs `unfixed_only` | corrected: one false sentence (what the fixes read could be) |
| 04555ad8b | The table of types lent across arguments is needed only where two or more arguments hold fixes | zedc-check check/walk.rs, the table of lent types | added: skipping it where the fixes lie in one argument changes no verdict |
| ad367e05f | A rejected call of n arguments is checked in O(n): repairs under `params_apart` are skipped | zedc-check check/walk.rs, the skip under `params_apart` | added: it drops no repair, four steps and the case left; read, not tested |
| 042103e29 | An argument of type `Never` binds its parameter's variable alike in any order of the arguments | zedc-check check/walk.rs `Ck::bind_never`, `apply_one` | corrected and marked unproved: proved for the binding the loop ends with (every write a union; `or_insert_with(v, empty)` a union with `Never`); not proved for `fit_needs`, which reads the binding made so far (`Never` before, the variable after); row PROOF-never-bind-order-fit-needs; test never::an_argument_of_type_never_binds_alike_before_or_after_a_function_with_needs (passes) |
| 4db94f302 | A call with an argument of type `Never` the call does not need keeps its substituted result | zedc-check check/walk.rs `apply_demanding`, the `Demand` block | added: soundness proof (an argument of no value is in every parameter type; `All` and `First` make the call `Never` only where it cannot give a value); what the test cannot catch |
| ed93da0f2, e5ff7920a | A function read from a family argument is rebuilt entry by entry, each entry at its place (PROOF-family-entry-place) | zedc-check check/walk.rs `entries_alike` | completed (tests): function_variance::a_function_taken_from_a_family_argument_misses_outside_its_domain; limits: tuple keys, nesting past one level, entries of several types |
| 39111129f, 90bf5612f | The parameters of a call own their fresh variables apart (PROOF-params-own-apart-fresh) | zedc-check check/walk.rs `params_own_apart` | completed (tests): the tests use only the defaults `p0` and `p0 == p1`, none a bounded or ranged default or `[p0]` |
| 3cc339fd1 | A trial's `Read` fit replaces the walk's; a span is fitted twice only inside an arrow lambda (PROOF-fit-twice-only-arrow-lambda) | zedc-check check/mod.rs `put` | completed: why a span the trial wrote itself keeps the refusal (`walk_read_replaced`); the test, red with the replacement off; the single writer is a `debug_assert`, checked in debug builds only |
| 7e40b1fdc | Comparing only the star pairs decides as comparing every pair; the early return on the pair count never fires on a star forest of nodes (PROOF-star-pairs) | zedc-types ty.rs `star_pairs`, its doc at `met_at`; COMPLEXITY.md | corrected: the count charged an edge's \|fs_l\|·\|gs_r\| pairs as \|fs_l\|; counterexample with 12 pairs read against a budget of 7; the bound holds per function, each pair read once, and a function in two nodes near one node can still exceed it; the return is a refusal, never a wrong verdict. The whole proof moved into the body; COMPLEXITY.md keeps the claim and a pointer (7b919c7c9) |
| 9778881e0 | `Forms::level` keeps every value's verdict with the marks cut and put in at every level | zedc-types ty.rs `Forms::level` | completed: the recursive-node case (induction on the value's depth) and struct parts and functions; tests, negative control, and their limit (no recursive type among them) |
| 23e187f2c, 4066c3c5d, c46193d80 | The rest of a payload shape decides by the kernel's verdict; a shape is within a union exactly when its rest is empty (PROOF-diff-exact-skip) | zedc-types ty.rs `Comparing`, `shape_rest` | already there (proof); completed (tests and what they cannot catch) |
| 236431136 | A class inside a function argument is found outside every owner (PROOF-held-own-outer-or-class) | zedc-types ty.rs `outer_or_class` | completed (tests): a name owned by two signatures at different depths is built one level only |
| c02b97d29 | A covering arrow's unbound variable is tried at each carrier, and that is complete (PROOF-unbound-carriers-complete) | zedc-types ty.rs `instance_within` | completed (tests): arrows of several parameters, payloads with fields and deeper nests rest on the proof |
| c02b97d29 | A bounded variable of a partial arrow's value type narrows at each binding (PROOF-met-partial-narrow-bindable) | zedc-types ty.rs `binds_nothing` / `met` | completed (tests): one exact and one partial arrow of one parameter only |
| a0fe9925d | `form_verdict`'s merged forms are right for `_`, nested functions and the memos (PROOF-form-verdict-merged-mark) | zedc-types ty.rs `Comparing::form_verdict` | already there |
| af1e518fb | A backjump of `quick_search` never passes over a branch with a point (PROOF-quick-search-backjump-sound) | zedc-presburger `quick_search` | already there |
| 046516bc8, 6951e61a6 | `solve_modular` gives one verdict whichever tied remainder row it reads first (PROOF-modular-tied-rows-names); answers do not follow the names (PROOF-solve-renaming-invariant) | zedc-presburger `solve_modular` | already there |
| 7685039ca, 88269f144 | A tie of `System::shrinking` is read on counts renewed for every variable (PROOF-shrink-counts-current); the symmetries found make the tie's group (PROOF-tie-depth2-generators-whole-group) | zedc-presburger presburger.rs `System::symmetries`, near line 17021 | already there |
| ac936938b | `settle_as_sets` projects over structural names and keeps the answers of renamed tests (PROOF-settle-marks-naming-free) | zedc-presburger presburger.rs, near lines 2859 and 3031 | already there |
| ac936938b, 6951e61a6 | The tied kernels of `stage_kernels` are settled free of naming (PROOF-settle-tied-kernels-naming-free) | zedc-presburger `stage_kernels` | already there: marked "Not proved", the row exists |
| 4f7b49896 | The shadow is exact (PRES-shadow-exact-comment) | zedc-presburger exact.rs | already there |
| b273d0f62 | A function's body is read once over canonical atoms and a call binds them to its affine arguments (LOAD-chain-affine) | zedc-preimage, zedc-presburger | already there |
| 7d12abbc2 | O(log n) per link of `normal_round_down` (PERF-ref-memo-nlogn-proof; Blelloch, with DOI) | zedc-preimage preimage_ref.rs `Tx::inverse_states`, near line 3488 | already there |
| cd44912dd | The reuse of an entry that stopped nowhere on a higher stack (PREIMAGE-entry-higher-stack) | zedc-preimage preimage.rs, near line 3788 | already there (proof and tests) |
| cd44912dd | The bound kept by `ByClass::clamp`, in E, V and M (PROOF-by-class-clamp-bound) | zedc-preimage preimage.rs, near line 11798 | already there |
| 7c4749998 | The writers of the listed ints (PROOF-ints-listed-writers) | zedc-preimage product.rs, near lines 207, 665 and 23192 | already there |
| 39b997944 | Row "Obligation below proof grade" retitled; `@strict` and `@proved` removed | zedc-base | already there: no argument to prove |
| 7d9e078c0 | Messages audited against sec:diagnostics | zedc-base | already there: no argument to prove |
| 80870e234 | Every treap bound is conditional (PROOF-treap-digest-priorities) | zed-kernel | other crate: zed-kernel |
