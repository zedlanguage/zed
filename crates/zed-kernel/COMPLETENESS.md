# Completeness: zed-kernel

Crate zed-kernel's own unit tests: the exact arithmetic of `num` (division, products, gcd,
Bezout coefficients, reciprocals and digit reading in `num/fast.rs`, each on both sides of its
crossover; `Rat` with kept prime powers in `num.rs`) and the L1 prelude words on scalars in
`words.rs` (casts, `String`, `abs`, `len`, `lower`, `upper`, `trim`, `codePoint`, `scalar`,
`utf8`, `fromUtf8`). Plan row TEST-complete-kernel (author P188, P189). The new tests are in
`src/completeness/` (`fast.rs`, `rat.rs`, `words.rs`); expected results come from DESIGN.md
L1.17, L1.18 and L1.39c, and for the arithmetic from num-bigint's schoolbook results.

Line coverage of the crate's unit tests (llvm-cov, `cargo test -p zed-kernel --lib`, benchmarks
skipped), before and after: whole crate 65.30% to 66.61%; `num.rs` 82.9% to 94.1%;
`num/fast.rs` 94.3% to 98.5%; `num/float_text.rs` 95.4% to 98.2%; `words.rs` 27.3% to 89.8%.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| Division handed to num-bigint at a divisor of 4096 bits, past the leaf at 4097; the same for the quotient's bits | `fast.rs::division_on_both_sides_of_the_leaf` | |
| Past the leaf: the sparse method (rows) at few nonzero divisor words, the reciprocal at full density, exactly one change between, and `div_by_rows` agreeing with `sparse_flip` | `fast.rs::past_the_leaf_both_methods_and_the_flip_between_them` | |
| Past the leaf, every path (`div_rem_uint`, `rem_uint`, `div_rem_past_leaf`, `div_rem_by_reciprocal`, `div_rem_sparse`) equal to num-bigint, an exact multiple and the largest remainder among them | `fast.rs::past_the_leaf_both_methods_and_the_flip_between_them`, `fast.rs::edge_forms_past_the_leaf` | |
| Divisor forms all ones, `2^(b-1)`, `2^(b-1)+1`, random | `fast.rs::edge_forms_past_the_leaf` | |
| Small divisions: dividend below the divisor, equal, one word | `fast.rs::small_divisions` | |
| Division by zero | `fast.rs::a_zero_divisor_panics` | |
| Products on both sides of the leaf (48 and 49 words), unequal lengths, rows and transforms each taken, sparse times dense by rows | `fast.rs::products_on_both_sides_of_the_leaf` | |
| Products against a kept spectrum (cached transform) on both sides of its flip | `fast.rs::kept_spectra_products` | |
| Reciprocals of 1 to 3000 bits at each leaf, including powers of two and one past | `fast.rs::reciprocals` | |
| gcd: iterative, recursive and the crossover hook at each leaf and lift, a zero operand | `fast.rs::gcds` | |
| Reading digits at each leaf | `fast.rs::digits_read_at_each_leaf` | |
| Bezout coefficients at both lifts, all four sign pairs, a zero operand | `fast.rs::bezout_coefficients` | |
| Euclidean `div` and `mod` at each pair of signs, `i64::MIN` by `-1` and by 7 (`-1 div 4, -1 mod 4` is `-1, 3`) | `rat.rs::euclidean_division_at_each_pair_of_signs` | |
| Euclidean division of kept powers (`2^100`, `1e1000`) by each sign and by a power; an exact division keeps the powers | `rat.rs::euclidean_division_of_kept_powers` | |
| Powers: 0, 1, -1 at huge even and odd exponents stay small; `0^-1` is none (`#divByZero`); negative exponents; a huge exponent kept | `rat.rs::powers_by_an_integer` | |
| Nearest `f64` and `f32`: infinite past the largest finite, the tie at the top, `MAX`, least subnormal, zero below half of it, ties to even, round to 1.0 | `rat.rs::nearest_floats` | |
| `neg`, `try_neg`, `abs` | `rat.rs::negation` | |
| Parity of plain and kept values, odd and even decimals | `rat.rs::parity` | |
| Borrowed and built numerator and denominator of kept values | `rat.rs::built_parts` | |
| Literal text of zero, integers, decimals, a huge exponent, ratios | `rat.rs::literal_texts` | |
| `int(s)`: leading zeros, `-0`, the `i64` ends and one past, a long digit string; `#invalid` for empty, `-`, `+5`, spaces, a point, an exponent, digits of another script, full-width digits | `words.rs::int_of_a_string` | |
| `rat(s)`: `3r`, `-1r/3r`, without the `r`s, decimals; `#invalid` for a zero denominator, mixed `r`, a negative denominator, `.5`, `5.`, `+1r`, empty, an exponent, another script | `words.rs::rat_of_a_string` | |
| `f64(s)`, `f32(s)`: signed zero, `inf`, `-inf`, `nan`, underflow to a signed zero, the least subnormal, a finite text past the range as the infinity of its sign, `#invalid` forms, `f32` rounded once from the digits | `words.rs::floats_of_a_string` | |
| Casts between number kinds: a float cast rounded to nearest with ties to even and to the infinity of its sign past the range (step L1.18), `int` of a number that is not whole a type error, `#invalid` for an infinity or NaN at `int` (which the checker rejects unless it proves the value whole), `rat` of an infinity `#overflow` and of the NaN `#NaN` (CAST-rat-nonfinite), `f64` of `f32` exact, a big integer `rat` to `int` | `words.rs::casts_between_number_kinds` | |
| `f64(-0.0)` and `f32(-0.0f64)` keep the sign of zero | `completeness::words::casts_between_number_kinds` | Fixed by row FAIL-values-cast-negzero: a finite `f64` is narrowed as a float, not through its rational, which has no sign of zero. Neighbors there: `0.0`, the least `f32` subnormal, `±1e-46` (the zero of its sign), the largest `f32` and the next `f64` past it at each sign (`f32::MAX`), and `f32::MAX + ulp/2` (the infinity, a tie to even). |
| A cast of a bool, tuple, atom or family; each other word at a kind it does not take | `words.rs::words_at_kinds_they_do_not_take` | |
| `abs` at each kind and sign, `i64::MIN` widening, `-0.0`, `-inf`, NaN, `f32` | `words.rs::abs_at_each_kind` | |
| `len` in code points; full case mappings (`straße`, `ﬁ`, final sigma, dotted `İ`); `trim` with Unicode white space, all space, empty, zero-width space kept | `words.rs::string_words` | |
| `codePoint` of one scalar, `#notScalar` for empty, two, a combining sequence; `scalar` at 0, `0xD7FF`, `0xE000`, `0x10FFFF`, `#notScalar` for surrogates, past `0x10FFFF`, negative, big | `words.rs::code_points_and_scalars` | |
| `utf8` of empty, two and four byte forms; `fromUtf8` round trip at each width, key order, empty; `#badUtf8` for overlong, surrogate, past `0x10FFFF`, truncated, stray continuation, `0xFF`, 256, -1, a big value | `words.rs::utf8_both_ways` | |
| `String(x)` of strings, floats (`0.1`, `1.0e300`, `inf`, `nan`, `-0.0`, `f32`), big integers, rats, named and payload atoms, sets, bools, a tuple with an `f32` member | `words.rs::string_of_each_kind` | |
| `len` of a string past `i64::MAX` code points | | Unreachable in a test: needs more than 2^63 characters. |
| A refused allocation in `num.rs`, `words.rs` and `num/room.rs` (`TooLarge`, `Watch`, the order and equality fallbacks to normal forms) | | Needs the system to refuse memory; tested where refusals are measured (COMPLEXITY.md K30 and the benchmark modules), not in small tests (P178). |
| `const fn` bodies in `num/fast.rs` (`Field::new`, `mont_of`, `inv_mod`) | | Evaluated at compile time, so llvm-cov reports them as not run. |
| `bits.rs` (bit words, machine operations) | | Covered by l01_39a_bit_words and l01_39f_int_machine_ops (TEST-complete-reduced). |
| `types/**`, `frames`, `value.rs` printing and keys | | Covered by l01_22_type_representation, l01_23_subtyping and crate zedc-types (TEST-complete-types). |
| `eval.rs`, `term.rs`, `term/walk.rs`, `print.rs`, `print/dag.rs` | | Reached through l01_15_kernel_terms to l01_18_scalar_interpreter and m0_09 to m0_11 (TEST-complete-names, TEST-complete-values, TEST-complete-m0). |
| `provenance.rs` | | Covered by l01_20_provenance (TEST-complete-diagnostics) and l01_24_refinement_lattices (TEST-complete-lattices). |
| `poly.rs`, `poly/roots.rs` | | Covered by l01_39_reduced_product (TEST-complete-reduced) and its own unit tests (96 to 98%). |
| `sites.rs`, `site_table.rs`, `address.rs`, `limits.rs`, `text.rs` | | Used by zedc, zedc-stage, zed-native and l01_37a_short_addresses; covered by TEST-complete-crates and TEST-complete-native. |
| Large sizes and scaling | the `bench` modules | Benchmarks (P178). |

## Row TEST-types-unreached-paths-3: zed-kernel `types/**`

The lines under `crates/zed-kernel/src/types` that the whole local suite left unreached at
5461fb972 (types8's coverage run, /home/luke/Work/wt/coverage/TEST-types-unreached-paths-3.txt).
Each case below was checked by an llvm-cov build of the zed-kernel unit tests, run once as
usual and once with `--features short-addresses` (8-bit digests), reading the target lines
each run reaches. Line numbers are those of 5461fb972.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| `bdd/set.rs` `same`: two sets of one sum, length and root literal whose roots hold a child on different sides (803) | `types::bdd::set::tests::sets_of_one_sum_and_root_with_children_on_different_sides_are_not_the_same` (the fourth literal solved so that the hashes sum alike) | |
| `bdd/list/treap.rs` `split` meeting the key itself (191-192) | | Removed for an `unreachable!` with the proof at the site: the one caller, `insert`, walks down the nodes above the new one in the order `(prio, key)`, and a node of the same key has the same priority, so the walk stops at it and gives it the new value; the subtree it splits never holds the key |
| `bucket.rs` the last node of a bucket leaving its treap (288) | `types::bucket::tests::a_bucket_of_one_node_is_found_left_and_written_over_when_dead` (now also takes the last node out and puts a new one in) | |
| `debug.rs` `fmt` of a `Bdd` alone (397-399) | `types::bdd::tests::the_delegating_orders_and_texts_of_parts_agree_with_what_they_delegate_to` | |
| `print.rs` `surface_in_union`, `surface_key`, `surface_bound`, `surfaces_spelled` (52-54, 67-75, 119-126) | | Removed: no caller (`surface_in_union` was used only in a failure message of `types::tests`, now written with `op`); docs that linked `surfaces_spelled` now link `surfaces_apart` |
| `print.rs` `surface_operand` (59-61) | | A `#[cfg(test)]` helper read only in failure messages |
| `print/order.rs` the order of `bf16`, `f16`, `f32`, `f64` and `bool` among names (84-91); two literals of one value and carrier, `0.0` and `-0.0` (136) | `types::print::order::tests::names_print_in_the_fixed_order` (the nine scalar names given shuffled), `types::print::order::tests::literals_of_one_value_and_carrier_go_by_the_value` | |
| `print/uses.rs` joining Patricia branches whose keys lie apart, on each side and at a higher bit (173, 179, 186), and a lookup of a key past every branch (203) | `types::print::uses::tests::branches_whose_keys_lie_apart_are_joined_beside_each_other` | |
| `print/uses.rs` `rebuild` given a leaf (113) | | Kept `unreachable!`: every caller passes a branch |
| `print/defs.rs` `forget_printed` with no table and with the table on (365); a type printed inside another, counted with the outermost (393); a wrapped tuple written whole in parentheses in a sentence (693) | `types::print::defs::tests::forgetting_the_printed_parts_empties_what_is_kept`, `a_type_printed_inside_another_counts_with_the_outermost`, `a_sentence_writes_a_wrapped_tuple_whole_in_parentheses` | |
| `types.rs` `rewrite_levels` (2098-2099) | types8's `types::tests::a_recursive_node_is_rewritten_only_where_level_keeps_its_unfolding` | |
| `empty/shared.rs` `list_step` (289) and `empty/escape.rs` `node` (408), `decide_counted` (551): a listed atom name with neither the bare atom nor a payload | | Kept as `unreachable!` with the reason at each site: a finite map of atoms lists no name whose part is none (`Atoms::set` leaves the default out, and every write goes through `set`), and each site has checked the map is finite |
| `empty/shared.rs` `list_step` a part over one atom true at both values (310) | | Kept as a check with a `debug_assert!`: a part over one atom is the atom, its complement or a leaf (`Part::zip_at_once` for `a | a`, `Connect::zipped` for `a | !a`), so one true where its atom holds is false where it fails |
| Comparisons and maps when two digests tie: `empty/shared.rs` `ByType` with several keys of one digest (53, 76-98); `rec/group.rs` the numbering's next probe (131) and a group of one digest and other definitions (203-204); `hash.rs` the short `mix` (9); `bdd.rs` `before` by contents (801), the set walk's ends (2650-2651); `empty.rs` 3656, 12628; `types.rs` the orders by contents after a tie (913-914, 958, 962, 1068, 1073, 1148-1149, 1191, 1230-1234, 1245, 7841, 7856, 8168, 8178) | zed-kernel unit tests `types::empty::`, `types::rec::`, `types::bdd::`, `types::print` and `types::tests::` in the short-addresses build | Reached only when digests tie, which 64-bit digests do not do in these tests. The suite builds short addresses only for l01_37 and l01_37a, not for the kernel's unit tests; in that build two of them fail on an assumption of few ties (`rec::group::tests::an_instance_whose_parts_were_unfolded_is_freed_at_the_end_of_its_unit`, `bdd::set::tests::chosen_literals_give_a_logarithmic_height`). Row TEST-kernel-units-short-addresses runs them there |
| `bes.rs` the arms for `Top` and `Bot` in `lfp` (350-351), `is_cut` (433), the parent walk of `gfp` (481), `delete_cascade` (608, 617-618); a `Mor` or constant node with two undecided children in `refusal` (741) | | Now `unreachable!` with the reason at each site: a constant node has no child (`Bes::add`, `Bes::set` assert it; `simplify` gives a node it makes `Bot` no children), so it is no node's parent and on no cycle, and these passes see only nodes of a component with a tuple cycle; a `Mor` node has one child. The arm of `gfp` over the nodes of `sub` (460) stays, since `settle` passes it a component of one constant node |
| `rec/group.rs` `of` (98), `regular` (253), `rec/unfold.rs` (348, 511), `empty/refused.rs` `site` (196) | | Existing `unreachable!` guards with their reasons: a leaf shape is never built as a node; only a recursive occurrence is kept as the bad one; a member is a recursive node |
| `rec/unfold/show.rs` `fmt` outside the surface syntax (17) | `types::rec::unfold::tests::a_part_s_name_is_unchanged_when_the_names_inside_it_are_shared` (its helper `spelled` checks that `Display` writes the spelled-out text) | |
| Failure arms of tests and their helpers (`bucket.rs` 403, `rec/group.rs` 864, `empty.rs` 14382, `bdd/list/treap/tests.rs` 39, 46, `bdd/set/tests.rs` 322) | | Panic and assertion messages and failing checks, run only when their test fails |
| Test branches for other builds and inputs (`bdd/set/tests.rs` 351-353 and 492, the short-addresses branches, reached in that build; 395-397, a benchmark; 450, an atom met twice in a union, which the reference allows for) | | Not product code |

The other entries of this list, most of them in `empty.rs`, `bdd.rs`, `types.rs`, `empty/sweep.rs`,
`empty/escape.rs`, `empty/refused.rs`, `bes.rs` (`delete_cascade` 634-677, 766), the rest of `print.rs` and `rec/`, are row
TEST-kernel-unreached-paths-4.

### Row TEST-kernel-unreached-paths-4 (cover2, in progress)

A differential test over random small types,
`types::empty::tests::random_types_agree_with_membership_on_a_finite_set_of_values`: 3,000
random types (literals, `int`, atoms with payloads, one- and two-tuples, union, meet,
difference, complements and random recursive groups of one or two definitions) are checked
against `Type::contains` on the values listed up to three levels deep; the verdict of `t & bound`, its
emptiness, and subtyping between consecutive types must agree with membership. All 3,000 are
decided and agree (2 s). It reaches only three of the list's lines (`empty.rs` 14784-14785 and
one in `types.rs`): the other entries need structures random small types do not form (prefix
chains of list carriers, chain witnesses, nested pieces, morphisms, residues), and each still
needs its own test, proof at the site, or removal. At this commit 210 of the 240 entries are
open: `empty.rs` 75, `types.rs` 45, `bdd.rs` 34, `print.rs` 15, `empty/sweep.rs` 11,
`empty/refused.rs` 7, `rec/unfold.rs` 7, `rec/group.rs` 6, `empty/escape.rs` 4, `bes.rs`,
`empty/shared.rs` 2 each, `print/uses.rs`, `rec/unfold/show.rs` 1 each. 63 of their lines are
`unreachable!`, `panic!`, `expect` or assertion guards.

Second round (cover2, 2026-11-18). Tests added:

- `l01_37a_short_addresses` `the_order_of_types_of_every_kind_of_part_is_total`: 1,200 types
  (600 of every kind of part, 600 unions of bare atoms, atoms with payloads and small tuples);
  the order is antisymmetric, equal exactly when the texts and `==` are, and transitive, in both
  the normal and the short-address build. In the short build it reaches `types.rs` 1091 (two
  atom payloads that tie in digest).
- `l01_23_groups_and_refusals` `lists_the_prefix_chains_leave_to_the_search_agree_with_the_oracle`:
  seven list shapes `find_prefix_chains` declines, each verdict equal to the list oracle's. It
  reaches `empty.rs` 7400 (chains to carriers of two cycles) and 7495 (a link payload of fewer
  than two rows). The first carrier loop's lines (7375, 7377) are not reached by the meets
  written there; why is open.
- `sweep_agreement` `the_sweep_agrees_on_random_groups_of_every_head`: 300 random cases; passes,
  and reaches none of the list's lines.

Proofs written at the site (each a comment above the guard):

- `bdd.rs`: `opposite` "both tested" (the arm's guard); `negate` (one caller, `Connect::not`,
  answers a diagram itself); `rebuild` (each of its three `base` closures answers every diagram);
  the `as_literal` guard in the exclusive-or reading.
- `empty.rs`: `tuple_item` and `list_parts` (each caller reads `v` under the shape made from
  `shown[v]`, and `shown` is only pushed to while a search runs); `system`'s closed-part arm (a
  `Ref` is taken at the top of `Step::Visit`, a `Param` or `Type` is never `recursive`) and its
  `Step::Make` arm; `find_prefix_chains` 7329 and 7475 (finite atoms keep no name whose part is
  `AtomPart::none()`, since `Atoms::set` is the one insertion and skips the default) and 7513
  (two rows or more, and a second non-carrier row gives up, so one row is a carrier).
- `empty/refused.rs` `site`; `empty/sweep.rs` `walk`; `print/uses.rs` `rebuild`;
  `rec/group.rs` `of`; `rec/unfold.rs` both "a leaf is not built" guards;
  `types.rs` `PartsRef` deref, `p_held`, the vertex merge's two guards, the overlay's
  "a list reads no node", and `Expr` copy's leaf arm.

The guard's own message is its proof (the line above shows it): `empty/shared.rs`
`or_insert_with`, its three guards.

Failure branches of tests and benchmarks, run only when a test fails, so not to be reached:
`bdd/bench.rs` 621, 717; `bdd/set/tests.rs` 371; `bdd/tests.rs` 934, 944, 1533, 1589, 1620,
1709, 2278, 2645, 2654, 2659, 2702, 2705, 2711, 2766, 2860, 2877; `bucket.rs` 403 (in its
`#[cfg(test)]` module); `empty/tests.rs` 522, 528, 710; `rec/group.rs` 871;
`rec/unfold/tests.rs` 49; `types/tests.rs` 1075.

Third round (cover2, 2026-11-18), proofs written at the site: `empty/sweep.rs` `walk`
rechecked (each `walked` entry is written once, the path last link first, so an `Item` is
written only after the entry it leads to, also when `pick` gives up part way); `empty.rs`
`system`'s `Not` arm (`Group::new`, the one maker of a group and its `Env`, rejects a recursive
`!` found by `flipped`, which visits every node), `Rep::key` (both callers answer `Of` and
`Closure` first), the value-shape read (`local` never answers an `Of`), the two-operand arm,
`pair_picks` (`extract` reaches it only where `pair` gave the answer, so both leaves exist) and
the exclusive-or component (`Choices::index` makes a component only with a cell); `print.rs`
`put` (a text of class `Of` is made only by `Printer::node`; a list's text takes
`first[0].class` only where it is that item alone) and `folded` (`meet_of_literals` holds only of
lists and meets of its own); `rec/group.rs` `regular`; `types.rs` `part_boxes` (the second pass
reads only operands the first found to have boxes).

`print.rs` `write_out` (old 2083-2096): no kernel test printed a type apart (only zedc-types
calls `Type::surfaces_apart`). Test `print::tests::a_type_printed_apart_is_written_out_and_parenthesized_by_its_place`:
`int \ 1` apart at a union's place is `(int \ 1)`, at any place `int \ 1`; beside `(Part1,
Part1)` it is written out, not named `Part1`, where printed not apart it is `Part1`.

`print.rs` `list`, the arm for a block of value `false` with no text: removed. A block is a
set of one literal or more (`Bdd::list`), each refused literal goes to `first` (or the meet
there) and each taken one to `taken`, so the two are never both empty; the arm could not be
reached, and no test can reach `put` with such a block. The proof is at the site and in `put`.

Fourth round (cover4, 2026-11-18): every kernel file but `types/empty.rs`, which cover3 takes.

Coverage was run again at 847a31d3e (395a28b68 and a comment in `print.rs`):
`tools/run_tests.sh --cov` over every local piece but the short-addresses ones, which are not
built for coverage (2,664 pieces, 22 failed, all of them executables, links, runs and builds of
programs that fail under the coverage build, none a kernel test; load 64 to 315), merged with the
toolchain's `llvm-profdata` and read with `llvm-cov export` over the 157 test executables the
run built. Under `crates/zed-kernel/src/types`, outside `empty.rs`, benchmarks and test files,
340 lines in 251 ranges are unreached; the list is
/home/luke/Work/wt/coverage/TEST-kernel-unreached-paths-4-cover4.txt (`file line`, numbered at
847a31d3e). `llvm-cov` warned of 2,014 functions with mismatched data (one function built with
different features in several binaries); a line it lists is checked by hand before it is closed.
The rest of `crates/zed-kernel/src` (`eval.rs`, `value.rs`, `poly.rs` and others, 1,700 lines)
was not in this row's list and is not taken here.

Closed in this round:

- `empty/shared.rs` `ByType`, the arms for two keys of one digest (`Tied::Many` in `get_mut`,
  `remove`, `retain`, 53, 76-85, 97-98): test
  `types::empty::shared::tests::a_map_by_type_agrees_with_an_ordered_map_also_where_digests_tie`,
  every operation against a `BTreeMap` on 600 atoms. In the short-addresses build (8-bit
  digests) it reaches each of those lines (llvm-cov of that build, 53: 341 runs, 76-77: 496,
  97-98: 270 and 135); negative control: `remove` made to keep the key of a shared digest fails
  the test in that build. In the normal build no two of the keys share a digest.
- `bes.rs` 436, 484, 612, the arms for a constant node where a child, a parent or a cycle is
  read: proofs at the site (`Bes::add` and `Bes::set` assert a constant has no child,
  `simplify` makes a node `Bot` only with none, `Bes::seal` makes parents only of children,
  and `cyclic` holds only of a component whose nodes each have a child in it).
- `print.rs` `list`, the arm for a block of value `false` (cover2's claim that its texts are
  never both empty): checked by tracing every path that builds a cell. `Cell::block` is an
  `Arc<Set<A>>`, a treap node holding a literal, so every block of `Bdd::list` has one; the
  one block whose texts are left empty follows a block with `merged`, which is set only where
  that block has value `true`. The claim holds; the proof is at the site.
- Lines that run only in another build: `hash.rs` 9 (the short-addresses digest);
  `bdd.rs` 88-94 (`Tables::new`, a `const fn` evaluated in the `const` initializers of the
  thread-locals `TUPLES` and `MORPHISMS`, `types.rs`, so never at run time).
- Failure branches of test checkers (`#[cfg(test)]`): `bdd.rs` `index_is_sound` and
  `cells_are_sound` (4441, 4448, 4489, 4503, 4508, 4513), each `return false` read only when a
  test's `assert!` fails.
- Guards with their proof already at the site (cover2 or earlier): `bdd/list/treap.rs` 195;
  `bdd.rs` 1039, 1238, 1966, 2495; `bes.rs` 352, 622, 747; `empty/escape.rs` 411, 557;
  `empty/refused.rs` 198; `empty/shared.rs` 134, 144, 147 (each on the line after the match that
  makes it), 291, 315; `empty/sweep.rs` 1194; `print.rs` 139, 309, 916; `print/uses.rs` 114;
  `rec/group.rs` 100, 256; `rec/unfold.rs` 350, 516; `types.rs` 395, 1637, 1640, 4617, 5952,
  5973, 6102, 7298. `bucket.rs` 403 and `rec/group.rs` 874 are in `#[cfg(test)]` helpers.

- `rec/unfold/show.rs` 29 (a `Show` in the surface syntax whose types share a part declares
  it): test `types::rec::group::tests::a_rejection_quoting_types_that_share_a_part_declares_the_part_first`;
  llvm-cov: line 29 runs once. Negative control: the declaration skipped fails the test. Inside
  a rejection's message the part is lifted under the sentence instead (`defs::lift`), so only a
  text written outside a message reaches the line.
- `bes.rs` `decide`: test `types::bes::tests::decide_agrees_with_the_game_on_systems_drawn_at_random`,
  40,000 systems of 3 to 12 nodes, each answer not refused equal to the Büchi game the module
  comment describes, solved by nested fixed points. Negative control: the one-`Mor` step of
  step 4 without its assumption fails it. A second control, the same step without its second
  least fixed point, passes it: no draw needs that pass (open, below).
- `bes.rs` `delete_cascade`, a node of `u_set` with `need` 0 (old 638-639): proof at the site
  (such a node's `hi` was made false by the last pass of `bounds`, so it is not in `u_set`); the
  arm is now `unreachable!`. The proof was then traced through `decide` line by line and
  written out at the site without the bottom-up ordering argument: each such child has
  `lo == hi == false` (else `reaches_refused` refuses `r_scc`), which makes both `lo[v]` and
  `hi[v]` false in the last `bounds`. The proofs at `sweep.rs` 1194 (`walk` is called only from
  `list_sweep_value`, on a `Sweep` of its own, so `pick` never writes this `walked`),
  `print.rs` 139 (`refer` answers one `Seg::Node`), 309, 916 (`meet_of_literals` is true only
  of a list or an `&` of two such) and `uses.rs` 114 (callers match a `Branch` first) were
  re-derived in the same round and hold. The test reaches `delete_cascade` (52 of the 40,000 systems) and
  never panics there.

Open from this round: `bes.rs` `delete_cascade` 645-689 (a tuple cycle losing its last seed,
and the cascade after it; no draw reaches it, and no proof yet: it needs an exit node true in
the least fixed point of `bounds` and false in its last pass), and the second least fixed point
of the one-`Mor` step (no draw changes an answer with it). The proofs relied on above (cover2's
and earlier) were re-derived in this round: `treap.rs` 195 (heap order by `(prio, key)` with the
priority a function of the key), `bdd.rs` 1039, 1238 (only caller `Connect::not`), 1966 (all
three `base` closures answer every `Part::Bdd`), 2495, `bes.rs` 352, 622, 747 (`Bes::add`,
`Bes::set` asserts), the atom-map guards in `escape.rs` and `shared.rs` (`Atoms::set` is the only
writer of `names` and drops a name whose part is the default; `zip` keeps `cofinite` where it
clones), `types.rs` 395, 1637, 1640 (`Type::p` unfolds in a loop), 6102 (`parents` filled only
from `Not`, `Or`, `And`, `Xor`); the others are stack-machine guards whose proof is in the same
function. All hold.

Open (the other ranges of the list), for the next round: see the handoff
/home/luke/Work/wt/pause/cover4-2026-11-18-handoff.md.

Fourth round (cover3, 2026-11-18). Coverage re-run at zed-impl 395a28b68 (`tools/run_tests.sh
--cov`, the short-address pieces left out, load 77 to 315): 2,664 pieces, 3 failed
(`l01_23_groups_and_refusals::group_oracle` and `zedc_presburger`'s library timed out, so their
coverage is missing from this run; `l01_39_scope_relations` `audit_seeds_against_the_oracle`
failed). `empty.rs` has 8,912 instrumented lines, of which 351 were not reached; the list with
each line's text is `wt/coverage/TEST-kernel-unreached-paths-4-empty-395a28b68.txt`.

Why cover2's meets do not reach the first carrier loop: a probe showed that `forced` lists both
rows of `cell(int, La) & cell(int, Lb)` (two taken, one refused), so the meet is not normalized
first. `find_prefix_chains` is never called on those lists: the front sweep
(`sweep::list_sweep_checked`, run before `prefix_chains`) decides them, and `prefix_chains` runs
only on the heads (`int`, `bool`). With the heads `1` and `1 | 2` the sweep declines.

- `find_prefix_chains`, the first loop's test of `carriers` for a second row's carrier (old
  7412): removed with the record it guarded, for the reason given in the next entry. The
  test could not have been true in any case: `forced` lists each row once, and every row met there has
  the head `c.item`, so two rows differ in their carrier.
- The second loop's arm for a second carrier of the one cycle (old 7430-7434): reached by the new
  test `l01_23_groups_and_refusals` `chains_to_two_carriers_of_one_cycle_with_other_heads_agree_with_the_oracle`
  (three cases, each the oracle's verdict on lists of up to 4 items). The negative control (the
  type not kept) left all three verdicts unchanged. The reason: `is_carrier` accepts any carrier of
  the cycle without `carrier_set`, so `walk` maps it to node 0. The push only saved that test, and
  it is removed, with the proof at the site.
