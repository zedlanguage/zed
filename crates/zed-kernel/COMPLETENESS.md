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

For cover7's `empty.rs` arms that read a leaf operand: `bdd.rs` now makes every expression in
its module `build`, where `Part::expr` is private; `Part::connect` folds a leaf operand of an
`Or` or `And` away, and the other constructors (`not_expr`, `of_form`, and `xor::halves`'s
form) assert that no operand is a leaf. The rule is stated on `enum Form`. The test
`connecting_keeps_the_value_of_the_unfolded_expression` compares `connect` with the unfolded
expression on 2000 random pairs, leaves mixed in, at all 64 assignments; with `a | false` made
`false` it fails. `xor::halves` proves at the site, from its callers' contract (two or more
atoms), that neither operand is a leaf, so the claim does not rest on its `debug_assert`.

`bdd.rs` 385 and 391 (numbered at 847a31d3e, `chain_without` of a part that is no list, and of
an atom not on the chain) are now `unreachable!`, with the proof at the site: every caller
passes a chain of `Operands::Chain` (made only when `is_long_chain` holds) and an atom that
`chain_takes` found with the polarity passed. The arm that returned a leaf for the literal
fixed to the passed-over value is unreachable by the same reading and is folded into the same
`unreachable!`. All 551 kernel library tests pass.

`bdd.rs` 88-94 (numbered at 847a31d3e, `Tables::new`) runs only at compile time, in the
`const { … }` initializers of `TUPLES` and `MORPHISMS`; the note is at the site. 1017-1018
(`lists_opposite` of leaves) are reached by `leaves_are_opposite_only_to_the_other_leaf`, which
fails with the leaf arm made `p == q`. 2657-2658 (`Rest::next` when one sequence ends first) are
reached by `the_rest_of_two_sequences_orders_the_shorter_first`, which fails with the two arms'
orders swapped (on disjoint atoms: on shared ones the table can make a subtree of one set a node
of the other, which is passed over whole, and the count of keys read then follows the run).
2738-2740 (`Expr`'s `eq`) are reached by `expressions_are_equal_exactly_when_they_compare_equal`.

Direct tests, each failing under the control named: 846 and 849 (`union_of_literals` of an atom
both ways, and of none; `0` made `true`); 1917 and 1937 (`map_atoms` of a leaf, and of a block
with an odd count of literals; the leaf flipped, the odd literal complemented), by
`atoms_mapped_keep_the_value_at_the_mapped_assignment`, 300 random parts at all 64
assignments; 2269 (`disjoint_disjuncts` of a union met twice; the `seen` test dropped);
2354 (`taken_toward` through `Not`; the value not flipped); 2463 and 2478 (`clause` of `false`,
and of an operand met twice; `false` passed over, the `seen` test dropped, which lists `x_1`
twice); 2879 (`Part::xor` of no atoms), by `the_exclusive_or_of_no_atoms_is_its_constant`.

Proved at the site, now `unreachable!` or noted: 1372 (`choose` of two `false` branches, equal
and so answered by its first test); 755 (`Form::holds` of `Not`: the one caller, `negate`, asks
only in its branch for a choice, after its branch for `Not` declined; the arm is kept as a
comment-proved general answer); 2499 (`clause` of an `Or`, declined before by `is_or`); 2898,
2907 and 2927 (`Part::xor` and `node`: `node` and `found` give only expressions); 2976-2977
(`xor::meet` of two lists: its one caller, `halves`, passes two lists only as literals of two
atoms); 3004 (`pair` of a chain that lists other than two, after the test for a chain of two);
3576 (`reindex` of more than one new block: every call of `replace` passes none or one); 3717
(`same_seq` of an empty and a non-empty sequence: both calls, in `implies_by_blocks`, pass two of
equal length).

`print.rs` (numbered at 847a31d3e): 1311-1312 (`part`'s `operand` of a leaf) are now
`unreachable!`, with the proof at the site (no form has a leaf operand; see `enum Form`).
53-55 (`surface_operand`) is the `#[cfg(test)]` helper in the table above. Open, with what was
found: 908, 912 and 997-1006 (`folded` and `meet_of_literals` on an `&` node of the morphisms) and
960 (`meet_text` refused). A probe of 6,000 random types of unions, meets, differences and tuples
of morphism types (depth 3 to 7, three literal key and value types, exact, partial and bounded
arrows) reached `meet_text`'s `Empty` arm 25 times and an `&` node in `meet_of_literals` once
(999, already decided), but never an `&` of two meets of literals: every such meet came out as one
list, as `Connect::zipped` joins two chains under `And` at once (`zip_chain`). No proof was found
that a list equal to a meet of its atoms is always a chain, so the arms stay; the next round
should try that proof (a canonical form of a conjunction among `Bdd::List`s) or find an input.
The other print.rs lines of the list (730, 979, 985, 1031, 1048, 1533-1547, 1596-1641, 1768,
1918-1950, 1975, 2054, 2069), `types.rs` and `empty/refused.rs` are not yet taken (handoff).

The cut-edge test of the parent walk in `gfp` (`bes.rs`, `is_cut` in the walk) was missing: with
the test removed from the walk, every `decide` test still passed, since a `lo` that is too small
stays sound and the later passes recover it. The test
`the_narrowed_greatest_fixed_point_does_not_count_a_cut_edge_twice` calls the narrowed `gfp`
directly on an `Or` cycle with one way out and fails without the test (the `Or` node loses its
one counted child). For an `And` parent the test in the walk is redundant: a cut child already
makes it dead in the first pass.

`bes.rs` `delete_cascade` 645-689 (numbered at 847a31d3e: the kill of a tuple cycle with no
seed, and the cascade after it) is reached by the test
`a_tuple_cycle_dies_when_its_last_seed_does`, which calls `delete_cascade` directly and checks
it against the game: no system drawn for `decide` makes the cascade kill a node, and no proof
that `decide` never does was found (it would need an exit node true in the least fixed point of
`bounds` and false in its last pass). With the kill on a cycle's last seed removed it fails
(node `a`); with the count-down of a parent's need removed it fails (node `e`). The second least fixed point of
the one-`Mor` step is closed: the 40,000 draws never reach it, a search of about 3.6 million
draws (4 to 43 nodes, few `Mor` nodes) found 20-node systems that do, and one is the test
`one_morphism_whose_assumption_fails_takes_the_second_least_fixed_point`; with the second pass
disabled it fails (node 15 answered inhabited, the game says not). A proof that the pass is
unreachable was tried first and does not hold. The random test now also draws 420,000 wide
systems (4 to 43 nodes, a `Mor` rate of 1 to 5 in 40 per system); they reach the second pass
2 times (draws 89,504 and 413,455; at first 600,000 were drawn, which pushed the test near its
24 s limit and reached it no more), checked in two tests (`..._drawn_at_random` and
`..._drawn_at_random_second_half`) that each assert their hit, and with the second pass
disabled it fails. The proofs relied on above (cover2's
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

Fifth round (cover7, 2026-11-18), `empty.rs` only. Coverage re-run at zed-impl 16279bfc5 (the
short-address pieces left out, 4 jobs, load 54 to 146): 2,665 pieces, 23 failed (the pieces that
link executables fail under `-C instrument-coverage`; `group_oracle` and `case_wake` timed out, so
their coverage is missing). `empty.rs` has 8,906 instrumented lines, of which 332 were not
reached; the list with each line's text is
`wt/coverage/TEST-kernel-unreached-paths-4-empty-16279bfc5.txt` (numbers at 16279bfc5).

Closed, 27 lines (20 arms):

- Five `(false, true) => {}` arms (7076 `cycle_meet`, 7366 and 7516 `find_prefix_chains`, 8902
  `check_chain_witness`, 13505 `list_rows`), now `unreachable!`. Each follows a test that the atoms
  are finite. `Atoms::set` is the one writer of `names` outside a test, and it does not list a name
  whose part is `AtomPart::none()` (`bare` false, payload empty) when the atoms are finite. `zip`
  assigns `cofinite` after cloning, but the value it assigns is the clone's own, and the universe
  constructor (`types.rs` 2018) sets it on a part with no names. 5 lines, 5 arms.
- `read_two_sat`'s reading of a diagram node with two inner branches as the union of its arms
  (`At::Arm`: 12289, 12351-12354, 12358-12363), removed. The match is now `(None, None) =>
  unreachable!`. The reason: `branch` of a list is `Bdd::view`, which puts the leaf of the first
  block's value on one side, so one branch is always a leaf. 10 lines, 3 arms.
- Existing `unreachable!` lines whose proofs were re-derived: 2154, 2675, 3546, 3558, 10780,
  10781, 11300, 11541, 12851, 14866, 14874, 14931. 12 lines, 12 arms.

New test: `types::empty::tests::read_two_sat_agrees_with_enumeration_on_built_and_random_parts`
(built parts, and 3,000 random parts of five rows checked against enumeration). It reaches no
listed line, but it is the first test that calls `read_two_sat` directly. Negative control:
`contradiction` adding no clause fails it (`Bdd(false)`, solver `true`, enumeration `false`).

Open, 305 lines, with the reason for each group:

- 11430 `pair_picks`: has an `unreachable!` whose proof (through `extract`, `pair` and `read`)
  was read but not re-derived this round.
- `read_two_sat` 12421-12422, 12438-12440, 12451-12452: these need an `or` operand or a forced
  operand that is a leaf. A diagram never gives one, so only an expression form with a leaf
  operand would. Proving no such form is built means checking every `Part::expr` site in
  `bdd.rs` (cover4's file).
- The fork and blame restore paths (`tuples_on` 5722-6057, morphisms 10868-10971, 4725-4726,
  4977-4983, 5114-5119, 6150): need a search that meets a fork under a trial budget. No built
  input found this round.
- `nested_pieces` 6799-6859, `find_prefix_chains` 7520-8655, `chain_rep` 8664-8710,
  `check_chain_witness` 8752-9384, `find_rep`'s `no_keys` 9973-10198, the `decided` parts
  fallback 4633-4643, `system` 14808-14809, and about 90 single lines elsewhere: not studied this
  round.

Sixth round (cover8, 2026-11-19): cover4's open list outside `empty.rs`, at zed-impl 4f7bb8726
(old numbers from 847a31d3e mapped by `git diff -U0`). Coverage measured with an instrumented
build of the kernel's unit tests (`build/cov-k`, `-C instrument-coverage`), one filtered run each.
Baseline 567 kernel unit tests passed.

Closed in `types/bdd.rs` (numbers at this round's commit):

- `Bdd::reaching`: the `seen` test that skips a node met twice, and the join of two states, are
  `unreachable!`, with the proof at the function. `Bdd::view` puts a leaf on one side of each
  node, so the nodes reached form one chain, each with fewer literals than those before it, and
  live lists have distinct ids. The unused `join` argument is removed, with its closure in
  `list_boxes` (`types.rs`). The leaf input and a stop by `f` are reached by
  `bdd::tests::reaching_visits_the_nodes_a_walk_of_every_path_finds`, which compares every call
  with a walk of every path (529 lists, 562 stops). Control: with `f`'s `false` ignored the test
  fails ("stopped at call 1").
- `Part::before`'s tie of digests: `a_part_goes_before_itself`.
- `Part::not_as_kept`'s `Form::Not` arm: `the_complement_as_kept_of_a_not_is_its_operand`.
- `Part::choice_of_as_kept`, two chains with two opposite literals (`return None`) and the final
  `None` for no condition or two: `a_union_with_two_conditions_or_none_is_no_choice_as_kept`,
  with one-condition cases that give the choice.
- `Bdd::implies_by_blocks` on an operand that is a leaf: `unreachable!`, with the proof at the
  site. `absorbed` is called only after `Part::zip_at_once` gave `None`, which it never gives
  for a leaf operand.
- `union_rows` passing over an expression met twice, `taken_toward` passing over a cell in
  `seen`, `atoms_unseen` stopping when `f` fails on shared set nodes:
  `walks_pass_over_what_they_met_and_stop_when_f_fails` (the controls for these three were
  reasoned, not run: each check removed makes its assertion fail).

Open in `types/bdd.rs`. No kernel unit test reaches these, and this round built no input for
them:

- `Expr::link` with a complement that is an expression not holding `self`.
- `Connect::negate`: a `Not` whose operand is an expression, and a complement made through a
  choice that gets a `Source::Form`.
- `Connect::choose`: the `xor::xor_choice` return, and the rule for two choices on one condition.
- A walk's `continue` at an expression already in `exprs` (about line 2270), the join of two
  blocks of one value in the merge at about line 3847, and a literal set false that empties the
  last block (about line 4063).

Seventh round (cover9, 2026-11-19): the remainder of the sixth round's open list, at zed-impl
a279c3f51. Coverage measured with instrumented builds (`build/cov-k`, `-C instrument-coverage`):
the kernel's unit tests, and every test of l01_22_type_representation, l01_23_groups_and_refusals,
l01_23_subtyping and l01_26_type_resolution, each run alone (2079 tests), with the kernel's shared
library given to `llvm-cov`.

Closed:

- `empty/refused.rs`, `written` with a definition that has parameters:
  `a_site_on_a_cycle_writes_the_parameters_of_its_definitions` (l01_23_subtyping). Control run:
  with the parameters left out, the line read `type L = #nil | #cons(T, L(T));` and the test
  failed.
- `types.rs`, `makeable`'s `Value::Path` arm:
  `a_membership_keyed_by_f32_values_and_asked_of_a_path_agrees_with_contains`. Control run: with
  the arm answering `true` the test still passes, because the row index then reads the path as
  `Kind::Other` and gives the same verdict. The arm saves work and changes no verdict, so no test
  can fail on it; the test pins that `Membership::contains` agrees with `Type::contains` there.
- `types/bdd.rs`, `Connect::negate`'s `Source::Form` arm: reached once by the integration groups.
  Not reached by a kernel unit test.

Open, with the reason. Every line below has count 0 in both runs:

- `types/bdd.rs`: `Expr::link` with a complement that is an expression not holding `self`;
  `Connect::negate` on a `Not` whose operand is an expression; `Connect::choose`'s
  `xor::xor_choice` return and the rule for two choices on one condition; the lines near 2270,
  3847 and 4063. No input was built for them. Proving them unreachable would mean proving facts
  about how expressions are shared across threads and the order of the caches, and this round
  did not prove that.
- `types.rs`: the `Value::Family`/`Value::Path` arms of `kind`, `kind_status` and `spine`, and the
  `Float32` arms of `erasable` and `witness` (about 5160, 5319, 5486, 5507, 5531). `holds_in` has
  three callers, and each one is given only makeable values. That makes the Path and Family arms
  unreachable only if no maker ever makes a path or a family value. No constructor for one exists
  in `types.rs` or `types/*.rs`, but this round did not prove it for the whole crate, so the arms
  stay rather than becoming `unreachable!`. An `f32` key in the test above did not reach the
  `Float32` arms.
- `types.rs`, the order ties (about 1081-1298, 7992-8032, 8319-8329, 8592-8597): every one needs
  two distinct parts with equal digests. With full-width digests no test meets one. The
  `short-addresses` feature (8-bit digests) is the build that could, and this round built no
  instrumented copy of it.
- `print.rs`: the listed lines and cover4's meet arms. No test reaches them, and none was written.
- `empty/refused.rs`: the `Kind::Bot` set for a fixed node (130), `Recheck::Decided` and
  `Recheck::Refused` (146, 148, 432, 437), the shared-part lift with a local definition (178),
  `listed([])` (281), "one cycle" (373), the `_ => &[]` arm (383), the tuple that is `None` (401),
  the "lets the checker decide it" ending (442) and the repair over several definitions (459-462).
  Every refused fixture known reads a meet, so the repair leaves the member to the search and the
  `Decided` ending never comes. Every fixture has two or more cycles, and its tuple is always
  present. `listed([])` would be unreachable if `open` could be proved never empty, and that
  proof is not done.

Eighth round (cover10, 2026-11-18): the seventh round's open list. Coverage measured with the
same instrumented build, `l01_23_subtyping`'s `group_refusal` tests run alone, with the kernel's
shared library given to `llvm-cov`.

Closed:

- `types.rs`, the `Value::Path`/`Value::Family` arms of `kind`, `kind_status` and `spine`: now
  `unreachable!`, with the proof at `makeable` (its three callers, and by induction a `Lit`
  holds only values of its own kind). `Kind::Other` is gone. Control run: `makeable`'s `Path`
  arm answering `true` makes
  `a_membership_keyed_by_f32_values_and_asked_of_a_path_agrees_with_contains` panic at the new
  `unreachable!`.
- `types.rs`, the `Float32` arms of `erasable` and `witness`:
  `a_membership_reading_f32_values_by_their_spine_agrees_with_contains` (reached 8 and 4 times).
  Control run: `witness` giving an `f64` value makes it fail.
- `empty/refused.rs`, a refused meet's open operands: the message now names them by the
  program's text in the order written, from the nodes `system` records per meet (`Why::meets`),
  with the proof that every meet node has its record at `meet_operands`.
  `a_meet_named_by_the_message_lists_its_open_operands_as_written`; controls run: the old zip of
  sorted nodes, and the record not reversed, each name `_` and `Q` and fail.
- `empty/refused.rs`, `open` never empty: proved at the site (a node in `tuples` has two
  distinct children in the refused component, all refused in that run), and `listed([])` is
  `unreachable!` with the proof that each caller passes a non-empty list. The `_ => &[]` arm is
  gone.
- `empty/refused.rs`, "one cycle":
  `a_refused_definition_that_refers_only_to_itself_makes_one_cycle`. Control run: the arm
  tested on `cycles == 0` prints "1 independent cycles" and fails.
- `empty/refused.rs`, the repair over several definitions:
  `a_repair_over_several_definitions_lists_them_by_name`. Control run: the first name dropped
  from the list fails.
- `empty/refused.rs`, the shared-part lift outside a message (178):
  `a_site_outside_a_message_declares_a_part_written_twice_after_the_definitions`. Control run:
  the lifted parts not declared fails.
- `empty/refused.rs`, a recursive meet among a meet's operands (316):
  `a_meet_written_inside_a_meet_is_read_as_its_operands`. Control run: the inner meet not read
  as its operands panics at the count check.
- `empty/refused.rs`, `first_member` finding no member (260):
  `a_type_reading_no_group_has_no_refusal_site`. Control run: returning the last type walked
  panics at `site`'s `unreachable!`.
- `empty/refused.rs`, `Recheck::Refused`: reached once by the tests above.

The fixtures of the "one cycle" and several-definition tests were found by a random search
over groups of one to three definitions, each a union of one to three arms, an arm a pair, a
1-tuple or `int -> x`, and `x` a reference, a reference met with `(_, _)`, with a reference, or
with `int -> ` a reference, or `#k` (seeds 0 to 399999): 1017 members refused for
`Refusal::Group`, 116 of them with one cycle, 11 with a repair over several definitions. With
no meets allowed, the same 400000 seeds give no refused member at all.

Open, with the reason:

- `empty/refused.rs`, the `Kind::Bot` set for a fixed node in a re-check (130), and
  `Recheck::Decided` with its ending "lets the checker decide it" (500, 510). None of the 1017
  refused members above reaches them. A repair is decided only for a member that reaches no
  meet or difference (`settled` with `wide` false), and every refused member found reaches a
  meet: the search found no refusal without one. Proving that a member reaching no meet is
  never refused would close both, and is not done.
- `empty/refused.rs`, the tuple that is `None` (the path past `if let Some(..) = &tuple`, count
  0 at its closing brace): every refused member found reaches a refusal for shape, and each such
  refusal lists at least one `And` node (`bes::refusal` keeps a component only with
  `branching_and >= 1`). A member refused in a run with no refusal for shape among the nodes it
  reaches would take it. Whether `decide` can refuse a node that way is not proved here.

The rest of the eighth round (cover10, 2026-11-18), at zed-impl 6f871b3fc: the order ties of
`types.rs`, `types/bdd.rs` and the meet arms of `types/print.rs`. Two instrumented builds: the
normal one (`build/cov-k`) and one with the `short-addresses` feature, 8-bit digests
(`build/cov-ks`). In each, the 21 modules of `l01_23_subtyping` were run one at a time (benches
skipped), and `l01_37a_short_addresses` was run in the short build.

`types.rs`, the order ties. The short build reaches nearly all of them. That includes:

- the tie of payload digests in `atom_names` (601 times);
- the `Step::Lens` resume in `tuple_lens`;
- the `Cells`, `Sets`, `SetsInOrder`, `SetRest` and `CellRest` arms of `walk`;
- the `Exprs` arm with its exclusive-or test;
- `Expr::clone`;
- `Key::order`.

In those ranges, 192 lines are reached in `l01_23` and 15 are not. These lines have count 0 in
both short runs:

- In `atom_names`, the return when two names differ after a resume. A resume starts past the
  last name read, and two maps that tied up to it can still differ there; no input was built
  for this.
- The `Cells(None, Some)` and `Cells(Some, None)` arms: two lists whose digests tie but whose
  lengths differ.
- The `Exprs` arm's `(Some(_), None)` case: an exclusive or and an expression that is not one,
  with tied digests.
- The early returns of `Key::order` after its digest tie (about 8616-8641), and those of the
  key comparison at about 8928-8938.
- `Node::same_head`, which no test calls in either build.

These lines need a collision between two particular shapes. No input was built for them, and no
proof was made that they cannot happen. A tie of 64-bit digests can occur, so the arms must stay.
The short-build reach above is not protected by any test. `merge_check` runs the short build only
for `l01_37a_short_addresses` and `l01_37_oracle`, and `l01_37a` alone reaches only the
`atom_names` and `tuple_lens` ties and the `Sets` arms. It reaches neither the `Exprs` arm nor
`Key::order` (both count 0).

In the short build, three tests of `l01_23_subtyping` fail. All three are in the normal build's
`l01_23` piece and pass there. Each failure was checked, and none gives a wrong verdict:

- `refusal_cost::random_3_cnf_seed_2_is_refused_at_8_bits_and_16` (now
  `random_3_cnf_seed_2_is_refused_at_8_bits_and_found_at_16`): at 16 bits (5 models) the
  short build answered `Inhabited` where the normal build refused. The value it shows was
  printed and is a member of the type (`contains` agrees). The normal build now finds a value
  too (REFUSAL-r3-seed2-16-inhabited); the test asserts `Inhabited` in the normal build only,
  and under `short-addresses` takes a refusal or an `Inhabited` verdict whose value is in the
  difference, since the short build orders the pairs of `refine` by other digests.
- `listing::tuples_are_checked_against_the_tuple_types_that_may_hold_them`: the same 13 tuples
  come out in another order. The boxes are listed in digest order; in the normal build the
  first box listed is already box 1, not box 0. The test pins one build's digest order, and
  the comment "each box in turn" holds only for that order.
- `oracle::the_systems_reaching_rare_branches_both_ways_agree_with_the_oracle`: system (4, 3114)
  is decided on both routes in the short build (2, 0, 0), where the normal build refuses once
  (1, 0, 1). Every verdict was checked against the oracle and agrees.

Closed at zed-impl 809acbd54: all three now pass in both builds (all 22 `l01_23` modules run in
each). `listing` compares the tuples as sets; the `oracle` test asserts the verdicts only (the
refusal counts stay in its table as the full build's record); the 16-bit assertion of
`random_3_cnf_seed_2` asserts that no verdict is `Empty`, that a refusal is at shared cells, and
that an `Inhabited` verdict rests on a value of the difference, found with the new
`Type::witness` and checked with `Type::contains`. Control run: `Type::witness` returning `None`
fails that test in the short build, so its `Inhabited` arm is reached there.

`types/bdd.rs`:

- Closed: `Expr::link` with a complement that is an expression not holding `self`. It is reached
  7.35k times in the normal build. The seventh round recorded count 0 here, and that was wrong.
  Control run: the arm returning the expression itself as its complement makes 10 tests fail,
  among them `oracle::verdicts_agree_with_the_oracle_in_any_order` and
  `one_pass::random_meets_of_lists_and_exclusive_ors_are_decided_as_enumeration_decides_them`.
- Closed: `Connect::negate` on a `Not` whose operand is an expression. It is reached 5.56k times
  in the normal build, and the seventh round's count 0 here was also wrong. Control run:
  returning the `Not` itself instead of its operand makes the same 10 tests fail, among them
  `one_pass::random_parts_of_one_choice_per_component_are_decided_as_enumeration_decides_them`.
- Closed: `Connect::negate`'s `Source::Form` arm. The counts above are of the integration
  groups only; the kernel's own unit tests reach it. Control run: the arm making `Not` of the
  expression instead of the form kept fails `bdd::tests::a_complement_is_found_while_it_lives_and_rebuilt_alike_after`
  and `bdd::tests::batch_and_single_file_agree_on_a_complement_whose_holder_was_freed`.
- Closed: the `xor::xor_choice` return in `Connect::choose`, by the new unit test
  `bdd::tests::choices_whose_branches_join_to_opposite_exclusive_ors_are_one` (two choices on one
  condition joined branch by branch; `c&x | !c&!x` built directly is found before `choose`).
  The return is a shortcut: with it skipped, `Part::union_as_kept` reaches the same node, so the
  test passes (measured). Control run: the arm returning `x` fails the test.
- Closed (TEST-kernel-unreached-paths-4, cover11): the three paths left at count 0 above.
  - `Part`'s walk of expressions has two checks of `exprs`. The first, at an `(e, None)` entry,
    is reached by `bdd::tests::three_valued_operations_keep_the_assignments` (`e & !e`, two
    clusters sharing an operand), found by a temporary probe; the counts above were of the
    integration groups only. Control run: that check removed fails the test on the new
    `debug_assert!` below. The second, at an `(e, Some(ops))` entry (the "about 2270" here), is
    now a proof at the site and a `debug_assert!`: between the push of `(e, Some(ops))` and its
    pop only entries for operands of `e`'s cluster, at some depth, are popped, and none of them is
    put in `exprs` before its own operands are, so `e` cannot be put there in that time.
  - The `continue` in `Cell::atoms` at a cell whose atoms are made: kept, with a comment proving
    that one thread never reaches it (a cell is pushed with no atoms, only cells below it are made
    before its pop, and a list in its one form meets no cell twice). Only another thread making
    the same cell's atoms at that moment reaches it, which no test does; the skip only saves
    making the same set again.
  - The literal set false that empties the last block of two or more (`or_literal`): now
    `unreachable!`, with the proof at the site. In a list's one form two or more blocks end in a
    block of two or more literals, so one literal set false leaves one; one block is the `at == 0`
    arm.

`types/print.rs` (the file cover4's list means; the earlier entries say `print.rs`): `folded`,
`meet_text` and `meet_of_literals` have count 0 in both builds, since `l01_23` prints no meet of
morphism types. cover4's open question still stands: whether a list equal to a meet of its atoms
is always a chain. This round did not work on it.

Closed in the next round. cover4's question is answered yes, by proof: a list is in its one form
(module `list` in `bdd.rs`), whose first block holds every literal under which the function is
constant; the meet `a1 & … & ak` is constant (`false`) under each `!ai` and under no other
literal, so the list is the one block `{!a1, …, !ak}` of value `false` with default `true`, the
chain under `And`. `Connect::zipped` calls `Bdd::zip_chain` before `Part::connect`, and
`zip_chain` answers with a list whenever one operand is such a chain and the other a list;
`xor::meet` joins two literals as a list; so no `&` node has two operands that are meets of
literals. `folded`'s `&` arm is therefore unreachable: `folded` now reads the one list, with
the proof at the site and `unreachable!` for any other form. The new module
`l01_23_subtyping::printed_meets` (3 tests) prints meets of morphism types and reaches every
arm of `meet_text` (`Inhabited`, a value no literal names, one bound, both bounds, neither
written, and a refused comparison of the bounds, using `refusal_cost::r3(16, 7)`) and the `&`
arm of `meet_of_literals`, with a meet joined to an exclusive or. Control runs: `Inhabited`
giving `None` fails the first test; the `&` arm's `&&` made `||` reaches `folded`'s
`unreachable!` in the second; `Refused` printed as `Never` fails the third. All three pass in
both builds.

The order ties, closed in the same round where a test reaches them. The new test
`l01_37a_short_addresses::collide::families_that_tie_in_digest_reach_every_arm_of_the_order`
runs in the short build in `merge_check`'s `l01_37a` group. It builds seven families of types that
differ in one place only, so that many pairs tie in 8-bit digest: unions of `#a(int)` and
`#n<i>(int)`; exclusive ors and choices of morphism types; unions of morphism types by bit mask;
negated choices and meets with an exclusive or; and recursive groups that differ in name, in a
payload literal, or in shape. On every pair it checks that the order is antisymmetric and is
`Equal` only for one member (the members are distinct by construction; texts would not do, since
two groups of one name print alike, and `==` on `Type` is the order itself), and that the sorted
family is in order. In the full build no pair ties and the test asserts that. Temporary probes on
each arm showed these reached by the test: the names that differ after a tied payload in
`atom_names`, and that tie itself; the `SetsInOrder` ends of `walk`; in the `Exprs` arm the tie,
both exclusive-or orders and both mixed cases, and the `Source::Form` operands equal and unequal;
in `Key::order` the differing groups, the canonical forms unequal and the names unequal; in
`Canon::order` the tie of forms, the class heads unequal and the held types tied and unequal.
Control runs, each in the short build, each failing the new test while the other 8 `collide` tests
pass: `atom_names` answering `Equal` for two names that differ; the payload tie dropping its
`Step::Names` resume; the `SetsInOrder(None, Some)` end answering `Equal`; the `Exprs` arm's
`(Some, None)` case answering `Equal`; the form operands answering `Equal` when unequal; and
`Key::order` answering `Equal` where the canonical forms differ and where the names differ.

Still open:

- `Canon::order` answering on unequal class heads. The test reaches it, but only outside `blind`,
  where `Key::order` compares the definition graphs (`names_order`) after it, and they decide
  the same pairs: the control making that return `Equal` passes (measured). Under `blind` its
  answer is the only one, since `names_order` is skipped, and two groups of different shapes would
  be given one number in an emptiness search. `blind` runs only in `empty.rs`'s `Ids`, and no
  test calls `Canon::order` under it: probes found no call in the four `l01_37a` modules or in
  the `rec`, `deep_rec`, `setop`, `rec_order`, `group_refusal` and `witnesses` modules of
  `l01_23` in the short build, although `Ids` buckets held tied keys there (985 in `setop`), all
  of them lists and tuples. An attempt with an empty group `S = #c(p, S) | #d(S)` and an
  inhabited `S = #c(p, S) | #d(p)` that tie in digest, decided together in unions, tuples, a
  subtype check and one tuple of 200 groups, put no two groups in one bucket: the searches
  decide such groups without numbering them. A test needs a search that numbers two different
  groups whose canonical forms tie.
- The `Cells` and `Sets` ends of `walk` (`(None, Some)` and `(Some, None)`). The probes never
  saw them, in the new test or in the `l01_37a` group; only the `SetsInOrder` ends are reached.
  No input was built for them.
- `Node::same_head`, which no test calls.

Closed by cover11 (TEST-kernel-unreached-paths-4), except the part named at the end:

- `Canon::order` under `blind`. The new test
  `l01_37a_short_addresses::collide::an_emptiness_search_tells_apart_groups_whose_forms_tie`
  builds 600 groups `A = #a | #c<x>(int, A)`, `B = #b | #c<x>(int, B)`,
  `C = #a | #d<x>(int, C)` with `M = A & B` (empty) or `M = A & C` (inhabited), for x in 0..300.
  The ends `#a` and `#b` are held types, which the group's decider does not meet, so every `M` is
  left to the search (the test asserts `decided_by_group() == None`). For each pair of one empty
  and one inhabited `M` that tie in digest it checks that their union is inhabited and their
  tuple empty, each with the emptiness answers forgotten first; in the full build no pair ties
  and the test asserts that. A temporary probe showed the arm reached under `blind`, deciding on
  the children's classes (`xs.cmp(ys)`) with the heads equal. Control run: the arm answering
  `Equal` under `blind` fails the test in the short build (the tuple assertion), while the other
  `collide` tests pass. A comment at the site names the test.
- Still open: the class heads alone deciding under `blind`. An earlier family (ends held as
  `#a(int)` and `#b(int)`, atoms of tuple payload) reached unequal heads under `blind` (probe),
  but the control making only that case answer `Equal` passed: every pair differing in emptiness
  there also differed in the held types or the children's classes, compared after. No family was
  found where only the heads tell an empty group from an inhabited one: the decider reads atom
  names, so groups that differ in an atom name on a path that decides emptiness are decided
  without the search. Whether such a family exists is not proved either way.
- The `Cells` and `Sets` ends: removed. Every construction of `Walk::Cells` and `Walk::Sets` (in
  `walk` and in `set/tests.rs`) passed `Some` on both sides, so the arms were unreachable; both
  now hold references, and the end arms remain only for `SetsInOrder`, which reaches them.
- `Node::same_head`: removed, with `impl PartialEq for Shape` (its one user, itself used only by
  `unfold::partial`, which now matches the shape) and the `Tree::same_head` method;
  `Expr::same_head` is now an inherent method and `walk::equal` takes expressions only.

Ninth round (kernel12, 2026-11-19): the row's list outside `empty.rs`, re-measured at zed-impl
23b16794b with `tools/run_tests.sh --cov` (every piece, the kernel's unit tests in chunks), the
profiles merged and read with `llvm-cov export`. Four pieces left no profile and are not counted:
`group_oracle`, `case_wake`, `zedc_presburger` and `l01_36b`. The lines at count 0 outside
`types/empty.rs` are listed in /home/luke/Work/wt/coverage/TEST-kernel-unreached-paths-4-kernel12-23b16794b.txt
(186 lines, `file line text`, numbered at 23b16794b). 84 of them are in the files and functions
the row names; the other 102 are counted at the end.

Closed by a test, each with a control run that the new test fails while the others pass:

- `bes.rs` `delete_cascade` (673, 699, 706): `a_cascade_passes_over_the_dead_and_keeps_what_still_has_a_seed_or_a_child`
  calls it directly (no system drawn for `decide` makes it kill a node). Controls: a node killed
  on any decrement of `need`; on any decrement of its seeds; `kill` not testing `cur`.
- `bes.rs` `gfp`'s `Kind::Mor` arm of the cut test (435):
  `the_narrowed_greatest_fixed_point_keeps_the_edge_of_a_morphism_to_itself`. A `Mor` node is
  alone in its tuple component (edges out of `Mor` nodes are not followed there), so the arm is
  reached only by a `Mor` node whose child is itself. Control: the arm answering `true`.
- `bdd.rs` `clause`, a literal under a `Not` (2575): an assertion added to
  `a_clause_reads_a_shared_operand_once`, on the `And` of `Not(!a4)` and `a5`, read as the atoms
  4 and 5 taken (only `negate` makes `Form::Not` in product code). Control: that arm pushing to `refused`.
- `print.rs` 1051, the `", "` between the arguments of a member written by name (outside the
  row's functions, closed with them): `a_member_of_two_parameters_written_by_name_lists_its_arguments`.
  Control: the separator dropped.
- `rec/group.rs` 192, a rejection inside a message: added to
  `a_rejection_quoting_types_that_share_a_part_declares_the_part_first`. Control: the test of
  `local` made `true`.
- `rec/group.rs` 261, a recursive occurrence with arguments where the definition has no
  parameters: `a_recursive_occurrence_given_arguments_where_there_are_no_parameters_is_rejected`
  (`N = () | (int, N(int))`). Control: the arm writing `N()`.
- `rec/unfold.rs` 276, a part kept unevaluated asked for its group's members:
  `a_part_kept_unevaluated_has_no_group_members`. Control: `Key::members` without its
  `At::Member` test.

Closed by a proof at the site:

- `bes.rs` 687, a node of `u_set` outside every tuple component in `delete_cascade`'s queue
  loop: `unreachable!`, since `u_set` is the union of the tuple components `t_sccs` it is given;
  the test `cp != u32::MAX` of the parent loop is removed by the same proof.
- `empty/escape.rs` 150, a value of a type's integers that is no integer: `unreachable!`.
  `Type::lit` and `Type::ints_of` (which asserts it) put only integers there, the universe holds
  none, and `Lits::zip` and `Lits::not` keep only values of their operands.
- `empty/escape.rs` 255, `intersect_many` of one set: the shortcut is removed. Both callers pass
  two sets or more, and the general branches give the set itself for one.
- `empty/escape.rs` 1082, a clause of one atom: `unreachable!`. The loop before it ends only when
  no place narrows, strengthening only cuts a clause to two atoms, and an empty clause returns
  earlier.
- `rec/unfold.rs` 371, `component` of an eager part: `unreachable!`. Its one caller in product
  code is `eval`'s `Step::Component` arm, which comes after the eager arm.

Guards whose proofs stand from earlier rounds (each a comment at the site; not reached, as
proved): `bes.rs` 352, 438, 488, 619, 629, 664, 772; `bdd.rs` 395 and 405 (`chain_without`),
1442 (`choose`, two `false` branches), 2578 and 2583 (`clause`), 2983, 2994, 3016, 3079 and 3114
(module `xor`); `empty/escape.rs` 517, 660; `rec/group.rs` 100, 256; `rec/unfold.rs` 350, 516.
The failure branch of a test: `rec/group.rs` 874.

Open, with the reason:

- `bdd.rs` `choose`, a `true` and a `false` branch (1443, 1444). This round wrote a proof that
  no caller passes two unequal leaves, and withdrew it before it landed: it holds only if no
  part that is not a leaf stands for a constant. Branches of a choice are operands of `And` and
  `Or` forms or chains of one literal or more, so no leaf; but an expression is not kept in one
  form, and that an `And` of two such branches is never the leaf `true` (nor an `Or` the leaf
  `false`) was not proved for every route through `zip`. The arms are correct as written.
- `bdd.rs` `choose`, the rule for two choices on one condition (1491, 1495, 1503): no input was
  built where `Part::union_as_kept` fails on two meets that are both choices on one condition.
- `print.rs` `meet_of_literals`, an operand already met (1005) and the push of an operand not
  met (1022): reached only by a meet of morphism types that shares an operand between two of
  its own meets; `printed_meets` has none, and no input was built.
- `print.rs` `collect` (1940, 1946, 1952-1957, 1960-1964, 1972): an alias of a node whose text is
  one name; a node neither a tuple nor marked; and a marked node whose body waits on a
  definition of a cycle (the `WAIT` arms and `defs::fill`). No message in any test collects a
  cycle of definitions with a counted or named member; no input was built.
- `empty/escape.rs`: `node` meeting a type again on its path (455) and a second stop that differs
  (526); `decide_counted`'s unsatisfiable clauses with `exact && !wide` (1127) and an empty
  carrier head (1350, 1351); `take` on a cell whose integers are inside the head (1442, 1443);
  the re-sort for another modulus (2112, 2113). No input was built; each needs a list group of
  a shape the tests do not form (for 455, a cycle of two list members met through
  `escape::decide`).
- `empty/refused.rs` 130, 146, 469, 500, 510: the reasons of the eighth round stand (every
  refused member found reaches a meet, and every refusal lists an `And` node).
- `rec/group.rs` 133 and 205-206, and `hash.rs` 9: ties of digests, which only the short build
  can meet; the instrumented run here was of the normal build.
- `rec/group.rs` 566-570 (an instance made by another thread first, or freed), 805 (a thread's
  table dropped at its end), 820 (a poisoned lock), and `rec/unfold.rs` 78, 137, 170 (the same
  races and thread teardown in the unfolding caches): reached only when two threads race on one
  group or a thread ends during a run; no test does this.
- `rec/unfold.rs` 453, a parameter printed with the instance's arguments in `rope_with`: no test
  prints a definition's body under arguments; no input was built.

Counts for the 84 lines: closed by a test 9, closed by a proof 5, guards proved earlier 23, the
failure branch of a test 1, open 46.

The other 102 lines are outside the row's list and were not examined in this round:
`bdd.rs` 28 (among them `Tables::new`, a `const fn` run at compile time, 91-97, and the
`#[cfg(test)]` checks 4573-4645), `print.rs` 24 (among them the `#[cfg(test)]` helper
`surface_operand`, 53-55), `empty/sweep.rs` 27, `empty/shared.rs` 13, `empty/names.rs` 3,
`empty/refused.rs` 3 (guards: 198, 341, 456), `bdd/list/treap.rs`, `bucket.rs`,
`print/uses.rs` 1 each (guards).

Tenth round (kernel13, 2026-11-19): the ninth round's 46 open lines, line numbers at 23b16794b.

Closed by a test, each with a control run that the new test fails while the others pass:

- `bdd.rs` `choose`, the rule for two choices on one condition (1491, 1495, 1503):
  `a_choice_whose_meets_choose_on_one_condition_with_equal_unions_is_that_union` (the arms
  `c == d` and opposite conditions) and `a_choice_whose_meets_choose_on_two_conditions_keeps_their_union`
  (the arm `None`, an input found by a random search over the connectives and reduced by hand;
  the test checks the complement's values on all 64 sets of the atoms).
- `print.rs` `meet_of_literals`, an operand already met (1005):
  `a_meet_whose_operands_share_a_part_folds_the_meet_in_it` (`x & (m & x)`, over 38 `x`, since
  the digests decide which order the walk takes). The same test reaches the push of an operand
  not met (1022).
- `print.rs` `collect` (1940, 1946, 1952-1955, 1957, 1960-1962, 1972):
  `a_message_collects_the_definitions_of_a_cycle`, on four messages: a mutual pair
  `KM0 = #ma | #ml(KM1)`, `KM1 = #mb | #mm(KM0)`; `KT = #stop | (int, KT)` alone and inside a
  tuple; and `KN = (int, #stop | KN)`. Controls, each failing the test: an unmarked tuple not
  skipped (1946); a counted node that waits keeping its mark (1953); aliases not given the
  reference (1940); waiting bodies filled with nothing (1972).
- `rec/unfold.rs` `rope_with`, a parameter written as its argument (453):
  `a_part_s_name_writes_each_parameter_as_its_argument` (`pp(x, y) = (#pa, x, y | pp(x, y))` at
  `int, bool`, part named `bool | pp(int, bool)`). Control: `args[0]` for `args[*i]`; it needs
  the two parameters, since with one the control is the same code.
- `empty/escape.rs` `node`, a row tail outside the class of the first list (455, 526):
  `node_tests::a_tail_that_links_by_another_atom_is_outside_the_class` and
  `a_tail_that_ends_at_another_stop_is_outside_the_class`. Each asserts that `decide` gives no
  answer and that the type is inhabited. The control used was a panic in each arm, which shows
  the arm is reached; the first control tried, the arm falling through, did not fail the tests,
  since a later check refuses the same rows. So these tests show the arms are reached and the
  answers right, but not that the arms are needed for the answer.
- `rec/group.rs` 133, a node numbering probing past a tied hash of another shape: reached in
  the short build (1382 times in the kernel's unit tests, by a probe). Control: the tie taken as
  the same node; it fails
  `l01_37a_short_addresses::collide::an_emptiness_search_tells_apart_groups_whose_forms_tie` in
  the short build, while the kernel's own short-build tests pass.

Closed by a proof at the site:

- `bdd.rs` `choose`, two leaves (1443, 1444, and the guard 1442): the three arms are removed. Both `false` is `x == y`,
  answered first; `x` true with `y` false gives the parts `c` and `false`, and the reverse gives
  `false` and `!c`, which `Part::union_as_kept` joins by `Part::zip_at_once` first, giving the
  operand other than the leaf `false`: what the arms returned. The proof is of equal results,
  so it does not need the withdrawn claim that no non-leaf part stands for a constant.
- `rec/group.rs` 567 (`instance`, the instance made meanwhile): only the maker thread inserts
  into its own table, and between its two locks it runs only `eval`, and no product code of the
  crate calls `instance`; so `Some(first)` is not reached. The comment there said another thread
  may have made the instance meanwhile, which was wrong (each thread has its own table); it is
  corrected.
- `hash.rs` 9: under the short build, `SHORT` is `cfg!(feature = "short-addresses")`, so every
  call of `mix` takes this line; every short-build test reaches it. The coverage run did not
  measure the short build.

Re-examined, standing: `empty/escape.rs` 150 and 1082 (the ninth round's weakest proofs). For 150,
every write of a `Parts`'s `ints` in the crate was read; for 1082, each exit of the loops before
it. Each proof comment now says what was checked.

Reached, with no control: `rec/group.rs` 205-206 (`Group::new` keeping the groups it looked at
until the lock is released): 8540 times in the short build's kernel tests (probe). The line
exists so that no group is dropped under the lock, which would take the lock again; no test
makes the group looked at the last handle while the lock is held, which needs two threads.

Open, with the reason:

- `print.rs` `collect`, the arm `(false, false)` (1964): a node named but not counted whose body
  waits on nothing and is no alias and no tuple. Not reached by the four messages above, nor by
  four messages that print a tuple again in a later type (taken from the earlier print). A
  counted node is any but a tuple, a recursive type, a token and a part taken from an earlier
  print, so the arm needs a forced recursive node, or a forced token, whose text is not one
  reference; no such node was found, and no proof was found that none exists.
- `rec/group.rs` 566, 569, 570 (a dead handle in the table): another thread dropped the last handle of
  this thread's instance and has not yet removed the entry; 805; 820 (a poisoned `GROUPS`: a
  panic under it needs a panic in `Def` equality, which compares types through `Type::cmp`, and
  that the whole order never panics is not proved); `rec/unfold.rs` 78 (thread teardown), 137
  and 170 (two threads making one member or node). Each needs two threads racing, or a thread's
  end, at a chosen moment; no test does this.
- `empty/escape.rs` 1127, 1350-1351, 1442-1443, 2112-2113: no input was built (as in the ninth
  round).
- `empty/refused.rs` 130, 146, 469, 500, 510: as in the eighth round.

Found, not fixed: one recursive type written by two types of one message is defined twice, once
per type (`Part1` and `(Part2, Part2)`, with `Part1 = (int, Part1) | #stop` and
`Part2 = (int, Part2) | #stop`). A cycle's places are merged with none (`defs::reserve`), and
`Printer::remember` keeps no part holding a recursive node. Row FAIL-print-cycle-defined-twice,
test in /home/luke/Work/wt/failing-tests/FAIL-print-cycle-defined-twice.rs. Fixed in the
eleventh round (below).

Counts: the ninth round's open list, line by line from the list file, has 47 lines, not 46
(`collect` lists 12 lines, `escape.rs` 9). Closed by a test 20 (bdd 3, print 1005 and 1022,
`collect` 11, unfold 453, escape 455 and 526, group 133); closed by a proof 4 (bdd 1443 and 1444,
group 567, hash 9); reached without a control 2 (group 205-206); open 21 (print 1964; group 566,
569, 570, 805, 820; unfold 78, 137, 170; escape 7; refused 5). The 102 lines outside the row's
functions were not examined in this round either; they stay in this row.

Eleventh round (kernel14, 2026-11-19): the tenth round's 21 open lines, line numbers at
23b16794b. Each test below was run with a control (the change named) that it fails while the
other tests pass, unless the row says otherwise.

| Line | Closed by | Test or site | Control |
|---|---|---|---|
| `print.rs` 1964, `collect`'s arm `(false, false)` | test | `print::tests::a_recursive_type_whose_body_is_a_tuple_is_defined_by_the_tuple`: `KP0 = (int, KP1)`, `KP1 = #pa \| #pb(KP0)`, alone and with `(KP0, 1)` in one message | the arm given a reserved place, as a waiting body is: the message defines `Part3 = Part2` and `Part4 = Part2` |
| `rec/group.rs` 566, 569, 570, `instance`, an entry holding a dead handle | proof, code removed | `instance` now inserts `env` without looking: the dead-handle arm did what the vacant arm did, and the live arm (567) is proved not reached (the proof at the site: between the two locks the thread runs only `eval` of plain bodies, which calls no `instance`); a `debug_assert` checks the handle replaced is dead or missing | none needed: the arms are gone |
| `rec/group.rs` 805, `Drop for Env`, an entry no longer its own | test | `an_instance_dropped_after_its_entry_was_handed_on_leaves_the_entry` | `mine` read as `true`: the second instance's entry is removed |
| `rec/group.rs` 820, `Drop for Checked` on a poisoned lock | fixed bug and test | `a_poisoned_group_table_is_used_as_it_is`. Bug: after one panic holding `GROUPS`, every later `Group::new` panicked (`expect`) and `Drop for Checked` left its dead handles; both now take the lock with `PoisonError::into_inner`, since the map is whole between steps | either lock taken as before |
| `rec/unfold.rs` 78, `end_unit` after the thread's unit is dropped | test | `a_unit_ended_after_its_thread_dropped_it_is_left` (a thread-local whose destructor runs after the unit's) | `UNIT.with` for `UNIT.try_with`: the destructor panics and the process aborts |
| `rec/unfold.rs` 137, `member`, a cell set by another thread | proof, made structural | the cell always holds the node made here (proof at the site, from `Env::node` giving one live node per place); `register` is unconditional, with a `debug_assert` | none needed: the branch is gone |
| `rec/unfold.rs` 170, `node`, a node made while the place's node is made | test | `a_node_made_while_its_place_is_made_again_gives_way_to_the_one_kept_first` | the node just made kept in place of the arm `Some(n)` |
| `empty/escape.rs` 1127, the 2-SAT with no model | test | `node_tests::clauses_with_no_model_give_empty` (three bits, six refused lists whose clauses read `x2 = x1`, `x3 = x2`, `x3 != x1`) | `return None` in place of `Empty` |
| `empty/escape.rs` 1350-1351, a carrier with an empty head | test | `node_tests::a_carrier_with_an_empty_head_gives_no_longer_list` (`H = int & #z(L)`, kept recursive, holds no value) | the check removed: `decide` panics picking a value of the empty cell |
| `empty/escape.rs` 1442-1443, `take` on a cell inside the head | proof | `unreachable!` at the site. The pair listing is the one caller; for a finite `pl[j]` list `x` holds `excl[x]` and the finite heads without `x`, and for a cofinite one the cons nodes are filtered by `subset`, so `pl[j]` is never within `hv` | none |
| `empty/escape.rs` 2112-2113, the re-sort for another modulus | test | `a_list_sorted_for_another_modulus_is_sorted_again` (12 nodes, five rows; about one random input in 200,000 reaches the sort) | the sort removed: row 2 loses its atom at place 6 |
| `empty/refused.rs` 130, a fixed node read as `Bot` in the re-check's low run | test | `l01_23_subtyping::group_refusal::a_repair_re_check_reads_an_arm_with_no_value_as_empty` (B's extra arm `int & #k`) | `Kind::Top` for `Kind::Bot`: the repair names `A` alone |
| `empty/refused.rs` 146, 500, 510, a repair that lets the checker decide | test | `group_refusal::a_member_reaching_no_meet_is_decided_once_repaired` (a group of five members, one holding a type refused outside it) | `Decided` read as `Searched`: the message names `Node` with the search ending |
| `empty/refused.rs` 469, a refused member with no tuple | proof | `unreachable!` with the proof at the site: every refusal lists a tuple (`branching_and >= 1`), and every refused node reaches one along refused children, by the four ways a node is refused in a run | none |

Fixed, FAIL-print-cycle-defined-twice: `Printer::collect` keeps the reference it gave each part
of a cycle by the part's key (`Kept.cycles`), so a later type of the message that meets the
part takes that reference and the cycle is defined once. Test
`print::tests::a_cycle_written_by_two_types_of_a_message_is_defined_once` (the failing test,
moved into the crate), in both orders of the two types and for a mutual pair.

Group 567 is now structural (the item the tenth round left as a proof in a comment): the
`Some(first)` arm is gone with the others above.

Correction to the tenth round, escape 455 and 526: the controls with each arm falling through
do fail the tests `a_tail_that_links_by_another_atom_is_outside_the_class` and
`a_tail_that_ends_at_another_stop_is_outside_the_class` (`decide` answers `Empty` and
`is_empty` `true` for an inhabited type); the tenth round's note that they did not was not
reproduced. Both arms are needed for the answer.

Observation, not a defect: in `print.rs` 1964 the arm's body is one reference in every input
found (a tuple's, or a part reused from an earlier print), and writing that reference itself,
as an alias is written, passes every print test. The arm is kept as it is.

Counts: 21 lines; closed by a test 14 (print 1964; group 805, 820; unfold 78, 170; escape 1127,
1350, 1351, 2112, 2113; refused 130, 146, 500, 510), by a proof 7 (group 566, 569, 570; unfold
137; escape 1442, 1443; refused 469), open 0. One bug fixed (group 820, the poisoned lock). The
102 lines outside the row's functions were not examined in this round either. They, and the
305 `empty.rs` lines the fifth round left open, are the row TEST-kernel-unreached-paths-5.

Twelfth round (kernel15, 2026-11-19), row TEST-kernel-unreached-paths-5: the 102 lines outside
the row's functions (line numbers at 23b16794b) and the `empty.rs` lines the fifth round left
open (the list file has 332, at 16279bfc5). Both lists were re-measured with llvm-cov at
d9e847e11 over the test groups `zed_kernel`, `l01_22_type_representation`, `l01_23_subtyping`,
`l01_23_groups_and_refusals`, `l01_26_type_resolution`, `l01_26a_generic_literals`,
`l01_29_diagnostics` and `l01_29_repairs_and_printing` (1295 pieces; `group_oracle` timed out
under coverage and left no profile). The lines were carried to d9e847e11 through the hunks of
`git diff -U0`, and each carried line's text was checked against the text in the list. Line
numbers below are at d9e847e11.

The "102 lines" are 101: the per-file counts of the ninth round's list (28, 24, 27, 13, 3, 3,
1, 1, 1) sum to 101. All 101 still count 0. Of the 332 `empty.rs` lines, 30 lie in code changed
since 16279bfc5 and 2 are now reached, which leaves 300 that still count 0.

| Line | Closed by | Test or site | Control |
|---|---|---|---|
| `empty.rs` 7260-7320 (30 lines), the cut one cell at a time in `nested_pieces`, now `Searching::pieces_one_at_a_time` | test | `l01_23_groups_and_refusals::nested_cover::pieces_cut_one_cell_at_a_time_are_those_found_two_at_a_time`. Product code takes this cut only when `laminar_pieces` meets a test it cannot decide, and no test input does that. The test runs each type under `Type::with_pieces_compared`, which also makes the one-at-a-time cut, checks that it equals the two-at-a-time cut whenever that one is decided, and answers with it. The verdict must equal the plain verdict and agree with `inhabited`. Inputs: 300 random draws for each of widths 2 to 4, three crossing cells whose exclusive or is the type, and the nested rows `((#_, i) \ (#a, i), 1)` for i in 0..4, less `((#_, int), 1 \| 2)` | (1) `held.extend(&cs)` removed in the within-all branch; (2) `pieces[i].0 = &pieces[i].0 - &t` replaced by a clone. Both fail the new test with "the pieces found two at a time and one at a time differ", and the other `nested_cover` tests pass |
| `empty.rs` 7160-7161, `nested_cover` merging two pieces held by the same cells | proof | `debug_assert!` with the proof at the site. No two pieces are held by the same cells. In the two-at-a-time cut the pieces form a forest, and each piece is held by the cells on its path to the root. In the one-at-a-time cut this holds by induction: each step adds a new, non-empty cell set `cs`, and `p - t` keeps `held(p)` while `p & t` gets `held(p) ∪ cs` | none |
| `empty.rs` 2216, 2737, 3608, 3620, 11406, 11407, 11926, 12056, 12167, 13472, 17237, 17245, 17307 | proof (standing) | `unreachable!` guards, each with its proof at the site. For 2216 the proof is the `while` condition just above, and for 13472 it is the bodies of `literal_keys` and `flat_keys`, which make only `Key::Bool`, `Key::Lit` and `Key::Atom`. Each proof was read and checked against its callers | none |
| `bdd.rs` 517, 555, 1107, 1306, 2038, 3689, 3833, 4098, 4230; `print.rs` 139, 309, 932, 1338; `empty/sweep.rs` 1197; `empty/refused.rs` 198, 341, 456; `empty/shared.rs` 134, 144, 147, 291, 315, 316; `bdd/list/treap.rs` 195; `print/uses.rs` 114 | proof (standing) | `unreachable!` or `debug_assert!` guards, each with its proof at the site, read and checked. `shared.rs` 316 is the release-build return after the `debug_assert!` at 315 | none |
| `bdd.rs` 91-97 | not run code | `Tables::new` is a `const fn` evaluated by the compiler in the `const` initializers of `TUPLES` and `MORPHISMS` (comment at the site) | none |
| `bdd.rs` 4576, 4583, 4624, 4638, 4643, 4648; `print.rs` 53-55; `bucket.rs` 403 | test-only code | failure branches of `#[cfg(test)]` checks, the `#[cfg(test)]` helper `surface_operand`, and the panic of a test helper. A passing test does not reach them | none |

Fixed in passing: `zedc-resolve`'s `Resolver::struct_fields` (from d31b1f860) failed
`clippy -D warnings` (`type_complexity`). The field's type now uses the alias `FieldNames`.

Open, `empty.rs` (255 lines, at d9e847e11): 117, 125, 406-408, 517, 521, 618, 800, 910, 923, 1825,
2025, 2199, 2224, 2802, 2984, 3048, 3097, 3110, 3124, 3128, 3163, 3194, 3293, 3651, 3748, 4073,
4285, 4642, 4644, 4646, 4867, 4909, 4928, 4990; the list fallback after `chain_rep` fails,
5042-5052 (10 lines); 5151, 5263, 5344, 5347; fork and blame restores 5386, 5391, 5392, 5523,
5528; 6020, 6075; 6158, 6162, 6163, 6165, 6177, 6324; the restores in `tuples_on`, 6394-6409 (8
lines) and 6478-6495 (13 lines); 6509, 6518, 6611, 6647, 6915, 7008, 7065, 7146; 7288 and 7299
(the two `return None` lines of the crossing check in `pieces_one_at_a_time`: the new test is
not confirmed to reach them, since this round measured no coverage after adding it);
`find_prefix_chains` 7589, 7595, 7622, 7697, 7698, 7749, 7987, 8003, 8023, 8060, 8090-8094 (4
lines), 8123-8127 (4 lines), 8650, 8718, 8802-8832 (17 lines), 8863, 8913, 9097, 9139;
`chain_rep` 9148, 9157, 9174-9178, 9194; `check_chain_witness` 9236, 9249, 9300, 9362, 9383, 9397,
9405, 9409, 9424, 9434, 9438, 9478-9482 (4 lines), 9508-9512 (4 lines); the walk over `no_keys`
in `find_rep` 9663-9922 (39 lines); 10103, 10120, 10125, 10246, 10460, 10461, 10499, 10564,
10571, 10637-10643 (6 lines), 10681, 10685, 11494, 11495; the restores for morphisms
11550-11597 (21 lines); 11891, 11912, 11997, 11998, 12061, 12271, 12337, 12508; `Side::mentions`
12621-12626 (5 lines; its one caller, 12123 at d9e847e11, is in `rest_choice`), 12672, 12750,
12772, 12778, 13143, 13149, 13166, 13167, 13314, 13368, 13647, 13890, 14552, 14560, 14607, 14632,
14930, 17179, 17180, 17375. Every open line, with its text, is listed in
`wt/coverage/TEST-kernel-unreached-paths-5-kernel15-d9e847e11.txt` (314 lines).

Open, outside `empty.rs` (59 lines, at d9e847e11):
- `bdd.rs`: 715, 792, 1320 and 1333; 832 (`holds`, `Form::Not`, argued at the site, not
  guarded); and 3877 (a race between threads on `OnceLock`, argued at the site, no test).
- `print.rs`: 734 (`force_cycles`, argued at the site by a sweep of seeds), 1072, 1559, 1560,
  1573, 1622, 1623, 1628, 1629, 1659, 1665-1667, 1794, 2038, 2117 and 2132.
- `empty/sweep.rs`: 746, 857, 867, 1002, 1118, 1150, 1156, 1167, 1168, 1234, 1286, 1287, 1348,
  1470, 1471, 1588, 1595, 1753, 1767, 1773, 1776, 1840, 1937, 1991, 2069 and 2136.
- `empty/shared.rs`: 53, 76, 77, 81, 85, 97 and 98. These are the `Tied::Many` arms of the map
  keyed by `name_digest`, reached only when two different types share a digest. A test needs a
  hook that forces the digest.
- `empty/names.rs`: 246, 316 and 353.

Counts: 401 lines (101 outside `empty.rs`, 300 in it). Closed by a test 30, by a proof at the
site 40 (2 new, 38 standing guards read), not run or test-only code 17, open 314 (59 outside
`empty.rs`, 255 in it, 7288 and 7299 among them). They go to the row
TEST-kernel-unreached-paths-6.
