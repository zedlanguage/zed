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
