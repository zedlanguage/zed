# L1.24 completeness: the refinement lattices and the cell

Code under test: crates/zedc-lattice/src `lattice.rs` (the `Lattice` trait, congruences, finite
sets, cardinalities, the type lattice), `cell.rs` (entries, premise sets, literal cells),
`float.rs` (float classes and widths), `affine.rs` (symbolic bounds) and `landmarks.rs`, against
DESIGN.md step L1.24, step M0.5 (the widenings and narrowings), sec:domains (literal domains,
`card` and `len`) and sec:type_resolution rule 5. The interval sets, ends and the backward table
are listed in tests/steps/m0_05_widening_and_iteration/COMPLETENESS.md. Lines reached
(llvm-cov over the crate's unit tests and the tests of this group and of
m0_05_widening_and_iteration, without the `bench` modules):

| File | Before | After |
|---|---|---|
| lattice.rs | 72.1% (77 of 276 missed) | 100% |
| cell.rs | 77.9% (60 of 272) | 100% |
| float.rs | 97.5% (3 of 120) | 100% |
| affine.rs | 99.7% (1 of 379) | 100% |
| landmarks.rs | 100% (of 36) | 100% |

Regions over the whole crate went from 90.42% to 93.85%, lines from 90.53% to 94.56%.

| Case | Covering test, or the reason none is needed |
|---|---|
| Congruence printing: bottom, one value (positive, negative), any, a class; a negative modulus and an out-of-range residue normalized; modulus 1 is any | `complete::a_congruence_prints_each_of_its_forms` |
| Congruence membership: bottom, one value (in, out), any, a class with positive and negative members and non-members | `complete::a_congruence_holds_the_members_of_its_class` |
| Congruence join: bottom on either side, the top absorbs, two values, equal values, two classes (gcd of moduli and difference), classes joining to any; the widening is the join (DESIGN M0.5) | `complete::congruence_join_and_meet_on_every_kind_of_operand` |
| Congruence meet: bottom on either side, the top as unit, a value in and out of a class (both orders), two values, two classes by the Chinese remainder theorem, incompatible classes, equal classes; the order read off the meet | `complete::congruence_join_and_meet_on_every_kind_of_operand` |
| Congruence narrowing takes `b` only from ⊤, or when `b` is one value or none (DESIGN M0.5) | `complete::a_congruence_narrowing_takes_next_only_from_the_top_or_for_one_value_or_none` |
| Congruence chains end when the modulus stops dividing; at most three narrowings | `widening::congruence_chains_end_when_the_modulus_stops_dividing`, `widening::a_congruence_narrows_at_most_three_times` (m0_05) |
| Classes and meets past the 64-bit range | `past_i64::two_offsets_past_the_64_bit_range_share_their_least_class`, `past_i64::a_meet_of_classes_past_the_64_bit_range_is_their_chinese_remainder` |
| Finite set join and meet with ⊤ on either side and on both, two sets, a meet to the empty set; the order | `complete::finite_set_join_and_meet_with_the_top_on_either_side` |
| Finite-set widening: from the bottom (to a set and to ⊤), nothing added, growing to ⊤, the landmarks `k-1`, `k`, `k+1` of a literal and no other integer, one added member with a landmark and one without, an integer past 64 bits as a landmark, strings and atoms as landmarks, a string, atom or bool that is not one (DESIGN M0.5) | `complete::a_finite_set_widening_keeps_landmark_members_and_otherwise_goes_to_the_top`, `widening::a_finite_set_widens_to_the_top_at_a_member_the_program_does_not_write` (m0_05) |
| Finite-set narrowing is `b`: from ⊤, from a set, to the empty set | `complete::a_finite_set_widening_keeps_landmark_members_and_otherwise_goes_to_the_top` |
| Cardinality: the range met with `[0..]`, a range wholly negative is empty, every integer gives ⊤ | `complete::a_cardinality_is_one_interval_of_the_nonnegative_integers` |
| Cardinality join is the hull, with the bottom and ⊤; meet, disjoint meet, meet with ⊤; the order | `complete::a_cardinality_is_one_interval_of_the_nonnegative_integers` |
| Cardinality widening and narrowing are the interval ones met with `int[0..]`: a lower end moving down with no landmark goes to 0, an upper end to ∞ or to a landmark, from the bottom, nothing new; narrowing from ∞, to a landmark, a finite end kept, to the empty set (DESIGN M0.5) | `complete::a_cardinality_is_one_interval_of_the_nonnegative_integers`, `widening::a_growing_buffer_length_widens_to_unbounded_and_stays_nonnegative` (m0_05) |
| Type lattice: bottom, top, join is `|`, meet is `&`, the order is subtyping | `complete::the_type_lattice_widens_and_narrows_by_whole_parts` |
| Type widening takes whole each base and the rest of each universe that gained a value: a string, a tuple, an atom (the rest of the scalar universe, no base), `bool`, `f64`, `f32`; from the bottom; a second widening on the same gain changes nothing; ⊤ | `complete::the_type_lattice_widens_and_narrows_by_whole_parts` |
| Type narrowing takes `next` in a part `self` holds whole: from ⊤, to the bottom, a part not whole stays, a part `self` lacks, a universe part | `complete::the_type_lattice_widens_and_narrows_by_whole_parts` |
| Premise sets: `without` with nothing to drop (shared), on the empty set, one premise without itself and without another, one from each side, both from one side, all, a later premise not held (shared), an equal premise made apart (kept), a part shared twice, dropping the only widening | `complete::removing_premises_rebuilds_only_the_unions_that_held_them` |
| Premise sets compare by their premises: empty, one, made apart, different unions of the same premises, against a plain set and from one, Debug as the plain set, `insert` of a held and a new premise, `contains`; `same` compares parts | `complete::premise_sets_compare_by_their_premises`, `cell::premises_are_found_by_part_not_address` |
| A meet adds premises only when it narrows; a join rests on both sides; a widening past the join is a premise and not proof grade | `cell::a_meet_adds_its_premises_only_when_it_narrows`, `cell::a_join_rests_on_both_sides`, `cell::a_widening_past_the_join_is_a_premise_and_not_proof_grade` |
| The cell of each kind of literal is the singleton in each domain that reads its kind (DESIGN sec:domains, literal domains): `i64` at both ends, -1 and 0; an integer past 64 bits (point and one-value class); `true`, `false`, an atom (finite set only); the empty string (length 0); `f64` infinities and a value past `f32` | `complete::the_cell_of_each_kind_of_literal`, `cell::a_literal_fills_the_domains_that_read_its_kind` |
| An `f32` literal's float class is the singleton class of its value | Fails: row FAIL-lattice-f32-literal, source /home/luke/Work/wt/failing-tests/FAIL-lattice-f32-literal.rs. `Cell::literal` (cell.rs) fills the float class only for `Value::Float`, so an `f32` literal leaves it at ⊤ |
| A cell joins and widens entry by entry; a length is never negative | `cell::a_cell_joins_and_widens_entry_by_entry`, `cell::a_length_is_never_negative` |
| Float width: the narrowest format holding a value exactly, at 0, at each format's largest value and past it, negative, NaN, and the least subnormal of each format and half of it | `complete::float_widths_and_printed_classes`, `float::each_float_has_its_narrowest_width` |
| Float classes: meet exact, join holds both sides, the facets a key needs; printed forms of each kind and the bottom | `float::meet_is_exact_and_join_holds_both_sides`, `float::the_facets_a_key_needs_read_off_the_class`, `complete::float_widths_and_printed_classes` |
| `bf16`, listed among the formats of step L1.24 | None here: float.rs has no `bf16` width; row FLOAT-interval owns the float formats and their intervals |
| Affine bounds: meet, join, widening, order, offsets, crossing bounds, tighter bounds; printing with each sign of the constant, a negated symbol, a scaled symbol, constant 0 and negative, terms that cancel | `bounds::*` (seven tests), `complete::affine_bounds_print_each_sign_of_their_constant`, `past_i64::an_affine_bound_scaled_past_the_64_bit_range_is_exact` |
| Landmarks: the literals `k-1`, `k`, `k+1`; other literal values; a loop takes the landmarks of its own loops only | `complete::a_finite_set_widening_keeps_landmark_members_and_otherwise_goes_to_the_top`, `iteration::a_loop_takes_the_landmarks_of_the_loops_inside_it_only` (m0_05), `iteration::a_literal_at_the_end_of_the_machine_word_gives_landmarks_past_it` (m0_05) |
| Loops keep their symbolic bounds; every solution holds every value a run takes | `loops::*` (three tests) |
| Ends, kept powers, decimal text of ends, addresses of wide ends | `ends::*`, `boundary::*`, `num_text::*`, `kept_serial::*`, `past_i64::*` |
| Large sizes | `scaling::*`; the `bench` modules run apart |
