# M0.5 completeness: widening, narrowing and the iteration

Code under test: crates/zedc-lattice/src `interval.rs` (interval unions, their ends, widening,
narrowing and snapping), `iterate.rs` (the two-phase iteration), `wto.rs` (the weak topological
order and its keys), `schedule.rs` (the scheduler) and `revision.rs` (the tonicity and
interval-revision tables), against DESIGN.md step M0.5 and sec:constraints. The congruence,
finite-set, cardinality and type lattices, the cell and the float classes are listed in
tests/steps/l01_24_refinement_lattices/COMPLETENESS.md. Lines reached (llvm-cov over the crate's
unit tests and the tests of this group and of l01_24_refinement_lattices, without the `bench`
modules):

| File | Before | After |
|---|---|---|
| interval.rs | 86.4% (207 of 1523 missed) | 87.1% (197); outside `bit_word`, 16 missed before and 6 after |
| iterate.rs | 99.4% (1 of 160) | 99.4% (1) |
| wto.rs | 98.0% (5 of 255) | 99.6% (1, an instantiation of `same_or_cmp` no test makes; its lines run in the others) |
| schedule.rs | 98.7% (3 of 228) | 100% |
| revision.rs | 99.0% (7 of 690) | 99.1% (6 by the summary, 5 lines by the line listing: 614–616, 672, 886; LATTICE-pow-end-dead then deleted 614–616, and 672 and 886 are now 669 and 883) |

The lines still not reached are listed at the end of the table, each with its reason.

| Case | Covering test, or the reason none is needed |
|---|---|
| The interval set as a `Lattice`: bottom is the empty set, top every integer, join, meet, the order read off the meet (empty, equal, top), the trait's widening and narrowing are the set's | `complete::an_interval_set_is_a_lattice_with_the_empty_set_and_every_integer` |
| Ends from `i64` and `i128`, `i128::MAX`; `to_i64` at `i64::MIN`, past `i64::MAX`, and of ±∞ | `complete::an_end_from_each_integer_type_and_back` |
| Interval widening moves each finite end of `b` outward to the nearest old end or landmark, else to ±∞ (DESIGN M0.5): from the bottom, both empty, equal operands with no landmark, infinite ends, a new piece between old pieces, a new piece above every old end with and without a landmark | `complete::interval_widening_on_the_bottom_equal_operands_and_infinite_ends`, `widening::interval_widening_chains_stay_on_the_first_ends_and_the_landmarks`, `widening::a_moved_endpoint_goes_to_the_next_landmark_or_infinity` |
| Interval narrowing moves each finite end of `b` outward to the nearest of `a`'s ends or landmarks, and keeps it when there is none (DESIGN M0.5): to the empty set, equal operands, ⊤ by ⊤, from ⊤ with and without landmarks, an infinite end of `b` kept, two pieces inside one old piece | `complete::interval_narrowing_on_the_bottom_equal_operands_and_infinite_ends`, `widening::interval_narrowing_chains_stay_on_the_first_ends_and_the_landmarks`, `widening::a_narrowing_keeps_old_ends_and_takes_a_bound_for_an_infinite_one` |
| Snapping each end to a landmark or to infinity: no landmark, a landmark on one side, infinite ends, ends already on landmarks, the empty set, ⊤, two pieces snapping to one | `complete::snapping_moves_each_end_to_a_landmark_or_to_infinity` |
| Debug output of the empty set and of distinct sets | `complete::interval_sets_print_their_pieces_for_debugging_and_compare_by_members` |
| Equality: one and many pieces built apart, equal piece counts differing in one piece, empty against non-empty both ways, a set built by joins against the one built from its pieces | `complete::interval_sets_print_their_pieces_for_debugging_and_compare_by_members` |
| Union, intersection and difference of sets that share most pieces (one removed at the ends and in the middle, one added); a set less itself, held once or twice; less the empty set; the empty set less a set | `complete::set_operations_on_sets_that_share_most_pieces` |
| Join, meet, membership, the cap on pieces, images of operators | `scaling::*` in l01_24 (`cap_follows_the_merge_rule`, `join_and_contains_agree_with_membership`, the image tests) |
| Vertex keys order by name, then address, then form, then keypath (DESIGN M0.5): the same key by reference, equal forms held apart, each part deciding, a keypath before a longer one it begins, a local binder's level name before every written name; `partial_cmp` agrees with `cmp` | `complete::vertex_keys_compare_part_by_part`, `order::*` |
| Weak topological order: Bourdoncle against the declarative definition, backward edges to an enclosing head, nested components, the head picked by the traversal order, keyed order | `wto::*` |
| The two-phase iteration: phase one against the stack machine, a sound post-fixpoint, counters stop at landmarks, the widening point, phase two until a round changes nothing, phase two ends where meets alone would descend forever, no cap needed, equations read through the trait | `iteration::*`, `invariant::*` |
| The scheduler: a new one has no value; keyed writes, evaluations unlocked by checks, mutual recursion as one component, refusals of a value needed for its own check and of a once fact reading itself, shortest cycle named, new checks, nodes added by evaluation, the meaning under every order | `complete::a_new_scheduler_has_no_value`, `schedule::*` |
| The tonicity and revision tables | `revision::*` |
| `^` backward with a kept exponent `2 ^ 200`: results in `0..=1` give `-1..=1`, result 0 gives 0, negative results give nothing, a bound past `2 ^ u32::MAX` holds `-1..=1` and stays in the operand; forward at -1, 0, 1; an odd kept exponent; the exponent written as a big integer | `complete::backward_powers_with_a_kept_exponent_hold_every_root`, `past_i64::an_exponent_with_no_exact_form_bounds_outward` (l01_24) |
| The exact backward result of `^` with a kept exponent and a bound past `2 ^ u32::MAX` | Only soundness is asserted: the outward bound is the plan's stated approximation (revision.rs, `pow_end`; COMPLEXITY.md S36) |
| Large sizes | `scaling::*`; the `bench` modules run apart |
| interval.rs lines 1495–1782: `bit_word` and its helpers | None here: TEST-complete-reduced owns the bit-word tests (l01_39f) |
| interval.rs line 246 (`run_between`), 704 (`Walk::open`), 1140 (the cap's gap): `unreachable!` arms | None: only the outer ends of a set are infinite, and only a subtree is opened |
| interval.rs line 932: `same_tree` on two empty sets | None: a `#[cfg(test)]` helper of the crate's unit tests |
| interval.rs lines 1380, 1388: equality walks finding a differing piece, or one tree ending first | None: reached only when two sets have equal piece counts and equal 61-bit content hashes but differ, a hash collision a small test cannot build; 1388 not even then, since equal counts end both walks together |
| interval.rs, the shared-subtree arms of `union` and `intersection` (regions on lines 463 and 490) | None needed for correctness: a fast path whose result equals the general one; `join` and `meet` return a shared operand when one holds the other, so the top-level call never meets equal trees, and the recursion did not meet one subtree held by both on the inputs of `set_operations_on_sets_that_share_most_pieces`. The difference arm (line 535) is reached |
| iterate.rs line 316: `unreachable!` after phase two | None: a chain of narrowings is finite, so the loop returns |
| `pow_end` for a base of 0, 1 or -1 | Deleted (LATTICE-pow-end-dead): the arms were dead, since `Num::pow_by` (crates/zedc-int/src/int.rs) returns a value for every `k` that fits `u32` and, past it, for every base of magnitude at most 1. These bases are covered through `pow_by` by `complete::backward_powers_with_a_kept_exponent_hold_every_root` (forward at -1, 0, 1 with a kept exponent) |
| revision.rs line 672: `unreachable!` in `reduce_finite` | None: `FiniteSet::of` always builds a set |
| revision.rs line 886: the panic of a test helper that reports a lost solution | None: it runs only when a revision loses a solution, which would fail the test that calls it |
