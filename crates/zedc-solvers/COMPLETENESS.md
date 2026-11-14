# Completeness: zedc-solvers unit tests

Row TEST-complete-crates (author P189). The code these unit tests exercise is the linear-relation
domain's solvers of step L1.38 (DESIGN.md sec:domains): the rationals `Q` (`src/linear.rs`), the
two-variable test `twovar`, the UTVPI test `utvpi`, and the negative-weight shortest-path searches
of `negsssp` (Duong's search, BF-Dijkstra and `Rounds`). Expected results come from the
mathematics: a potential holds on every edge exactly when the graph has no negative cycle, and
the searches are checked against Bellman–Ford, against least walk weights, or against a search
of every integer point of a box. Tests named without a file are in `src/negsssp/completeness.rs`;
`utvpi::`, `twovar::`, `linear::` and `negsssp::tests::` name the older tests in those files.

`live3.rs` (the fixed-dimension LP at `live = 3`) has no unit tests: it is tested in
`tests/steps/l01_38_presburger` (`live3.rs`, `oracle.rs`), which is that step's row.

llvm-cov lines (unit tests of the crate, benchmarks none):

| File | Before | After |
|---|---|---|
| `linear.rs` | 97/97 (100%) | 97/97 (100%) |
| `twovar.rs` | 432/432 (100%) | 432/432 (100%) |
| `utvpi.rs` | 777/778 (99.87%) | 777/778 (99.87%) |
| `negsssp.rs` | 1112/1141 (97.46%) | 1140/1141 (99.91%) |

The lines the brief named (287, 386, 392-394, 402-410, 993-995, 1001, 1153-1156, 1165-1168) are
reached by the new tests, except line 287: `relax_one`'s `let Some(..) = &mut self.settling else
{ return Ok(()) }`. Every caller of `relax_one` checks `settling.is_some()` first, so the `else`
cannot run. `utvpi.rs` line 113 is the `unreachable!` arm of `graph` for a row of neither one
nor two terms; `integer_empty` takes only such rows by contract (its documentation).

| Case | Test, or reason none is needed |
|---|---|
| `Q::new`: lowest terms, negative denominator, zero over a negative, a whole number | `linear::tests::rationals_stay_in_lowest_terms_with_a_positive_denominator` |
| `Q` `add`, `sub`, `mul`, `div`, `neg` on whole numbers (the short way) and on fractions; `floor`, `ceil` each side of zero and at a whole number; signs; order | `linear::tests::rationals_stay_in_lowest_terms_with_a_positive_denominator` |
| `Q` division by zero | None needed: `d` is "not 0" by contract (doc of `Q::new`); callers divide by coefficients they checked |
| `floor_sum` on every `n` 0..12, `m` 1..7, `a`, `b` in -9..9 | `twovar::tests::the_floor_sum_matches_the_sum` |
| `twovar::ends` on random rows in boxes, both orders of the box rows | `twovar::tests::the_ends_match_a_search_of_the_box` |
| `ends` open on one side, on both, empty though the reals have a point, parallel lines with points at every third `x` | `twovar::tests::an_end_with_no_bound_is_none`, `twovar::tests::a_point_of_one_variable_or_of_y_bounded_one_way` |
| `twovar::point` with and without `want`, both answers | `twovar::tests::the_points_match_a_search_of_the_box` |
| `point` over `x` alone, a row with no variable, `y` bounded one way, `x` free, gap rising and falling without end | `twovar::tests::a_point_of_one_variable_or_of_y_bounded_one_way` |
| `utvpi::integer_empty`, `integer_point` and the `_by` forms with every `Search`: halves, a free variable, no rows | `utvpi::tests::rows_with_halves_a_free_variable_or_no_rows` |
| The same on random rows in boxes, both answers, every `Search` | `utvpi::tests::the_rows_get_the_answers_of_a_search_of_the_box` |
| `rounded` and `odd_zero_cycle` on tight halves, odd and even | `utvpi::tests::halves_on_tight_edges_are_rounded_together` |
| `potential` on an acyclic graph (the topological pass) | `utvpi::tests::acyclic_signed_edges_have_an_exact_potential` |
| A negative cycle rejected by `goldberg_radzik`, `bf_dijkstra` and `potential_alone` | `utvpi::tests::a_negative_cycle_is_still_rejected` |
| Every search and `race` against Bellman–Ford–Moore on random graphs of `integer_empty`'s shape; the potential holds on every edge | `utvpi::tests::random_graphs_get_the_decisions_of_bellman_ford_moore`, `utvpi::tests::small_graphs_get_the_answers_of_bellman_ford_moore` |
| Shared labels of the two searches in `race`, forward and reversed | `utvpi::tests::shared_labels_keep_the_answers_of_bellman_ford` |
| The bad-GOR family (many passes) | `utvpi::tests::bad_gor_augmented_has_a_potential_that_holds_on_every_edge` |
| `negsssp` round bound: a cycle found before the parent walk, the longest path finishing, agreement with Bellman–Ford | `negsssp::tests::the_round_bound_reports_a_cycle_before_the_parent_walk`, `negsssp::tests::the_round_bound_lets_the_longest_path_finish`, `negsssp::tests::the_round_bound_agrees_with_bellman_ford` |
| `potential_alone` on the empty graph | `negsssp::tests::the_empty_graph_has_the_empty_potential` |
| `Ball::feed`: core up to `t` steps, shell up to one more, both inclusive | `a_ball_takes_its_core_up_to_t_steps_and_its_shell_up_to_one_more_inclusive` |
| `Ball::feed`: a shell too heavy for its core joins it and the next shell is tested | `a_shell_too_heavy_for_its_core_joins_it_and_the_next_shell_is_tested` |
| `Ball::feed`: core reaching an eighth of the mass is heavy, at once or after growing | `a_ball_whose_core_reaches_an_eighth_of_the_mass_is_heavy_at_once_or_after_growing` |
| `Ball::feed` at the end of the search (`next` is `None`): core completed, then shell | `the_end_of_the_search_completes_the_core_and_then_the_shell` |
| `Radii`: step `⌈d / scale⌉` in whole steps | `the_radius_step_is_d_over_scale_rounded_up_to_whole_steps` |
| `heavy` with no empty shell: cut at the lightest shell, the first among equals | `the_heavy_split_with_no_empty_shell_cuts_at_the_lightest_shell_the_first_among_equals` |
| `heavy` cut at the first empty shell | `the_heavy_split_cuts_at_the_first_empty_shell` |
| `merge` of children sharing vertices gives a potential of the whole | `a_merge_of_children_that_share_vertices_gives_a_potential_of_the_whole` |
| `merge` reports a negative cycle that no child holds | `a_merge_reports_the_negative_cycle_no_child_holds` |
| `merge` of random overlapping covers, both answers, shared vertices | `merges_of_random_overlapping_covers_agree_with_bellman_ford` |
| `potential_alone` gives exactly the least walk weights from labels 0 (large weights, the recursion runs) | `large_weights_give_the_least_walk_weights_of_bellman_ford` |
| Ball growth end to end: weights just above `-W/2`, acyclic and cyclic rounds | `weights_just_above_minus_w_over_2_grow_balls_and_keep_the_answers_of_bellman_ford` |
| `Rounds` (`new`, `labels`, `take_lowered`, `ends_round`, `lower_to`, `step`) | `utvpi::tests::shared_labels_keep_the_answers_of_bellman_ford` and the `race` cases above: `race` drives `Rounds` and shares its labels |
| `Progress::left` and the `potential` tick | `utvpi::tests::shared_labels_keep_the_answers_of_bellman_ford`, `utvpi::tests::small_graphs_get_the_answers_of_bellman_ford_moore` (through `race`) |
| Interaction with language features (units, unions, ports, staging and the rest) | None needed: the solvers take integer rows below the language; their language-level uses are tested in step L1.38's groups |
