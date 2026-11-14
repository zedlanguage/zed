# M0.6 completeness: the cost scalarization

Code under test: `zedc::cost` (crates/zedc-base/src/cost.rs): the target profile, `brent`,
`feasible`, the footprints under a static and a work-stealing schedule, `scalarize`, `vector`,
`dominates`, `frontier`, `pick`. Lines of cost.rs reached: 100% before and after this pass (by
llvm-cov), so the cases below add checks of values, worked out by hand from DESIGN.md steps M0.6
and M0.6a, at the boundaries a line count does not see.

| Case | Covering test, or the reason none is needed |
|---|---|
| Default profile: one CPU, 8 cores, 1 unit per work, 16 GiB, nothing else | `cases::the_default_profile_is_one_cpu_of_8_cores_with_16_gib`, `the_default_profile_runs_everything_on_eight_cores` |
| Unbounded cardinality read as 2^20; a bound of 0, 5 and `u64::MAX` kept | `cases::the_default_profile_is_one_cpu_of_8_cores_with_16_gib` |
| Transfer of 0, 1, 63, 64, 65, 128, 129 bytes: latency plus whole 64-byte blocks | `cases::a_transfer_is_a_latency_plus_whole_64_byte_blocks` |
| Transfer of `u64::MAX` bytes (no overflow), a per-block cost that overflows (saturates), no latency | `cases::a_transfer_is_a_latency_plus_whole_64_byte_blocks` |
| Brent: no work; work a multiple of the cores and not; depth equal to work; one core; saturating sizes | `cases::brent_is_the_rest_of_the_work_shared_among_the_cores_plus_the_depth` |
| Brent: zero cores read as one, depth above work read as the work; bounds between depth and work | unit test `cost::tests::brent_bounds_lie_between_depth_and_work` |
| Scalar: sum over devices times their time per work, plus one transfer per cut edge | `cases::the_scalar_sums_the_devices_and_adds_one_transfer_per_cut_edge` |
| Scalar: regions on one device add work and depth before the bound | `cases::the_scalar_sums_the_devices_and_adds_one_transfer_per_cut_edge` |
| Scalar: an idle device costs 0; no region gives only the transfers | `cases::the_scalar_sums_the_devices_and_adds_one_transfer_per_cut_edge` |
| Scalar and vector saturate | unit test `cost::tests::arithmetic_saturates` |
| One more cut edge costs one more transfer | `a_plan_that_cuts_one_more_edge_costs_one_more_transfer` |
| GPU chosen when work pays for the transfer | `the_gpu_wins_when_the_work_is_large_enough_to_pay_for_the_transfer` |
| Vector layout: work, depth, footprint per device, then edges and blocks; empty plan | `cases::the_vector_lists_work_depth_footprint_per_device_then_edges_and_blocks` |
| Feasible at capacity, infeasible one byte above, the same bytes fit on another device | `cases::a_plan_is_feasible_up_to_each_device_capacity_and_no_further`, `a_plan_over_a_device_capacity_is_not_picked` |
| A target of no device: an empty plan is feasible, a placed region is not | `cases::a_plan_is_feasible_up_to_each_device_capacity_and_no_further` |
| A region on a device the target lacks; a schedule naming a region twice, never, or out of range; spans of the wrong count; compositions over too many entries | `overlap::a_schedule_that_does_not_name_each_region_once_makes_the_plan_infeasible` |
| Empty nestings, compositions of nothing, no spans | `overlap::a_schedule_that_does_not_name_each_region_once_makes_the_plan_infeasible` |
| Footprint in sequence: the largest of a region's footprint plus what earlier ones retain (M0.6a's 10 GiB, 10 GiB + 8 GiB example) | `peak::two_jobs_that_each_fit_run_one_after_another`, `peak::bytes_a_job_keeps_for_later_ones_count_while_those_run` |
| Retained bytes above the footprint read as the footprint; kept on one device only; until the schedule ends | `peak::retained_bytes_above_the_footprint_are_read_as_the_footprint`, `peak::bytes_kept_on_one_device_do_not_count_on_another`, `peak::retained_bytes_count_until_the_schedule_ends` |
| Footprint saturates | `peak::the_peak_saturates_at_huge_sizes`, `overlap::huge_sizes_saturate` |
| Parallel regions on a multi-core device add; on one core the worse order's peak | `overlap::two_regions_that_run_at_once_count_together`, `overlap::a_device_of_one_core_holds_the_peak_of_the_worse_order` |
| Static schedule: ends before starts at an instant; a region of length 0 beside every region then | `overlap::a_static_schedule_counts_what_runs_at_each_instant` |
| A DAG that is not series-parallel judged at the upper bound | `overlap::a_dag_that_is_not_series_parallel_is_judged_at_the_upper_bound` |
| Footprint against its definition on random plans, both schedules | `overlap::the_footprint_agrees_with_its_definition`, `peak::the_peak_agrees_with_its_definition_and_lies_between_the_largest_and_the_sum` |
| Dominance: equal, better in one, better in all, worse, incomparable both ways, empty | `cases::dominance_is_no_worse_everywhere_and_better_somewhere` |
| Frontier keeps incomparable plans and drops dominated ones | `the_frontier_keeps_incomparable_plans_and_drops_dominated_ones` |
| Frontier keeps every plan of an equal vector, in address order | `cases::plans_of_equal_vectors_are_all_kept_in_address_order` |
| No plan, no feasible plan: empty frontier, no pick | `cases::no_plan_and_no_feasible_plan_give_an_empty_frontier_and_no_pick` |
| Pick: least scalar first, even at a higher address | `cases::a_lower_scalar_wins_over_a_lower_address` |
| Pick: equal scalar ordered by content address | `plans_of_equal_cost_are_ordered_by_content_address`, `cases::plans_of_equal_vectors_are_all_kept_in_address_order` |
| Pick: colliding addresses ordered by contents, any arrival order | `cases::plans_whose_addresses_collide_are_ordered_by_their_contents`, `the_pick_is_the_same_in_every_arrival_order_and_minimal_over_every_feasible_plan` |
| Scalar monotone in work, depth, cut edges; footprint monotone, so pruning keeps the pick | `the_scalar_is_monotone_in_work_depth_and_cut_edges`, `peak::the_peak_is_monotone_so_pruning_to_the_frontier_keeps_the_pick`, `overlap::the_footprint_is_monotone_so_pruning_to_the_frontier_keeps_the_pick` |
| Large frontiers, long schedules, many devices | `bench` module (scaling, run with `--bench`); small sizes in the `..._at_small_sizes` tests |
| The `cost` prelude unit and the L24.5 placement solver using the same function | None here: DESIGN.md names the unit but gives it no Zed-visible content to test, and step L24.5 is not built; both reach this code through `zedc::cost`, which the cases above test |
