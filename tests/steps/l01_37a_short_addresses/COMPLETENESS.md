# l01_37a_short_addresses: completeness (step L1.37a)

The code under test is the truncation of addresses (`crates/zed-kernel/src/address.rs`) and
every place that compares by address and confirms by contents: the lowering's keys
(`canon::Shape`), the order and digests of types, the thread's tables of rows, morphism types
and set nodes, and the query database's numbering of definitions. Also the replay of
counterexamples, `counterexamples` in `tests/src/oracle.rs`. Each row is a case; the second
column names the test that covers it, or says why no test is needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **Both builds agree** | |
| verdicts and outputs of every enabled fence, front verdicts of every fence, rejected variants, step units, corpus programs, step programs on corpus inputs, printed types | `record::*` (snapshots shared by both builds) |
| **Collisions** | |
| colliding nodes stay distinct in the lowering; equal nodes stay one | `collide::colliding_nodes_stay_distinct_in_the_lowering`, `collide::equal_sums_are_still_one_node`, `scaling::two_equal_lambdas_built_apart_are_one_node`, `scaling::sums_built_twice_apart_are_one_node_each` |
| colliding types distinct and ordered by contents; unions in either order | `collide::colliding_types_are_distinct_and_ordered_by_contents` |
| digests spread over all 256 values | `collide::digests_spread_over_all_their_values` |
| types tying in digest level after level; the order total on 900 random types | `collide::types_that_tie_in_digest_level_after_level_are_ordered`, `collide::the_order_of_types_is_total_on_every_pair_of_900` |
| rows dropped on another thread, passed over by lookups | `collide::rows_dropped_on_another_thread_leave_entries_that_lookups_pass_over`, `scaling::rows_and_morphism_types_that_tie_in_digest_are_found_and_dropped` |
| the tables of several definitions (the numbering of definitions) | `scaling::the_tables_of_several_definitions_pass` |
| **Counterexamples replayed** | |
| wrong rows replayed with the result they name; a replay that disagrees | `cex::a_wrong_row_is_replayed_with_the_result_it_names`, `cex::a_replay_that_disagrees_is_reported` |
| an engine that stops on a replay | `cex::an_engine_that_stops_on_a_replay_is_reported` |
| a row of `main`'s table; a row whose call stops; one wrong row written twice; a rejected unit | `cex::only_rows_whose_failure_names_a_result_are_replayed` |
| every enabled source (none has a wrong row) | `cex::every_enabled_source_replays_its_counterexamples` |
| **Scaling** | in `bench.rs` (`--bench`); the small sizes in `scaling.rs` (P178) |

## Coverage

`address.rs`'s `short64` and `short256`'s truncation run only in the `short-addresses` build;
the coverage run is of the full build, where `short64` is folded at compile time and shows as
not run. Every regular test of this group passes in the `short-addresses` build
(`run_tests.sh --only '^short-l01_37'`).
