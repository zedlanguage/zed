# l01_37_oracle: completeness (step L1.37, DESIGN.md Part G)

The code under test is the differential oracle, `tests/src/oracle.rs` (`bindings`, `outcomes`,
the walk `Runs`, `unit`, `program`, `labeled`, `corpus`, `step_units`), the native engines it
runs (`zed_native::through`, `counted`) and the runtime's list of live cells
(`zed_rt::Heap::survivors`). `counterexamples` is step L1.37a's (`tests/steps/l01_37a_short_addresses`).
Each row is a case; the second column names the test that covers it, or says why no test is
needed.

| Case | Covering test, or reason none is needed |
|---|---|
| **Sources compared** | |
| every enabled fence; every step unit; every enabled corpus program (none at L1); every step program on every corpus input | `oracle::*` |
| **A unit's bindings** | |
| no definitions; one binding | `alone::each_binding_gives_what_its_run_alone_gives` ("no definitions"), `scaling::a_unit_of_one_binding_or_none_is_compared` |
| all bindings run as one tuple | `scaling::a_chain_of_bindings_is_compared`, `oracle::every_step_unit_agrees` |
| a stop at each place, 1 to 6 bindings, chained and independent: the prefixes and every way the halving goes | `alone::a_stop_at_each_place_gives_each_binding_what_its_run_alone_gives` |
| a chain through a stop; a stop in a definition that is no binding; two stops reached; an unknown stop before a known one; a stop after a function | `alone::each_binding_gives_what_its_run_alone_gives`, `alone::natively_too` |
| a binding the checker typed `_` that is a function | `alone::each_binding_gives_what_its_run_alone_gives` (not natively: item NATIVE-stop-cells) |
| the expected outcome of each binding | `alone::the_outcomes_are_those_expected` |
| a chain whose last binding stops | `alone::a_chain_whose_last_binding_stops_is_compared` |
| stops that reach functions: the walk ends at the second, the rest not compared, a later binding reading a known stop still compared | `alone::stops_that_reach_functions_end_the_walk_at_the_second`, `alone::a_second_stop_through_functions_is_not_compared` |
| an engine that gives an outcome where the interpreter gives none | `alone::a_second_stop_through_functions_is_not_compared` (`refuse` on `b1`, `c2`, `b2`) |
| **A unit's table checks** | |
| equal under each engine; different, both lists printed | `oracle::every_step_unit_agrees`, `report::the_table_checks_are_compared_under_each_engine` |
| a rejected unit compares nothing; an empty unit is accepted | `report::a_rejected_unit_compares_nothing` |
| **A program's writes** | |
| port writes equal; an engine that stops | `oracle::every_step_program_agrees_on_every_corpus_input`, `report::a_programs_writes_are_compared_under_each_engine` |
| no writes; a program that does not load (a name not defined, no `main`, empty) | `report::a_program_that_writes_nothing_or_does_not_load` |
| a wave of many lines | `scaling::the_inputs_are_compared_as_they_should_be` |
| a program the interpreter stops on at run time | none: no such program was found at L1 (`1 / 0` in a write is rejected, so `program` compares nothing); the engine side of the same `writes` branch is covered by `report::a_programs_writes_are_compared_under_each_engine` |
| **Reports** | |
| mismatches and outcomes not compared added together, each prefixed with its source | `scaling::the_inputs_are_compared_as_they_should_be`, and at many in `bench.rs` |
| **Corpus layers** | |
| `// layer L<n>` read, spaces after it, other files passed over, name order | `report::the_layer_of_each_program_is_read_from_its_first_line` |
| a program with no layer line | none: a panic of the test helper, which states the corpus's format; the corpus check (`oracle::every_enabled_corpus_program_agrees_and_writes_its_output`) reads every program |
| **The runtime's counts** | |
| live cells by type and allocating node; a freed cell reused by another node | `counts::live_cells_are_listed_by_type_and_allocating_node` |
| the count of runs starts again when read | `counts::reading_the_runs_counted_starts_the_count_again` |
| **Both builds** | every regular test here also passes in the `short-addresses` build (`run_tests.sh --only '^short-l01_37'`) |
| **Scaling** | in `bench.rs` (`--bench`); the small sizes in `scaling.rs` (P178) |

## Coverage

`oracle.rs` lines left uncovered after this pass are three `unreachable!` arms (a definition
marked with a position that is not a stop; a run reaching a definition that reads a stop or was
left unrun; a check that is not `call == want`), which the walk's invariants rule out.
