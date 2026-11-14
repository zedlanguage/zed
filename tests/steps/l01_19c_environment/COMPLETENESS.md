# Completeness: l01_19c_environment

Step L1.19c (DESIGN.md): the environment port `m.env`, a lookup by name giving the value or
`#notFound`, a value read that is not UTF-8 a usage error naming it, the names read and what
each gave recorded and replayed with the variables unset. Plan row TEST-complete-ports
(author P189). Coverage before and after is in l01_19_whole_file_ports/COMPLETENESS.md.

| Case | Covering test | Or reason none is needed |
|---|---|---|
| A variable read; an empty value is the empty string; an unset name misses | `reads.rs::a_program_reads_a_variable`, `reads.rs::an_empty_value_is_the_empty_string`, `reads.rs::a_name_that_is_not_set_misses` | |
| A non-ASCII value, a value holding `=`, spaces, a line end | `combinations.rs::names_and_values_of_each_kind` | |
| The empty name is never set; a name holding `=` | same test (empty_name_is_never_set, name_holding_equals) | |
| Names are case sensitive; a non-ASCII name | same test (names_are_case_sensitive, non_ascii_name) | |
| An unread variable whose name is not UTF-8; no variables at all | same test (unread_name_not_utf8, no_variables_at_all); `reads.rs::a_variable_the_program_does_not_read_may_hold_anything` | |
| A read value that is not UTF-8 is a usage error naming it | `reads.rs::a_value_that_is_not_utf8_is_a_usage_error_naming_it`, `binary.rs::zedc_names_the_variable_that_is_not_utf8` | |
| Two names, one not UTF-8 and read | `combinations.rs::a_variable_is_read_in_each_position` (two_names_one_bad_and_read) | |
| Read twice, in a condition, at a name from an argument, through a helper of type `String ->? String`, cast to `int`, with `else #notFound ->` | `combinations.rs::a_variable_is_read_in_each_position` | |
| A miss left undisposed is rejected | `reads.rs::a_miss_left_undisposed_is_rejected_before_the_run` | |
| The environment is a field of `MainArgs`; `main` rows give it as a function | `reads.rs::the_environment_is_a_field_of_main_args`, `reads.rs::a_main_row_gives_the_environment_as_a_function` | |
| A record keeps each kind of value and replays it with the variables unset | `combinations.rs::a_record_keeps_each_kind_of_value`; `replay.rs` (both tests); `binary.rs::zedc_gives_main_a_variable_and_replays_it_unset` | |
| An executable reads its own variables | `binary.rs::an_executable_reads_its_own_variables` | |
| `m.args.map(n -> m.env[n] ...)` | | Left out: `map` is a layer L3 word (DESIGN words table). |
| Many variables | `bench.rs` (both tests) | Benchmarks (P178). |
