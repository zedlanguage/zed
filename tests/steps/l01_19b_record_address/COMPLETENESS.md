# Completeness: l01_19b_record_address

Step L1.19b (DESIGN.md step L1.19): a record names the content address of the program it was
made from. The address covers the term `main` runs, closed over the definitions it reaches, and
the port declarations, and nothing else. A replay against another program is refused.
Plan row TEST-complete-ports (author P189).

| Case | Covering test | Or reason none is needed |
|---|---|---|
| A record replays against its own program | `mod.rs::a_record_replays_against_its_own_program` | |
| Local names and layout keep the address | `mod.rs::local_names_and_layout_keep_the_address` | |
| A comment added keeps the address | `combinations.rs::what_keeps_the_address_and_what_changes_it` (comment_added) | |
| A definition `main` does not reach, added, keeps the address | same test (unreached_definition_added) | |
| Definitions in another order keep the address | same test (definitions_in_another_order) | |
| `main(m)` in place of `main(m: MainArgs)` keeps the address | same test (parameter_type_left_out) | |
| A test table added keeps the address | same test (test_table_added) | |
| The body of a reached helper changed changes it | same test (reached_helper_body_changed) | |
| A literal in `main` changed changes it | same test (literal_in_main_changed) | |
| A write to another port changes it | same test (written_to_another_port) | |
| A new read of stdin, an argument or a variable changes it | same test (reads_standard_input, reads_an_argument, reads_a_variable) | |
| Reads at other keys, of other ports or other names have other addresses | `combinations.rs::reads_at_other_keys_or_names_have_other_addresses` | |
| The inputs a program reads are part of the address | `mod.rs::the_inputs_a_program_reads_are_part_of_the_address` | |
| A chain of functions has an address of its own | `mod.rs::a_chain_of_functions_has_an_address_of_its_own` | |
| A record of another program is refused | `mod.rs::a_record_of_another_program_is_refused` | |
| A record that names no program is refused | `mod.rs::a_record_that_names_no_program_is_refused` | |
| The program entry is first and well formed | `mod.rs::a_program_entry_must_be_first_and_well_formed` | |
| A reached helper renamed, with its calls, keeps the address | same test (reached_helper_renamed) | Decided from DESIGN step L1.19: the address covers the term `main` runs closed over what it reaches, and a closed term holds no names, as for the local names above. |
| A parameter of a reached helper renamed, with its calls, keeps the address | same test (parameter_of_a_reached_helper_renamed) | Decided as the row above. |
| Address of a large program | `bench.rs::the_address_of_a_program_scales` | Benchmark (P178). |
