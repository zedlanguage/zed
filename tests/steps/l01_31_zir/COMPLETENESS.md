# l01_31_zir: completeness of the correctness tests

DESIGN L1.31: ZIR, its text and binary forms, and the validator. Code under test:
crates/zedc-zir/src/zir/{mod.rs, text.rs, binary.rs, validate.rs}. Tables of cases name each
case in their failure message, so one run lists every mismatch.

| Case | Covering test | Or the reason none is needed |
|---|---|---|
| **Text form, whole graphs** | | |
| Each graph shape real programs lower to (fold with identity, wave and push, two ports, match on atoms, gen, fix lattice, group with reindex, if with facts, rec, constants, f32 constants), text and binary round trips | graphs.rs (11 tests) | |
| Every op the validator accepts, each with its region shape: lambda with 0 and 2 ports, if and match threading states, wave with two ports, gen after with a capture, fix definedness, reindex catalog, discard, fold with no identity, scan, join with two outputs, a prim as a value, a variadic prim with 0 and 3 inputs, apply with 0 arguments and of a captured function, rec of one function, a match on every pattern form | validation.rs `each_shape_the_validator_accepts_round_trips` (16 graphs) | |
| Blank lines anywhere and lines in any order read to the same graph | reading.rs `blank_lines_and_line_order_do_not_change_the_graph` | |
| Ports named `main::x` and by a field of `main`'s argument | reading.rs `ports_named_by_main_and_by_a_field_read_back`, items.rs `a_port_named_by_a_field_of_main_args_reads_back` | |
| Empty text, blank text | reading.rs `each_graph_the_reader_refuses_names_the_line_and_column` | |
| No root header line | same | |
| A region's lines with no line for its node | same | |
| A region's results with no header line under a present node | none merged | FAIL-zir-text-reader-messages: reported as "not in the graph" |
| An operation written on a region's path; a line with no path; a node line with no `->` | same | |
| Each unknown word of a choice: region kind, reindex way, fix kind, gen position, port op | same | |
| `main::a.b` and a port path part that is no name | same | The text gives "expected `(`"; the binary form reaches the `main::` message (binary_forms.rs) |
| An output list and a type form with no `)` | same | |
| Version line, unknown op, bad path, duplicated node and the other 30 earlier rejections | rejections.rs `each_rejection_names_its_cause` | |
| **Types** | | |
| Each type form read back: morphism of 2 and 3, partial morphism, union, meet, empty meet `_`, complement, atom forms, tuple, struct, numbers kept as powers, negative powers, rational literal types | reading.rs `each_type_form_reads_back_or_is_refused`, items.rs `types_read_back` | |
| Wrong arity of `->`, `->?` | reading.rs | |
| Wrong arity of `!` and `#ok`; `(\)` with no type | none merged | FAIL-zir-text-reader-messages: "takes 1 types", "not a type form" |
| Unknown form, unknown word, power that is no number, form with no `)` | reading.rs | |
| An atom form whose head is no name | items.rs `an_atom_type_form_with_a_head_that_is_no_name_is_rejected` | |
| **Edge facts** | | |
| Interval, set, class (empty, one, many), facets, hints, read back | reading.rs `each_edge_fact_reads_back_or_is_refused`, items.rs `edges_read_back` | |
| Interval with no `..`, class with no number | reading.rs | |
| **Values** | | |
| Every value form, f32 and f64 bits kept (nan, -0.0, subnormals), big integers, rationals reduced (`6r/3r` is `2r`, `1e3r`) | reading.rs `each_value_form_reads_back_or_is_refused`, items.rs `values_read_back`, `floats_keep_their_bits` | |
| Strings: each one-letter escape, `\u{…}`, no closing quote, unfinished escape, `\u` without `{`, a surrogate, no hex | reading.rs, items.rs `string_escapes` | |
| Atoms: named fields sorted, named and positional mixed refused | items.rs `named_payload_fields_sort`, reading.rs | |
| One-tuple written with a comma | items.rs `a_one_tuple_is_written_with_a_comma` | |
| Words that are no number: `12ab`, `3f32`, `1.2.3f32`, `1.5r`, `1r/0r`, `1.2.3`, a lone `-` | reading.rs | |
| A family literal with a repeated key, text and binary | rejections.rs (2 tests) | |
| **Patterns** | | |
| Each pattern form: literal, wildcard, any atom `#_`, bare atom, fields with none, named fields nested, positional, tuple, one-tuple, type test of a union | reading.rs `each_pattern_form_reads_back_or_is_refused`, items.rs `patterns_read_back`, validation.rs (match on every form) | |
| `#a( )` reads as `#a()` | none merged | FAIL-zir-text-reader-messages: reads as the bare atom `#a` |
| Type test with no `)` | reading.rs | |
| **Names** | | |
| Names by the lexer's rule; generated binders; names that are not names where a name belongs | names.rs (3 tests), items.rs `names_the_lexer_accepts_read_back`, `a_name_starts_as_the_lexer_starts_one`, `generated_binders_read_back` | |
| **Binary form** | | |
| Every graph above reads back from binary | `round` in mod.rs, used by every round trip | |
| A tag past the last case of each choice: operation, primitive, grade, boolean, guard position, derived node, pattern, value | binary_forms.rs `each_choice_with_a_tag_past_its_last_case_is_refused` | |
| The last case of each choice reads | binary_forms.rs `each_tag_at_its_last_case_reads` | |
| A rational with denominator 0; an f32 word wider than 32 bits; an atom with fewer values than fields; a count past the end; `main::a.c` as a port | binary_forms.rs (5 tests) | |
| Truncated data, a wrong magic or version, trailing bytes | rejections.rs `damaged_binary_data` | |
| Atom fields out of order in binary | rejections.rs `binary_atom_fields_in_order` | |
| **Validator** | | |
| Derived with no input or output; apply with no input; match with no arm; rec with no output | validation.rs `each_broken_rule_names_the_node_and_the_rule` | |
| Wrong input count of read, push, discard, reindex, fold with identity, fam, fix, gen, if, lambda | same | |
| Wrong output, region, region kind (if, wave, rec, lambda, gen), argument and result counts | same | |
| A state into a loop or rec region, captured into fam or lambda, as an if condition, out of a prim or fam | same | |
| Push and read with a state in the wrong place; apply's state rules (function a state, value after state, missing or first state output, no output) | same | |
| A lambda region's states in the wrong order or its value not first | same | |
| A result that does not fit its output (value for a state, state for a value, wrong state) | same | |
| An error deep in a graph named by its path | scaling.rs `an_error_deep_in_a_graph_is_named_by_its_path` | |
| **Debug printing** | scaling.rs `a_graph_prints_for_debugging_as_a_derived_debug_would` | |
| **Depth and size** | bench/ (deep.rs, scaling.rs, names.rs) | Unusual sizes are benchmarks (P178) |
