# L1.13 completeness: the formatter

Code under test: the source formatter (`crates/zedc-syntax/src/format.rs`) over the statements
`ast::unit` builds. Expected output: what the formatter writes builds to the same statements,
keeps every comment and formats to itself (DESIGN.md step L1.13); where a test names the text,
it is the layout the step describes.

Coverage (llvm-cov, regions, before and after this pass): `format.rs` 96.8% to 98.8%. What is
left:

- lines 192 to 201 (`starts_with_in` walking down the left operand of an index key): every unit
  that reaches them, `x[(i in s)..<5]` and the rest listed in `positions.rs`, is refused by
  `ast::unit` as not compiled yet, and the formatter only sees what `unit` builds; they are
  reached once those forms are compiled;
- the `}` lines of the list jobs (`Updates`, `Cases`, `Types`, `RecordType`, `Patterns`,
  `FieldPats`, lines 650 to 776): the empty list, which no job is pushed with, since each is
  pushed only with a non-empty rest and each list the grammar allows holds one item at least;
- line 1216, a call that curries with no argument, `f(...)`: the grammar puts `...` after one
  argument at least, so `f(...)` does not parse (checked);
- line 1435, `unreachable!("a block")`.

| Case | Covering test, or the reason none is needed |
|---|---|
| Every alternative of the grammar that builds formats to a fixed point | `alternatives::every_case_that_builds_formats_to_a_fixed_point` (the 502 cases of l01_08 `grammar_cases.rs`) |
| Every fence of DESIGN.md, every corpus program, every prelude file | `fences::*`, `corpus::*`, `prelude::*` |
| Each parenthesis a position needs (a block, `for` or `loop` as a first operand, a brace after a lambda's `->` or an `else`, an index key starting with `in`, a curried call, each head-flag case of l01_08) | `positions::each_parenthesis_a_position_needs_is_kept` |
| Spacing, parentheses, block layout, test tables, comments, blank lines, matches, imports, annotations, one-tuples, bounds, sort keys, types, unions, powers | `layout::*` (23 tests) |
| A source that does not parse or does not load is reported at its line and column | `layout::a_source_that_does_not_parse_is_reported_at_its_line_and_column`, `a_source_that_does_not_load_is_reported_at_its_line_and_column` |
| `main`'s header with its parameter, with an untyped parameter, with none, each with `-> int` | `main_header::main_is_written_with_the_parameter_and_type_it_was_given` |
| Triple-quoted strings at any depth and indentation, holes over lines, a comment after one, every escape byte for byte, CRLF sources | `strings::*` (6 tests) |
| Large inputs | Benchmarks; `scaling::each_benchmark_unit_is_formatted_at_small_sizes` |
