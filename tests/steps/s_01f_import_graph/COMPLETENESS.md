# S.1f import graph: cases and the tests that cover them

Code under test: `crates/zed-tools/src/imports.rs` and `imports/lex.rs` (the tool that draws the
import graph of a Rust crate). Measured with `-C instrument-coverage` and `llvm-cov` over this
group alone, regions% / lines%: `imports.rs` 97.36 / 96.94 before and 98.05 / 97.92 after;
`imports/lex.rs` 95.44 / 96.00 before and 99.67 / 100 after.

| Case | Test that covers it | Or reason none is needed |
|---|---|---|
| `use crate::...` paths, `mod` declarations, nested modules | mod.rs tests | |
| Each line of the report: file and import counts, unreached `.rs` files, `#[path]` modules, untyped method receivers, `impl` of an unknown type, no cycle | complete.rs `the_report_names_each_kind_of_file_and_call_it_leaves_out` | |
| A cycle in the report | mod.rs tests | |
| No argument; a directory that does not exist | complete.rs `the_tool_needs_a_directory_it_can_read` | |
| Raw identifiers (`r#type`, `r#match`) | complete.rs `a_raw_identifier_is_a_name_and_not_its_keyword` | |
| A string, raw string or char cut off at the end of the file | complete.rs `text_cut_off_at_the_end_of_a_file_names_nothing` | |
| Every prefix of a file using each scanned form (generics, `impl`, `fn` headers, patterns, closures, `for`, `match`, paths) | complete.rs `a_file_cut_off_at_every_length_is_read_without_failing` | |
| Scaling with files, calls and the known list | bench.rs (6 benchmarks) | |
| `shortest_cycle`'s `vec![start]` | none | Unreachable: it is called only on a node of a cycle, so the search always finds a path back |
| `read_sources` errors on a non-UTF-8 file name or a failing directory entry | none | Needs a file system that returns such names or errors |
