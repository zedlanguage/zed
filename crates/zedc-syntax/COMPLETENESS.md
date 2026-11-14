# Completeness: zedc-syntax unit tests

Row TEST-complete-crates (author P189). The crate has no unit tests: `src/` holds no `#[test]`
and no `#[cfg(test)]` module, so no code is exercised by unit tests of its own and there are no
cases to list here. Its code (the lexer `src/lex`, the parser `src/parse`, the syntax tree
`src/ast` and the formatter `src/format.rs`) is tested through the compiler by the step groups
of layer L1, each with its own case list (`COMPLETENESS.md` in the group):

| Code | Step group |
|---|---|
| Source loading | `tests/steps/l01_01_source_loading` |
| Names | `tests/steps/l01_02_lexer_names` |
| Integer literals | `tests/steps/l01_03_lexer_integers` |
| Float and rational literals | `tests/steps/l01_04_lexer_floats_and_rationals` |
| Strings | `tests/steps/l01_05_lexer_strings` |
| Other tokens | `tests/steps/l01_06_lexer_tokens` |
| Fences | `tests/steps/l01_07_fences` |
| Parser | `tests/steps/l01_08_parser` |
| Postfix chains | `tests/steps/l01_09_postfix_chains` |
| Lambdas, types, `else`, tuples | `tests/steps/l01_10_lambdas_types_else_tuples` |
| Statements | `tests/steps/l01_11_statements` |
| Declarations | `tests/steps/l01_12_declarations` |
| Formatter | `tests/steps/l01_13_formatter` |

Later layers' syntax is tested by `l02_01_parser_structs`, `l02_02_parser_match_imports`,
`l03_01_parser` and `l06_01_parser`.
