# Completeness: l02_06c_infix_calls

Step L2.6c (DESIGN.md sec:power, tier 6; author, Q36), infix calls: `a ~f~ b` is the call
`f(a, b)`, between Range and Additive, left-associative. Plan row INFIX-call. Before this group
the step had no tests; the lexer token and its reserved-word rejection are tested in
l01_02_lexer, and the formatter's rejected alternatives and the near-miss table carry one case
each (l01_13_formatter, l01_21_test_runner).

| Case | Covering test | Or reason none is needed |
|---|---|---|
| The value is that of the written-out call | `calls.rs::an_infix_call_is_the_call` | |
| A chain associates to the left; parentheses on the right | `calls.rs::a_chain_associates_to_the_left` | |
| The tier: looser than `+`, `*`, `^`, prefix; tighter than ranges, comparisons, `><`, `with`, `&&`, `else` | `calls.rs::the_tier_between_range_and_additive` | |
| Operands: postfix chains, calls, indexes, lambdas and comparisons in parentheses | `calls.rs::operands` | |
| A prefix `-` or `!` opening the right operand is accepted | `calls.rs::a_prefix_operator_opens_the_right_operand` | |
| The call's errors: a parameter too many or too few, a named parameter, an undefined name, a wrong type, overloads; placed in a chain | `calls.rs::the_calls_rules` | |
| Overload and recursion verdicts the same as the written-out call | `calls.rs::agrees_with_the_overload_cycle_cases` | |
| `operator +` and `(+)` declarations are syntax errors | `calls.rs::no_operator_definitions` | |
| A binary operator opening the right operand rejected with both readings, exact text | `rejections.rs::a_binary_operator_opening_the_right_operand` | |
| A binary or prefix operator closing the left operand rejected with both readings | `rejections.rs::an_operator_closing_the_left_operand` | |
| Every binary operator on each edge, and in a chain | `rejections.rs::every_edge` | |
| Parentheses leave one reading | `rejections.rs::parentheses_leave_one_reading` | |
| A qualified name rejected with the call written out | `rejections.rs::a_qualified_name` | |
| A reserved word between the tildes | | In l01_02_lexer: the lexer rejects it. |
| Printed back infix with minimal parentheses | `printing.rs::printed_back_infix` | |
| Random expressions: the round trip keeps the tree, each printed pair of parentheses is needed | `printing.rs::round_trip_and_minimal_parentheses` | `(1).len` keeps parentheses the tree does not need, so that `1.len` does not read as a decimal. |
| A chain of n calls, accepted and rejected; 4,000 deep on a test thread | `scaling.rs` | The ratio at n and 8n is in `bench/scaling.rs` (P178). |
| Point and Vec operands, methods as infix functions | | Structs and methods are steps L2.4 to L2.6, not built yet; an infix call's meaning does not depend on the operand types. |
