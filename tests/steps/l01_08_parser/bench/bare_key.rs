//! Finding a union, intersection or difference written bare as a key is a scan of its type and
//! two more parses, each linear: the benchmarks of `bare_key.rs`, whose test reports each input
//! at small sizes.

use zed_tests::scaling::{check, inputs};
use zedc::rejection::Row;

use crate::bare_key::{a_bare_key_of_many_operands, definitions_before_a_bare_key, many_bare_keys};
use crate::reserved::refusal;

/// The time is linear in the number of definitions before the type, in the number of operands
/// of its key, and in the number of its arrows (COMPLEXITY.md, PARSE-union-key-parens).
#[test]
fn finding_a_bare_key_is_linear() {
    let many = inputs(500, definitions_before_a_bare_key);
    check(
        "n definitions before `f(x: int | #a -> int) = 0;`",
        500,
        |n| {
            assert_eq!(refusal(&many[&n]).row, Some(Row::BareKey));
        },
    );
    let wide = inputs(500, a_bare_key_of_many_operands);
    check(
        "a bare key `int | #a0 | … -> int` of n operands",
        500,
        |n| {
            assert_eq!(refusal(&wide[&n]).row, Some(Row::BareKey));
        },
    );
    let long = inputs(200, many_bare_keys);
    check(
        "a type `#a0 | #b0 -> … -> int` of n bare keys",
        200,
        |n| {
            assert_eq!(refusal(&long[&n]).row, Some(Row::BareKey));
        },
    );
}
