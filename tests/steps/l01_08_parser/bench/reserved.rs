//! Finding a reserved word written as a name takes at most a few more parses, each linear: the
//! benchmarks of `reserved.rs`, whose test reports each input at small sizes.

use zed_tests::scaling::{check, inputs};
use zedc::rejection::Row;

use crate::reserved::{bindings_before_a_word, many_reserved_words, refusal, terms_before_a_word};

/// The time is linear in the number of statements before the word, and in the length of its
/// statement.
#[test]
fn finding_the_word_is_linear() {
    let many = inputs(500, bindings_before_a_word);
    check("n bindings before `without = 3;`", 500, |n| {
        assert_eq!(refusal(&many[&n]).row, Some(Row::ReservedWordAsName));
    });
    let long = inputs(500, terms_before_a_word);
    check("a statement of n terms ending in `y.if`", 500, |n| {
        assert_eq!(refusal(&long[&n]).row, Some(Row::ReservedWordAsName));
    });
}

/// Each word tried is one more parse, and at most three are tried, so the time stays linear
/// (COMPLEXITY.md, MSG-keyword-as-name).
#[test]
fn many_reserved_words_in_one_statement_are_linear() {
    let long = inputs(500, many_reserved_words);
    check("a statement of n words `true` ending in `is ;`", 500, |n| {
        assert_eq!(refusal(&long[&n]).row, Some(Row::SyntaxError));
    });
}
