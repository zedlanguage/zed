//! The long texts the benchmarks of `bench.rs` lex, and what lexing each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170).

use zedc::lex::lex;

/// `n` times five literals and a range `1..10` of three tokens.
pub(super) fn literals(n: usize) -> String {
    "0.5 1.5e-3 6.022_140_76e23 0.1r 2.5e-3r 1..10 ".repeat(n)
}

pub(super) fn lexes_eight_tokens_each(text: &str, n: usize) {
    assert_eq!(lex(text).unwrap().len(), 8 * n);
}

/// A rational of `5n` digits: a long float with a long exponent.
pub(super) fn long_float_with_a_long_exponent(n: usize) -> String {
    format!(
        "{}.{}e-{}r",
        "1_0".repeat(n),
        "0_5".repeat(n),
        "1".repeat(n)
    )
}

pub(super) fn lexes_one_token(text: &str, _: usize) {
    assert_eq!(lex(text).unwrap().len(), 1);
}

/// A float of `2n` digits run into a name.
pub(super) fn long_float_into_a_name(n: usize) -> String {
    format!("{}.5{}", "1_0".repeat(n), "m".repeat(n))
}

pub(super) fn is_rejected(text: &str, _: usize) {
    assert!(lex(text).is_err());
}

#[test]
fn each_benchmark_text_lexes_as_its_benchmark_expects_at_small_sizes() {
    type Case = (fn(usize) -> String, fn(&str, usize));
    let cases: [Case; 3] = [
        (literals, lexes_eight_tokens_each),
        (long_float_with_a_long_exponent, lexes_one_token),
        (long_float_into_a_name, is_rejected),
    ];
    for (make, expect) in cases {
        for n in [1, 2, 9] {
            expect(&make(n), n);
        }
    }
}
