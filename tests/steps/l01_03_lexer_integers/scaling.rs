//! The long texts the benchmarks of `bench.rs` lex, and what lexing each must give, checked
//! here at small sizes (TEST-bench-move-rest, P170).

use zedc::lex::lex;

/// `n` times five literals, one in each base and one with separators.
pub(super) fn literals_in_every_base(n: usize) -> String {
    "1_048_576 0o755 0xFF_88_00 0b1011 8080 ".repeat(n)
}

pub(super) fn lexes_five_integers_each(text: &str, n: usize) {
    assert_eq!(lex(text).unwrap().len(), 5 * n);
}

/// One integer of `2n + 1` digits with separators.
pub(super) fn long_literal(n: usize) -> String {
    "1_0".repeat(n) + "9"
}

pub(super) fn lexes_one_token(text: &str, _: usize) {
    assert_eq!(lex(text).unwrap().len(), 1);
}

/// A hex integer of `2n` digits run into a name.
pub(super) fn long_literal_into_a_name(n: usize) -> String {
    format!("0x{}g", "F_0".repeat(n))
}

pub(super) fn is_rejected(text: &str, _: usize) {
    assert!(lex(text).is_err());
}

#[test]
fn each_benchmark_text_lexes_as_its_benchmark_expects_at_small_sizes() {
    type Case = (fn(usize) -> String, fn(&str, usize));
    let cases: [Case; 3] = [
        (literals_in_every_base, lexes_five_integers_each),
        (long_literal, lexes_one_token),
        (long_literal_into_a_name, is_rejected),
    ];
    for (make, expect) in cases {
        for n in [1, 2, 9] {
            expect(&make(n), n);
        }
    }
}
