//! Products of powers of the same factors (POLY-nf-power-value, QUESTIONS A98): each side read
//! as a constant times powers of sums and names, each sum expanded once, the sides not at all.

use std::sync::Arc;

use zed_kernel::poly::{Carrier, Refused, Verdict, limit};
use zed_kernel::term::Term;
use zed_tests::scaling;

use super::{decide_sides, law, sides_of};

#[test]
fn split_is_proved_without_expanding_a_side() {
    let d = law(
        "x: int",
        "(1 + x) ^ 4294967296",
        "(1 + x) ^ 2147483648 * (1 + x) ^ 2147483648",
        Carrier::Int,
    );
    assert_eq!(
        (d.verdict, d.factored, d.terms),
        (Verdict::Proved, true, None)
    );
    // The factors may be written differently: `(x + 1)` and `(2 * x + 2) / 2` at `rat`.
    let d = law(
        "x: rat",
        "(1 + x) ^ 4294967296",
        "(x + 1) ^ 2147483648 * ((2 * x + 2) / 2) ^ 2147483648",
        Carrier::Rat,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
}

#[test]
fn the_a98_laws_at_exponent_1000() {
    let d = law(
        "x: int",
        "(1 + x) ^ 1000",
        "(1 + x) ^ 500 * (1 + x) ^ 500",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
    // Different factors on the two sides: the expansion would form 1001 monomials of up to
    // 1000 bits, more work than the limit of this size, so the law is refused (QUESTIONS A98),
    // at most the limit spent.
    let d = law(
        "x: int",
        "(1 + x) ^ 1000 * (1 - x) ^ 1000",
        "(1 - x ^ 2) ^ 1000",
        Carrier::Int,
    );
    let Verdict::Refused(r) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    assert_eq!((r.why, d.factored), (Refused::Work(d.size), false));
    assert!(d.work <= limit(d.size));
    eprintln!(
        "exponent 1000: size {} work {} limit {}",
        d.size,
        d.work,
        limit(d.size)
    );
    // At 2^32, which never finished before the work was counted, it is refused as soon.
    let d = law(
        "x: int",
        "(1 + x) ^ 4294967296 * (1 - x) ^ 4294967296",
        "(1 - x ^ 2) ^ 4294967296",
        Carrier::Int,
    );
    assert!(matches!(d.verdict, Verdict::Refused(_)), "{:?}", d.verdict);
    assert!(d.work <= limit(d.size));
    // At 10 it is expanded.
    let d = law(
        "x: int",
        "(1 + x) ^ 10 * (1 - x) ^ 10",
        "(1 - x ^ 2) ^ 10",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    assert_eq!(d.terms, Some([11, 11]));
}

#[test]
fn a_false_split_is_refuted_at_a_point() {
    for (lhs, rhs) in [
        (
            "(1 + x) ^ 4294967296",
            "(1 + x) ^ 2147483648 * (1 + x) ^ 2147483649",
        ),
        ("(1 + x) ^ 4294967296", "(1 - x) ^ 4294967296"),
        ("(2 * x + 2) ^ 2", "2 * (x + 1) ^ 2"),
    ] {
        let d = law("x: int", lhs, rhs, Carrier::Int);
        assert!(
            matches!(d.verdict, Verdict::Refuted(_)),
            "{lhs} == {rhs}: {:?}",
            d.verdict
        );
    }
}

#[test]
fn the_row_examples() {
    // `(x + y) ^ 1048576 == (y + x) ^ 1048576`: one factor, written two ways.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 1048576",
        "(y + x) ^ 1048576",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
    // A false identity that needs the expansion of such a power is refuted at a point.
    let d = law(
        "x: int",
        "(1 + x) ^ 1048576 - (1 - x) ^ 1048576",
        "0",
        Carrier::Int,
    );
    assert!(matches!(d.verdict, Verdict::Refuted(_)), "{:?}", d.verdict);
}

/// `(1 + x) ^ e == (1 + x) ^ h * (x + 1) ^ (e - h)` for `e = 2^bits - 1`, `h = 2^(bits - 1)`,
/// elaborated from Zed source.
fn split_of(bits: usize) -> (Term, Term, Vec<Arc<str>>) {
    let e = (1u128 << (bits - 1)) - 1 + (1u128 << (bits - 1));
    let h = 1u128 << (bits - 1);
    let src = format!(
        "split(x: int) = ((1 + x) ^ {e}, (1 + x) ^ {h} * (x + 1) ^ {});\n",
        e - h
    );
    sides_of(&src, &["split"]).remove(0)
}

#[test]
fn the_split_scales_with_its_exponent_digits() {
    // 16 and 128 bits: the work is the points' powers, one squaring a bit, and the factors'
    // expansion, the same at both.
    let ins = scaling::inputs(16, split_of);
    scaling::check(
        "(1 + x) ^ e == (1 + x) ^ h * (x + 1) ^ (e - h), e of n bits",
        16,
        |n| {
            let d = decide_sides(&ins[&n], Carrier::Int);
            assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
        },
    );
}
