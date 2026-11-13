//! The tests the plan row names.

use zed_kernel::poly::{Carrier, Verdict};

use super::{decide_sides, law, sides_of};

#[test]
fn diff_squares_is_proved() {
    let d = law(
        "x: int, y: int",
        "(x + y) * (x - y)",
        "x * x - y * y",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!(d.terms, Some([2, 2]));
}

#[test]
fn three_sums_equal_their_eight_monomials() {
    let d = law(
        "a: int, b: int, c: int, d: int, e: int, f: int",
        "(a + b) * (c + d) * (e + f)",
        "a * c * e + a * c * f + a * d * e + a * d * f + b * c * e + b * c * f + b * d * e + b * d * f",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!((d.sums, d.terms), (3, Some([8, 8])));
}

#[test]
fn sum_square_is_proved() {
    // 16 products of 4 terms by 4, merged into 7 monomials.
    let d = law(
        "x: int",
        "(1 + x + x ^ 2 + x ^ 3) ^ 2",
        "(1 + x) ^ 2 * (1 + x ^ 2) ^ 2",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!((d.terms, d.degree), (Some([7, 7]), Some(6)));
    // Each side counts two sums: a power of a sum of two terms counts one, and the left's
    // base of four terms squared counts two, the fewer of 2 and 4 - 1.
    assert_eq!(d.sums, 2);
}

#[test]
fn wrong_is_refuted_at_one_one() {
    let d = law(
        "x: int, y: int",
        "(x + y) * (x + y)",
        "x * x + y * y",
        Carrier::Int,
    );
    let Verdict::Refuted(p) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    assert_eq!(p.to_string(), "x = 1, y = 1");
}

#[test]
fn the_points_are_the_same_alone_and_in_a_batch() {
    // A refused true identity reports its points; they depend on the identity alone, not on
    // the unit around it or on the run. Each side is a sum, so it is expanded, not read as a
    // product of the same four factors.
    const FOUR: &str = "four(a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int) = ((a + b) * (c + d) * (e + f) * (g + h) - a, (g + h) * (e + f) * (c + d) * (a + b) - a);\n";
    const OTHER: &str = "other(x: int, y: int) = ((x + y) * (x - y), x * x - y * y);\n";
    let alone = decide_sides(&sides_of(FOUR, &["four"])[0], Carrier::Int);
    let batch = sides_of(&format!("{OTHER}{FOUR}"), &["other", "four"]);
    let in_batch = decide_sides(&batch[1], Carrier::Int);
    let again = decide_sides(&sides_of(FOUR, &["four"])[0], Carrier::Int);
    assert!(
        matches!(alone.verdict, Verdict::Refused(_)),
        "{:?}",
        alone.verdict
    );
    assert_eq!(alone.verdict, in_batch.verdict);
    assert_eq!(alone.verdict, again.verdict);
    assert_eq!(
        decide_sides(&batch[0], Carrier::Int).verdict,
        Verdict::Proved
    );
}
