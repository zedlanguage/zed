//! The refused shapes: a product of four or more sums over two or more names, and an exponent
//! past `u64::MAX` (`poly::REFUSED_SUMS`). A true identity of such a shape is rejected with
//! the refusal; a false one is refuted at a point first.

use zed_kernel::poly::{Carrier, Refused, Verdict};

use super::law;

const EIGHT: &str = "a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int";
const FOUR: &str = "(a + b) * (c + d) * (e + f) * (g + h)";

/// The 16 monomials of `FOUR`, plus `extra`.
fn written(extra: &str) -> String {
    let mut terms = Vec::new();
    for x in ["a", "b"] {
        for y in ["c", "d"] {
            for z in ["e", "f"] {
                for w in ["g", "h"] {
                    terms.push(format!("{x} * {y} * {z} * {w}"));
                }
            }
        }
    }
    format!("{}{extra}", terms.join(" + "))
}

#[test]
fn a_true_identity_of_four_sums_is_rejected() {
    let d = law(EIGHT, FOUR, &written(""), Carrier::Int);
    let Verdict::Refused(r) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    assert_eq!(r.why, Refused::Sums(4));
    assert_eq!(r.agreed.len(), 2);
    let law_text = format!("law four({EIGHT}) = {FOUR} == {}", written(""));
    let m = r.message(&law_text);
    let lines: Vec<&str> = m.lines().collect();
    assert_eq!(
        lines[0],
        "Cannot expand `((((a + b) * (c + d)) * (e + f)) * (g + h))`: it multiplies 4 sums of more than one name."
    );
    assert_eq!(
        lines[1],
        "  note: a product of 4 or more sums is expanded only when its sums are all in one name, as `(1 + x) ^ 2 * (1 + x ^ 2) ^ 2`."
    );
    assert!(
        lines[2].starts_with("  note: the two sides agree at every point tried: `a = "),
        "{m}"
    );
    assert_eq!(
        lines[3],
        format!("  Try `{law_text} proof {{ … }}` instead.")
    );
    assert_eq!(lines.len(), 4);
}

#[test]
fn a_false_identity_of_four_sums_is_refuted() {
    let d = law(EIGHT, FOUR, &written(" + a"), Carrier::Int);
    let Verdict::Refuted(p) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    // `-a` alone differs: every binder but `a` at 0, and `a` at 1.
    assert_eq!(
        p.to_string(),
        "a = 1, b = 0, c = 0, d = 0, e = 0, f = 0, g = 0, h = 0"
    );
}

#[test]
fn a_power_counts_its_exponent() {
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 4",
        "x ^ 4 + 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4",
        Carrier::Int,
    );
    assert!(matches!(d.verdict, Verdict::Refused(ref r) if r.why == Refused::Sums(4)));
    // Three is not refused.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 3",
        "x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
}

#[test]
fn sums_in_one_name_are_never_refused() {
    let d = law(
        "x: int",
        "(1 + x) ^ 64",
        "(1 + x) ^ 32 * (1 + x) ^ 32",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!(d.terms, Some([65, 65]));
    // Sums in one name times a name: the sums are still in one name.
    let d = law(
        "x: int, y: int",
        "(1 + x) ^ 8 * y",
        "y * (1 + x) ^ 4 * (1 + x) ^ 4",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
}

#[test]
fn a_ring_identity_of_four_sums_is_rejected_too() {
    let d = law(EIGHT, FOUR, &written(""), Carrier::Ring);
    assert!(matches!(d.verdict, Verdict::Refused(_)), "{:?}", d.verdict);
    // At a ring a point that differs proves nothing either way, and no refusal is reported.
    let d = law(EIGHT, FOUR, &written(" + a"), Carrier::Ring);
    assert_eq!(d.verdict, Verdict::Differs);
}
