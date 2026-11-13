//! The refusal: an identity whose expansion is predicted to take more than 250 ms, the work
//! `poly::LIMIT` (QUESTIONS A99), or that holds an exponent past `u64::MAX`. A true identity
//! past the limit is rejected with the refusal; a false one is refuted at a point first.

use zed_kernel::poly::{Carrier, LIMIT, Refused, Verdict};

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
fn a_true_identity_of_four_sums_is_proved() {
    // Sixteen products of one word each: far below the limit.
    let d = law(EIGHT, FOUR, &written(""), Carrier::Int);
    assert_eq!(d.verdict, Verdict::Proved);
    assert!(d.work <= LIMIT / 10_000.0, "{} of {LIMIT}", d.work);
}

#[test]
fn a_power_past_the_limit_is_rejected() {
    const XY: &str = "x: int, y: int";
    // The product has 1025 ^ 2 monomials of up to 1024 bits: far past the limit, while the four
    // powers before it cost a few hundredths of it.
    let (lhs, rhs) = (
        "(1 + x) ^ 1024 * (1 + y) ^ 1024 - x",
        "(1 + y) ^ 1024 * (1 + x) ^ 1024 - x",
    );
    let d = law(XY, lhs, rhs, Carrier::Int);
    let Verdict::Refused(r) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    let Refused::Work(work) = r.why else {
        panic!("{:?}", r.why)
    };
    assert_eq!(r.agreed.len(), 2);
    // Each operation is charged before it runs, so the refusal spends at most the limit, and
    // the work it reports is what was spent and the refused product's charge.
    assert!(d.work <= LIMIT / 20.0, "{}", d.work);
    assert!(work > LIMIT, "{work}");
    let law_text = format!("law two({XY}) = {lhs} == {rhs}");
    let m = r.message(&law_text);
    let lines: Vec<&str> = m.lines().collect();
    assert_eq!(
        lines[0],
        format!(
            "Cannot expand `{}`: expanding the law takes at least {} ms, more than 250 ms.",
            r.product,
            (work / LIMIT * 250.0).ceil()
        )
    );
    assert_eq!(
        lines[1],
        format!(
            "  note: the time is predicted from the sizes of the sums and products: at least {work:.0} units of work, against a limit of 17500000 units measured as 250 ms on one machine, so that every machine refuses the same laws."
        )
    );
    assert!(
        lines[2].starts_with("  note: the two sides agree at every point tried: `x = "),
        "{m}"
    );
    assert_eq!(
        lines[3],
        format!("  Try `{law_text} proof {{ … }}` instead.")
    );
    assert_eq!(lines.len(), 4);
    // At a sixteenth of the exponent it is expanded, a 256th of the work.
    let d = law(
        XY,
        "(1 + x) ^ 64 * (1 + y) ^ 64 - x",
        "(1 + y) ^ 64 * (1 + x) ^ 64 - x",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    // The split law that the size rule of QUESTIONS A98 refused from exponent 72 on is proved
    // at 128 and 1024, a few milliseconds of work (`calibration` times it).
    for k in [128, 1024] {
        let d = law(
            XY,
            &format!("(x + y) ^ {k} - x"),
            &format!("(x + y) ^ {} * (y + x) ^ {} - x", k / 2, k / 2),
            Carrier::Int,
        );
        assert_eq!((d.verdict, d.factored), (Verdict::Proved, false), "{k}");
    }
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
fn a_power_of_a_sum_is_expanded() {
    // A base of two monomials counts one sum at any exponent: `(x + y) ^ n` has n + 1 terms.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 4",
        "x ^ 4 + 4 * x ^ 3 * y + 6 * x ^ 2 * y ^ 2 + 4 * x * y ^ 3 + y ^ 4",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
    assert_eq!(d.sums, 1);
    // As a product of powers of one factor it is proved with neither side expanded.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 64",
        "(x + y) ^ 32 * (y + x) ^ 32",
        Carrier::Int,
    );
    assert_eq!(
        (d.verdict, d.factored, d.terms),
        (Verdict::Proved, true, None)
    );
    // In a sum it is expanded: 65 monomials less `x ^ 64`.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 64 - x ^ 64",
        "(x + y) ^ 32 * (y + x) ^ 32 - x ^ 64",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    assert_eq!(d.terms, Some([64, 64]));
    // A false one is refuted at a point: every binder at 0 but `x` at 1 gives 1 against 2.
    let d = law(
        "x: int, y: int",
        "(x + y) ^ 64",
        "(x + y) ^ 32 * (y + x) ^ 32 + x",
        Carrier::Int,
    );
    let Verdict::Refuted(p) = d.verdict else {
        panic!("{:?}", d.verdict)
    };
    assert_eq!(p.to_string(), "x = 1, y = 0");
    // A base of five monomials to the 4th counts the fewer of 4 and 5 - 1 sums, and is
    // expanded in a sum (as a product of powers of one factor it is proved without).
    const FIVE: &str = "a: int, b: int, c: int, d: int, f: int";
    let d = law(
        FIVE,
        "(a + b + c + d + f) ^ 4 - f ^ 4",
        "(f + d + c + b + a) ^ 2 * (a + b + c + d + f) ^ 2 - f ^ 4",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored, d.sums), (Verdict::Proved, false, 4));
    let d = law(
        FIVE,
        "(a + b + c + d + f) ^ 4",
        "(f + d + c + b + a) ^ 2 * (a + b + c + d + f) ^ 2",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
    // To the 3rd it counts three, and is expanded.
    let d = law(
        FIVE,
        "(a + b + c + d + f) ^ 3 - f ^ 3",
        "(f + d + c + b + a) ^ 2 * (a + b + c + d + f) - f ^ 3",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    assert_eq!(d.sums, 3);
}

#[test]
fn sums_in_one_name_are_never_refused() {
    let d = law(
        "x: int",
        "(1 + x) ^ 64 - 1",
        "(1 + x) ^ 32 * (1 + x) ^ 32 - 1",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, false));
    assert_eq!(d.terms, Some([64, 64]));
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
fn a_ring_identity_is_decided_as_an_int_one() {
    let d = law(EIGHT, FOUR, &written(""), Carrier::Ring);
    assert_eq!(d.verdict, Verdict::Proved);
    let d = law(
        "x: int, y: int",
        "(1 + x) ^ 1024 * (1 + y) ^ 1024 - x",
        "(1 + y) ^ 1024 * (1 + x) ^ 1024 - x",
        Carrier::Ring,
    );
    assert!(matches!(d.verdict, Verdict::Refused(_)), "{:?}", d.verdict);
    // At a ring a point that differs proves nothing either way, and no refusal is reported.
    let d = law(EIGHT, FOUR, &written(" + a"), Carrier::Ring);
    assert_eq!(d.verdict, Verdict::Differs);
}
