//! The normal form as printed, each kind of leaf (constants, names, atoms, `let`), powers 0
//! and 1, the carriers `int`, `rat` and a ring, the refusal of an exponent past `u64::MAX`, and
//! the witness read from the expanded difference when the points cannot be evaluated (DESIGN
//! sec:verification rung 2: "products of sums are expanded, `x^n` with a literal `n` is the
//! monomial `x` to the `n`, and like monomials are merged"; at any other carrier the term is
//! an atom).

use zed_kernel::poly::{Carrier, Decision, Refused, Verdict, normal_form};

use super::{law, sides_of};

/// The normal form of `e` over `params` at `carrier`, or the refusal's message for the law `L`.
fn nf(params: &str, e: &str, carrier: Carrier) -> Result<String, String> {
    let s = &sides_of(&format!("sides({params}) = ({e}, 0);\n"), &["sides"])[0];
    let names: Vec<&str> = s.2.iter().map(|p| &**p).collect();
    normal_form(&s.0, &names, carrier).map_err(|r| r.message("L"))
}

/// Each `(params, expression, carrier, normal form)`, every mismatch in one failure.
fn forms(cases: &[(&str, &str, Carrier, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(p, e, c, want)| {
            let got = nf(p, e, *c).unwrap_or_else(|m| format!("refused: {m}"));
            (got != *want).then(|| format!("{e} at {c:?}: got {got:?}, want {want:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

const XY: &str = "x: int, y: int";

#[test]
fn the_normal_form_prints_the_highest_degree_first_then_by_the_names_order() {
    forms(&[
        (XY, "(x + y) ^ 2", Carrier::Int, "x ^ 2 + 2 * x * y + y ^ 2"),
        (XY, "(x - y) * (x + y)", Carrier::Int, "x ^ 2 - y ^ 2"),
        (
            XY,
            "y * x ^ 2 + x * y ^ 2 + x ^ 3",
            Carrier::Int,
            "x ^ 3 + x ^ 2 * y + x * y ^ 2",
        ),
        (XY, "y + x", Carrier::Int, "x + y"),
        (XY, "y * y - x", Carrier::Int, "y ^ 2 - x"),
        ("x: int", "-x", Carrier::Int, "-x"),
        ("x: int", "(-x) ^ 3", Carrier::Int, "-x ^ 3"),
        ("x: int", "0 - 2 * x", Carrier::Int, "-2 * x"),
        (
            "x: int",
            "123456789012345678901234567890 * x",
            Carrier::Int,
            "123456789012345678901234567890 * x",
        ),
        // A ring's normal form is the integer one.
        (
            "x: int",
            "(1 + x) ^ 3",
            Carrier::Ring,
            "x ^ 3 + 3 * x ^ 2 + 3 * x + 1",
        ),
    ]);
}

#[test]
fn constants_and_the_powers_0_and_1() {
    forms(&[
        ("x: int", "3", Carrier::Int, "3"),
        ("x: int", "x - x", Carrier::Int, "0"),
        ("x: int", "x * 0", Carrier::Int, "0"),
        ("x: int", "x ^ 0", Carrier::Int, "1"),
        ("x: int", "x ^ 1", Carrier::Int, "x"),
        // A base of 0, 1 or -1 takes an exponent of any width: its power is a constant.
        ("x: int", "1 ^ 18446744073709551616", Carrier::Int, "1"),
        ("x: int", "0 ^ 18446744073709551616", Carrier::Int, "0"),
        ("x: int", "(-1) ^ 18446744073709551617", Carrier::Int, "-1"),
        ("x: int", "-(1 ^ 18446744073709551617)", Carrier::Int, "-1"),
        // The widest exponent a monomial holds.
        (
            "x: int",
            "x ^ 18446744073709551615",
            Carrier::Int,
            "x ^ 18446744073709551615",
        ),
    ]);
    for (l, r) in [
        ("x ^ 0", "1"),
        ("x", "x"),
        ("(-1) ^ 18446744073709551617", "-1"),
    ] {
        assert_eq!(
            law("x: int", l, r, Carrier::Int).verdict,
            Verdict::Proved,
            "{l}"
        );
    }
}

#[test]
fn rationals_are_coefficients_only_at_rat() {
    forms(&[
        ("r: rat", "r / 2 - r / 3", Carrier::Rat, "1/6 * r"),
        ("r: rat", "r * 2 / 4", Carrier::Rat, "1/2 * r"),
        ("r: rat", "0.5 * r", Carrier::Rat, "1/2 * r"),
        // At `int` the division is an atom.
        ("r: rat", "r / 2", Carrier::Int, "(r / 2r)"),
    ]);
    let d = law(XY, "x * y", "y * x", Carrier::Rat);
    assert_eq!(d.verdict, Verdict::Proved);
}

#[test]
fn a_term_that_is_not_ring_arithmetic_is_an_atom() {
    forms(&[
        ("x: int", "abs(x) * 2 + x", Carrier::Int, "x + 2 * abs(x)"),
        // `x ^ n` is a monomial only for a literal `n`.
        ("x: int", "x ^ 2 ^ 3", Carrier::Int, "(x^(2^3))"),
    ]);
    // Two different atoms differ, and no point refutes them.
    let d = law("x: int", "\"a\" == \"a\"", "true", Carrier::Int);
    assert_eq!(d.verdict, Verdict::Differs);
}

#[test]
fn a_let_is_read_through() {
    forms(&[(
        "x: int",
        "{ s = x + 1; s * s }",
        Carrier::Int,
        "x ^ 2 + 2 * x + 1",
    )]);
    // A `let` whose name is not used adds nothing.
    let d = law("x: int", "{ s = x * x; x }", "x", Carrier::Int);
    assert_eq!(d.verdict, Verdict::Proved);
}

#[test]
fn at_a_ring_a_true_identity_is_proved_and_a_false_one_only_differs() {
    for (l, r) in [("x + x", "2 * x"), ("x * x", "x ^ 2")] {
        assert_eq!(
            law("x: int", l, r, Carrier::Ring).verdict,
            Verdict::Proved,
            "{l}"
        );
    }
    // It holds mod 2, so at a ring of unknown characteristic it is not refuted.
    let (l, r) = ("(x + y) * (x + y)", "x * x + y * y");
    assert_eq!(law(XY, l, r, Carrier::Ring).verdict, Verdict::Differs);
    assert_eq!(
        law(XY, l, r, Carrier::Int).verdict.clone(),
        Verdict::Refuted(refuted_at(&[("x", 1), ("y", 1)]))
    );
}

fn refuted_at(p: &[(&str, i64)]) -> zed_kernel::poly::Point {
    zed_kernel::poly::Point(p.iter().map(|(n, v)| ((*n).into(), (*v).into())).collect())
}

fn refusal(d: &Decision) -> &zed_kernel::poly::Refusal {
    match &d.verdict {
        Verdict::Refused(r) => r,
        v => panic!("{v:?}"),
    }
}

#[test]
fn an_exponent_past_u64_max_is_refused() {
    // In the normal form: the power, and a product whose degree passes `u64::MAX`.
    for (e, product) in [
        ("x ^ 18446744073709551616", "(x^18446744073709551616)"),
        (
            "(x ^ 9223372036854775808) * (x ^ 9223372036854775808)",
            "((x^9223372036854775808) * (x^9223372036854775808))",
        ),
    ] {
        assert_eq!(
            nf("x: int", e, Carrier::Int),
            Err(format!(
                "Cannot expand `{product}`: an exponent is above 18446744073709551615.\n  Try \
                 `L proof {{ … }}` instead."
            )),
            "{e}"
        );
    }
    // In a law the points come first, at every carrier, and are listed when they agree.
    let (l, r) = (
        "x ^ 18446744073709551616 + x",
        "x + x ^ 18446744073709551616",
    );
    for c in [Carrier::Int, Carrier::Ring] {
        let d = law("x: int", l, r, c);
        let r = refusal(&d);
        assert_eq!(
            (&r.why, r.product.as_str()),
            (&Refused::Exponent, "(x^18446744073709551616)")
        );
        assert_eq!(r.agreed.len(), 2);
        let m = r.message("L");
        let lines: Vec<&str> = m.lines().collect();
        assert_eq!(lines.len(), 3, "{m}");
        assert_eq!(
            lines[1],
            format!(
                "  note: the two sides agree at every point tried: `{}` and `{}`.",
                r.agreed[0], r.agreed[1]
            )
        );
    }
    // A false law is refuted at a point before the exponent is looked at; a law whose sides are
    // the same power is found equal as powers of the same factor.
    let d = law("x: int", "x ^ 18446744073709551616", "x", Carrier::Int);
    assert_eq!(d.verdict, Verdict::Refuted(refuted_at(&[("x", -1)])));
    let d = law(
        "x: int",
        "x ^ 18446744073709551616",
        "x ^ 18446744073709551616",
        Carrier::Int,
    );
    assert_eq!((d.verdict, d.factored), (Verdict::Proved, true));
}

#[test]
fn where_no_point_can_be_evaluated_the_witness_is_read_from_the_expanded_difference() {
    // The denominator is the prime `2^61 - 1` the points are taken modulo, so no point is
    // evaluated, the sides are expanded, and the witness is found from their difference.
    const R: &str = "r: rat";
    for (l, r, terms) in [
        ("r / 2305843009213693951", "0", [1, 0]),
        ("r / 2305843009213693951 + r", "r + 1", [1, 2]),
    ] {
        let d = law(R, l, r, Carrier::Rat);
        assert_eq!(d.verdict, Verdict::Refuted(refuted_at(&[("r", 1)])), "{l}");
        assert_eq!(d.terms, Some(terms), "{l}");
    }
    let d = law(
        R,
        "r / 2305843009213693951 * 2305843009213693951",
        "r",
        Carrier::Rat,
    );
    assert_eq!((d.verdict, d.terms), (Verdict::Proved, Some([1, 1])));
}
