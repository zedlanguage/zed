//! The measurement that fixes the refused shapes: the normal forms of the corpus's
//! obligations. The obligations are the spec's laws over ring operations (DESIGN.md
//! sec:verification, sec:theories, sec:optimizer and DOCS-TODO) and the associativity and
//! commutativity obligations of the reducers of the studies' corpora (ASSOC-infer, H10-hull),
//! each written out with its operands substituted, a tuple's components as separate
//! obligations. The 31 programs of `corpus/` state no law. None of the obligations multiplies
//! more than three sums, so `poly::REFUSED_SUMS` refuses none (COMPLEXITY.md POLY-nf-sums).

use zed_kernel::poly::{Carrier, REFUSED_SUMS, Verdict};

use super::law;

/// The expected verdict of an obligation.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Expect {
    Proved,
    Refuted,
    Differs,
}

/// Each obligation: its source, its binders, the two sides, the carrier, the verdict.
const OBLIGATIONS: &[(&str, &str, &str, &str, Carrier, Expect)] = {
    use Carrier::{Int, Rat, Ring};
    use Expect::{Differs, Proved, Refuted};
    const I3: &str = "a: int, b: int, c: int";
    const I2: &str = "a: int, b: int";
    const R3: &str = "a: rat, b: rat, c: rat";
    &[
        // The spec's laws.
        (
            "cube",
            I2,
            "(a + b) ^ 3",
            "a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3",
            Int,
            Proved,
        ),
        (
            "square",
            I2,
            "(a + b) * (a + b)",
            "a * a + 2 * a * b + b * b",
            Ring,
            Proved,
        ),
        (
            "subSq",
            I2,
            "(a - b) * (a - b)",
            "a * a - 2 * a * b + b * b",
            Ring,
            Proved,
        ),
        ("addC", I2, "a + b", "b + a", Int, Proved),
        ("mulC", I2, "a * b", "b * a", Int, Proved),
        (
            "w, h at abs",
            "a: int",
            "abs(a) + -abs(a)",
            "0",
            Ring,
            Proved,
        ),
        (
            "evenRun body",
            "x: int",
            "x * (x + 1)",
            "x ^ 2 + x",
            Int,
            Proved,
        ),
        (
            "six body",
            "x: int",
            "x ^ 3 - x",
            "(x - 1) * x * (x + 1)",
            Int,
            Proved,
        ),
        (
            "oddSq8 body",
            "q: int",
            "(2 * q + 1) * (2 * q + 1)",
            "4 * q ^ 2 + 4 * q + 1",
            Int,
            Proved,
        ),
        // a + b, a * b and the moments' componentwise sums.
        ("+ assoc", I3, "(a + b) + c", "a + (b + c)", Int, Proved),
        ("* assoc", I3, "(a * b) * c", "a * (b * c)", Int, Proved),
        // a - b.
        ("- assoc", I3, "(a - b) - c", "a - (b - c)", Int, Refuted),
        ("- comm", I2, "a - b", "b - a", Int, Refuted),
        // (a + b) / 2.
        (
            "mean assoc",
            R3,
            "((a + b) / 2 + c) / 2",
            "(a + (b + c) / 2) / 2",
            Rat,
            Refuted,
        ),
        (
            "mean comm",
            "a: rat, b: rat",
            "(a + b) / 2",
            "(b + a) / 2",
            Rat,
            Proved,
        ),
        // 2 * a + 2 * b.
        (
            "2a+2b assoc",
            I3,
            "2 * (2 * a + 2 * b) + 2 * c",
            "2 * a + 2 * (2 * b + 2 * c)",
            Int,
            Refuted,
        ),
        (
            "2a+2b comm",
            I2,
            "2 * a + 2 * b",
            "2 * b + 2 * a",
            Int,
            Proved,
        ),
        // a + 2 * b.
        (
            "a+2b assoc",
            I3,
            "(a + 2 * b) + 2 * c",
            "a + 2 * (b + 2 * c)",
            Int,
            Refuted,
        ),
        ("a+2b comm", I2, "a + 2 * b", "b + 2 * a", Int, Refuted),
        // a * b + 1.
        (
            "ab+1 assoc",
            I3,
            "(a * b + 1) * c + 1",
            "a * (b * c + 1) + 1",
            Int,
            Refuted,
        ),
        ("ab+1 comm", I2, "a * b + 1", "b * a + 1", Int, Proved),
        // a + b + a * b.
        (
            "a+b+ab assoc",
            I3,
            "(a + b + a * b) + c + (a + b + a * b) * c",
            "a + (b + c + b * c) + a * (b + c + b * c)",
            Int,
            Proved,
        ),
        (
            "a+b+ab comm",
            I2,
            "a + b + a * b",
            "b + a + b * a",
            Int,
            Proved,
        ),
        // a * b - a - b + 2.
        (
            "ab-a-b+2 assoc",
            I3,
            "(a * b - a - b + 2) * c - (a * b - a - b + 2) - c + 2",
            "a * (b * c - b - c + 2) - a - (b * c - b - c + 2) + 2",
            Int,
            Proved,
        ),
        (
            "ab-a-b+2 comm",
            I2,
            "a * b - a - b + 2",
            "b * a - b - a + 2",
            Int,
            Proved,
        ),
        // a * b + a.
        (
            "ab+a assoc",
            I3,
            "(a * b + a) * c + (a * b + a)",
            "a * (b * c + b) + a",
            Int,
            Refuted,
        ),
        ("ab+a comm", I2, "a * b + a", "b * a + b", Int, Refuted),
        // The affine maps (a.0 * b.0, b.0 * a.1 + b.1), components 0 and 1.
        (
            "affine.0 assoc",
            "a0: int, b0: int, c0: int",
            "(a0 * b0) * c0",
            "a0 * (b0 * c0)",
            Int,
            Proved,
        ),
        (
            "affine.1 assoc",
            "a0: int, a1: int, b0: int, b1: int, c0: int, c1: int",
            "c0 * (b0 * a1 + b1) + c1",
            "(b0 * c0) * a1 + (c0 * b1 + c1)",
            Int,
            Proved,
        ),
        // M(n: b.n - a.n, s: a.s + b.s), component n; tup(b.0 - a.0, a.1 + b.1) alike.
        ("M.n assoc", I3, "c - (b - a)", "(c - b) - a", Int, Refuted),
        // M(n: a.n + b.n, s: a.s + b.n), component s.
        (
            "M.s assoc",
            "sa: int, bn: int, cn: int",
            "(sa + bn) + cn",
            "sa + (bn + cn)",
            Int,
            Proved,
        ),
        // (a + b) / (1 + a * b) divides by a sum: the quotient is an atom.
        (
            "velocity comm",
            "a: rat, b: rat",
            "(a + b) / (1 + a * b)",
            "(b + a) / (1 + b * a)",
            Rat,
            Differs,
        ),
    ]
};

#[test]
fn no_obligation_is_refused() {
    let mut most = 0;
    for (name, params, lhs, rhs, carrier, expect) in OBLIGATIONS {
        let d = law(params, lhs, rhs, *carrier);
        let got = match &d.verdict {
            Verdict::Proved => Expect::Proved,
            Verdict::Refuted(_) => Expect::Refuted,
            Verdict::Differs => Expect::Differs,
            Verdict::Refused(r) => panic!("{name} refused: {r:?}"),
        };
        assert_eq!(got, *expect, "{name}: {:?}", d.verdict);
        eprintln!(
            "{name:16} sums {} degree {:?} terms {:?} {:?}",
            d.sums, d.degree, d.terms, d.verdict
        );
        most = most.max(d.sums);
    }
    assert_eq!(most, 3, "the most sums an obligation multiplies");
    assert!(most < REFUSED_SUMS);
}
