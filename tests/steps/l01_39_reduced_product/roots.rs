//! The integer roots of an obligation's equation are a listed set (DESIGN.md sec:constraints,
//! "Reduction", QUESTIONS A81, plan row ROOTS-listed): where a division's divisor is a
//! polynomial in one name, each written constraint is evaluated at each integer root of the
//! divisor in the name's range, and a root a constraint rules out does not reach the division.

use num_bigint::BigInt;
use zed_kernel::poly::roots::{Roots, Sparse, integer_roots};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::{sig, type_errors};
use zedc::store::preimage::counts::evaluations;

/// A written constraint no domain decides, so that only its evaluation at a member does: true
/// where `p mod 9` is 1, 2 or 3, and false where it is 4 to 8 (at 4, 5, 7 and 10, false,
/// false, false and true). DESIGN's `g` and `h` write `isPrime(p)`; the walk reads a call as a
/// value it knows nothing of, so a constraint it evaluates is written with operators.
const C: &str = "(p * (p + 1) * (p + 2)) mod 9 == 6";

/// `g(p: int) = if {range} && {test} { 10 div ({divisor}) } else { 0 };`, its signature, and
/// the written constraints evaluated while it was checked.
fn g(range: &str, test: &str, divisor: &str) -> (String, u64) {
    let text = format!("g(p: int) = if {range} && {test} {{ 10 div ({divisor}) }} else {{ 0 }};\n");
    let before = evaluations();
    let s = sig(&text, "g");
    (s, evaluations() - before)
}

const SMALL: &str = "p >= 4 && p <= 12";
const WIDE: &str = "p >= 0 && p <= 1000000000";

fn int(evaluated: u64) -> (String, u64) {
    ("(p: int) -> int".to_string(), evaluated)
}

fn may_fail(evaluated: u64) -> (String, u64) {
    ("(p: int) -> int | #divByZero".to_string(), evaluated)
}

/// DESIGN's `g` and `h`: the root 4 of `p - 4` breaks `C`, and of the roots 4 and -1 of
/// `p * p - 3 * p - 4` only 4 is in the range; each is evaluated once.
#[test]
fn g_and_h() {
    assert_eq!(g(SMALL, C, "p - 4"), int(1));
    assert_eq!(g(SMALL, C, "p * p - 3 * p - 4"), int(1));
}

/// A cubic with the three roots 4, 5 and 7, each ruled out by `C`, and its contrast with the
/// roots 4, 5 and 10, where `C` holds at 10 and the division may fail. Each root is evaluated
/// once.
#[test]
fn a_cubic_with_three_roots() {
    assert_eq!(g(WIDE, C, "p * p * p - 16 * p * p + 83 * p - 140"), int(3));
    assert_eq!(
        g(WIDE, C, "p * p * p - 19 * p * p + 110 * p - 200"),
        may_fail(3)
    );
}

/// A range of 10^9 members costs what a range of 9 does: one evaluation at the one root.
#[test]
fn a_range_of_a_billion_members_is_evaluated_at_its_roots_alone() {
    assert_eq!(g(WIDE, C, "p - 4"), int(1));
}

/// An equation with no integer root in the range decides the division with no evaluation.
#[test]
fn no_root_decides_with_no_evaluation() {
    assert_eq!(g(WIDE, C, "p * p - 2"), int(0));
}

/// A root at which the constraint holds keeps `#divByZero`: 16 mod 3 is 1.
#[test]
fn a_root_the_constraint_keeps_reaches_the_division() {
    assert_eq!(g(SMALL, "(p * p) mod 3 == 1", "p - 4"), may_fail(1));
}

/// The solutions of a congruence are not listed: `p mod 9 == 4`, though it has more than 10^8
/// solutions in the range, is held by the name's congruence, which decides the root 4 (it
/// holds there) with no evaluation; `p mod 9 == 5` does not hold there. Until
/// PRES-interval-strided-piece the test was evaluated once, at the root 4.
#[test]
fn a_congruence_is_evaluated_at_the_roots_only() {
    assert_eq!(g(WIDE, "p mod 9 == 4", "p - 4"), may_fail(0));
    assert_eq!(g(WIDE, "p mod 9 == 5", "p - 4").0, int(0).0);
}

/// A constraint that gives neither `true` nor `false` at a root cannot rule it out, and the
/// division is rejected, naming the constraint, what it gave, the root and the equation.
#[test]
fn a_constraint_that_fails_at_a_root_is_rejected() {
    let text = format!(
        "g(p: int) = if {SMALL} && 12 div (p - 4) > 0 {{ 10 div (p - 4) }} else {{ 0 }};\n"
    );
    let errors = type_errors(&text);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].starts_with(
            "`10 div (p - 4)` may divide by 0: `12 div (p - 4) > 0` gives `#divByZero` at \
             `p = 4`, a root of `p - 4 == 0`."
        ),
        "{}",
        errors[0]
    );
}

/// A root that another written constraint rules out (gives `false` there) is not reached,
/// whatever a third constraint gives there, so a constraint failing at it is not reported
/// (DESIGN.md sec:diagnostics, the row for a root of an obligation's equation; plan row
/// Q-early-pass-root-failures, applied by PROOFDOC6-author-questions). `C` is false at 4. Each
/// order and each of the constants 12 and 13 is checked: before the fix the constraints were
/// evaluated in the sort order of their terms, so `C` written first with 12 was refused and
/// with 13 accepted. The control: where no constraint rules the root out, the failure is still
/// reported in both orders (`(p * p) mod 3 == 1` holds at 4).
#[test]
fn a_failure_at_a_root_another_constraint_rules_out_is_not_reported_in_either_order() {
    for k in [12, 13] {
        let f = format!("{k} div (p - 4) > 0");
        for (a, b) in [(C, f.as_str()), (f.as_str(), C)] {
            let text = format!(
                "g(p: int) = if {SMALL} && {a} && {b} {{ 10 div (p - 4) }} else {{ 0 }};\n"
            );
            let errors = type_errors(&text);
            assert!(errors.is_empty(), "{text}{errors:#?}");
        }
        let keep = "(p * p) mod 3 == 1";
        for (a, b) in [(keep, f.as_str()), (f.as_str(), keep)] {
            let text = format!(
                "g(p: int) = if {SMALL} && {a} && {b} {{ 10 div (p - 4) }} else {{ 0 }};\n"
            );
            let errors = type_errors(&text);
            assert_eq!(errors.len(), 1, "{text}{errors:#?}");
            assert!(
                errors[0].starts_with(&format!(
                    "`10 div (p - 4)` may divide by 0: `{f}` gives `#divByZero` at `p = 4`"
                )),
                "{}",
                errors[0]
            );
        }
    }
}

/// A failing member of a rooted name stays a member until a constraint gives `false` there, so
/// each constraint written after the failing one is evaluated at the root too: once each, so the
/// evaluations grow linearly in the constraints. `n` constraints
/// `(p * (p + 1) * (p + i)) mod 1013 != 1012` (at 4, `20 * (4 + i) mod 1013`, which is 1012 for
/// no `i` below 64; a cubic like `C`, which no domain decides, where `(p * p + i) mod 97 != 96`
/// was decided with no evaluation) follow `12 div (p - 4) > 0`, which fails at the root 4; the
/// failure is still reported, and the evaluations at n = 8 and 8n = 64 are held to the
/// preferred ratio of a linear count (Part G).
#[test]
fn constraints_after_a_failing_one_are_evaluated_once_each_at_the_root() {
    let run = |n: usize| {
        let mut test = "12 div (p - 4) > 0".to_string();
        for i in 0..n {
            test.push_str(&format!(" && (p * (p + 1) * (p + {i})) mod 1013 != 1012"));
        }
        let text = format!("g(p: int) = if {SMALL} && {test} {{ 10 div (p - 4) }} else {{ 0 }};\n");
        let before = evaluations();
        let errors = type_errors(&text);
        let spent = evaluations() - before;
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(
            errors[0].contains("gives `#divByZero` at `p = 4`"),
            "{}",
            errors[0]
        );
        spent
    };
    let (small, large) = (run(8), run(64));
    scaling::hold_linear(
        "constraints after one failing at a root, 8 and 64",
        "evaluations",
        small,
        large,
    );
}

/// `(x^n + 1)(x - 4)`, expanded: four terms of degree `n + 1`.
fn of_degree(n: u64) -> Sparse {
    let c = |k: i64| BigInt::from(k);
    Sparse::new([(0, c(-4)), (1, c(1)), (n, c(-4)), (n + 1, c(1))])
}

/// `(x - a)(x - b)(x - 5)` with `a = 2^bits + 3` and `b = -(2^bits + 7)`, expanded, and `a`
/// and `b`.
fn of_bits(bits: u64) -> (Sparse, BigInt, BigInt) {
    let a = (BigInt::from(1u8) << bits) + BigInt::from(3);
    let b = -((BigInt::from(1u8) << bits) + BigInt::from(7));
    let c = BigInt::from(5);
    let e2 = -(&a + &b + &c);
    let e1 = &a * &b + &b * &c + &c * &a;
    let e0 = -(&a * &b * &c);
    (
        Sparse::new([(0, e0), (1, e1), (2, e2), (3, BigInt::from(1))]),
        a,
        b,
    )
}

/// `(x - r)(1 + x^2 + x^4 + … + x^(2n - 2))`, expanded: `2n` terms of degree `2n`.
fn of_terms(n: usize, r: &BigInt) -> Sparse {
    let mut terms = Vec::with_capacity(2 * n);
    for i in 0..n as u64 {
        terms.push((2 * i, -r.clone()));
        terms.push((2 * i + 1, BigInt::from(1)));
    }
    Sparse::new(terms)
}

/// The polynomials of the benchmark `roots_scale_in_the_degree_and_in_the_bits`, at small
/// sizes: `(x^n + 1)(x - 4)` has the root 4, and -1 too for odd `n`; the cubic of
/// [`of_bits`] has its three roots.
#[test]
fn the_roots_of_sparse_and_wide_polynomials() {
    for n in [3, 4, 1000, 1001] {
        let expected: Vec<BigInt> = match n % 2 {
            0 => vec![BigInt::from(4)],
            _ => vec![BigInt::from(-1), BigInt::from(4)],
        };
        assert_eq!(
            integer_roots(&of_degree(n), None, None),
            Roots::Listed(expected),
            "degree {n}"
        );
    }
    for bits in [8, 64] {
        let (f, a, b) = of_bits(bits);
        let expected = vec![b, BigInt::from(5), a];
        assert_eq!(
            integer_roots(&f, None, None),
            Roots::Listed(expected),
            "{bits} bits"
        );
    }
}

/// The polynomial of [`of_terms`] of the benchmark `roots_are_linear_in_the_number_of_terms`
/// has its one root, at 4, which the cuts of the interval reach, and at `2^40`, which
/// Newton's method reaches.
#[test]
fn a_polynomial_of_many_terms_has_its_one_root() {
    let large = BigInt::from(1u8) << 40u32;
    for r in [BigInt::from(4), large] {
        for n in [1, 2, 8, 64] {
            assert_eq!(
                integer_roots(&of_terms(n, &r), None, None),
                Roots::Listed(vec![r.clone()]),
                "{n} terms, root {r}"
            );
        }
    }
}

/// The product of `x - r` for each `r` in `rs`, expanded.
fn expanded(rs: &[BigInt]) -> Sparse {
    let mut c = vec![BigInt::from(1)];
    for r in rs {
        let mut next = vec![BigInt::from(0); c.len() + 1];
        for (i, a) in c.iter().enumerate() {
            next[i + 1] += a;
            next[i] -= a * r;
        }
        c = next;
    }
    Sparse::new(c.into_iter().enumerate().map(|(e, a)| (e as u64, a)))
}

/// `x^3 - 3c x^2 + 3(c^2 + 1) x - (c^3 + 3c + 1)` at `c = 2^bits`, that is `(x - c)^3 +
/// 3(x - c) - 1`: increasing (`p' = 3((x - c)^2 + 1)`), its one real root in `c..c + 1`, so no
/// integer root. The branch and bound alone took about `c^(1/2)` intervals on it (plan row
/// ROOTS-interval-bound).
fn of_flat_cubic(bits: u64) -> Sparse {
    let c = BigInt::from(1u8) << bits;
    let c2 = &c * &c;
    Sparse::new([
        (0, -(&c2 * &c + 3 * &c + BigInt::from(1))),
        (1, 3 * (c2 + BigInt::from(1))),
        (2, -3 * &c),
        (3, BigInt::from(1)),
    ])
}

/// The four roots `2^bits..=2^bits + 3`: the branch and bound alone took about `c^(2/3)`
/// intervals on them, for `c = 2^bits` (plan row ROOTS-interval-bound).
fn cluster(bits: u64) -> Vec<BigInt> {
    let c = BigInt::from(1u8) << bits;
    (0..4).map(|i| &c + BigInt::from(i)).collect()
}

/// The families on which the branch and bound's count of intervals is exponential in the
/// bits are answered exactly at 16 to 512 bits, where it alone would take from 2^8 to past
/// 2^256 intervals: the cubic with no integer root, the cluster, and roots at the powers of 2
/// and one past them, where its cuts fall.
#[test]
fn families_that_defeat_the_cuts_have_their_roots() {
    for bits in [16, 64, 512] {
        assert_eq!(
            integer_roots(&of_flat_cubic(bits), None, None),
            Roots::Listed(vec![]),
            "the cubic at {bits} bits"
        );
        let rs = cluster(bits);
        assert_eq!(
            integer_roots(&expanded(&rs), None, None),
            Roots::Listed(rs),
            "the cluster at {bits} bits"
        );
    }
    for m in [8u32, 40] {
        let at: Vec<BigInt> = (1..=m).map(|j| BigInt::from(1u8) << j).collect();
        let past: Vec<BigInt> = at.iter().map(|x| x + BigInt::from(1)).collect();
        for rs in [at, past] {
            assert_eq!(
                integer_roots(&expanded(&rs), None, None),
                Roots::Listed(rs.clone()),
                "roots {rs:?}"
            );
        }
    }
}

mod bench;
