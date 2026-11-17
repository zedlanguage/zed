//! Grades at range ends near and past 2^53, 2^63 and larger (plan row TONIC-big-ends). The
//! grader keeps a range's ends as `f64`s, rounded outward where they are not `f64`s
//! (`crates/zedc-lattice/src/grade.rs`, `Bounds`). Each case grades `x * (T)` in `x`, with
//! `y` in a range `[lo, hi]` and `T` a sum, product, `div` or `^` in `y`, so the grade is the
//! sign rule's on `T`'s values. The exact grade comes from running `T` in the kernel at the
//! range's ends (and at 0 when the range holds it; each `T` is monotone on each side of 0),
//! and the test asserts:
//! - soundness: the exact grade implies the grader's (`const` implies ↑ and ↓, a strict grade
//!   its weak one, and every grade implies none);
//! - the grader's grade, pinned, with a note where rounding weakens it;
//! - the claimed order of `x * T` at `x` from -3 to 3, `y` at each of those points.
//!
//! The cases where `T`'s value is a few units from a rounded `f64` make a wrongly rounded end
//! claim a grade the exact check refutes (checked with negative controls, 2026-11-17, each
//! failing the soundness assertion: no outward rounding in `lower` and `upper` fails
//! `y - (2^53 + 4)`, `3 y - 2^53` and `y div 3 - c` at `y = 2^62`; no outward rounding of an
//! `i64` quotient fails that last one; none of a power fails `y ^ 2 - 9007199515875288` at
//! `y = 94906267`). The `Bounds` operations are also checked one by one against exact
//! integer arithmetic in `grade.rs`'s unit tests.

use std::cmp::Ordering;

use num_bigint::BigInt;
use zed_kernel::num::Rat;
use zed_kernel::{Shared, Term, Value, eval};
use zedc::axioms::Tonicity::{self, Const, Down, StrictDown, StrictUp, Up};
use zedc::store::grade::{Arith, grade};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::preimage::Domains;

use super::function;

const P52: &str = "4503599627370496";
const P53: &str = "9007199254740992";
const P62: &str = "4611686018427387904";
const P70: &str = "1180591620717411303424";

fn big(s: &str) -> BigInt {
    s.parse().expect("a number")
}

fn plus(s: &str, d: i64) -> String {
    (big(s) + d).to_string()
}

fn neg(s: &str) -> String {
    (-big(s)).to_string()
}

fn as_rat(v: &Value) -> Rat {
    match v {
        Value::Int(n) => Rat::int(BigInt::from(*n)),
        Value::Big(r) | Value::Rat(r) => (**r).clone(),
        other => panic!("not a number: {other:?}"),
    }
}

fn cmp(a: &Rat, b: &Rat) -> Ordering {
    a.try_cmp(b).expect("integers compare")
}

/// The value of `body` at `x` and `y`.
fn run(body: &Term, x: i64, y: &BigInt) -> Rat {
    let env = [("x", Value::Int(x)), ("y", Value::int(y.clone()))];
    let bound = env.iter().rev().fold(body.clone(), |t, (n, v)| {
        Term::Let(
            (*n).into(),
            Shared::new(Term::Lit(v.clone())),
            Shared::new(t),
        )
    });
    as_rat(&eval(&bound).expect("the term evaluates"))
}

/// The grade of `x * c` over `c` from `min` to `max`.
fn sign_grade(min: &Rat, max: &Rat) -> Option<Tonicity> {
    let zero = Rat::int(BigInt::from(0));
    match (cmp(min, &zero), cmp(max, &zero)) {
        (Ordering::Greater, _) => Some(StrictUp),
        (_, Ordering::Less) => Some(StrictDown),
        (Ordering::Equal, Ordering::Equal) => Some(Const),
        (Ordering::Equal, _) => Some(Up),
        (_, Ordering::Equal) => Some(Down),
        _ => None,
    }
}

/// Whether the grade `exact` implies `got`.
fn implies(exact: Option<Tonicity>, got: Option<Tonicity>) -> bool {
    match (exact, got) {
        (_, None) => true,
        (Some(e), Some(g)) if e == g => true,
        (Some(Const), Some(Up | Down)) => true,
        (Some(StrictUp), Some(Up)) | (Some(StrictDown), Some(Down)) => true,
        _ => false,
    }
}

fn keeps(g: Tonicity, o: Ordering) -> bool {
    match g {
        StrictUp => o == Ordering::Less,
        Up => o != Ordering::Greater,
        Const => o == Ordering::Equal,
        Down => o != Ordering::Less,
        StrictDown => o == Ordering::Greater,
    }
}

/// Grades `x * (term)` with `x` any int and `y` from `lo` to `hi`, and checks it as the module
/// says; `want` is the grader's grade.
fn case(term: &str, lo: &str, hi: &str, want: Option<Tonicity>) {
    let src = format!("ok(x: int, y: int) = x * ({term});");
    let (_, body) = function(&src);
    let (lo, hi) = (big(lo), big(hi));
    let mut ds = Domains::new();
    ds.insert("x".into(), IntervalSet::range(End::NegInf, End::PosInf));
    ds.insert(
        "y".into(),
        IntervalSet::range(End::Fin(Num::from(&lo)), End::Fin(Num::from(&hi))),
    );
    let got = grade(&body, "x", &ds, Arith::Int);
    let zero = BigInt::from(0);
    let mut ys = vec![lo.clone(), hi.clone()];
    if lo < zero && zero < hi {
        ys.push(zero);
    }
    let mut ts: Vec<Rat> = ys.iter().map(|y| run(&body, 1, y)).collect();
    ts.sort_by(cmp);
    let exact = sign_grade(&ts[0], &ts[ts.len() - 1]);
    let what = format!("{src} with y in [{lo}, {hi}]");
    assert!(
        implies(exact, got),
        "{what}: graded {got:?}, but its values give {exact:?}"
    );
    assert_eq!(got, want, "{what} (exactly {exact:?})");
    if let Some(g) = got {
        for y in &ys {
            let rs: Vec<Rat> = (-3..=3).map(|x| run(&body, x, y)).collect();
            for i in 0..rs.len() {
                for j in i + 1..rs.len() {
                    assert!(
                        keeps(g, cmp(&rs[i], &rs[j])),
                        "{what}: claimed {g:?}, at y = {y}: {:?} then {:?}",
                        rs[i],
                        rs[j]
                    );
                }
            }
        }
    }
}

#[test]
fn sums_and_differences() {
    // Below 2^53 every end is exact: 2^52 + 1 was rounded to 2^52 before TONIC-big-ends, so
    // `T` might be -1 and the grade was none.
    case(
        &format!("y - {}", plus(P52, 1)),
        &plus(P52, 1),
        &plus(P52, 5),
        Some(Up),
    );
    case(
        &format!("y + y - {}", plus(P53, -2)),
        &plus(P52, -1),
        &plus(P52, 1),
        Some(Up),
    );
    // 2^53 + 3 is no `f64`; it rounds to 2^53 + 4, the literal, so an end not widened would
    // make `T` at least 0, a claim of ↑ that y = 2^53 + 3 refutes.
    case(
        &format!("y - {}", plus(P53, 4)),
        &plus(P53, 3),
        &plus(P53, 8),
        None,
    );
    // ↑s, but y >= 2^53 + 5 is widened to y >= 2^53 + 2.
    case(
        &format!("y - {}", plus(P53, 4)),
        &plus(P53, 5),
        &plus(P53, 12),
        None,
    );
    // 2^53 + 1 rounds to 2^53: `T` is 1, and widened it is from -1 to 2.
    case(&format!("y + 1 - {P53}"), P53, P53, None);
    // Ends that are `f64`s stay exact past 2^53.
    case(&format!("y - {P62} + 1"), P62, P62, Some(StrictUp));
    // Near and past `i64`: i64::MAX is no `f64`, and a literal past `i64` is read as at
    // least 2^63, so neither difference has a grade, though the first is ↑s and the second ↓s.
    let max = i64::MAX.to_string();
    case(&format!("y - {}", plus(&max, -1)), &max, &max, None);
    case("y - 9223372036854775808", &max, &max, None);
    case(&format!("y - {P70}"), &plus(P70, 1), &plus(P70, 9), None);
    case("y", P70, &plus(P70, 3), Some(StrictUp));
    case("-y", P70, &plus(P70, 3), Some(StrictDown));
    case("y", &neg(P70), &neg(P70), Some(StrictDown));
}

#[test]
fn products() {
    // 3 * 3002399751580331 is 2^53 + 1, which rounds to 2^53: `T` is 1.
    case(
        &format!("y * 3 - {P53}"),
        "3002399751580331",
        "3002399751580331",
        None,
    );
    // 94906265^2 = 9007199136250225 is below 2^53 and exact; 94906266^2 is past it.
    case("y * y - 9007199136250225", "94906265", "94906267", Some(Up));
    // 2^64 is past `i64`, so the literal is read as at least 2^63.
    case(
        "y * y - 18446744073709551616",
        "4294967296",
        "4294967297",
        None,
    );
    case(&format!("y * {P70}"), "1", "2", Some(StrictUp));
    case("y * y", &neg(P70), &neg(P70), Some(StrictUp));
    case(&format!("y * -{P70}"), "1", "2", Some(StrictDown));
}

#[test]
fn quotients() {
    // (2^53 - 2) div 3 = 2^53 div 3 = 3002399751580330; 2^53 is an `f64`, so exact.
    case(
        "y div 3 - 3002399751580330",
        &plus(P53, -2),
        P53,
        Some(Const),
    );
    // (2^53 - 1) div (2^52 - 1) is 2, which the `f64` quotient, rounded to 2, gave as 1 to
    // 2 before TONIC-big-ends.
    case(
        &format!("y div {} - 2", plus(P52, -1)),
        &plus(P53, -1),
        &plus(P53, -1),
        Some(Const),
    );
    // 2^62 div 3 = 1537228672809129301, whose nearest `f64` is 1537228672809129216: `T` is
    // 85, and the rounded quotient is widened a place each way, so no grade.
    case("y div 3 - 1537228672809129216", P62, P62, None);
    case(&format!("y div {P70}"), "1", "5", Some(Const));
    case("y div 3 - 1", "3", P70, Some(Up));
    // Euclidean: -6 div -7 = 1 and 0 div -7 = 0; -1 div 2 = -1.
    case("y div -7", "-6", "0", Some(Up));
    case("y div 2", "-1", "0", Some(Down));
}

#[test]
fn powers() {
    case("y ^ 2 - 9007199136250225", "94906265", "94906267", Some(Up));
    // 94906267^2 = 9007199515875289, past 2^53 and odd, so no `f64`; the literals on each side
    // are. It rounds to 9007199515875288 (ties to even): `T` is 1 and then -1, and the power
    // widened a place each way covers 0 in the first and is at most 0 in the second.
    case("y ^ 2 - 9007199515875288", "94906267", "94906267", None);
    case(
        "y ^ 2 - 9007199515875290",
        "94906267",
        "94906267",
        Some(Down),
    );
    // (2^21)^3 = 2^63 > i64::MAX, which is no `f64`.
    case("y ^ 3 - 9223372036854775807", "2097152", "2097153", None);
    case("y ^ 64", "2", "3", Some(StrictUp));
    case("y ^ 2 - 1", "-3", "5", None);
    case("y ^ 2 - 1", "1", "5", Some(Up));
    case("-(y ^ 2)", &neg(P70), &neg(P70), Some(StrictDown));
    case(
        "y ^ 3",
        "-1267650600228229401496703205376",
        "-1267650600228229401496703205376",
        Some(StrictDown),
    );
}
