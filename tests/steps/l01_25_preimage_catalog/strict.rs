//! Strict tonicity (plan row TONIC-strict; DESIGN.md sec:property_tracking, "strict
//! tonicity"): the grade ↑s, ↑, `const`, ↓ or ↓s of a term in its binder `x`, each claim
//! checked by running the term. The oracle evaluates the term at increasing values of `x`, the
//! other input fixed, and requires the claimed order between every two results that evaluate;
//! a strict claim also requires every value to evaluate (the grade says the term is total in
//! `x`) or none to. At `rat` the values include ones near 0 (±1/1000, ±1/1000000), where a
//! product's sign rule would break first; at a `@checked` type an operation fails outside
//! `i8`. `bench/strict.rs` measures the grading at `n` and `8n`.

use std::cmp::Ordering;
use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::num::Rat;
use zed_kernel::{Prim, Shared, Term, Value, eval};
use zed_tests::instances::Rng;
use zedc::axioms::Tonicity::{self, Const, Down, StrictDown, StrictUp, Up};
use zedc::store::grade::{Arith, grade};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::Domains;

use super::{function, run_seed};

/// A domain written `(lo, hi)`, `None` an infinite end.
type Dom = (Option<i64>, Option<i64>);

const ALL: Dom = (None, None);
const NONNEG: Dom = (Some(0), None);
const NONPOS: Dom = (None, Some(0));

fn set((lo, hi): Dom) -> IntervalSet {
    IntervalSet::range(
        lo.map_or(End::NegInf, End::of),
        hi.map_or(End::PosInf, End::of),
    )
}

fn domains(x: Dom, y: Dom) -> Domains {
    [("x", x), ("y", y)]
        .into_iter()
        .map(|(n, d)| (Arc::<str>::from(n), set(d)))
        .collect()
}

/// The grade of the function `ok` of `src` in `x`, with `x` in `x` and `y` in `y`.
fn graded(src: &str, x: Dom, y: Dom, arith: Arith) -> Option<Tonicity> {
    let (_, body) = function(src);
    grade(&body, "x", &domains(x, y), arith)
}

fn rat(n: i64, d: i64) -> Rat {
    Rat::new(BigInt::from(n), BigInt::from(d)).expect("a nonzero denominator")
}

fn as_rat(v: &Value) -> Option<Rat> {
    match v {
        Value::Int(n) => Some(Rat::int(BigInt::from(*n))),
        Value::Big(r) | Value::Rat(r) => Some((**r).clone()),
        _ => None,
    }
}

fn cmp(a: &Rat, b: &Rat) -> Ordering {
    a.try_cmp(b).expect("small numbers compare")
}

/// Whether `v` lies in the domain `(lo, hi)`, its ends read as numbers.
fn inside(v: &Rat, (lo, hi): Dom) -> bool {
    let at_least = |e: i64| cmp(v, &Rat::int(BigInt::from(e))) != Ordering::Less;
    let at_most = |e: i64| cmp(v, &Rat::int(BigInt::from(e))) != Ordering::Greater;
    lo.is_none_or(at_least) && hi.is_none_or(at_most)
}

/// `body` with each name bound to its value.
fn bind(body: &Term, env: &[(&str, Value)]) -> Term {
    env.iter().rev().fold(body.clone(), |t, (n, v)| {
        Term::Let(
            (*n).into(),
            Shared::new(Term::Lit(v.clone())),
            Shared::new(t),
        )
    })
}

/// The values of `x` the oracle tries: the integers `-w..=w` at `int`, and at `rat` those and
/// values near 0, in increasing order, each within `d`.
fn xs(arith: Arith, d: Dom, w: i64) -> Vec<Rat> {
    let mut out: Vec<Rat> = (-w..=w).map(|n| rat(n, 1)).collect();
    if arith == Arith::Rat {
        for (n, den) in [(1, 2), (1, 1000), (1, 1_000_000), (7, 3)] {
            out.push(rat(n, den));
            out.push(rat(-n, den));
        }
        out.sort_by(cmp);
    }
    out.retain(|v| inside(v, d));
    out
}

fn value(arith: Arith, v: &Rat) -> Value {
    match arith {
        Arith::Rat => Value::rat(v.clone()),
        _ => as_rat_int(v),
    }
}

fn as_rat_int(v: &Rat) -> Value {
    let n = v.to_integer().expect("an integer value");
    Value::Int(i64::try_from(n).expect("a small integer"))
}

/// The value of `t` under `env`, or `None` when it fails; at [`Arith::Checked`] it fails
/// when the value of any operation in it lies outside `i8`, as a checked `i8` operation does.
fn run(t: &Term, env: &[(&str, Value)], arith: Arith) -> Option<Rat> {
    if arith == Arith::Checked
        && let Term::Prim(_, args) = t
    {
        for a in args {
            if matches!(a, Term::Prim(..)) {
                run(a, env, arith)?;
            }
        }
    }
    let v = as_rat(&eval(&bind(t, env)).ok()?)?;
    let small = |e: i64| Rat::int(BigInt::from(e));
    if arith == Arith::Checked
        && (cmp(&v, &small(-128)) == Ordering::Less || cmp(&v, &small(127)) == Ordering::Greater)
    {
        return None;
    }
    Some(v)
}

/// Whether results `a` at `x` and `b` at a larger `x'` keep the order `g` claims.
fn keeps(g: Tonicity, o: Ordering) -> bool {
    match g {
        StrictUp => o == Ordering::Less,
        Up => o != Ordering::Greater,
        Const => o == Ordering::Equal,
        Down => o != Ordering::Less,
        StrictDown => o == Ordering::Greater,
    }
}

/// Checks the claim `g` of `body` at each value of `x` in `xs`, `y` fixed at each of `ys`:
/// the order between every two results that evaluate, and for a strict claim, which says the
/// term is total, that all evaluate. Returns the number of pairs compared.
fn oracle(body: &Term, g: Tonicity, xs: &[Rat], ys: &[Rat], arith: Arith) -> Result<usize, String> {
    let mut pairs = 0;
    let no_y = [None];
    let ys: Vec<Option<&Rat>> = if ys.is_empty() {
        no_y.to_vec()
    } else {
        ys.iter().map(Some).collect()
    };
    for y in ys {
        let at = |x: &Rat| {
            let mut env = vec![("x", value(arith, x))];
            if let Some(y) = y {
                env.push(("y", value(arith, y)));
            }
            run(body, &env, arith)
        };
        let rs: Vec<Option<Rat>> = xs.iter().map(at).collect();
        let shown = |i: usize| format!("x = {:?}, y = {y:?}: {:?}", xs[i], rs[i]);
        if g.is_strict()
            && let Some(i) = rs.iter().position(Option::is_none)
        {
            return Err(format!(
                "claimed {g:?}, which is total, but fails at {}",
                shown(i)
            ));
        }
        for i in 0..rs.len() {
            for j in i + 1..rs.len() {
                if let (Some(a), Some(b)) = (&rs[i], &rs[j]) {
                    pairs += 1;
                    if !keeps(g, cmp(a, b)) {
                        return Err(format!("claimed {g:?}: {} then {}", shown(i), shown(j)));
                    }
                }
            }
        }
    }
    Ok(pairs)
}

/// The integers of the domain `d` within `-w..=w`, up to three of them, as values of `y`; when
/// the window holds none, `d`'s integer nearest 0; none when `d` is empty.
fn some_ys(arith: Arith, d: Dom, w: i64) -> Vec<Rat> {
    let mut all = xs(arith, d, w);
    if all.is_empty() {
        let (lo, hi) = (d.0.unwrap_or(i64::MIN), d.1.unwrap_or(i64::MAX));
        if lo <= hi {
            all.push(rat(0.clamp(lo, hi), 1));
        }
    }
    let pick = [0, all.len() / 2, all.len().saturating_sub(1)];
    let mut out: Vec<Rat> = pick.iter().filter_map(|&i| all.get(i).cloned()).collect();
    out.dedup_by(|a, b| cmp(a, b) == Ordering::Equal);
    out
}

/// Asserts the grade of `src` and checks it against the oracle.
fn case(src: &str, x: Dom, y: Dom, arith: Arith, want: Option<Tonicity>) {
    let got = graded(src, x, y, arith);
    assert_eq!(got, want, "{src} with x in {x:?}, y in {y:?} at {arith:?}");
    if let Some(g) = got {
        let (_, body) = function(src);
        let ys = if src.contains("y:") {
            some_ys(arith, y, 6)
        } else {
            vec![]
        };
        oracle(&body, g, &xs(arith, x, 12), &ys, arith)
            .unwrap_or_else(|e| panic!("{src} with x in {x:?}, y in {y:?}: {e}"));
    }
}

fn int(src: &str, x: Dom, want: Option<Tonicity>) {
    case(&format!("ok(x: int) = {src};"), x, ALL, Arith::Int, want);
}

#[test]
fn design_examples_at_int() {
    // DESIGN.md sec:property_tracking and the row's tests.
    int("3 * x + x div 2", ALL, Some(StrictUp));
    int("x * x", NONNEG, Some(StrictUp));
    int("x * x", NONPOS, Some(StrictDown));
    int("x * x", ALL, None);
    int("x ^ 3", ALL, Some(StrictUp));
    int("x * x * x", ALL, None);
    int("x * x * x", NONNEG, Some(StrictUp));
    int("-(x ^ 3) + 7", ALL, Some(StrictDown));
    int("x div 2", ALL, Some(Up));
    int("min(x, 50)", ALL, Some(Up));
    int("x mod 3", ALL, None);
    // Sums, differences and the other rules.
    int("x + 1", ALL, Some(StrictUp));
    int("2 * x", ALL, Some(StrictUp));
    int("7 - 2 * x", ALL, Some(StrictDown));
    int("x - x", ALL, None);
    int("x + x div 2", ALL, Some(StrictUp));
    int("x div 2 + x div 3", ALL, Some(Up));
    int("max(2 * x, x + 1)", ALL, Some(StrictUp));
    int("min(x, x div 2)", ALL, Some(Up));
    int("min(x, -x)", ALL, None);
    int("x ^ 2", NONNEG, Some(StrictUp));
    int("x ^ 2", NONPOS, Some(StrictDown));
    int("x ^ 2", ALL, None);
    int("(x - 3) * (x - 3)", (Some(3), None), Some(StrictUp));
    int("(x - 3) * (x - 3)", (Some(2), None), None);
    int("(x + 1) * x", NONNEG, Some(StrictUp));
    int("-(x ^ 4)", NONNEG, Some(StrictDown));
    int("x div -2", ALL, Some(Down));
    int("(x ^ 3) ^ 3", ALL, Some(StrictUp));
    int("x ^ 3 * 5 + x", ALL, Some(StrictUp));
    int("abs(x)", ALL, None);
}

#[test]
fn corner_cases() {
    // An empty domain: every claim holds at no pair; the rules still give the sign rule's.
    int("x * x", (Some(5), Some(4)), Some(StrictUp));
    // One point.
    int("x * x", (Some(5), Some(5)), Some(StrictUp));
    int("x * x", (Some(0), Some(0)), Some(StrictUp));
    // `x * c` at c == 0 is constant; c touching 0 from one side weakens; both signs none.
    int("x * 0", ALL, Some(Const));
    let y = |src: &str, d: Dom, want| {
        case(
            &format!("ok(x: int, y: int) = {src};"),
            ALL,
            d,
            Arith::Int,
            want,
        )
    };
    y("x * y", (Some(0), Some(0)), Some(Const));
    y("x * y", (Some(0), Some(4)), Some(Up));
    y("x * y", (Some(-4), Some(0)), Some(Down));
    y("x * y", (Some(1), Some(4)), Some(StrictUp));
    y("x * y", (Some(-4), Some(-1)), Some(StrictDown));
    y("x * y", (Some(-1), Some(1)), None);
    y("x + y * y", (Some(-1), Some(1)), Some(StrictUp));
    // `x ^ 0` is 1 at every x, 0 included.
    int("x ^ 0", ALL, Some(Const));
    int("x + x ^ 0", ALL, Some(StrictUp));
    // `x div -1` is `-x`, but the rule weakens every division.
    int("x div -1", ALL, Some(Down));
    // A divisor that may be 0 fails there, so a strict sum is weakened: total no longer.
    y("x div y", (Some(0), Some(3)), Some(Up));
    y("x + x div y", (Some(0), Some(3)), Some(Up));
    y("x + x div y", (Some(1), Some(3)), Some(StrictUp));
    y("x div y", (Some(-3), Some(3)), None);
    y("x div y", (Some(-3), Some(-1)), Some(Down));
    // A divisor that depends on x has no rule. A constant one that may be 0 makes a constant
    // that may fail, at every x when it does, so the sum is total no longer.
    int("x div x", NONNEG, None);
    y("x + 5 mod y", (Some(0), Some(3)), Some(Up));
    y("x + 5 mod y", (Some(1), Some(3)), Some(StrictUp));
    y("x + x mod y", (Some(1), Some(3)), None);
    // A negative power is no int (the elaborator rejects `x ^ -1` at int; the term is built).
    let inverse = Term::Prim(
        Prim::Pow,
        vec![Term::Var("x".into()), Term::Lit(Value::Int(-1))],
    );
    assert_eq!(grade(&inverse, "x", &domains(ALL, ALL), Arith::Int), None);
    // `y` is constant in x, whatever it is.
    y("y", ALL, Some(Const));
    y("y ^ 2 - y", ALL, Some(Const));
    // A function with no rule may fail, so it keeps the sum from being strict.
    y("x + abs(y)", ALL, Some(Up));
    y("x - y", ALL, Some(StrictUp));
    y("y - x", ALL, Some(StrictDown));
}

/// The grader keeps a range's ends as `f64`s rounded outward: exact below 2^53, and past it a
/// rounded end may cover 0, so a rule gives no grade, never a wrong one. Each claim is run at
/// `x` from `from` to `from + 24`.
#[test]
fn ends_past_two_to_the_53() {
    let at = |src: &str, from: i64, want: Option<Tonicity>| {
        let src = format!("ok(x: int) = {src};");
        let d = (Some(from), None);
        let got = graded(&src, d, ALL, Arith::Int);
        assert_eq!(got, want, "{src} with x >= {from}");
        if let Some(g) = got {
            let (_, body) = function(&src);
            let xs: Vec<Rat> = (from..=from + 24).map(|v| rat(v, 1)).collect();
            oracle(&body, g, &xs, &[], Arith::Int).unwrap_or_else(|e| panic!("{src}: {e}"));
        }
    };
    let two53 = 1_i64 << 53;
    // Exact: 2^53 - 10 is an f64, and x - c lies at or above 13.
    at(
        "(x - 9007199254740982) * (x - 9007199254740982)",
        two53 + 3,
        Some(StrictUp),
    );
    // 2^53 + 3 is no f64: both it and the literal round to a range [2^53 + 2, 2^53 + 4], so
    // x - c may be -2 and the square has no grade, though it is ↑s.
    at(
        "(x - 9007199254740995) * (x - 9007199254740995)",
        two53 + 3,
        None,
    );
    // Below 2^53 the same term is exact.
    at("(x - 1000003) * (x - 1000003)", 1_000_003, Some(StrictUp));
    // Past i64: a literal of 2^70 reads as at least 2^63.
    at("x * 1180591620717411303424 + 1", 0, Some(StrictUp));
    at("x * -1180591620717411303424", -12, Some(StrictDown));
    at("x * x * 1180591620717411303424", 0, Some(StrictUp));
    // An end past i64 in a domain.
    let big = |lo: &str| {
        let lo: num_bigint::BigInt = lo.parse().expect("a number");
        let mut ds = domains(ALL, ALL);
        ds.insert(
            "y".into(),
            IntervalSet::range(End::Fin(zedc::store::interval::Num::from(&lo)), End::PosInf),
        );
        ds
    };
    let (_, body) = function("ok(x: int, y: int) = x * y;");
    let pos = big("1180591620717411303424");
    assert_eq!(grade(&body, "x", &pos, Arith::Int), Some(StrictUp));
    let neg = big("-1180591620717411303424");
    assert_eq!(grade(&body, "x", &neg, Arith::Int), None);
}

fn rat_case(src: &str, x: Dom, want: Option<Tonicity>) {
    case(&format!("ok(x: rat) = {src};"), x, ALL, Arith::Rat, want);
}

#[test]
fn rules_at_rat_near_zero() {
    rat_case("x * 0.001r", ALL, Some(StrictUp));
    rat_case("x * -0.001r", ALL, Some(StrictDown));
    rat_case("x * (1r / 1000r)", ALL, Some(StrictUp));
    rat_case("x * (-1r / 1000000r)", ALL, Some(StrictDown));
    rat_case("x * 0r", ALL, Some(Const));
    rat_case("x + 0.001r", ALL, Some(StrictUp));
    rat_case("x * x", NONNEG, Some(StrictUp));
    rat_case("x * x", NONPOS, Some(StrictDown));
    rat_case("x * x", ALL, None);
    rat_case("x * x * x", ALL, None);
    rat_case("x * x * x", NONNEG, Some(StrictUp));
    rat_case("x ^ 3", ALL, Some(StrictUp));
    rat_case("x ^ 2", NONNEG, Some(StrictUp));
    rat_case("x ^ 2", ALL, None);
    rat_case("-(x ^ 3) + 7r", ALL, Some(StrictDown));
    rat_case("(x + 0.001r) * (x + 0.001r)", NONNEG, Some(StrictUp));
    rat_case("(x - 0.001r) * (x - 0.001r)", NONNEG, None);
    rat_case("(x + 0.001r) * x", NONNEG, Some(StrictUp));
    rat_case("min(x * 0.001r, x)", ALL, Some(StrictUp));
    rat_case("max(x, 0r)", ALL, Some(Up));
    // DESIGN's power rule is for n >= 1: no grade below, and `0r ^ -1` fails.
    rat_case("x ^ -1", NONNEG, None);
    rat_case("x ^ -2", ALL, None);
    rat_case("x ^ 0", ALL, Some(Const));
    // The rat `/` has no rule; by a constant it is constant.
    rat_case("1r / x", (Some(1), None), None);
    rat_case("x + 1r / 3r", ALL, Some(StrictUp));
    let y = |src: &str, d: Dom, want| {
        case(
            &format!("ok(x: rat, y: rat) = {src};"),
            ALL,
            d,
            Arith::Rat,
            want,
        )
    };
    y("x * y", (Some(0), None), Some(Up));
    y("x * y", (Some(1), None), Some(StrictUp));
    y("x * y", (Some(-1), Some(1)), None);
    // `1r / y` fails at y = 0, at every x, so the sum is total only where y keeps off 0.
    y("x + 1r / y", ALL, Some(Up));
    y("x + 1r / y", (Some(1), None), Some(StrictUp));
    y("x + 1r / y", (None, Some(-1)), Some(StrictUp));
}

#[test]
fn nothing_is_strict_at_a_float() {
    let f = |src: &str, want| {
        let src = format!("ok(x: f64) = {src};");
        assert_eq!(graded(&src, ALL, ALL, Arith::Float), want, "{src}");
    };
    f("x + 1.0", Some(Up));
    f("x - 1.0", Some(Up));
    f("1.0 - x", Some(Down));
    f("x * -2.0", Some(Down));
    f("-x", Some(Down));
    f("min(x, 1.0)", Some(Up));
    f("max(x * 3.0 + 1.0, -1.0)", Some(Up));
    f("x", Some(Up));
    f("2.5", Some(Const));
    // `0 * inf` is NaN; a constant that is not a literal may be NaN; `x * x` has no rule.
    f("x * 0.0", None);
    f("x + (1.0e308 * 10.0 - 1.0e308 * 10.0)", None);
    f("x * x", None);
    f("x / 2.0", None);
    let src = "ok(x: f64, y: f64) = x + y;";
    assert_eq!(graded(src, ALL, ALL, Arith::Float), None, "{src}");
    let src = "ok(x: f32) = x * 2.0;";
    assert_eq!(graded(src, ALL, ALL, Arith::Float), Some(Up), "{src}");
    // The claims, run at values from -inf to inf, both zeros in turn (they compare equal, so
    // they are never a pair x < x').
    for (src, g) in [
        ("x + 1.0", Up),
        ("x * -2.0", Down),
        ("max(x * 3.0 + 1.0, -1.0)", Up),
        ("1.0e16 - x", Down),
    ] {
        let (_, body) = function(&format!("ok(x: f64) = {src};"));
        for zero in [-0.0, 0.0] {
            let xs = [
                f64::NEG_INFINITY,
                -1.0e308,
                -1.0e16,
                -1.0,
                -1.0e-300,
                zero,
                1.0e-300,
                1.0,
                1.0e16,
                1.0e16 + 2.0,
                1.0e308,
                f64::INFINITY,
            ];
            let rs: Vec<f64> = xs
                .iter()
                .map(|&x| match eval(&bind(&body, &[("x", Value::float(x))])) {
                    Ok(Value::Float(v)) => v.get(),
                    other => panic!("{src} at {x}: {other:?}"),
                })
                .collect();
            for i in 0..rs.len() {
                for j in i + 1..rs.len() {
                    let o = rs[i].partial_cmp(&rs[j]);
                    assert!(
                        o.is_some_and(|o| keeps(g, o)),
                        "{src}: {} at {}, {} at {}",
                        rs[i],
                        xs[i],
                        rs[j],
                        xs[j]
                    );
                }
            }
        }
    }
    // Strictness fails at a float: `x + 1.0` is equal at two values.
    assert_eq!(1.0e16_f64 + 1.0, 1.0e16_f64);
}

#[test]
fn nothing_is_strict_at_a_checked_type() {
    for (src, x, want) in [
        ("3 * x + x div 2", ALL, Up),
        ("x ^ 3", ALL, Up),
        ("-(x ^ 3) + 7", ALL, Down),
        ("x * x", NONNEG, Up),
        ("x + 1", ALL, Up),
        ("x div 2", ALL, Up),
    ] {
        let src = format!("ok(x: int) = {src};");
        assert_eq!(graded(&src, x, ALL, Arith::Checked), Some(want), "{src}");
        let (_, body) = function(&src);
        oracle(&body, want, &xs(Arith::Checked, x, 12), &[], Arith::Checked)
            .unwrap_or_else(|e| panic!("{src}: {e}"));
    }
}

/// A random term of depth at most `d` over `x` and `y` in `arith`.
fn random_term(rng: &mut Rng, arith: Arith, d: u32) -> Term {
    let var = |n: &str| Term::Var(n.into());
    let lit = |rng: &mut Rng| match arith {
        Arith::Rat => {
            let den = rng.pick(&[1, 2, 1000]);
            Term::Lit(Value::rat(rat(rng.int(-3, 3), den)))
        }
        _ => Term::Lit(Value::Int(rng.int(-3, 3))),
    };
    if d == 0 || rng.below(5) == 0 {
        return match rng.below(4) {
            0 | 1 => var("x"),
            2 => var("y"),
            _ => lit(rng),
        };
    }
    let sub = |rng: &mut Rng| random_term(rng, arith, d - 1);
    let two = |rng: &mut Rng, p: Prim| Term::Prim(p, vec![sub(rng), sub(rng)]);
    let small = |rng: &mut Rng| match rng.below(3) {
        0 => var("y"),
        _ => lit(rng),
    };
    match rng.below(10) {
        0 | 1 => two(rng, Prim::Add),
        2 => two(rng, Prim::Sub),
        3 => Term::Prim(Prim::Neg, vec![sub(rng)]),
        4 | 5 => two(rng, Prim::Mul),
        6 => {
            let lo = if arith == Arith::Rat { -2 } else { 0 };
            let n = Term::Lit(Value::Int(rng.int(lo, 3)));
            Term::Prim(Prim::Pow, vec![sub(rng), n])
        }
        7 => {
            let p = if rng.below(2) == 0 {
                Prim::Min
            } else {
                Prim::Max
            };
            two(rng, p)
        }
        _ => {
            // A division by a constant, mostly, or by anything.
            let by = if rng.below(4) == 0 {
                sub(rng)
            } else {
                small(rng)
            };
            let p = match (arith, rng.below(2)) {
                (Arith::Rat, _) => Prim::Div,
                (_, 0) => Prim::IntDiv,
                _ => Prim::Mod,
            };
            Term::Prim(p, vec![sub(rng), by])
        }
    }
}

fn random_dom(rng: &mut Rng) -> Dom {
    let lo = rng.int(-6, 4);
    let hi = lo + rng.int(-1, 8);
    match rng.below(6) {
        0 | 1 => (Some(lo), Some(hi)),
        2 => (Some(lo), None),
        3 => (None, Some(hi)),
        4 => (Some(rng.int(0, 2)), None),
        _ => ALL,
    }
}

#[test]
fn random_terms_against_running_them() {
    let mut rng = Rng::new(run_seed("strict::random_terms_against_running_them"));
    for (arith, cases) in [(Arith::Int, 1500), (Arith::Rat, 800), (Arith::Checked, 300)] {
        let mut counts = std::collections::BTreeMap::new();
        let mut pairs = 0;
        for _ in 0..cases {
            let t = random_term(&mut rng, arith, 4);
            let (x, y) = (random_dom(&mut rng), random_dom(&mut rng));
            let g = grade(&t, "x", &domains(x, y), arith);
            *counts.entry(format!("{g:?}")).or_insert(0) += 1;
            let Some(g) = g else { continue };
            if arith == Arith::Checked {
                assert!(!g.is_strict(), "{t} is {g:?} at a checked type");
            }
            let ys = some_ys(arith, y, 5);
            if ys.is_empty() {
                // `y`'s domain is empty: no run binds it, and every claim holds at no point.
                continue;
            }
            let w = if arith == Arith::Rat { 4 } else { 8 };
            pairs += oracle(&t, g, &xs(arith, x, w), &ys, arith)
                .unwrap_or_else(|e| panic!("{t} with x in {x:?}, y in {y:?} at {arith:?}: {e}"));
        }
        println!("{arith:?}: {counts:?}, {pairs} pairs compared");
        // The test reaches every grade.
        for g in [StrictUp, Up, Const, Down, StrictDown] {
            let want = if arith == Arith::Checked && g.is_strict() {
                0
            } else {
                1
            };
            let n = counts.get(&format!("{:?}", Some(g))).copied().unwrap_or(0);
            assert!(n >= want, "{arith:?}: {g:?} {n} times: {counts:?}");
        }
    }
}

/// A chain of `n` stages, `x + 1`, `2 * …`, `… - 3`, …, its constants 1 to 5: deep enough
/// at the bench sizes (`bench/strict.rs`) to overflow a recursive walk.
pub(crate) fn chain(n: usize) -> Term {
    let mut t = Term::Var("x".into());
    for i in 0..n {
        let c = Term::Lit(Value::Int(i as i64 % 5 + 1));
        t = match i % 3 {
            0 => Term::Prim(Prim::Add, vec![t, c]),
            1 => Term::Prim(Prim::Mul, vec![c, t]),
            _ => Term::Prim(Prim::Sub, vec![t, c]),
        };
    }
    t
}

/// `x1 = x + x; x2 = x1 + x1; …; xk`: each name read twice, so a walk that substitutes takes
/// time 2^k.
pub(crate) fn doubling(k: usize) -> Term {
    let name = |i: usize| -> Arc<str> {
        if i == 0 {
            "x".into()
        } else {
            format!("x{i}").into()
        }
    };
    let mut body = Term::Var(name(k));
    for i in (1..=k).rev() {
        let e = Term::Prim(
            Prim::Add,
            vec![Term::Var(name(i - 1)), Term::Var(name(i - 1))],
        );
        body = Term::Let(name(i), Shared::new(e), Shared::new(body));
    }
    body
}

#[test]
fn deep_and_shared_terms() {
    let ds = domains(NONNEG, ALL);
    assert_eq!(grade(&chain(30), "x", &ds, Arith::Int), Some(StrictUp));
    assert_eq!(grade(&doubling(200), "x", &ds, Arith::Int), Some(StrictUp));
    let all = domains(ALL, ALL);
    assert_eq!(grade(&chain(30), "x", &all, Arith::Int), Some(StrictUp));
    assert_eq!(grade(&chain(30), "x", &all, Arith::Checked), Some(Up));
    // The binder shadowed by a `let`: the inner `x` is a constant.
    let shadow = Term::Let(
        "x".into(),
        Shared::new(Term::Lit(Value::Int(4))),
        Shared::new(Term::Prim(
            Prim::Add,
            vec![Term::Var("x".into()), Term::Var("x".into())],
        )),
    );
    assert_eq!(grade(&shadow, "x", &ds, Arith::Int), Some(Const));
    // A bound value that may fail, though unread, weakens a strict body.
    let unread = Term::Let(
        "z".into(),
        Shared::new(Term::Prim(
            Prim::Pow,
            vec![Term::Var("x".into()), Term::Lit(Value::Int(-1))],
        )),
        Shared::new(Term::Var("x".into())),
    );
    assert_eq!(grade(&unread, "x", &ds, Arith::Int), Some(Up));
    // An unknown name and a call of a lambda have no grade.
    assert_eq!(grade(&Term::Var("q".into()), "x", &ds, Arith::Int), None);
}
