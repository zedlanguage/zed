//! `min` and `max` on floats are IEEE 754-2019 `minimum` and `maximum` (DESIGN.md
//! sec:reduction, item 5) in the kernel and inline in native code: a NaN in either position
//! gives the NaN, `min(-0.0, 0.0)` is `-0.0` in both orders and `max` of the two zeros `0.0`,
//! and `clamp(x, lo, hi)`, written `max(lo, min(x, hi))`, follows. Every pair and triple of the
//! corner values, in every order, gives the kernel's value bit for bit, at both of Cranelift's
//! optimization levels, with no kernel call.

use zed_kernel::term::build::{app, lam, let_, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};

use super::{float, kernel, planned};

/// The corner values: the NaN, both zeros, both infinities and a number of each sign.
const CORNERS: [f64; 7] = [
    f64::NAN,
    -0.0,
    0.0,
    f64::INFINITY,
    f64::NEG_INFINITY,
    1.0,
    -1.0,
];

/// `t` run natively at `level`; its value and the count of its kernel calls.
fn at(level: OptLevel, t: &Term) -> (Value, u64) {
    let (g, p) = planned(t);
    let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{t:?}: {e}"));
    (o.value, o.kernel_calls)
}

/// The bits of a float value.
fn bits(v: &Value) -> u64 {
    match v {
        Value::Float(x) => x.get().to_bits(),
        other => panic!("{other} is no float"),
    }
}

/// `clamp(x, lo, hi)` as DESIGN.md writes it, on terms.
fn clamp(x: Term, lo: Term, hi: Term) -> Term {
    prim(Prim::Max, vec![lo, prim(Prim::Min, vec![x, hi])])
}

/// The value of `t` by the kernel and natively at both levels, all three the same bits, and no
/// kernel call in native code.
fn agreed(t: &Term) -> Value {
    let want = kernel(t).unwrap_or_else(|e| panic!("{t:?}: {e}"));
    for level in [OptLevel::None, OptLevel::Speed] {
        let (got, calls) = at(level, t);
        assert_eq!(bits(&got), bits(&want), "{t:?} at {level:?}");
        assert_eq!(calls, 0, "{t:?} at {level:?}");
    }
    want
}

/// `body` on literals, and on the parameters of a function applied to them, so no constant of
/// the term decides the result before the code runs.
fn both_forms(body: impl Fn(Vec<Term>) -> Term, args: &[f64]) -> [Term; 2] {
    let names = ["a", "b", "c"];
    let params: Vec<Term> = names[..args.len()].iter().map(|n| var(n)).collect();
    let lits: Vec<Term> = args.iter().map(|&x| float(x)).collect();
    [
        body(lits.clone()),
        app(lam(&names[..args.len()], body(params)), lits),
    ]
}

#[test]
fn every_pair_of_corner_values_in_both_orders_agrees() {
    let mut n = 0;
    for op in [Prim::Min, Prim::Max] {
        for x in CORNERS {
            for y in CORNERS {
                for t in both_forms(|xs| prim(op, xs), &[x, y]) {
                    let v = agreed(&t);
                    // The result is one of the operands, the NaN if either is one.
                    let b = bits(&v);
                    if x.is_nan() || y.is_nan() {
                        assert_eq!(b, f64::NAN.to_bits(), "{op:?}({x}, {y})");
                    } else {
                        assert!(b == x.to_bits() || b == y.to_bits(), "{op:?}({x}, {y})");
                    }
                    n += 1;
                }
            }
        }
    }
    assert_eq!(n, 2 * 49 * 2);
}

/// The cases DESIGN.md names, each in both orders, against the values written out.
#[test]
fn the_named_cases_give_the_ieee_values() {
    let (nan, inf) = (f64::NAN, f64::INFINITY);
    let cases = [
        (Prim::Min, -0.0, 0.0, -0.0),
        (Prim::Max, -0.0, 0.0, 0.0),
        (Prim::Min, nan, 1.0, nan),
        (Prim::Max, nan, 1.0, nan),
        (Prim::Min, nan, -inf, nan),
        (Prim::Max, nan, inf, nan),
        (Prim::Min, inf, -0.0, -0.0),
        (Prim::Max, -inf, -0.0, -0.0),
        (Prim::Min, -inf, 1.0, -inf),
        (Prim::Max, inf, -1.0, inf),
        (Prim::Min, 1.0, -1.0, -1.0),
        (Prim::Max, 1.0, -1.0, 1.0),
    ];
    for (op, x, y, want) in cases {
        for (a, b) in [(x, y), (y, x)] {
            for t in both_forms(|xs| prim(op, xs), &[a, b]) {
                assert_eq!(
                    bits(&agreed(&t)),
                    want.to_bits(),
                    "{op:?}({a}, {b}) is {want}"
                );
            }
        }
    }
}

#[test]
fn clamp_on_every_triple_of_corner_values_agrees() {
    let mut n = 0;
    for x in CORNERS {
        for lo in CORNERS {
            for hi in CORNERS {
                let three = |xs: Vec<Term>| {
                    let [x, lo, hi]: [Term; 3] = xs.try_into().expect("three operands");
                    clamp(x, lo, hi)
                };
                for t in both_forms(three, &[x, lo, hi]) {
                    agreed(&t);
                    n += 1;
                }
            }
        }
    }
    assert_eq!(n, 343 * 2);
    // A NaN anywhere gives the NaN; a negative zero below a zero bound is raised to it; bounds
    // the wrong way round give `lo`.
    let (nan, inf) = (f64::NAN, f64::INFINITY);
    for (x, lo, hi, want) in [
        (nan, 0.0, 1.0, nan),
        (0.5, nan, 1.0, nan),
        (0.5, 0.0, nan, nan),
        (-0.0, 0.0, 1.0, 0.0),
        (0.0, -1.0, -0.0, -0.0),
        (5.0, 1.0, 0.0, 1.0),
        (inf, -inf, 2.0, 2.0),
        (-inf, -1.0, inf, -1.0),
    ] {
        let t = clamp(float(x), float(lo), float(hi));
        assert_eq!(bits(&agreed(&t)), want.to_bits(), "clamp({x}, {lo}, {hi})");
    }
}

/// `min` and `max` of two ints, and of an int and a float, still run in the kernel, which
/// gives the int or refuses the mix; native code gives the same.
#[test]
fn ints_and_mixed_operands_go_to_the_kernel() {
    use zed_kernel::term::build::lit;
    for op in [Prim::Min, Prim::Max] {
        let t = prim(op, vec![lit(3i64), lit(-4i64)]);
        let (v, calls) = at(OptLevel::None, &t);
        assert_eq!(v, kernel(&t).unwrap());
        assert_eq!(calls, 1);
        let t = prim(op, vec![lit(3i64), float(1.0)]);
        let (g, p) = planned(&t);
        let got = zed_native::run(&g, &p, &mut Evaluator::new(World::new())).map(|o| o.value);
        assert_eq!(got, kernel(&t), "{op:?}");
    }
}

/// `m1 = min(x0, x1); m2 = min(m1, x2); …`: a fold of `min` over `n` floats, which alternate
/// in sign and grow in size, `-0.0` and `0.0` first, so the least is the last negative one.
fn fold(n: usize) -> Term {
    let x = |i: usize| match i {
        0 => -0.0,
        1 => 0.0,
        _ => i as f64 * if i.is_multiple_of(2) { -0.5 } else { 0.5 },
    };
    let last = format!("m{}", n - 1);
    (1..n).rev().fold(var(&last), |body, i| {
        let acc = if i == 1 {
            float(x(0))
        } else {
            var(&format!("m{}", i - 1))
        };
        let_(
            &format!("m{i}"),
            prim(Prim::Min, vec![acc, float(x(i))]),
            body,
        )
    })
}

/// A fold of `min` over `n` floats runs natively, inline, and gives the kernel's value, the
/// last negative one.
pub(crate) fn fold_agrees(n: usize) {
    let t = fold(n);
    let (g, p) = planned(&t);
    let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(o.kernel_calls, 0);
    assert_eq!(o.value, kernel(&t).unwrap());
    let last_even = (n - 1) & !1;
    let least = if last_even == 0 {
        -0.0
    } else {
        last_even as f64 * -0.5
    };
    assert_eq!(bits(&o.value), least.to_bits());
}

/// The small instances of `bench::minmax`: folds of two, three and six floats.
#[test]
fn a_short_fold_of_min_gives_the_least() {
    for n in [2, 3, 6] {
        fold_agrees(n);
    }
}
