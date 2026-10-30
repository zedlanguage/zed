//! The tonicity of each scalar primitive in each argument, checked by running it. Each
//! claim is tested on every pair of points within one sign part of the argument, the other
//! argument fixed at each value of a window; `false` is below `true`, and a failure is
//! skipped, since no demand holds it.

use zed_kernel::{Prim, Term, Value, eval};
use zedc::store::preimage::tonicity;
use zedc::store::revision::{self, Op, Tonicity};

const W: i64 = 9;

/// The values an argument of `p` ranges over.
fn values(p: Prim) -> Vec<Value> {
    match p {
        Prim::And | Prim::Or | Prim::Not => vec![Value::Bool(false), Value::Bool(true)],
        _ => (-W..=W).map(Value::Int).collect(),
    }
}

/// A value's place in the order, `None` for a failure.
fn key(v: &Value) -> Option<i64> {
    match v {
        Value::Int(n) => Some(*n),
        Value::Bool(b) => Some(*b as i64),
        _ => None,
    }
}

fn run(p: Prim, args: &[Value]) -> Option<i64> {
    let t = Term::Prim(p, args.iter().cloned().map(Term::Lit).collect());
    key(&eval(&t).expect("a primitive on literals evaluates"))
}

/// Which way the result must move as the argument rises from `a` to `b`, with the other
/// argument `other`: `Some(true)` up, `Some(false)` down, `None` either.
fn direction(t: Tonicity, a: i64, b: i64, other: Option<i64>) -> Option<Option<bool>> {
    use Tonicity::*;
    let o = other.unwrap_or(0);
    Some(match t {
        Up => Some(true),
        Down => Some(false),
        Const => Option::None,
        UpWhereOtherNonneg if o >= 0 => Some(true),
        UpWhereOtherNonneg => Some(false),
        DownWhereOtherNonneg if o >= 0 => Some(false),
        DownWhereOtherNonneg => Some(true),
        DownThenUp if b <= 0 => Some(false),
        DownThenUp if a >= 0 => Some(true),
        // A pair across 0 is not in one sign part.
        DownThenUp => return Option::None,
        Tonicity::None => return Option::None,
    })
}

/// Checks that `p` moves in argument `arg` as `t` says; returns the number of pairs checked,
/// or the first pair that does not.
fn holds(p: Prim, arg: usize, t: Tonicity, arity: usize) -> Result<usize, String> {
    let vs = values(p);
    let others: Vec<Option<Value>> = if arity == 1 {
        vec![None]
    } else {
        vs.iter().cloned().map(Some).collect()
    };
    let mut n = 0;
    for o in &others {
        for a in &vs {
            for b in &vs {
                let (ka, kb) = (key(a).unwrap(), key(b).unwrap());
                // Within one sign part of the argument: both below 0 or both at least 0.
                if ka >= kb || (ka < 0) != (kb < 0) && t != Tonicity::DownThenUp {
                    continue;
                }
                let Some(dir) = direction(t, ka, kb, o.as_ref().and_then(key)) else {
                    continue;
                };
                let at = |x: &Value| {
                    let mut args = vec![x.clone()];
                    if let Some(o) = o {
                        args.insert(1 - arg, o.clone());
                    }
                    run(p, &args)
                };
                let (Some(fa), Some(fb)) = (at(a), at(b)) else {
                    continue;
                };
                let ok = match dir {
                    Some(true) => fa <= fb,
                    Some(false) => fa >= fb,
                    None => fa == fb,
                };
                if !ok {
                    return Err(format!(
                        "{p:?} arg {arg} {t:?}: {a} -> {fa}, {b} -> {fb}, other {o:?}"
                    ));
                }
                n += 1;
            }
        }
    }
    Ok(n)
}

const TABLE: &[(Prim, usize, Option<Tonicity>)] = {
    use Prim::*;
    use Tonicity::*;
    &[
        (Add, 0, Some(Up)),
        (Add, 1, Some(Up)),
        (Sub, 0, Some(Up)),
        (Sub, 1, Some(Down)),
        (Mul, 0, Some(UpWhereOtherNonneg)),
        (Mul, 1, Some(UpWhereOtherNonneg)),
        (IntDiv, 0, Some(UpWhereOtherNonneg)),
        (IntDiv, 1, Some(DownWhereOtherNonneg)),
        (Mod, 0, Option::None),
        (Mod, 1, Option::None),
        (Min, 0, Some(Up)),
        (Min, 1, Some(Up)),
        (Max, 0, Some(Up)),
        (Max, 1, Some(Up)),
        (Neg, 0, Some(Down)),
        (Abs, 0, Some(DownThenUp)),
        (Lt, 0, Some(Down)),
        (Lt, 1, Some(Up)),
        (Le, 0, Some(Down)),
        (Le, 1, Some(Up)),
        (Gt, 0, Some(Up)),
        (Gt, 1, Some(Down)),
        (Ge, 0, Some(Up)),
        (Ge, 1, Some(Down)),
        (Not, 0, Some(Down)),
        (And, 0, Some(Up)),
        (And, 1, Some(Up)),
        (Or, 0, Some(Up)),
        (Or, 1, Some(Up)),
        (Eq, 0, Option::None),
        (Ne, 1, Option::None),
        (Concat, 0, Option::None),
    ]
};

fn arity(p: Prim) -> usize {
    p.arity().unwrap_or(2)
}

#[test]
fn the_table_gives_each_primitive_its_tonicity() {
    for &(p, arg, t) in TABLE {
        assert_eq!(tonicity(p, arg), t, "{p:?} arg {arg}");
    }
}

#[test]
fn each_claimed_tonicity_holds_when_the_primitive_is_run() {
    let mut checked = 0;
    for &(p, arg, t) in TABLE {
        if let Some(t) = t {
            let n = holds(p, arg, t, arity(p)).unwrap_or_else(|e| panic!("{e}"));
            assert!(n > 0, "{p:?} arg {arg}: no pair checked");
            checked += n;
        }
    }
    assert!(checked > 10_000, "{checked}");
}

#[test]
fn each_power_with_a_constant_exponent_has_its_tonicity() {
    for k in 0..=5u32 {
        let t = revision::tonicity(Op::Pow(k), 0);
        let vs: Vec<i64> = (-W..=W).collect();
        for &a in &vs {
            for &b in &vs {
                if a >= b {
                    continue;
                }
                let pw = |x: i64| run(Prim::Pow, &[Value::Int(x), Value::Int(k as i64)]).unwrap();
                let Some(dir) = direction(t, a, b, None) else {
                    continue;
                };
                let ok = match dir {
                    Some(true) => pw(a) <= pw(b),
                    Some(false) => pw(a) >= pw(b),
                    None => pw(a) == pw(b),
                };
                assert!(ok, "x ** {k} {t:?}: {a}, {b}");
            }
        }
    }
}

#[test]
fn a_wrong_claim_is_caught() {
    use Prim::*;
    use Tonicity::*;
    for (p, arg, t) in [
        (Sub, 1, Up),
        (Mul, 0, Up),
        (IntDiv, 1, UpWhereOtherNonneg),
        (Abs, 0, Up),
        (Lt, 0, Up),
        (Not, 0, Up),
        (Or, 0, Down),
        (Mod, 0, Up),
        (Max, 1, Const),
    ] {
        assert!(
            holds(p, arg, t, arity(p)).is_err(),
            "{p:?} arg {arg} {t:?} passed"
        );
    }
}
