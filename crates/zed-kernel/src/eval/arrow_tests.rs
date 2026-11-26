//! Plan row KERNEL-prim-arrow-table: the evaluator takes a tuple of scalar operands exactly
//! when [`Prim::arrows`], the table the checker builds `op_sig` and `word_sig` from, has an
//! arrow for their carriers, and gives that arrow's carrier or one of its atoms. Before, the
//! rule was written twice, as match arms in [`super::prim_on`] and as `Arrow` lists in the
//! checker, and nothing tied the two together.

use num_bigint::BigInt;

use super::prim_data;
use crate::num::Rat;
use crate::term::{Prim, ScalarArrow, ScalarType};
use crate::value::{KernelError, Value};

/// Every primitive, by [`Prim::code`]; the test checks the codes are `0 ..< 91`, each once.
const ALL: [Prim; 91] = Prim::ALL;

const TYPES: [ScalarType; 6] = [
    ScalarType::Bool,
    ScalarType::Int,
    ScalarType::Rat,
    ScalarType::F32,
    ScalarType::F64,
    ScalarType::Str,
];

/// A value of each carrier that every arrow's operation is defined on: `2`, so no operand is
/// a zero divisor, a negative exponent or a surrogate, and `"2"`, which every cast reads.
fn sample(t: ScalarType) -> Value {
    match t {
        ScalarType::Bool => Value::Bool(true),
        ScalarType::Int => Value::Int(2),
        ScalarType::Rat => Value::rat(Rat::int(BigInt::from(2))),
        ScalarType::F32 => Value::float32(2.0),
        ScalarType::F64 => Value::float(2.0),
        ScalarType::Str => Value::str("2"),
    }
}

/// The carrier of a scalar value, `None` for any other value.
fn carrier(v: &Value) -> Option<ScalarType> {
    Some(match v {
        Value::Bool(_) => ScalarType::Bool,
        Value::Int(_) | Value::Big(_) => ScalarType::Int,
        Value::Rat(_) => ScalarType::Rat,
        Value::Float32(_) => ScalarType::F32,
        Value::Float(_) => ScalarType::F64,
        Value::Str(_) => ScalarType::Str,
        _ => return None,
    })
}

/// Every tuple of `n` carriers, `6^n` of them.
fn tuples(n: usize) -> Vec<Vec<ScalarType>> {
    (0..n).fold(vec![Vec::new()], |acc, _| {
        acc.iter()
            .flat_map(|t| {
                TYPES.iter().map(move |&c| {
                    let mut t = t.clone();
                    t.push(c);
                    t
                })
            })
            .collect()
    })
}

/// What disagrees, for each primitive with a table: a tuple the table has an arrow for that
/// the evaluator refuses or gives another carrier for, or a tuple the evaluator takes that the
/// table has no arrow for. The arrows the checker refuses by design
/// ([`ScalarArrow::refused`]) are held to the evaluator like the others, so the table names
/// every tuple the evaluator takes and no gap is left unlisted.
fn disagreements(arrows_of: impl Fn(Prim) -> Option<&'static [ScalarArrow]>) -> Vec<String> {
    let mut found = Vec::new();
    for p in ALL {
        let Some(arrows) = arrows_of(p) else { continue };
        let n = p
            .arity()
            .expect("a primitive with a table has a fixed arity");
        for ts in tuples(n) {
            let arrow = arrows.iter().find(|a| a.params == ts.as_slice());
            let got = prim_data(p, ts.iter().map(|&t| sample(t)).collect());
            match (arrow, got) {
                (Some(a), Ok(v)) => {
                    let fits = match &v {
                        Value::Atom(atom) => a.atoms.contains(&&*atom.name),
                        v => carrier(v) == Some(a.result),
                    };
                    if !fits {
                        found.push(format!("{p:?}{ts:?}: gives {v}, the table says {a:?}"));
                    }
                }
                (Some(a), Err(e)) => found.push(format!("{p:?}{ts:?}: {e:?}, the table has {a:?}")),
                (None, Ok(v)) => {
                    found.push(format!("{p:?}{ts:?}: gives {v}, the table has no arrow"))
                }
                (None, Err(KernelError::Type(_))) => {}
                (None, Err(e)) => found.push(format!("{p:?}{ts:?}: {e:?}, not a type error")),
            }
        }
    }
    found
}

/// [`Prim::ALL`] lists each primitive once, at the position of its code, which the ZIR binary
/// form relies on to number primitives by their codes. Not caught here: a new primitive given
/// the next code, 91, and left out of the list; the lists of `l01_15_kernel_terms::complete`
/// and `m0_07_canonicalization::prim_codes`, written apart, do not catch it either.
#[test]
fn every_primitive_is_listed_once_in_code_order() {
    let codes: Vec<u64> = ALL.iter().map(|p| p.code()).collect();
    assert_eq!(codes, (0..ALL.len() as u64).collect::<Vec<_>>());
}

/// Exhaustive over every primitive with a table and every tuple of scalar carriers of its
/// arity: 6, 36 or 216 tuples each, about 2 800 evaluations in all.
#[test]
fn prim_arrow_table() {
    let found = disagreements(Prim::arrows);
    assert!(found.is_empty(), "{}", found.join("\n"));
}

/// The arrows the checker refuses by design are exactly `==` and `!=` of two carriers (30
/// tuples each) and `min` and `max` of two strings or two bools; no other primitive has one.
#[test]
fn the_refused_arrows_are_the_named_ones() {
    let mut refused = Vec::new();
    for p in ALL {
        for a in p.arrows().unwrap_or(&[]) {
            if a.refused.is_some() {
                refused.push((p, a.params));
            }
        }
    }
    let count = |p: Prim| refused.iter().filter(|(q, _)| *q == p).count();
    assert_eq!((count(Prim::Eq), count(Prim::Ne)), (30, 30));
    assert_eq!((count(Prim::Min), count(Prim::Max)), (2, 2));
    assert_eq!(refused.len(), 64, "{refused:?}");
    assert!(refused.iter().all(|(p, ts)| match p {
        Prim::Eq | Prim::Ne => ts[0] != ts[1],
        _ => ts[0] == ts[1] && matches!(ts[0], ScalarType::Str | ScalarType::Bool),
    }));
}

/// Negative controls: a table missing one arrow, one with an arrow the evaluator does not
/// take, and one missing a refused arrow, are all caught.
#[test]
fn a_wrong_table_is_caught() {
    const MISSING: &[ScalarArrow] = &[ScalarArrow {
        params: &[ScalarType::Int, ScalarType::Int],
        result: ScalarType::Int,
        atoms: &[],
        refused: None,
    }];
    const EXTRA: &[ScalarArrow] = &[ScalarArrow {
        params: &[ScalarType::Str],
        result: ScalarType::Str,
        atoms: &[],
        refused: None,
    }];
    let missing = |p: Prim| {
        if p == Prim::Add {
            Some(MISSING)
        } else {
            p.arrows()
        }
    };
    let extra = |p: Prim| {
        if p == Prim::Neg {
            Some(EXTRA)
        } else {
            p.arrows()
        }
    };
    let found = disagreements(missing);
    assert_eq!(found.len(), 3, "{found:?}");
    assert!(
        found
            .iter()
            .all(|f| f.starts_with("Add") && f.contains("no arrow"))
    );
    let found = disagreements(extra);
    assert_eq!(found.len(), 5, "{found:?}");
    assert!(found.iter().any(|f| f.starts_with("Neg[Str]")));
    // `min` with its refused arrows dropped: the evaluator still takes two strings and two
    // bools, so both are found.
    let min = Prim::Min.arrows().unwrap();
    let kept: &'static [ScalarArrow] = Box::leak(
        (min.iter().copied())
            .filter(|a| a.refused.is_none())
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    );
    let found = disagreements(|p| {
        if p == Prim::Min {
            Some(kept)
        } else {
            p.arrows()
        }
    });
    assert_eq!(found.len(), 2, "{found:?}");
    assert!(
        found
            .iter()
            .all(|f| f.starts_with("Min") && f.contains("no arrow"))
    );
}

/// `f64 ^ int` (plan row POW-domains): the IEEE power of the exponent as an `f64`, with no atom;
/// a zero to a negative power is the infinity of the zero's sign at an odd exponent, the
/// positive one at an even one; an exponent past ±2^53 keeps its parity; the NaN gives the NaN.
/// Corner cases: ±2^53 itself, 2^53 + 1, and a negative exponent past it. Negative control: the
/// same power at `f32`, whose arrow was there before, agrees with it rounded to `f32`.
#[test]
fn float_to_an_int_power() {
    let pow = |x: f64, n: Value| match prim_data(Prim::Pow, vec![Value::float(x), n]) {
        Ok(Value::Float(r)) => r.get(),
        other => panic!("f64 ^ int gave {other:?}"),
    };
    let big = |s: &str| Value::integer(Rat::int(s.parse::<BigInt>().expect("digits")));
    assert_eq!(pow(2.0, Value::Int(10)), 1024.0);
    assert_eq!(pow(2.0, Value::Int(-2)), 0.25);
    assert_eq!(pow(0.0, Value::Int(-1)), f64::INFINITY);
    assert_eq!(pow(-0.0, Value::Int(-1)), f64::NEG_INFINITY);
    assert_eq!(pow(-0.0, Value::Int(-2)), f64::INFINITY);
    assert_eq!(pow(0.0, Value::Int(0)), 1.0);
    assert!(pow(f64::NAN, Value::Int(0)).is_nan());
    assert_eq!(pow(-1.0, Value::Int(1 << 53)), 1.0);
    assert_eq!(pow(-1.0, big("9007199254740993")), -1.0);
    assert_eq!(pow(-1.0, big("-9007199254740993")), -1.0);
    assert_eq!(pow(-1.0, big("100000000000000000000")), 1.0);
    assert_eq!(pow(2.0, big("100000000000000000000")), f64::INFINITY);
    assert_eq!(pow(-2.0, big("-100000000000000000001")), -0.0);
    assert!(pow(-2.0, big("-100000000000000000001")).is_sign_negative());
    for (x, n) in [(1.5f32, 7i64), (-3.0, -3), (0.1, 20)] {
        let at32 = prim_data(Prim::Pow, vec![Value::float32(x), Value::Int(n)]);
        let Ok(Value::Float32(r)) = at32 else {
            panic!("f32 ^ int gave {at32:?}")
        };
        assert_eq!(r.get(), pow(f64::from(x), Value::Int(n)) as f32);
    }
}
