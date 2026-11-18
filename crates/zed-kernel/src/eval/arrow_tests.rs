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

/// Every primitive, by [`Prim::code`]; the test checks the codes are `0 ..< 88`, each once.
const ALL: [Prim; 88] = {
    use Prim::*;
    [
        Add, Sub, Mul, Div, IntDiv, Mod, Neg, Eq, Ne, Lt, Le, Gt, Ge, And, Or, Not, Min, Max,
        Get, Count, Union, Path, PathKey, PathLen, Tuple, TupleGet, Concat, Pow, Atom, Show,
        CastInt, CastRat, CastF64, Abs, Len, Lower, Upper, Trim, Sum, BitAnd, BitOr, BitXor,
        BitNot, Shl, Shr, PopCount, LeadingZeros, TrailingZeros, Rotl, Rotr, F64Bits,
        CodePoint, Scalar, Utf8, FromUtf8, MulHi, BitReverse, ByteSwap, Pdep, Pext, FunnelShl,
        FunnelShr, At, CastF32, Sqrt, Fma, Entries, Has, Range, FirstEntry, LastEntry,
        EntryAfter, EntryBefore, First, Last, Split, Lines, Join, RangeFrom, ListConcat, Place,
        CallNamed, Round, RoundTiesAway, Floor, Ceil, Trunc, AwayFromZero,
    ]
};

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

/// The tuples of operand carriers the evaluator takes and the table leaves out, on purpose:
/// the checker is narrower there and refuses the program, so no checked program reaches them.
/// `==` and `!=` of two carriers: the evaluator compares any two values, and the checker
/// refuses two carriers that can never be equal (`Ck::equal`). `min` and `max` of two strings
/// or two bools: the evaluator orders any two values of one kind, and the checker's `min` and
/// `max` take numbers only.
fn wider(p: Prim, ts: &[ScalarType]) -> bool {
    match p {
        Prim::Eq | Prim::Ne => true,
        Prim::Min | Prim::Max => {
            ts[0] == ts[1] && matches!(ts[0], ScalarType::Str | ScalarType::Bool)
        }
        _ => false,
    }
}

/// What disagrees, for each primitive with a table: a tuple the table has an arrow for that
/// the evaluator refuses or gives another carrier for, or a tuple the evaluator takes that the
/// table has no arrow for and [`wider`] does not name.
fn disagreements(
    arrows_of: impl Fn(Prim) -> Option<&'static [ScalarArrow]>,
    wider: impl Fn(Prim, &[ScalarType]) -> bool,
) -> Vec<String> {
    let mut found = Vec::new();
    for p in ALL {
        let Some(arrows) = arrows_of(p) else { continue };
        let n = p.arity().expect("a primitive with a table has a fixed arity");
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
                (None, Ok(v)) if !wider(p, &ts) => {
                    found.push(format!("{p:?}{ts:?}: gives {v}, the table has no arrow"))
                }
                (None, Err(KernelError::Type(_)) | Ok(_)) => {}
                (None, Err(e)) => found.push(format!("{p:?}{ts:?}: {e:?}, not a type error")),
            }
        }
    }
    found
}

#[test]
fn every_primitive_is_listed_once() {
    let mut codes: Vec<u64> = ALL.iter().map(|p| p.code()).collect();
    codes.sort_unstable();
    assert_eq!(codes, (0..ALL.len() as u64).collect::<Vec<_>>());
}

/// Exhaustive over every primitive with a table and every tuple of scalar carriers of its
/// arity: 6, 36 or 216 tuples each, about 2 800 evaluations in all.
#[test]
fn prim_arrow_table() {
    let found = disagreements(Prim::arrows, wider);
    assert!(found.is_empty(), "{}", found.join("\n"));
}

/// Negative controls: a table missing one arrow, and one with an arrow the evaluator does not
/// take, are both caught.
#[test]
fn a_wrong_table_is_caught() {
    const MISSING: &[ScalarArrow] = &[ScalarArrow {
        params: &[ScalarType::Int, ScalarType::Int],
        result: ScalarType::Int,
        atoms: &[],
    }];
    const EXTRA: &[ScalarArrow] = &[ScalarArrow {
        params: &[ScalarType::Str],
        result: ScalarType::Str,
        atoms: &[],
    }];
    let missing = |p: Prim| if p == Prim::Add { Some(MISSING) } else { p.arrows() };
    let extra = |p: Prim| if p == Prim::Neg { Some(EXTRA) } else { p.arrows() };
    let found = disagreements(missing, wider);
    assert_eq!(found.len(), 3, "{found:?}");
    assert!(found.iter().all(|f| f.starts_with("Add") && f.contains("no arrow")));
    let found = disagreements(extra, wider);
    assert_eq!(found.len(), 5, "{found:?}");
    assert!(found.iter().any(|f| f.starts_with("Neg[Str]")));
}
