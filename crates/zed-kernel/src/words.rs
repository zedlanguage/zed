//! The L1 prelude words on scalars (step L1.18): `String`, the checked casts `int`, `rat`
//! and `f64`, `abs`, and the string words `len`, `lower`, `upper` and `trim`.
//!
//! A cast is a domain proof (DESIGN.md, "Casts are domain proofs"): `T(x)` is `x` as a `T`
//! when the value is the same number, `#inexact` when a numeric source has no equal `T`, and
//! `#invalid` when the source is not a `T` at all: a string that does not read as one, or a
//! float that is infinite or NaN cast to an exact kind.

use std::collections::HashSet;

use num_bigint::BigInt;

use crate::KernelError;
use crate::num::{Exact, Rat, TooLarge, exact_f64, show_f64};
use crate::term::Prim;
use crate::value::Value;

/// `p(x)` for one of the words above; a type error when `x` is not of a kind `p` takes.
pub(crate) fn word(p: Prim, x: &Value) -> Result<Value, KernelError> {
    let inexact = || Value::atom("inexact");
    let invalid = || Value::atom("invalid");
    let out = match (p, x) {
        (Prim::Show, Value::Str(_)) => x.clone(),
        (Prim::Show, Value::Float(f)) => Value::str(&show_f64(f.get())),
        // Printing a number builds its digits; the system is asked for that memory first.
        (Prim::Show, Value::Big(n) | Value::Rat(n)) => match n.text_room() {
            Ok(()) => Value::str(&x.to_string()),
            Err(e) => {
                return Err(KernelError::NumberTooLarge {
                    op: "String",
                    bits: e.bits,
                });
            }
        },
        // A tuple, keypath, atom or family prints each number inside it.
        (Prim::Show, _) => match room_to_print(x) {
            Ok(()) => Value::str(&x.to_string()),
            Err(e) => {
                return Err(KernelError::NumberTooLarge {
                    op: "String",
                    bits: e.bits,
                });
            }
        },
        (Prim::CastInt, Value::Str(s)) => match read_int(s) {
            Some(n) => Value::int(n),
            None => invalid(),
        },
        (Prim::CastRat, Value::Str(s)) => match read_rat(s) {
            Some(r) => Value::rat(r),
            None => invalid(),
        },
        (Prim::CastF64, Value::Str(s)) => match read_f64(s) {
            Some(f) if f.is_infinite() && !s.ends_with("inf") => inexact(),
            Some(f) => Value::float(f),
            None => invalid(),
        },
        (Prim::CastInt | Prim::CastRat | Prim::CastF64, _) => {
            if x.number_kind().is_none() {
                return type_err(p, x);
            }
            // A wide number is read where it is held, not copied: its copy would be built without
            // asking the system for the memory.
            let held;
            let r = match x {
                Value::Big(n) | Value::Rat(n) => &**n,
                _ => match x.exact() {
                    Exact::Finite(r) => {
                        held = r;
                        &held
                    }
                    _ if p == Prim::CastF64 => return Ok(x.clone()),
                    _ => return Ok(invalid()),
                },
            };
            match p {
                Prim::CastInt if r.is_integer() => Value::integer(r.clone()),
                Prim::CastInt => inexact(),
                Prim::CastRat => Value::rat(r.clone()),
                _ => match exact_f64(r) {
                    Ok(Some(f)) => Value::float(f),
                    Ok(None) => inexact(),
                    Err(e) => {
                        return Err(KernelError::RoundTooLarge {
                            to: "f64",
                            bits: e.bits,
                        });
                    }
                },
            }
        }
        (Prim::Abs, Value::Int(n)) => match n.checked_abs() {
            Some(n) => Value::Int(n),
            None => Value::int(-BigInt::from(*n)),
        },
        (Prim::Abs, Value::Big(n)) => Value::integer(n.abs()),
        (Prim::Abs, Value::Rat(r)) if r.is_negative() => Value::rat(r.neg()),
        (Prim::Abs, Value::Rat(_)) => x.clone(),
        (Prim::Abs, Value::Float(f)) => Value::float(f.get().abs()),
        // A string doubled 63 times holds more than `i64::MAX` characters.
        (Prim::Len, Value::Str(s)) => match i64::try_from(s.char_count()) {
            Ok(n) => Value::Int(n),
            Err(_) => Value::int(BigInt::from(s.char_count())),
        },
        (Prim::Lower, Value::Str(s)) => Value::str(&s.to_lowercase()),
        (Prim::Upper, Value::Str(s)) => Value::str(&s.to_uppercase()),
        (Prim::Trim, Value::Str(s)) => Value::str(s.trim()),
        _ => return type_err(p, x),
    };
    Ok(out)
}

fn type_err(p: Prim, x: &Value) -> Result<Value, KernelError> {
    Err(KernelError::Type(format!("{p:?} applied to {x}")))
}

/// A part of a value that more than one holder can share, read once by [`room_to_print`].
#[derive(PartialEq, Eq, Hash)]
enum Shared {
    Items(usize),
    Family(crate::family::Id),
}

/// `Ok` when the system gives the memory to write each number inside `v`, asked one number at
/// a time by [`Rat::text_room`], since printing builds each number's digits and frees them
/// before the next; else [`TooLarge`] for the first refused, before anything is written. A
/// shared sequence and a family, whose copies keep its id, are read once, so the walk costs
/// the distinct parts of `v`, not the paths to them.
fn room_to_print(v: &Value) -> Result<(), TooLarge> {
    let mut todo = vec![v];
    let mut seen = HashSet::new();
    let mut first = |s: Shared| seen.insert(s);
    while let Some(v) = todo.pop() {
        let items = match v {
            Value::Big(n) | Value::Rat(n) => {
                n.text_room()?;
                continue;
            }
            Value::Bool(_) | Value::Int(_) | Value::Float(_) | Value::Str(_) => continue,
            Value::Family(f) => {
                if first(Shared::Family(f.id())) {
                    todo.extend(f.iter().flat_map(|(k, w)| [k, w]));
                }
                continue;
            }
            Value::Tuple(items) | Value::Path(items) => items,
            Value::Atom(a) => &a.args,
        };
        if !items.is_shared() || first(Shared::Items(items.addr())) {
            todo.extend(items.as_slice());
        }
    }
    Ok(())
}

/// An optional `-` and decimal digits.
fn read_int(s: &str) -> Option<BigInt> {
    let digits = s.strip_prefix('-').unwrap_or(s);
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    s.parse().ok()
}

/// What `String` writes for a `rat`, `3r` or `-1r/3r`, or the same without the `r`s, or a
/// decimal such as `0.25`.
fn read_rat(s: &str) -> Option<Rat> {
    let part = |t: &str| read_int(t.strip_suffix('r').unwrap_or(t));
    if let Some((n, d)) = s.split_once('/') {
        return Rat::new(part(n)?, part(d)?);
    }
    if let Some(n) = part(s) {
        return Some(Rat::int(n));
    }
    let digits = s.strip_prefix('-').unwrap_or(s);
    let well_formed = digits.split_once('.').is_some_and(|(w, f)| {
        !w.is_empty() && !f.is_empty() && w.bytes().chain(f.bytes()).all(|b| b.is_ascii_digit())
    });
    if !well_formed {
        return None;
    }
    Rat::decimal(s)
}

/// What `String` writes for a float, correctly rounded: `-0.5`, `1.0e300`, `inf`, `nan`;
/// an integer such as `3` is read too.
fn read_f64(s: &str) -> Option<f64> {
    let body = s.strip_prefix('-').unwrap_or(s);
    if body == "inf" || body == "nan" {
        return s.parse().ok();
    }
    let (mantissa, exp) = match body.split_once('e') {
        Some((m, e)) => (m, Some(e)),
        None => (body, None),
    };
    let digits = |t: &str| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit());
    let mantissa_ok = match mantissa.split_once('.') {
        Some((w, f)) => digits(w) && digits(f),
        None => digits(mantissa),
    };
    let exp_ok = exp.is_none_or(|e| digits(e.strip_prefix('-').unwrap_or(e)));
    if !mantissa_ok || !exp_ok {
        return None;
    }
    s.parse().ok()
}
