//! The L1 prelude words on scalars (step L1.18): `String`, the checked casts `int`, `rat`
//! and `f64`, `abs`, and the string words `len`, `lower`, `upper` and `trim`.
//!
//! A cast is a domain proof (DESIGN.md, "Casts are domain proofs"): `T(x)` is `x` as a `T`
//! when the value is the same number, `#inexact` when a numeric source has no equal `T`, and
//! `#invalid` when the source is not a `T` at all: a string that does not read as one, or a
//! float that is infinite or NaN cast to an exact kind.

use num_bigint::BigInt;
use num_traits::{One, Signed};

use crate::KernelError;
use crate::num::{Exact, MAX_BITS, Rat, exact_f64, show_f64};
use crate::term::Prim;
use crate::value::Value;

/// `p(x)` for one of the words above; a type error when `x` is not of a kind `p` takes.
pub(crate) fn word(p: Prim, x: &Value) -> Result<Value, KernelError> {
    let inexact = || Value::atom("inexact");
    let invalid = || Value::atom("invalid");
    let out = match (p, x) {
        (Prim::Show, Value::Str(_)) => x.clone(),
        (Prim::Show, Value::Float(f)) => Value::str(&show_f64(f.get())),
        (Prim::Show, _) => Value::str(&x.to_string()),
        (Prim::CastInt, Value::Str(s)) => match read_int(s) {
            Some(n) => sized(n)?,
            None => invalid(),
        },
        (Prim::CastRat, Value::Str(s)) => match read_rat(s) {
            Some(r) if r.bits() > MAX_BITS => return Err(KernelError::Overflow),
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
            let r = match x.exact() {
                Exact::Finite(r) => r,
                _ if p == Prim::CastF64 => return Ok(x.clone()),
                _ => return Ok(invalid()),
            };
            match p {
                Prim::CastInt if r.denom().is_one() => Value::int(r.numer().clone()),
                Prim::CastInt => inexact(),
                Prim::CastRat => Value::rat(r),
                _ => match exact_f64(&r) {
                    Some(f) => Value::float(f),
                    None => inexact(),
                },
            }
        }
        (Prim::Abs, Value::Int(n)) => match n.checked_abs() {
            Some(n) => Value::Int(n),
            None => Value::int(BigInt::from(*n).abs()),
        },
        (Prim::Abs, Value::Big(n)) => Value::int(n.abs()),
        (Prim::Abs, Value::Rat(r)) if r.numer().is_negative() => Value::rat(r.neg()),
        (Prim::Abs, Value::Rat(_)) => x.clone(),
        (Prim::Abs, Value::Float(f)) => Value::float(f.get().abs()),
        (Prim::Len, Value::Str(s)) => Value::Int(s.chars().count() as i64),
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

fn sized(n: BigInt) -> Result<Value, KernelError> {
    if n.bits() > MAX_BITS {
        return Err(KernelError::Overflow);
    }
    Ok(Value::int(n))
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
        !w.is_empty() && !f.is_empty() && (w.to_owned() + f).bytes().all(|b| b.is_ascii_digit())
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
