//! The L1 prelude words on scalars (step L1.18): `String`, the checked casts `int`, `rat`
//! and `f64`, `abs`, and the string words `len`, `lower`, `upper` and `trim`.
//!
//! A cast is a domain proof (DESIGN.md, "Casts are domain proofs"): `T(x)` is `x` as a `T`
//! when the value is the same number, `#inexact` when a numeric source has no equal `T`, and
//! `#invalid` when the source is not a `T` at all: a string that does not read as one, or a
//! float that is infinite or NaN cast to an exact kind.

use std::collections::HashMap;
use std::fmt;

use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, Zero};

use crate::KernelError;
use crate::num::{Exact, Rat, TooLarge, exact_f64, room, show_f64};
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
        (Prim::Show, _) => print(x)?,
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
            // A wide number is read where it is held, and a cast to an exact kind shares its
            // digits: a copy would be built without asking the system for the memory.
            let r = match x.exact() {
                Exact::Finite(r) => r,
                _ if p == Prim::CastF64 => return Ok(x.clone()),
                _ => return Ok(invalid()),
            };
            match (p, x) {
                (Prim::CastInt, Value::Int(_) | Value::Big(_)) | (Prim::CastRat, Value::Rat(_)) => {
                    x.clone()
                }
                (Prim::CastRat, Value::Big(n)) => Value::Rat(n.clone()),
                (Prim::CastInt, Value::Rat(n)) if r.is_integer() => match r.small_integer() {
                    Some(k) => Value::int(k),
                    None => Value::Big(n.clone()),
                },
                (Prim::CastInt, _) if r.is_integer() => Value::integer(r.into_owned()),
                (Prim::CastInt, _) => inexact(),
                (Prim::CastRat, _) => Value::rat(r.into_owned()),
                _ => match exact_f64(&r) {
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
        // A wide number not negative is its own `abs`, shared; a negative one is copied, which
        // asks the system for the memory first.
        (Prim::Abs, Value::Big(n) | Value::Rat(n)) if n.is_negative() => {
            let r = n.try_neg().map_err(|e| KernelError::NumberTooLarge {
                op: "abs",
                bits: e.bits,
            })?;
            match x {
                Value::Big(_) => Value::integer(r),
                _ => Value::rat(r),
            }
        }
        (Prim::Abs, Value::Big(_) | Value::Rat(_)) => x.clone(),
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

/// What is left to read in [`room_to_print`].
enum Visit<'a> {
    Value(&'a Value),
    /// The end of a shared part, whose length is then known.
    Done(Shared),
}

/// What printing a value needs, from [`room_to_print`].
struct Room {
    /// At most this many bytes of text, each number's digits counted at their widest.
    bytes: Option<u128>,
    /// The widest build of one number's digits, in bits, held while the text is written.
    widest: BigUint,
}

/// Counts the bytes written to it.
struct Count(u128);

impl fmt::Write for Count {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.0 += s.len() as u128;
        Ok(())
    }
}

/// The length of `x` written by `Display` or `Debug`, writing nothing.
fn written(x: fmt::Arguments<'_>) -> u128 {
    let mut n = Count(0);
    fmt::write(&mut n, x).expect("counting cannot fail");
    n.0
}

/// `String` of a tuple, keypath, atom or family. The text is written into memory reserved
/// for all of it, after the system gives, with that memory held, the widest number's build
/// and the copy of the text into the value; else an error, before anything is written.
fn print(x: &Value) -> Result<Value, KernelError> {
    let need = room_to_print(x).map_err(|e| KernelError::NumberTooLarge {
        op: "String",
        bits: e.bits,
    })?;
    let text = need.bytes;
    let refused = || KernelError::TextTooLarge { bytes: text };
    let bytes = text
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(refused)?;
    let mut out = String::new();
    out.try_reserve_exact(bytes).map_err(|_| refused())?;
    room(need.widest.max(BigUint::from(bytes) << 3u32)).map_err(|_| refused())?;
    fmt::write(&mut out, format_args!("{x}")).expect("writing to a String");
    Ok(Value::str(&out))
}

/// The length of `v`'s text, and its widest number build; [`TooLarge`] for the first number
/// whose own build the system refuses ([`Rat::text_room`]), before anything is written. Each
/// leaf's length is the one it is written with, and each number's digits at most `bits *
/// log10(2) + 2`, from its width. A shared sequence and a family, whose copies keep its id, are
/// read once and their length added at each further occurrence, so the walk costs the
/// distinct parts of `v`, not the paths to them.
fn room_to_print(v: &Value) -> Result<Room, TooLarge> {
    let mut todo = vec![Visit::Value(v)];
    // The length of each shared part read, and of each part being read, innermost last.
    let mut known: HashMap<Shared, Option<u128>> = HashMap::new();
    let mut open: Vec<Option<u128>> = vec![Some(0)];
    // The length of a struct payload's field names, `name: ` each, by their shared list.
    let mut names: HashMap<(usize, usize), u128> = HashMap::new();
    let mut widest = BigUint::zero();
    let add = |open: &mut Vec<Option<u128>>, n: Option<u128>| {
        let sum = open.last_mut().expect("the whole value is open");
        *sum = sum.zip(n).and_then(|(a, b)| a.checked_add(b));
    };
    while let Some(visit) = todo.pop() {
        let v = match visit {
            Visit::Value(v) => v,
            Visit::Done(s) => {
                let n = open.pop().expect("a shared part is open");
                known.insert(s, n);
                add(&mut open, n);
                continue;
            }
        };
        let (own, items) = match v {
            Value::Big(n) | Value::Rat(n) => {
                n.text_room()?;
                let (bits, text) = n.text_size();
                widest = widest.max(bits + (&text << 3u32));
                // A sign, and the `r`, `r/` and `r` of a `rat`.
                add(&mut open, (text + 5u32).to_u128());
                continue;
            }
            Value::Bool(b) => (written(format_args!("{b}")), None),
            Value::Int(n) => (written(format_args!("{n}")), None),
            Value::Float(f) => (show_f64(f.get()).len() as u128, None),
            Value::Str(s) => (written(format_args!("{s:?}")), None),
            Value::Family(f) => {
                let key = Shared::Family(f.id());
                if let Some(&n) = known.get(&key) {
                    add(&mut open, n);
                    continue;
                }
                // Written as `{k -> v, ..}`, or a set by its members, as `Display` decides.
                let set = !f.is_empty() && f.iter().all(|(k, w)| k == w);
                let entries = f.len() as u128;
                let arrows = if set { 0 } else { 4 * entries };
                open.push(Some(2 + 2 * entries.saturating_sub(1) + arrows));
                todo.push(Visit::Done(key));
                match set {
                    true => todo.extend(f.iter().map(|(k, _)| Visit::Value(k))),
                    false => todo.extend(f.iter().flat_map(|(k, w)| [k, w]).map(Visit::Value)),
                }
                continue;
            }
            Value::Tuple(items) => (2 + 2 * (items.len() as u128).saturating_sub(1), Some(items)),
            Value::Path(items) => (2 + 4 * (items.len() as u128).saturating_sub(1), Some(items)),
            Value::Atom(a) => {
                let mut own = 1 + a.name.len() as u128;
                if !a.args.is_empty() {
                    let fields = &a.fields[..a.fields.len().min(a.args.len())];
                    let named = *names
                        .entry((fields.as_ptr().addr(), fields.len()))
                        .or_insert_with(|| fields.iter().map(|k| k.len() as u128 + 2).sum());
                    own += 2 + 2 * (a.args.len() as u128 - 1) + named;
                }
                (own, Some(&a.args))
            }
        };
        add(&mut open, Some(own));
        let Some(items) = items else { continue };
        if items.is_shared() {
            let key = Shared::Items(items.addr());
            if let Some(&n) = known.get(&key) {
                add(&mut open, n);
                continue;
            }
            open.push(Some(0));
            todo.push(Visit::Done(key));
        }
        todo.extend(items.as_slice().iter().map(Visit::Value));
    }
    let bytes = open.pop().expect("the whole value is open");
    Ok(Room { bytes, widest })
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::family::Family;

    /// The length [`room_to_print`] counts is the length written, for every kind of part, with
    /// sharing, and at most a few bytes more per number.
    #[test]
    fn the_counted_length_is_the_written_length() {
        let row = Value::tuple(vec![Value::Int(-12), Value::float(0.5), Value::Bool(true)]);
        let named = Value::atom_named(
            "ioError",
            vec![
                ("why".into(), Value::str("disk \"full\"\n")),
                ("op".into(), row.clone()),
            ],
        )
        .expect("distinct fields");
        let set = Value::Family(Family::of([
            (Value::Int(1), Value::Int(1)),
            (Value::Int(2), Value::Int(2)),
        ]));
        let map = Value::Family(Family::of([(Value::str("a"), row.clone())]));
        let exact = [
            Value::tuple(vec![]),
            Value::tuple(vec![row.clone(), row.clone(), named.clone(), named.clone()]),
            Value::Path(vec![Value::str("é\u{1}"), Value::Int(i64::MIN)].into()),
            Value::atom("notFound"),
            Value::atom_with("errs", vec![set.clone(), map.clone(), map.clone()]),
            Value::tuple(vec![set, Value::float(f64::NAN), Value::float(-1e300)]),
        ];
        for v in exact {
            let need = room_to_print(&v).expect("no number to build");
            assert_eq!(need.bytes, Some(v.to_string().len() as u128), "{v}");
        }
        let wide = Rat::int(BigInt::from(1u32) << 200u32);
        let third = Rat::new(BigInt::from(-1), BigInt::from(3)).expect("3 is not zero");
        let v = Value::tuple(vec![Value::integer(wide), Value::rat(third), Value::Int(0)]);
        let need = room_to_print(&v).expect("both fit");
        let written = v.to_string().len() as u128;
        let counted = need.bytes.expect("a short text");
        assert!(
            (written..=written + 16).contains(&counted),
            "{written} {counted}"
        );
    }
}
