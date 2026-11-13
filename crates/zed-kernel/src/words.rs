//! The L1 prelude words on scalars (step L1.18): `String`, the checked casts `int`, `rat`
//! and `f64`, `abs`, the string words `len`, `lower`, `upper` and `trim`, and the code point
//! and UTF-8 words `codePoint`, `scalar`, `utf8` and `fromUtf8` (step L1.39c).
//!
//! A cast is a domain proof (DESIGN.md, "Casts are domain proofs"): `T(x)` is `x` as a `T`
//! when the value is the same number, `#overflow` when a finite source lies beyond the largest
//! finite `T` (a float format, or a text that rounds past it), `#inexact` when a numeric source
//! in range has no equal `T`, and `#invalid` when the source is not a `T` at all: a string that
//! does not read as one, or a float that is infinite or NaN cast to an exact kind.

use std::collections::HashMap;
use std::fmt;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{ToPrimitive, Zero};

use crate::KernelError;
use crate::num::{
    Exact, FloatFormat, Rat, TooLarge, beyond_float, exact_f32, exact_f64, read_decimal,
    read_f32_ieee, read_f64_ieee, room, show_f32, show_f64,
};
use crate::term::Prim;
use crate::text::Text;
use crate::value::Family;
use crate::value::Value;

/// The format a float cast `p` gives: `f32` for `CastF32`, and `f64` for `CastF64`.
fn float_format(p: Prim) -> FloatFormat {
    match p {
        Prim::CastF32 => FloatFormat::F32,
        _ => FloatFormat::F64,
    }
}

/// `p(x)` for one of the words above; a type error when `x` is not of a kind `p` takes.
pub(crate) fn word(p: Prim, x: &Value) -> Result<Value, KernelError> {
    let inexact = || Value::atom("inexact");
    let invalid = || Value::atom("invalid");
    let overflow = || Value::atom("overflow");
    let out = match (p, x) {
        (Prim::Show, Value::Str(_)) => x.clone(),
        (Prim::Show, Value::Float(f)) => Value::str(&show_f64(f.get())),
        (Prim::Show, Value::Float32(f)) => Value::str(&show_f32(f.get())),
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
        // Reading a number's digits asks the system for the memory first, and so does the copy
        // of a string made by joins into one block to read.
        (Prim::CastInt, Value::Str(s)) => {
            let s = s.try_flat().map_err(|e| refused("int", e))?;
            match read_int(&s).map_err(|e| refused("int", e))? {
                Some(n) => Value::int(n),
                None => invalid(),
            }
        }
        (Prim::CastRat, Value::Str(s)) => {
            let s = s.try_flat().map_err(|e| refused("rat", e))?;
            match read_rat(&s).map_err(|e| refused("rat", e))? {
                Some(r) => Value::rat(r),
                None => invalid(),
            }
        }
        (Prim::CastF64, Value::Str(s)) => {
            let s = s.try_flat().map_err(|e| refused("f64", e))?;
            match read_f64(&s) {
                Some(f) if f.is_infinite() && !s.ends_with("inf") => overflow(),
                Some(f) => Value::float(f),
                None => invalid(),
            }
        }
        (Prim::CastF32, Value::Str(s)) => {
            let s = s.try_flat().map_err(|e| refused("f32", e))?;
            match read_f32(&s) {
                Some(f) if f.is_infinite() && !s.ends_with("inf") => overflow(),
                Some(f) => Value::float32(f),
                None => invalid(),
            }
        }
        // Every `f32` is an `f64`; an infinity or NaN is one in either format.
        (Prim::CastF64, Value::Float32(f)) => Value::float(f64::from(f.get())),
        (Prim::CastF32, Value::Float32(_)) => x.clone(),
        (Prim::CastF32, Value::Float(f)) if !f.get().is_finite() => Value::float32(f.get() as f32),
        (Prim::CastInt | Prim::CastRat | Prim::CastF64 | Prim::CastF32, _) => {
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
                // A number beyond the largest finite float is out of the format's range, which
                // is `#overflow`, ahead of the test for an equal float (A36).
                _ if beyond_float(&r, float_format(p)).map_err(|e| {
                    KernelError::RoundTooLarge {
                        to: float_format(p).name(),
                        bits: e.bits,
                    }
                })? =>
                {
                    overflow()
                }
                (Prim::CastF32, _) => match exact_f32(&r) {
                    Ok(Some(f)) => Value::float32(f),
                    Ok(None) => inexact(),
                    Err(e) => {
                        return Err(KernelError::RoundTooLarge {
                            to: "f32",
                            bits: e.bits,
                        });
                    }
                },
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
        (Prim::Abs, Value::Float32(f)) => Value::float32(f.get().abs()),
        // A string doubled 63 times holds more than `i64::MAX` characters.
        (Prim::Len, Value::Str(s)) => match i64::try_from(s.char_count()) {
            Ok(n) => Value::Int(n),
            Err(_) => Value::int(BigInt::from(s.char_count())),
        },
        (Prim::Lower, Value::Str(s)) => lower(s)?,
        (Prim::Upper, Value::Str(s)) => upper(s)?,
        (Prim::Trim, Value::Str(s)) => trim(x, s)?,
        // A string of one scalar is read; a longer one is known by its count, never written out.
        (Prim::CodePoint, Value::Str(s)) => match s.char_count() {
            1 => Value::Int(i64::from(u32::from(first_char(s)))),
            _ => Value::atom("notScalar"),
        },
        (Prim::Scalar, Value::Int(n)) => match u32::try_from(*n).ok().and_then(char::from_u32) {
            Some(c) => Value::str(c.encode_utf8(&mut [0; 4])),
            None => Value::atom("notScalar"),
        },
        (Prim::Scalar, Value::Big(_)) => Value::atom("notScalar"),
        (Prim::Utf8, Value::Str(s)) => Value::Family(utf8(s)),
        (Prim::FromUtf8, Value::Family(f)) => match from_utf8(f) {
            Some(r) => r,
            None => return type_err(p, x),
        },
        _ => return type_err(p, x),
    };
    Ok(out)
}

/// An empty string with room for `bytes` bytes, once the system gives that memory and the
/// memory of the value's copy of it (`Value::str`); else the error of `op`, before anything is
/// written.
fn reserved(op: &'static str, bytes: usize) -> Result<String, KernelError> {
    let refused = || KernelError::StringCopyTooLarge { op, bytes };
    let mut out = String::new();
    out.try_reserve_exact(bytes).map_err(|_| refused())?;
    room(BigUint::from(bytes) << 3u32).map_err(|_| refused())?;
    Ok(out)
}

/// `upper(s)`: each character's uppercase, which depends on that character alone, written
/// block by block into a string of the length a first pass counts, so a join is never written
/// out first.
fn upper(s: &Text) -> Result<Value, KernelError> {
    let upper = || s.chunks().flat_map(str::chars).flat_map(char::to_uppercase);
    let mut out = reserved("upper", upper().map(char::len_utf8).sum())?;
    out.extend(upper());
    Ok(Value::str(&out))
}

/// `lower(s)`, as `str::to_lowercase` writes it. The text is read as one `&str`, a join written
/// out into memory asked first ([`Text::try_flat`]), and the result's length is counted
/// first: each character's lowercase, `Σ` two bytes whether it ends a word or not.
// Complexity tradeoff: a join is written out once more than `upper` writes it, `O(n)` time and
// memory, asked first. Why: `Σ` lowers to `ς` at the end of a word, decided by the characters
// around it past any that case ignores (Unicode `Final_Sigma`), which may lie in other blocks,
// and the standard library does not expose the two properties (`Cased`, `Case_Ignorable`) a
// reading block by block would need. Trigger: `lower` of a joined string. Test:
// `l01_17_value_representation::string_copies` (refused at two lengths, exact when given);
// COMPLEXITY.md K30. A complete solution would carry the two properties' tables and decide `Σ`
// across blocks.
fn lower(s: &Text) -> Result<Value, KernelError> {
    let flat = s.try_flat().map_err(|_| KernelError::StringCopyTooLarge {
        op: "lower",
        bytes: s.len(),
    })?;
    let bytes: usize = flat
        .chars()
        .flat_map(char::to_lowercase)
        .map(char::len_utf8)
        .sum();
    // `to_lowercase` starts at the length of its input and doubles, so it holds at most twice
    // the larger of the two; the value copies the result.
    let held = 2 * bytes.max(s.len()) + bytes;
    room(BigUint::from(held) << 3u32)
        .map_err(|_| KernelError::StringCopyTooLarge { op: "lower", bytes })?;
    Ok(Value::str(&flat.to_lowercase()))
}

/// `trim(s)`: the text between the first and the last character that are not white space,
/// found block by block. A string with none to drop is `x` itself, shared; any other is
/// copied from the blocks into memory asked first.
fn trim(x: &Value, s: &Text) -> Result<Value, KernelError> {
    // The byte offsets of the first character kept and of the end of the last.
    let (mut start, mut end, mut at) = (None, 0, 0);
    for c in s.chunks() {
        for (i, ch) in c.char_indices() {
            if !ch.is_whitespace() {
                start.get_or_insert(at + i);
                end = at + i + ch.len_utf8();
            }
        }
        at += c.len();
    }
    let start = start.unwrap_or(0);
    if start == 0 && end == s.len() {
        return Ok(x.clone());
    }
    let mut out = reserved("trim", end - start)?;
    let mut at = 0;
    for c in s.chunks() {
        let (lo, hi) = (start.max(at), end.min(at + c.len()));
        if lo < hi {
            out.push_str(&c[lo - at..hi - at]);
        }
        at += c.len();
    }
    Ok(Value::str(&out))
}

/// The first character of the non-empty text `s`, read from its first block.
fn first_char(s: &Text) -> char {
    let first = s.chunks().next().and_then(|c| c.chars().next());
    first.expect("a string of one scalar")
}

/// The family of the UTF-8 bytes of `s`, keyed by byte offset from 0, as an array is. The keys
/// are made in increasing order, so the map is built in `O(n log n)` for `n` bytes; the text is
/// read by blocks.
fn utf8(s: &Text) -> Family {
    Family::from_map(
        s.chunks()
            .flat_map(str::bytes)
            .zip(0i64..)
            .map(|(b, i)| (Value::Int(i), Value::Int(i64::from(b))))
            .collect(),
    )
}

/// The string the values of `f`, read in key order, encode as UTF-8, or `#badUtf8` when they
/// are not well-formed: an overlong form, a surrogate, a scalar past `0x10FFFF`, or a truncated
/// or stray continuation byte (the Unicode Standard, table 3-7, as [`std::str::from_utf8`] checks it). An
/// int outside `0 ..= 255` is not a byte, so it gives `#badUtf8` too; `None` when a value is not
/// an int at all.
fn from_utf8(f: &Family) -> Option<Value> {
    let mut bytes = Vec::with_capacity(f.len());
    let mut byte = true;
    for v in f.iter().map(|(_, v)| v) {
        match v {
            Value::Int(n) => match u8::try_from(*n) {
                Ok(b) => bytes.push(b),
                Err(_) => byte = false,
            },
            Value::Big(_) => byte = false,
            _ => return None,
        }
    }
    Some(match byte {
        true => match String::from_utf8(bytes) {
            Ok(s) => Value::Str(s.into()),
            Err(_) => Value::atom("badUtf8"),
        },
        false => Value::atom("badUtf8"),
    })
}

fn type_err(p: Prim, x: &Value) -> Result<Value, KernelError> {
    Err(KernelError::Type(format!(
        "`{}` applied to `{}`",
        p.written(),
        x.kind_type()
    )))
}

/// A part of a value that more than one holder can share, read once by [`room_to_print`].
#[derive(PartialEq, Eq, Hash)]
enum Shared {
    Items(crate::value::Id),
    Family(crate::value::Id),
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
    let mut names: HashMap<(crate::value::Id, usize), u128> = HashMap::new();
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
                let text = n.text_size().1;
                widest = widest.max(n.text_ask());
                // A sign, and the `r`, `r/` and `r` of a `rat`.
                add(&mut open, (text + 5u32).to_u128());
                continue;
            }
            Value::Bool(b) => (written(format_args!("{b}")), None),
            Value::Int(n) => (written(format_args!("{n}")), None),
            Value::Float(f) => (show_f64(f.get()).len() as u128, None),
            Value::Float32(f) => (show_f32(f.get()).len() as u128, None),
            Value::Str(s) => (written(format_args!("{}", s.literal())), None),
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
                let args = a.args();
                if !a.is_bare() {
                    let fields = &a.fields[..a.fields.len().min(args.len())];
                    let named = *names
                        .entry((a.fields.id(), fields.len()))
                        .or_insert_with(|| fields.iter().map(|k| k.len() as u128 + 2).sum());
                    own += 2 + 2 * (args.len() as u128).saturating_sub(1) + named;
                }
                (own, Some(args))
            }
        };
        add(&mut open, Some(own));
        let Some(items) = items else { continue };
        if items.is_shared() {
            let key = Shared::Items(items.id());
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

/// The error for a number the system refused the memory to build or read for `op`.
fn refused(op: &'static str, e: TooLarge) -> KernelError {
    KernelError::NumberTooLarge { op, bits: e.bits }
}

/// An optional `-` and decimal digits.
fn read_int(s: &str) -> Result<Option<BigInt>, TooLarge> {
    let (sign, digits) = signed(s);
    Ok(read_decimal(digits)?.map(|n| BigInt::from_biguint(sign, n)))
}

/// The sign of a text and the rest of it after an optional `-`.
fn signed(s: &str) -> (Sign, &str) {
    match s.strip_prefix('-') {
        Some(rest) => (Sign::Minus, rest),
        None => (Sign::Plus, s),
    }
}

/// What `String` writes for a `rat`, `3r` or `-1r/3r`, or the same without the `r`s, or a
/// decimal with digits on both sides of the point, such as `0.25` or `-0.5`; [`TooLarge`] when
/// the system refuses the memory for reading it, asked before anything is built.
///
/// `String` writes a `rat` in lowest terms, the sign on the numerator only, a denominator only
/// when it is above 1, and no leading zero, so `1r/-3r`, `-0r`, `03r`, `2r/4r` and `3r/1r` are
/// read as nothing, and so are `1r/3`, `1/3r`, where only one part drops its `r`. A zero
/// denominator is not in lowest terms either. A decimal's digits are any digits.
fn read_rat(s: &str) -> Result<Option<Rat>, TooLarge> {
    let (sign, body) = signed(s);
    let digits = |t: &str| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit());
    if let Some((whole, frac)) = body.split_once('.') {
        if !digits(whole) || !digits(frac) {
            return Ok(None);
        }
        return Rat::decimal_parts(sign, whole, frac, None).map(Some);
    }
    let (num, den) = match body.split_once('/') {
        None => (body.strip_suffix('r').unwrap_or(body), None),
        Some((n, d)) => match (n.strip_suffix('r'), d.strip_suffix('r')) {
            (Some(n), Some(d)) => (n, Some(d)),
            (None, None) => (n, Some(d)),
            _ => return Ok(None),
        },
    };
    let printed = |t: &str| digits(t) && (t == "0" || !t.starts_with('0'));
    if !printed(num) || sign == Sign::Minus && num == "0" || den.is_some_and(|d| !printed(d)) {
        return Ok(None);
    }
    // Complexity tradeoff: the memory asked for is 48 bits for each digit of the two parts, a
    // measured bound, not a proved one, on reading both and the gcd that checks lowest terms
    // (the half gcd, `num::fast::gcd`): the peak heap was at most 28.3 bits per digit (8.52
    // times the `3.32 n` bits of the two numbers) over texts of 2^12 to 2^18 digits on each
    // side, nines over a one and sevens, and a power of 2 over a power of 3, and 31.3 with
    // glibc's default mmap threshold (2026-11-06). It matches the ask of reading an integer,
    // whose reading by halves needs more. So a text needing
    // less is refused when the free memory lies between the two, and none aborts. Tested by
    // `reading_a_long_number_from_a_string_is_refused_when_memory_is_short` (COMPLEXITY.md
    // K30). A complete solution would ask each allocation of the reading for its own memory.
    room(BigUint::from(num.len() + den.map_or(0, str::len)) * 48u32)?;
    let read = |t: &str| read_decimal(t).map(|n| n.expect("checked digits"));
    let num = BigInt::from_biguint(sign, read(num)?);
    Ok(match den {
        None => Some(Rat::int(num)),
        Some(den) => Rat::in_lowest_terms(num, read(den)?.into()),
    })
}

/// What `String` writes for a float, correctly rounded: `-0.5`, `1.0e300`, `inf`, `nan`;
/// an integer such as `3` is read too.
fn read_f64(s: &str) -> Option<f64> {
    let body = s.strip_prefix('-').unwrap_or(s);
    if body == "inf" || body == "nan" {
        return s.parse().ok();
    }
    float_text(body).then(|| read_f64_ieee(s))?
}

/// [`read_f64`] at `f32`.
fn read_f32(s: &str) -> Option<f32> {
    let body = s.strip_prefix('-').unwrap_or(s);
    if body == "inf" || body == "nan" {
        return s.parse().ok();
    }
    float_text(body).then(|| read_f32_ieee(s))?
}

/// Whether `body` is digits with an optional fraction and exponent, as `String` writes a
/// finite float without its sign.
fn float_text(body: &str) -> bool {
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
    mantissa_ok && exp_ok
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Family;

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
