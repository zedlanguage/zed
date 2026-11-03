//! The bit words (step L1.39a, DESIGN.md sec:domains): `bitAnd`, `bitOr`, `bitXor`,
//! `bitNot`, `shl`, `shr`, `popCount`, `leadingZeros`, `trailingZeros`, `rotl`, `rotr` and
//! `f64Bits`, on the unbounded `int`.
//!
//! Every operand but the `x` of `shl` and `shr` is a non-negative int, and the `x` of a word
//! that takes a width `w` lies in `0 ..< 2^w`. The checker rejects a call that breaks this
//! where it can show it; here a value outside the domain is a type error. No shift count is
//! masked: `shl(1, 64)` is `2^64`.
//!
//! An operation on machine integers whose result fits is computed in machine arithmetic. Past
//! that, the shifts, `bitNot` and the rotations are products, quotients, remainders and sums of
//! powers of two, which [`Rat`] keeps as exponents, so `shl(1, 2 ** 40)` costs a few words. The
//! digit-wise words, `bitAnd`, `bitOr`, `bitXor`, `popCount`, `leadingZeros` and
//! `trailingZeros`, build their operands' digits, asking the system for the memory first, as
//! [`Rat::to_integer`] does.

use std::borrow::Cow;

use num_bigint::BigInt;
use num_traits::One;

use crate::KernelError;
use crate::num::{Rat, TooLarge};
use crate::term::Prim;
use crate::value::Value;

/// The surface name of a bit word.
fn name(p: Prim) -> &'static str {
    match p {
        Prim::BitAnd => "bitAnd",
        Prim::BitOr => "bitOr",
        Prim::BitXor => "bitXor",
        Prim::BitNot => "bitNot",
        Prim::Shl => "shl",
        Prim::Shr => "shr",
        Prim::PopCount => "popCount",
        Prim::LeadingZeros => "leadingZeros",
        Prim::TrailingZeros => "trailingZeros",
        Prim::Rotl => "rotl",
        Prim::Rotr => "rotr",
        _ => "f64Bits",
    }
}

/// Whether `p` is a bit word.
pub fn is_bit_word(p: Prim) -> bool {
    matches!(
        p,
        Prim::BitAnd
            | Prim::BitOr
            | Prim::BitXor
            | Prim::BitNot
            | Prim::Shl
            | Prim::Shr
            | Prim::PopCount
            | Prim::LeadingZeros
            | Prim::TrailingZeros
            | Prim::Rotl
            | Prim::Rotr
            | Prim::F64Bits
    )
}

/// `p(args)` for a bit word `p`, its arguments in parameter order with the width last.
pub fn word(p: Prim, args: &[Value]) -> Result<Value, KernelError> {
    if p == Prim::F64Bits {
        return match args {
            [Value::Float(f)] => Ok(Value::int(BigInt::from(f.get().to_bits()))),
            _ => Err(KernelError::Type(format!(
                "`f64Bits` takes an f64, given {}",
                shown(args)
            ))),
        };
    }
    if let Some(v) = small(p, args)? {
        return Ok(v);
    }
    let ns: Vec<Cow<'_, Rat>> = match args.iter().map(Value::as_integer).collect() {
        Some(ns) => ns,
        None => {
            return Err(KernelError::Type(format!(
                "`{}` takes ints, given {}",
                name(p),
                shown(args)
            )));
        }
    };
    domain(p, &ns)?;
    big(p, &ns).map_err(|e| KernelError::NumberTooLarge {
        op: name(p),
        bits: e.bits,
    })
}

fn shown(args: &[Value]) -> String {
    let parts: Vec<String> = args
        .iter()
        .map(|v| format!("`{}`", v.kind_type()))
        .collect();
    parts.join(", ")
}

/// A type error for an operand outside its domain: which parameter, what it needs, and where
/// the value it was given lies, not the value, which may be too large to print.
fn outside(p: Prim, param: &str, needs: &str, is: &str) -> KernelError {
    KernelError::Type(format!(
        "`{}` needs `{param}` in {needs}, and it is {is}",
        name(p)
    ))
}

/// The names of `p`'s parameters, in order.
pub fn params(p: Prim) -> &'static [&'static str] {
    match p {
        Prim::BitAnd | Prim::BitOr | Prim::BitXor => &["a", "b"],
        Prim::Shl | Prim::Shr => &["x", "k"],
        Prim::PopCount | Prim::F64Bits => &["x"],
        Prim::BitNot | Prim::LeadingZeros | Prim::TrailingZeros => &["x", "width"],
        _ => &["x", "k", "width"],
    }
}

/// Whether `p` takes a width, its last argument.
pub fn has_width(p: Prim) -> bool {
    matches!(
        p,
        Prim::BitNot | Prim::LeadingZeros | Prim::TrailingZeros | Prim::Rotl | Prim::Rotr
    )
}

/// Checks the domain of each operand: every one non-negative but the `x` of `shl` and `shr`,
/// and the `x` of a word with a width below `2^w`.
fn domain(p: Prim, ns: &[Cow<'_, Rat>]) -> Result<(), KernelError> {
    let shift = matches!(p, Prim::Shl | Prim::Shr);
    for (i, (n, param)) in ns.iter().zip(params(p)).enumerate() {
        if n.is_negative() && !(shift && i == 0) {
            return Err(outside(p, param, "int[0..]", "negative"));
        }
    }
    if has_width(p) {
        let w = ns.last().expect("a word with a width has arguments");
        // `2^w` keeps its exponent, so this builds only the digits of `w`.
        let bound = two_pow(w).map_err(|e| KernelError::NumberTooLarge {
            op: name(p),
            bits: e.bits,
        })?;
        if *ns[0] >= bound {
            return Err(outside(
                p,
                "x",
                "int[0..<2 ** width]",
                "at least 2 ** width",
            ));
        }
    }
    Ok(())
}

/// `2^w`, kept as an exponent, or [`TooLarge`] when the system refuses the memory for `w`'s
/// digits.
fn two_pow(w: &Rat) -> Result<Rat, TooLarge> {
    let e = w.to_integer()?;
    Rat::int(BigInt::from(2)).pow(e.magnitude())
}

/// Whether the int `x` lies in `0 ..< 2^w` for the int `w >= 0`: the domain of the `x` of a word
/// with a width. `false` when either is no int, `w` is negative, or the system refuses the
/// memory for the digits of `w`.
pub fn below_two_pow(x: &Value, w: &Value) -> bool {
    match (x.as_integer(), w.as_integer()) {
        (Some(x), Some(w)) if !w.is_negative() && !x.is_negative() => {
            two_pow(&w).is_ok_and(|bound| *x < bound)
        }
        _ => false,
    }
}

/// The words on machine integers whose result fits, or `None` to take the exact path. A
/// domain error is found here when every operand is a machine integer.
fn small(p: Prim, args: &[Value]) -> Result<Option<Value>, KernelError> {
    let mut v = [0i64; 3];
    for (slot, a) in v.iter_mut().zip(args) {
        match a {
            Value::Int(n) => *slot = *n,
            _ => return Ok(None),
        }
    }
    if args.len() != params(p).len() {
        return Ok(None);
    }
    let shift = matches!(p, Prim::Shl | Prim::Shr);
    for (i, param) in params(p).iter().enumerate() {
        if v[i] < 0 && !(shift && i == 0) {
            return Err(outside(p, param, "int[0..]", "negative"));
        }
    }
    // The number of binary digits of a non-negative `x`.
    let digits = |x: i64| i64::from(64 - x.leading_zeros());
    if has_width(p) {
        let w = v[args.len() - 1];
        if digits(v[0]) > w {
            return Err(outside(
                p,
                "x",
                "int[0..<2 ** width]",
                "at least 2 ** width",
            ));
        }
    }
    let [x, y, z] = v;
    let out = match p {
        Prim::BitAnd => x & y,
        Prim::BitOr => x | y,
        Prim::BitXor => x ^ y,
        Prim::PopCount => i64::from(x.count_ones()),
        Prim::LeadingZeros => y - digits(x),
        Prim::TrailingZeros if x == 0 => y,
        Prim::TrailingZeros => i64::from(x.trailing_zeros()),
        // `2^w - 1 - x` fits when `w <= 63`.
        Prim::BitNot if y <= 63 => ((1i128 << y) - 1 - i128::from(x)) as i64,
        // `x * 2^k` with `k <= 62` fits in an `i128`; it is kept when it fits in an `i64`.
        Prim::Shl if y <= 62 => match i64::try_from(i128::from(x) << y) {
            Ok(n) => n,
            Err(_) => return Ok(None),
        },
        // An arithmetic shift is the Euclidean quotient by a positive power of two; past 63
        // places every `i64` gives 0 or -1, as the shift by 63 does.
        Prim::Shr => x >> y.min(63),
        Prim::Rotl | Prim::Rotr if z <= 63 => {
            if z == 0 {
                0
            } else {
                let r = y % z;
                let r = if p == Prim::Rotl { r } else { (z - r) % z };
                let (x, w, r) = (x as u64, z as u32, r as u32);
                let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
                // `x < 2^w`, so the low digits shifted out of the top are the high ones.
                let high = if r == 0 { 0 } else { x >> (w - r) };
                (((x << r) & mask) | high) as i64
            }
        }
        _ => return Ok(None),
    };
    Ok(Some(Value::Int(out)))
}

/// The words on exact numbers, every operand in its domain.
fn big(p: Prim, ns: &[Cow<'_, Rat>]) -> Result<Value, TooLarge> {
    let int = |b: BigInt| Value::int(b);
    let built = |r: &Rat| r.to_integer().map(|b| b.magnitude().clone());
    Ok(match p {
        Prim::BitAnd | Prim::BitOr | Prim::BitXor => {
            let (a, b) = (built(&ns[0])?, built(&ns[1])?);
            int(BigInt::from(match p {
                Prim::BitAnd => a & b,
                Prim::BitOr => a | b,
                _ => a ^ b,
            }))
        }
        Prim::PopCount => int(BigInt::from(built(&ns[0])?.count_ones())),
        Prim::LeadingZeros => {
            let digits = Rat::int(BigInt::from(built(&ns[0])?.bits()));
            Value::integer(ns[1].sub(&digits)?)
        }
        Prim::TrailingZeros => match built(&ns[0])?.trailing_zeros() {
            None => Value::integer(ns[1].clone().into_owned()),
            Some(t) => int(BigInt::from(t)),
        },
        Prim::BitNot => {
            let all = two_pow(&ns[1])?.sub(&Rat::int(BigInt::one()))?;
            Value::integer(all.sub(&ns[0])?)
        }
        Prim::Shl => Value::integer(ns[0].mul(&two_pow(&ns[1])?)),
        Prim::Shr => Value::integer(ns[0].div_euclid(&two_pow(&ns[1])?)?),
        _ => {
            let (x, k, w) = (&ns[0], &ns[1], &ns[2]);
            if w.is_zero() {
                return Ok(Value::Int(0));
            }
            let r = k.rem_euclid(w)?;
            let r = if p == Prim::Rotl {
                r
            } else {
                w.sub(&r)?.rem_euclid(w)?
            };
            // The `w - r` low digits move up `r` places; the `r` high digits move down to the
            // bottom.
            let low_width = two_pow(&w.sub(&r)?)?;
            let low = x.rem_euclid(&low_width)?.mul(&two_pow(&r)?);
            let high = x.div_euclid(&low_width)?;
            Value::integer(low.add(&high)?)
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(p: Prim, args: &[i64]) -> Value {
        let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
        word(p, &vs).unwrap()
    }

    /// The exact path, forced: every operand as a `Big`.
    fn run_big(p: Prim, args: &[i64]) -> Value {
        let ns: Vec<Cow<'_, Rat>> = args
            .iter()
            .map(|&a| Cow::Owned(Rat::int(BigInt::from(a))))
            .collect();
        big(p, &ns).unwrap()
    }

    #[test]
    fn the_machine_and_the_exact_paths_agree() {
        let cases: &[(Prim, &[i64])] = &[
            (Prim::BitAnd, &[12, 10]),
            (Prim::BitOr, &[12, 10]),
            (Prim::BitXor, &[12, 10]),
            (Prim::BitNot, &[5, 3]),
            (Prim::Shl, &[-3, 4]),
            (Prim::Shr, &[-17, 2]),
            (Prim::PopCount, &[255]),
            (Prim::LeadingZeros, &[1, 8]),
            (Prim::TrailingZeros, &[0, 8]),
            (Prim::TrailingZeros, &[40, 8]),
            (Prim::Rotl, &[8, 1, 4]),
            (Prim::Rotr, &[1, 1, 4]),
            (Prim::Rotl, &[0b1011, 7, 4]),
            (Prim::Rotl, &[i64::MAX, 1, 63]),
            (Prim::Rotl, &[0, 3, 0]),
        ];
        for &(p, args) in cases {
            assert_eq!(run(p, args), run_big(p, args), "{p:?} {args:?}");
        }
    }
}
