//! The bit words (step L1.39a, DESIGN.md sec:domains): `bitAnd`, `bitOr`, `bitXor`,
//! `bitNot`, `shl`, `shr`, `popCount`, `leadingZeros`, `trailingZeros`, `rotl`, `rotr` and
//! `f64Bits`, on the unbounded `int`, and the integer machine operations (step L1.39f,
//! DESIGN.md sec:linalg, machine operations) `mulHi`, `bitReverse`, `byteSwap`, `pdep`, `pext`,
//! `funnelShl` and `funnelShr`, each computed by its definition.
//!
//! Every operand but the `x` of `shl` and `shr` is a non-negative int. The operands a word with
//! a width `w` reads as `w` digits lie in `0 ..< 2^w`: the `x` of the words with one argument
//! besides the width, the `x` of the rotations, both factors of `mulHi` and both halves of a
//! funnel shift. The `k` of a funnel shift lies in `0 ..< w`, and the width of `byteSwap` is a
//! multiple of 8. The checker rejects a call that breaks this where it can show it; here a
//! value outside the domain is a type error. No other shift count is masked: `shl(1, 64)` is
//! `2^64`, and `rotl` turns by `k mod w`.
//!
//! An operation on machine integers whose result fits is computed in machine arithmetic. Past
//! that, the shifts, `bitNot`, the rotations, `mulHi` and the funnel shifts are products,
//! quotients, remainders and sums of powers of two, which [`Rat`] keeps as exponents, so
//! `shl(1, 2 ^ 40)` costs a few words. The digit-wise words, `bitAnd`, `bitOr`, `bitXor`,
//! `popCount`, `leadingZeros`, `trailingZeros`, `bitReverse`, `byteSwap`, `pdep` and `pext`,
//! build their operands' digits, asking the system for the memory first, as
//! [`Rat::to_integer`] does; `bitReverse` and `byteSwap` build only the digits of `x` and keep
//! the power of two that places them, and `pdep` and `pext` loop over the one digits of
//! `mask`, O(digits of `mask`).

use std::borrow::Cow;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use crate::KernelError;
use crate::num::{Rat, TooLarge};
use crate::term::Prim;
use crate::value::Value;

/// Whether `p` is a bit word or an integer machine operation.
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
            | Prim::MulHi
            | Prim::BitReverse
            | Prim::ByteSwap
            | Prim::Pdep
            | Prim::Pext
            | Prim::FunnelShl
            | Prim::FunnelShr
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
                p.written(),
                shown(args)
            )));
        }
    };
    domain(p, &ns)?;
    big(p, &ns).map_err(|e| too_large(p, e))
}

fn too_large(p: Prim, e: TooLarge) -> KernelError {
    KernelError::NumberTooLarge {
        op: p.written(),
        need: e,
    }
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
        p.written()
    ))
}

/// The type error for a width of `byteSwap` that is not a multiple of 8.
fn not_bytes(p: Prim) -> KernelError {
    KernelError::Type(format!(
        "`{}` needs `width` a multiple of 8, and it is not",
        p.written()
    ))
}

/// The names of `p`'s parameters, in order.
pub fn params(p: Prim) -> &'static [&'static str] {
    match p {
        Prim::BitAnd | Prim::BitOr | Prim::BitXor => &["a", "b"],
        Prim::Shl | Prim::Shr => &["x", "k"],
        Prim::PopCount | Prim::F64Bits => &["x"],
        Prim::BitNot
        | Prim::LeadingZeros
        | Prim::TrailingZeros
        | Prim::BitReverse
        | Prim::ByteSwap => &["x", "width"],
        Prim::MulHi => &["a", "b", "width"],
        Prim::Pdep | Prim::Pext => &["x", "mask"],
        Prim::FunnelShl | Prim::FunnelShr => &["hi", "lo", "k", "width"],
        _ => &["x", "k", "width"],
    }
}

/// Whether `p` takes a width, its last argument.
pub fn has_width(p: Prim) -> bool {
    matches!(
        p,
        Prim::BitNot
            | Prim::LeadingZeros
            | Prim::TrailingZeros
            | Prim::Rotl
            | Prim::Rotr
            | Prim::MulHi
            | Prim::BitReverse
            | Prim::ByteSwap
            | Prim::FunnelShl
            | Prim::FunnelShr
    )
}

/// The positions of `p`'s operands that lie in `0 ..< 2^width`: the first of a word with a
/// width, and the first two of `mulHi`, `funnelShl` and `funnelShr`; none for a word with no
/// width.
pub fn below_two_pow_width(p: Prim) -> &'static [usize] {
    match p {
        Prim::MulHi | Prim::FunnelShl | Prim::FunnelShr => &[0, 1],
        _ if has_width(p) => &[0],
        _ => &[],
    }
}

/// The position of `p`'s operand that lies in `0 ..< width`: the `k` of `funnelShl` and
/// `funnelShr`.
pub fn below_width(p: Prim) -> Option<usize> {
    matches!(p, Prim::FunnelShl | Prim::FunnelShr).then_some(2)
}

/// Whether `p`'s width is a multiple of 8: that of `byteSwap`.
pub fn whole_bytes(p: Prim) -> bool {
    p == Prim::ByteSwap
}

/// Checks the domain of each operand: every one non-negative but the `x` of `shl` and `shr`,
/// those [`below_two_pow_width`] names below `2^w`, the `k` of a funnel shift below `w`, and
/// the width of `byteSwap` a multiple of 8.
fn domain(p: Prim, ns: &[Cow<'_, Rat>]) -> Result<(), KernelError> {
    let names = params(p);
    let shift = matches!(p, Prim::Shl | Prim::Shr);
    for (i, (n, param)) in ns.iter().zip(names).enumerate() {
        if n.is_negative() && !(shift && i == 0) {
            return Err(outside(p, param, "int[0..]", "negative"));
        }
    }
    if !has_width(p) {
        return Ok(());
    }
    let w = ns.last().expect("a word with a width has arguments");
    if whole_bytes(p)
        && !w
            .rem_euclid(&Rat::int(BigInt::from(8)))
            .map_err(|e| too_large(p, e))?
            .is_zero()
    {
        return Err(not_bytes(p));
    }
    // `2^w` keeps its exponent, so this builds only the digits of `w`.
    let bound = two_pow(w).map_err(|e| too_large(p, e))?;
    for &i in below_two_pow_width(p) {
        if *ns[i] >= bound {
            return Err(outside(p, names[i], "int[0..<2^width]", "at least 2^width"));
        }
    }
    if let Some(i) = below_width(p)
        && *ns[i] >= **w
    {
        return Err(outside(p, names[i], "int[0..<width]", "at least width"));
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
    let mut v = [0i64; 4];
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
        if whole_bytes(p) && w % 8 != 0 {
            return Err(not_bytes(p));
        }
        for &i in below_two_pow_width(p) {
            if digits(v[i]) > w {
                return Err(outside(
                    p,
                    params(p)[i],
                    "int[0..<2^width]",
                    "at least 2^width",
                ));
            }
        }
        if let Some(i) = below_width(p)
            && v[i] >= w
        {
            return Err(outside(p, params(p)[i], "int[0..<width]", "at least width"));
        }
    }
    if let Some(n) = machine_op(p, v) {
        return Ok(Some(match i64::try_from(n) {
            Ok(n) => Value::Int(n),
            Err(_) => Value::int(BigInt::from(n)),
        }));
    }
    let [x, y, z, _] = v;
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

/// The integer machine operations on machine integers, every operand non-negative and in its
/// domain, in `u128` arithmetic; `None` for another word, or for a width past what that
/// arithmetic holds.
fn machine_op(p: Prim, [x, y, z, t]: [i64; 4]) -> Option<u128> {
    // Every operand is non-negative, so each conversion is exact.
    let u = |n: i64| n as u128;
    Some(match p {
        // Both factors are below `2^63`, so the product fits, and a shift past 127 places
        // leaves 0 as the shift by 127 does.
        Prim::MulHi => (u(x) * u(y)) >> z.min(127),
        // Digit `i` goes to `w - 1 - i`: to `127 - i` in the whole word, then down.
        Prim::BitReverse if y <= 128 => match y {
            0 => 0,
            _ => u(x).reverse_bits() >> (128 - y),
        },
        // Byte `j` goes to `w / 8 - 1 - j`: to `15 - j` in the whole word, then down.
        Prim::ByteSwap if y <= 128 => match y {
            0 => 0,
            _ => u(x).swap_bytes() >> (128 - y),
        },
        Prim::Pdep => u128::from(deposit(x as u64, y as u64)),
        Prim::Pext => u128::from(extract(x as u64, y as u64)),
        // `1 <= w <= 64` and `k < w`, so no shift reaches 128 places.
        Prim::FunnelShl | Prim::FunnelShr if t <= 64 => {
            let (hi, lo, k, w) = (u(x), u(y), z as u32, t as u32);
            let all = (1u128 << w) - 1;
            match (p, k) {
                (Prim::FunnelShl, 0) => hi,
                (_, 0) => lo,
                (Prim::FunnelShl, _) => ((hi << k) | (lo >> (w - k))) & all,
                _ => ((lo >> k) | (hi << (w - k))) & all,
            }
        }
        _ => return None,
    })
}

/// `pdep(x, mask)` on one machine word: digit `j` of `x` goes to the `j`-th lowest one digit
/// of `mask`. A loop over the one digits of `mask`, at most 64 steps.
fn deposit(x: u64, mut mask: u64) -> u64 {
    let (mut out, mut j) = (0, 0);
    while mask != 0 {
        let low = mask.isolate_lowest_one();
        if (x >> j) & 1 == 1 {
            out |= low;
        }
        j += 1;
        mask &= mask - 1;
    }
    out
}

/// `pext(x, mask)` on one machine word: the digit of `x` at the `j`-th lowest one digit of
/// `mask` goes to digit `j`. A loop over the one digits of `mask`, at most 64 steps.
fn extract(x: u64, mut mask: u64) -> u64 {
    let (mut out, mut j) = (0, 0);
    while mask != 0 {
        let low = mask.isolate_lowest_one();
        if x & low != 0 {
            out |= 1 << j;
        }
        j += 1;
        mask &= mask - 1;
    }
    out
}

/// `pdep` on the low 32-digit words `xs` of `x`, at least the `popCount(mask)` low digits of
/// `x`: the loop of [`deposit`] over the 32-digit words of `mask`, O(digits of `mask`).
fn deposit_big(xs: &[u32], mask: &BigUint) -> BigUint {
    let digit = |j: u64| {
        xs.get((j / 32) as usize)
            .is_some_and(|w| (w >> (j % 32)) & 1 == 1)
    };
    let mut j = 0u64;
    let out: Vec<u32> = mask
        .iter_u32_digits()
        .map(|mut m| {
            let mut kept = 0;
            while m != 0 {
                let low = m.isolate_lowest_one();
                if digit(j) {
                    kept |= low;
                }
                j += 1;
                m &= m - 1;
            }
            kept
        })
        .collect();
    BigUint::new(out)
}

/// `pext` on the low 32-digit words `xs` of `x`, at least as many as `mask` has: the loop of
/// [`extract`] over the 32-digit words of `mask`, O(digits of `mask`).
fn extract_big(xs: &[u32], mask: &BigUint) -> BigUint {
    let ones = mask.count_ones();
    let mut out = vec![0u32; ones.div_ceil(32) as usize];
    let mut j = 0u64;
    for (i, mut m) in mask.iter_u32_digits().enumerate() {
        let xw = xs.get(i).copied().unwrap_or(0);
        while m != 0 {
            let low = m.isolate_lowest_one();
            if xw & low != 0 {
                out[(j / 32) as usize] |= 1 << (j % 32);
            }
            j += 1;
            m &= m - 1;
        }
    }
    BigUint::new(out)
}

/// The 32-digit words of the int `x >= 0` that hold its `k` low digits, `ceil(k / 32)` of them
/// or fewer; the digits of the top word above `k` are kept, and [`deposit_big`] and
/// [`extract_big`] read none of them.
//
// Complexity tradeoff: the standard reduction, `x mod 2^k` by the general remainder
// (`Rat::rem_euclid`), builds `2^k` and divides by it, num-bigint's division below 512 words
// and a Newton reciprocal above: O(M(k)) time, and its bytes jump where the method changes, so
// `pdep` and `pext` on random masks of 16,384 and 131,072 digits allocated 2,941,600 and
// 43,977,920 bytes, 15.0 times, above the n log n limit 10.7 (PDEP-bytes). A built `x` needs
// no division: its low words are copied, O(k) time and bytes, at most the width of `mask`,
// which is already built. Only an `x` kept as powers (`3 ^ 10 ^ 6`) still takes the
// remainder, which builds no more of `x` than its `k` low digits. Nothing is given up; both
// give the same words. Tested by `l01_39f_int_machine_ops::scaling::
// pdep_and_pext_are_linear_in_the_digits_of_the_mask` and `reference::
// pdep_and_pext_agree_on_wide_and_kept_operands` (COMPLEXITY.md, the `zed_kernel::bits` row).
fn low_words(x: &Rat, k: u64) -> Result<Vec<u32>, TooLarge> {
    match x.integer_factors() {
        (built, []) => Ok(built
            .magnitude()
            .iter_u32_digits()
            .take(k.div_ceil(32) as usize)
            .collect()),
        _ => {
            let low = x.rem_euclid(&two_pow(&Rat::int(BigInt::from(k)))?)?;
            Ok(low.to_integer()?.magnitude().to_u32_digits())
        }
    }
}

/// The words on exact numbers, every operand in its domain.
fn big(p: Prim, ns: &[Cow<'_, Rat>]) -> Result<Value, TooLarge> {
    let int = |b: BigInt| Value::int(b);
    let built = |r: &Rat| r.to_integer().map(|b| b.magnitude().clone());
    let count = |n: u64| Rat::int(BigInt::from(n));
    // `n * 2^(w - d)`: `d` digits built, placed at the top of `w` digits by a kept power.
    let at_top = |n: BigUint, w: &Rat, d: u64| -> Result<Value, TooLarge> {
        let place = two_pow(&w.sub(&count(d))?)?;
        Ok(Value::integer(Rat::int(BigInt::from(n)).mul(&place)?))
    };
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
        Prim::Shl => Value::integer(ns[0].mul(&two_pow(&ns[1])?)?),
        Prim::Shr => Value::integer(ns[0].div_euclid(&two_pow(&ns[1])?)?),
        Prim::MulHi => Value::integer(ns[0].mul(&ns[1])?.div_euclid(&two_pow(&ns[2])?)?),
        Prim::BitReverse => {
            let x = built(&ns[0])?;
            if x.is_zero() {
                return Ok(Value::Int(0));
            }
            // The `d` digits of `x` reversed, its top digit 1 going to digit 0, then moved up
            // `w - d` places, so digit `i` lands at `w - 1 - i`.
            let d = x.bits();
            let mut words = x.to_u32_digits();
            words.reverse();
            for w in &mut words {
                *w = w.reverse_bits();
            }
            let spare = 32 * words.len() as u64 - d;
            at_top(BigUint::new(words) >> spare, &ns[1], d)?
        }
        Prim::ByteSwap => {
            let x = built(&ns[0])?;
            if x.is_zero() {
                return Ok(Value::Int(0));
            }
            // The `b` bytes of `x` reversed, then moved up to the top of the `w / 8` bytes.
            let bytes = x.to_bytes_le();
            at_top(
                BigUint::from_bytes_be(&bytes),
                &ns[1],
                8 * bytes.len() as u64,
            )?
        }
        Prim::Pdep => {
            let mask = built(&ns[1])?;
            // Only the `popCount(mask)` low digits of `x` are read; the rest are never built.
            let xs = low_words(&ns[0], mask.count_ones())?;
            int(BigInt::from(deposit_big(&xs, &mask)))
        }
        Prim::Pext => {
            let mask = built(&ns[1])?;
            let xs = low_words(&ns[0], mask.bits())?;
            int(BigInt::from(extract_big(&xs, &mask)))
        }
        Prim::FunnelShl | Prim::FunnelShr => {
            let (hi, lo, k, w) = (&ns[0], &ns[1], &ns[2], &ns[3]);
            // `0 <= k < w`. The high `w` digits of `(hi * 2^w + lo) * 2^k` are
            // `hi * 2^k + lo div 2^(w - k)`, and the low `w` digits of `(hi * 2^w + lo) div
            // 2^k` are `hi * 2^(w - k) + lo div 2^k`, each taken mod `2^w`.
            let rest = w.sub(k)?;
            let (up, down): (&Rat, &Rat) = match p {
                Prim::FunnelShl => (k, &rest),
                _ => (&rest, k),
            };
            let joined = hi
                .mul(&two_pow(up)?)?
                .add(&lo.div_euclid(&two_pow(down)?)?)?;
            Value::integer(joined.rem_euclid(&two_pow(w)?)?)
        }
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
            let low = x.rem_euclid(&low_width)?.mul(&two_pow(&r)?)?;
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

    #[test]
    fn the_machine_operations_agree_on_both_paths() {
        for w in 0..=6i64 {
            for a in 0..1i64 << w {
                if w % 8 == 0 {
                    assert_eq!(
                        run(Prim::ByteSwap, &[a, w]),
                        run_big(Prim::ByteSwap, &[a, w])
                    );
                }
                assert_eq!(
                    run(Prim::BitReverse, &[a, w]),
                    run_big(Prim::BitReverse, &[a, w])
                );
                for b in 0..1i64 << w {
                    assert_eq!(
                        run(Prim::MulHi, &[a, b, w]),
                        run_big(Prim::MulHi, &[a, b, w])
                    );
                    assert_eq!(run(Prim::Pdep, &[a, b]), run_big(Prim::Pdep, &[a, b]));
                    assert_eq!(run(Prim::Pext, &[a, b]), run_big(Prim::Pext, &[a, b]));
                    for k in 0..w {
                        for p in [Prim::FunnelShl, Prim::FunnelShr] {
                            let args = [a, b, k, w];
                            assert_eq!(run(p, &args), run_big(p, &args), "{p:?} {args:?}");
                        }
                    }
                }
            }
        }
        // `byteSwap` at 8 and 16 digits, where its width allows it.
        for (x, w) in [(0, 8), (0xab, 8), (0x0102, 16), (0x00ff, 16), (0x8000, 16)] {
            assert_eq!(
                run(Prim::ByteSwap, &[x, w]),
                run_big(Prim::ByteSwap, &[x, w])
            );
        }
    }

    #[test]
    fn the_machine_operations_refuse_operands_outside_their_domains() {
        let err = |p: Prim, args: &[i64]| {
            let vs: Vec<Value> = args.iter().map(|&a| Value::Int(a)).collect();
            match word(p, &vs) {
                Err(KernelError::Type(m)) => m,
                other => panic!("{p:?} {args:?} gave {other:?}"),
            }
        };
        assert_eq!(
            err(Prim::ByteSwap, &[1, 12]),
            "`byteSwap` needs `width` a multiple of 8, and it is not"
        );
        assert_eq!(
            err(Prim::FunnelShl, &[1, 2, 8, 8]),
            "`funnelShl` needs `k` in int[0..<width], and it is at least width"
        );
        assert_eq!(
            err(Prim::MulHi, &[1, 256, 8]),
            "`mulHi` needs `b` in int[0..<2^width], and it is at least 2^width"
        );
        assert_eq!(
            err(Prim::FunnelShr, &[256, 0, 0, 8]),
            "`funnelShr` needs `hi` in int[0..<2^width], and it is at least 2^width"
        );
        assert_eq!(
            err(Prim::Pdep, &[-1, 3]),
            "`pdep` needs `x` in int[0..], and it is negative"
        );
    }
}
