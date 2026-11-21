//! `floatMod(x, m)`, the remainder of a float (DESIGN.md sec:domains, "`floatMod`, the remainder
//! of a float"; QUESTIONS A174, author, 2026-11-21: "add `floatMod(x, m)` which gives the
//! floating point residue in `[0..<m]` after dividing by `m`"; plan row FLOAT-floatMod). For a
//! finite `m > 0` the result is the float of `[0.0, m)` nearest the exact residue
//! `ρ = x − m·⌊x/m⌋`, a tie to the even one. The choice among the definitions languages use, with
//! each candidate measured bit-exact against the exact residue on every pair of `f16` and of
//! `bf16` values, is zed-impl `docs/mod-study.md` (candidate (e), score 9 of 10).

use std::ops::{Add, Rem};

/// The float formats `floatMod` is built for in the kernel. `f16` and `bf16` are not yet values
/// of the kernel (step L1.18a); each implements this trait when it is.
pub trait Residue: Copy + PartialOrd + Add<Output = Self> + Rem<Output = Self> {
    /// `+0.0`.
    const ZERO: Self;
    /// IEEE 754-2019 5.3.1 `nextDown`: the greatest float below `self`.
    fn next_down(self) -> Self;
    /// Whether `self` is neither infinite nor NaN.
    fn finite(self) -> bool;
}

impl Residue for f64 {
    const ZERO: f64 = 0.0;
    fn next_down(self) -> f64 {
        f64::next_down(self)
    }
    fn finite(self) -> bool {
        self.is_finite()
    }
}

impl Residue for f32 {
    const ZERO: f32 = 0.0;
    fn next_down(self) -> f32 {
        f32::next_down(self)
    }
    fn finite(self) -> bool {
        self.is_finite()
    }
}

/// `floatMod(x, m)` for a finite `m > 0` and any `x`: the float of `[0.0, m)` nearest
/// `ρ = x − m·⌊x/m⌋`, ties to even; NaN for an infinite or NaN `x`. Three operations, each exact
/// or rounded to nearest, since Zed has no directed rounding (QUESTIONS A173):
/// `f = fmod(x, m)`; `f + 0.0` where `f >= 0`; else `s = RN(f + m)`, and `s` where `s < m`,
/// `nextDown(m)` where `s == m`.
///
/// The caller's modulus is the checker's to prove (DESIGN.md sec:domains: "A modulus that may
/// be NaN, infinite or at most `0.0` is refused as `mod`'s is"); [`float_mod_total`] is the
/// kernel's total form.
///
/// Proof, for finite `x` and finite `m > 0`, p the format's significand digits and Q(y) the
/// value of the last significand digit of `y` (the least subnormal for a subnormal or zero `y`);
/// the same proof, with the measurements, is DESIGN.md's at the definition.
/// (1) `x % m` is `fmod(x, m)` exactly. Rust's `%` on floats is LLVM's `frem`, whose LangRef
///     semantics (llvm.org/docs/LangRef.html, "'frem' Instruction", read 2026-11-21) are: "The
///     value produced is the floating-point remainder of the two operands. This is the same
///     output as a libm 'fmod' function, but without any possibility of setting errno." (Rust's
///     own text, "computed as: x - (x / y).trunc() * y", describes the value, not a rounded
///     computation: in f64 `1e17 % 3.0` is 1 while that formula evaluated in floats gives 0,
///     docs/mod-study.md, Local runs.) C11 F.10.7.1 (n1570, port70.net/~nsz/c/c11/n1570.html,
///     read 2026-11-21): "the returned value is exact and is independent of the current rounding
///     direction mode". Why it is exact: `x` and `m` are integer multiples of q = min(Q(x), Q(m)),
///     so r = x − m·trunc(x/m) = k·q; |r| ≤ |x| and |r| < m; if q = Q(x), |k|·q ≤ |x| < 2^p·Q(x)
///     gives |k| < 2^p, and if q = Q(m), |k|·q < m < 2^p·Q(m) does; every k·q with |k| < 2^p and
///     |k·q| below the finite `m` is a float of the format, so r is returned unrounded. So
///     f ≡ x (mod m), |f| < m, and `f` has the sign of `x` (C11 7.12.10.1).
/// (2) Where f > 0, x > 0, so trunc(x/m) = ⌊x/m⌋ and ρ = f. Where f is `±0.0`, `m` divides `x`
///     and ρ = 0. `f + 0.0` is exact, and is `+0.0` for f = `-0.0` under rounding to nearest
///     (IEEE 754-2019 6.3: "When the sum of two operands with opposite signs ... is exactly zero,
///     the sign of that sum ... shall be +0" in all rounding-direction attributes but
///     roundTowardNegative; the full citation is at zed-kernel `eval.rs`, fn `prim_on`,
///     `Prim::Sqrt`). So the result is ρ, in `[0.0, m)`.
/// (3) Where f < 0, x < 0 and `m` does not divide `x`, so ⌊x/m⌋ = trunc(x/m) − 1 and
///     ρ = f + m, with 0 < ρ < m. ρ is a multiple of q, so ρ ≥ q > 0; `q` and `m` are floats and
///     rounding to nearest is monotone, so q ≤ s = RN(ρ) ≤ m.
/// (4) Where s < m, `s` is the float nearest ρ and lies in `[0.0, m)`, so it is the float of
///     `[0.0, m)` nearest ρ, its tie broken to even by the rounding.
/// (5) Where s = m, ρ rounds to `m` and not to the float m − u, u = m − nextDown(m), so
///     ρ ≥ m − u/2; the greatest float of `[0.0, m)` is nextDown(m), exact (IEEE 754-2019 5.3.1)
///     and at least `0.0` since m > 0; for ρ in `[m − u/2, m)` it is the float of `[0.0, m)`
///     nearest ρ, its error in `[u/2, u)`.
/// (6) An infinite `x` gives f = NaN (C11 F.10.7.1: "fmod(x, y) returns a NaN ... for x
///     infinite"), and a NaN `x` gives f = NaN. Then `f >= 0` is false, s = NaN + m is NaN,
///     `s == m` is false, and the routine returns `s`, the NaN. The test is `s == m`, not
///     `!(s < m)`, so that a NaN never becomes `nextDown(m)`.
///
/// Checked: tests `l01_18_scalar_interpreter::float_mod` (the probe set of docs/mod-study.md,
/// the special values, and random `f64` and `f32` pairs against the exact `rat` residue,
/// nearest in `[0.0, m)`); the exhaustive check over every `f16` and `bf16` pair is in the
/// study and waits for those formats. Cost: O(1), one `fmod` (the C library's, a loop of
/// O(e_x − e_m) shift-subtract steps over the exponent difference, at most about 2100 for
/// f64), one add, two compares.
pub fn float_mod<F: Residue>(x: F, m: F) -> F {
    let f = x % m;
    if f >= F::ZERO {
        return f + F::ZERO;
    }
    let s = f + m;
    if s == m { m.next_down() } else { s }
}

/// The kernel's total `floatMod`: [`float_mod`] where `m` is finite and greater than 0, NaN for
/// any other `m`, which a checked program never passes (the checker refuses a modulus it does
/// not prove finite and greater than `0.0`).
pub fn float_mod_total<F: Residue>(x: F, m: F, nan: F) -> F {
    match m.finite() && m > F::ZERO {
        true => float_mod(x, m),
        false => nan,
    }
}
