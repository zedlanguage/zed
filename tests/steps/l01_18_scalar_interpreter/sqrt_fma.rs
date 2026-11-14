//! `sqrt` and `fma` at `f64` and `f32` (row FLOAT-sqrt; DESIGN.md sec:linalg, the table of
//! machine operations; sec:reduction items 5 and 6; step L1.18a): `sqrt(x)` is the square root
//! correctly rounded, `fma(a, b, c)` the exact `a * b + c` rounded once, each the IEEE 754
//! result of its own format bit for bit. `sqrt(-0.0)` is `-0.0`, a negative operand gives the
//! NaN (sec:failure: "`#NaN` covers 0/0, inf - inf, sqrt of a negative"), and a NaN operand
//! gives the canonical NaN. The kernel, the counting machine and native code at both of
//! Cranelift's levels give the same bits; native code runs both at `f64` with no kernel call.
//! No back end fuses a multiply and an add the program wrote apart: `a * b + c` rounds twice
//! where `fma(a, b, c)` rounds once, and the two differ on the cases below in every back end.
//! The expected bits are written out, not computed by the code under test, and the random
//! cases are checked against exact integer arithmetic.

use num_bigint::BigInt;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zed_tests::instances::Rng;

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_26_type_resolution::sig;
use zed_tests::step_helpers::l01_36_cranelift::{kernel, planned};
use zedc::run::load;
use zedc::zir::memory;

/// The canonical NaN of binary64 and of binary32 (DESIGN.md sec:reduction).
const NAN64: u64 = 0x7FF8_0000_0000_0000;
const NAN32: u64 = 0x7FC0_0000;

pub(crate) fn f64v(b: u64) -> Term {
    lit(Value::float(f64::from_bits(b)))
}

fn f32v(b: u32) -> Term {
    lit(Value::float32(f32::from_bits(b)))
}

/// The bits of a float value.
fn bits(v: &Value) -> u64 {
    match v {
        Value::Float(x) => x.get().to_bits(),
        Value::Float32(x) => u64::from(x.get().to_bits()),
        other => panic!("{other} is no float"),
    }
}

pub(crate) fn sqrt(x: Term) -> Term {
    prim(Prim::Sqrt, vec![x])
}

pub(crate) fn fma(a: Term, b: Term, c: Term) -> Term {
    prim(Prim::Fma, vec![a, b, c])
}

/// `a * b + c`, written apart.
fn mul_add(a: Term, b: Term, c: Term) -> Term {
    prim(Prim::Add, vec![prim(Prim::Mul, vec![a, b]), c])
}

/// `f = params -> body; f(args)`: lowering keeps the function as a `lambda` node and an
/// `apply`, so its parameters are edges and no constant decides the result before the code
/// runs.
fn called(params: &[&str], body: Term, args: Vec<Term>) -> Term {
    let_("f", lam(params, body), app(var("f"), args))
}

/// The operation `op` on literals, and on the parameters of a function applied to them.
fn both_forms(op: fn(Vec<Term>) -> Term, args: Vec<Term>) -> [Term; 2] {
    const NAMES: [&str; 3] = ["a", "b", "c"];
    let names = &NAMES[..args.len()];
    let vars = names.iter().map(|n| var(n)).collect();
    [op(args.clone()), called(names, op(vars), args)]
}

/// The value of `t` by the kernel, by the counting machine and natively at both levels, all
/// equal bit for bit (a float value compares by its bits); native code makes no kernel call
/// when `inline`.
fn agreed(t: &Term, inline: bool) -> Value {
    let want = kernel(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    let (g, p) = planned(t);
    let (m, _) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(m, want, "{t} by the counting machine");
    for level in [OptLevel::None, OptLevel::Speed] {
        let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("{t}: {e}"));
        assert_eq!(o.value, want, "{t} at {level:?}");
        if inline {
            assert_eq!(o.kernel_calls, 0, "{t} at {level:?}");
        }
    }
    want
}

fn sqrt_op(a: Vec<Term>) -> Term {
    prim(Prim::Sqrt, a)
}

fn fma_op(a: Vec<Term>) -> Term {
    prim(Prim::Fma, a)
}

fn mul_add_op(a: Vec<Term>) -> Term {
    let [x, y, z] = <[Term; 3]>::try_from(a).expect("three operands");
    mul_add(x, y, z)
}

#[test]
fn sqrt_at_f64_gives_the_correctly_rounded_bits() {
    for (x, want) in [
        (0x4000_0000_0000_0000, 0x3FF6_A09E_667F_3BCD), // 2: the f64 nearest sqrt(2)
        (0x4010_0000_0000_0000, 0x4000_0000_0000_0000), // 4: 2, exact
        (0x3FD0_0000_0000_0000, 0x3FE0_0000_0000_0000), // 0.25: 0.5
        (0x0000_0000_0000_0001, 0x1E60_0000_0000_0000), // the least subnormal 2^-1074: 2^-537
        (0x000F_FFFF_FFFF_FFFF, 0x1FFF_FFFF_FFFF_FFFF), // the greatest subnormal
        (0x7FEF_FFFF_FFFF_FFFF, 0x5FEF_FFFF_FFFF_FFFF), // the greatest finite: just below a tie
        (0x0000_0000_0000_0000, 0x0000_0000_0000_0000), // 0.0
        (0x8000_0000_0000_0000, 0x8000_0000_0000_0000), // -0.0 gives -0.0
        (0x7FF0_0000_0000_0000, 0x7FF0_0000_0000_0000), // inf
        (0xFFF0_0000_0000_0000, NAN64),                 // -inf
        (0xBFF0_0000_0000_0000, NAN64),                 // -1
        (0x8000_0000_0000_0001, NAN64),                 // the least negative subnormal
        (NAN64, NAN64),
        (0xFFF8_0000_0000_0000, NAN64), // the NaN x86-64 makes, sign set
        (0x7FF0_0000_0000_0001, NAN64), // a signaling NaN
    ] {
        for t in both_forms(sqrt_op, vec![f64v(x)]) {
            assert_eq!(bits(&agreed(&t, true)), want, "sqrt({x:#018x})");
        }
    }
}

#[test]
fn sqrt_at_f32_gives_the_correctly_rounded_bits() {
    for (x, want) in [
        (0x4000_0000, 0x3FB5_04F3), // 2: the f32 nearest sqrt(2)
        (0x4080_0000, 0x4000_0000), // 4: 2
        (0x0000_0002, 0x1A80_0000), // the subnormal 2^-148: 2^-74
        (0x0000_0001, 0x1A35_04F3), // the least subnormal 2^-149: 2^-74.5 rounded
        (0x7F7F_FFFF, 0x5F7F_FFFF), // the greatest finite
        (0x0000_0000, 0x0000_0000),
        (0x8000_0000, 0x8000_0000), // -0.0 gives -0.0
        (0x7F80_0000, 0x7F80_0000), // inf
        (0xFF80_0000, NAN32 as u32),
        (0xBF80_0000, NAN32 as u32), // -1
        (0xFFC0_0000, NAN32 as u32), // a NaN with its sign set
    ] {
        for t in both_forms(sqrt_op, vec![f32v(x)]) {
            assert_eq!(bits(&agreed(&t, false)), u64::from(want), "sqrt({x:#010x})");
        }
    }
}

/// `fma(a, b, c)` and `a * b + c` on `f64`s: (a, b, c, fma, a * b + c), each as bits.
const FMA64: [(u64, u64, u64, u64, u64); 10] = [
    // 0.1 * 10 is 1 + 2^-54 exactly, which rounds to 1: the fma keeps the 2^-54.
    (
        0x3FB9_9999_9999_999A,
        0x4024_0000_0000_0000,
        0xBFF0_0000_0000_0000,
        0x3C90_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    // (1 + 2^-52)^2 - (1 + 2^-51) is 2^-104; the product alone rounds it away.
    (
        0x3FF0_0000_0000_0001,
        0x3FF0_0000_0000_0001,
        0xBFF0_0000_0000_0002,
        0x3970_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    // The greatest finite times 2 overflows alone; minus itself it is exact.
    (
        0x7FEF_FFFF_FFFF_FFFF,
        0x4000_0000_0000_0000,
        0xFFEF_FFFF_FFFF_FFFF,
        0x7FEF_FFFF_FFFF_FFFF,
        0x7FF0_0000_0000_0000,
    ),
    // Half the least subnormal plus it is 1.5 of it, a tie that goes to the even 2; the
    // product alone rounds to 0 by ties to even, and the sum is then 1.
    (
        0x0000_0000_0000_0001,
        0x3FE0_0000_0000_0000,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0002,
        0x0000_0000_0000_0001,
    ),
    // 2^-537 squared is the least subnormal, exact both ways.
    (
        0x1E60_0000_0000_0000,
        0x1E60_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0001,
    ),
    // Signed zeros: -0 * 1 + -0 is -0, -0 * 1 + 0 is 0.
    (
        0x8000_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0000,
        0x8000_0000_0000_0000,
    ),
    (
        0x8000_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    // inf * 0 is invalid, whatever c is.
    (
        0x7FF0_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        NAN64,
        NAN64,
    ),
    // inf * 1 - inf is invalid.
    (
        0x7FF0_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0xFFF0_0000_0000_0000,
        NAN64,
        NAN64,
    ),
    // A NaN addend with its sign set.
    (
        0x3FF0_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0xFFF8_0000_0000_0000,
        NAN64,
        NAN64,
    ),
];

#[test]
fn fma_at_f64_rounds_once_and_a_multiply_and_an_add_round_twice() {
    for (a, b, c, want, apart) in FMA64 {
        let args = vec![f64v(a), f64v(b), f64v(c)];
        for t in both_forms(fma_op, args.clone()) {
            assert_eq!(bits(&agreed(&t, true)), want, "{t}");
        }
        for t in both_forms(mul_add_op, args) {
            assert_eq!(bits(&agreed(&t, true)), apart, "{t}");
        }
    }
    // The first four cases are the ones where one rounding and two differ.
    assert!(FMA64[..4].iter().all(|r| r.3 != r.4));
}

#[test]
fn fma_at_f32_rounds_once_and_a_multiply_and_an_add_round_twice() {
    // (a, b, c, fma, a * b + c), each as bits.
    for (a, b, c, want, apart) in [
        // 0.1f32 * 10 is 1 + 2^-26 exactly, which rounds to 1 in f32.
        (
            0x3DCC_CCCD,
            0x4120_0000,
            0xBF80_0000,
            0x3280_0000,
            0x0000_0000,
        ),
        // (1 + 2^-23)^2 - (1 + 2^-22) is 2^-46.
        (
            0x3F80_0001,
            0x3F80_0001,
            0xBF80_0002,
            0x2880_0000,
            0x0000_0000,
        ),
        // The greatest finite times 2, minus itself.
        (
            0x7F7F_FFFF,
            0x4000_0000,
            0xFF7F_FFFF,
            0x7F7F_FFFF,
            0x7F80_0000,
        ),
        // Half the least subnormal plus it: a tie that goes to the even 2.
        (
            0x0000_0001,
            0x3F00_0000,
            0x0000_0001,
            0x0000_0002,
            0x0000_0001,
        ),
        (
            0x8000_0000,
            0x3F80_0000,
            0x8000_0000,
            0x8000_0000,
            0x8000_0000,
        ),
        (
            0x7F80_0000,
            0x0000_0000,
            0x3F80_0000,
            NAN32 as u32,
            NAN32 as u32,
        ),
    ] {
        let args = vec![f32v(a), f32v(b), f32v(c)];
        for t in both_forms(fma_op, args.clone()) {
            assert_eq!(bits(&agreed(&t, false)), u64::from(want), "{t}");
        }
        for t in both_forms(mul_add_op, args) {
            assert_eq!(bits(&agreed(&t, false)), u64::from(apart), "{t}");
        }
    }
}

#[test]
fn a_nan_operand_of_fma_gives_the_canonical_nan() {
    let one = 0x3FF0_0000_0000_0000;
    for nan in [NAN64, 0xFFF8_0000_0000_0000, 0x7FF0_0000_0000_0001] {
        for args in [
            [nan, one, one],
            [one, nan, one],
            [one, one, nan],
            [nan, 0, 0],
        ] {
            let t = fma(f64v(args[0]), f64v(args[1]), f64v(args[2]));
            assert_eq!(bits(&agreed(&t, true)), NAN64, "{t}");
        }
    }
    let t = fma(f32v(0xFFC0_0000), f32v(0x3F80_0000), f32v(0));
    assert_eq!(bits(&agreed(&t, false)), NAN32, "{t}");
}

/// A float as `m * 2^e`, `m` an integer with the float's sign; `None` for inf and NaN.
fn exact(x: f64) -> Option<(BigInt, i64)> {
    if !x.is_finite() {
        return None;
    }
    let b = x.to_bits();
    let (field, frac) = ((b >> 52) & 0x7FF, b & ((1 << 52) - 1));
    let (m, e) = match field {
        0 => (frac, -1074),
        _ => (frac | (1 << 52), field as i64 - 1075),
    };
    let m = BigInt::from(m);
    Some((if x.is_sign_negative() { -m } else { m }, e))
}

/// `m * 2^e` as an integer multiple of `2^at`, for `at <= e`.
fn at(v: &(BigInt, i64), at: i64) -> BigInt {
    &v.0 << (v.1 - at) as usize
}

/// Whether `r`, of the format whose neighbors of `r` are `below` and `above`, is the value of
/// the format nearest the exact `v`, a tie going to the even significand (`even`): the
/// distance from `v` to `r` is at most that to either neighbor. All finite.
fn nearest(v: &(BigInt, i64), r: f64, below: f64, above: f64, even: bool) -> bool {
    let [r, below, above] = [r, below, above].map(|x| exact(x).expect("finite"));
    let e = [v.1, r.1, below.1, above.1].into_iter().min().unwrap();
    let v = at(v, e);
    let d = |x: &(BigInt, i64)| (&v - at(x, e)).magnitude().clone();
    let (dr, db, da) = (d(&r), d(&below), d(&above));
    dr <= db && dr <= da && (even || (dr != db && dr != da))
}

/// Whether `r > 0` is the square root of `x > 0` correctly rounded, `below` and `above` its
/// neighbors: `x` lies strictly between the squares of the midpoints of `r` and each neighbor.
/// No square root of a float is a tie, so the bounds are strict: a midpoint is `m * 2^e` with
/// `m` odd and 54 bits wide, so its square has the odd 107- or 108-bit factor `m^2`, which no
/// `f64` (53 bits) holds. Cost: exact integers of O(p) bits for precision `p`, a few products
/// per case, so O(1) per case at a fixed format.
fn nearest_root(x: f64, r: f64, below: f64, above: f64) -> bool {
    let [x, r, below, above] = [x, r, below, above].map(|x| exact(x).expect("finite"));
    let e = [r.1, below.1, above.1].into_iter().min().unwrap();
    // (r + n)^2 against 4x, all as multiples of 2^(2e) or of 2^(x.1 + 2).
    let twice_mid_sq = |n: &(BigInt, i64)| {
        let s = at(&r, e) + at(n, e);
        (&s * &s, 2 * e)
    };
    let (lo, hi) = (twice_mid_sq(&below), twice_mid_sq(&above));
    let four_x = (x.0, x.1 + 2);
    let f = [lo.1, hi.1, four_x.1].into_iter().min().unwrap();
    at(&lo, f) < at(&four_x, f) && at(&four_x, f) < at(&hi, f)
}

/// A random `f64` of every class: any bit pattern, so subnormals, zeros, infinities and NaNs
/// of both signs come up, with the special exponents drawn more often than by chance.
fn any_f64(rng: &mut Rng) -> f64 {
    let b = rng.next_u64();
    let b = match rng.below(8) {
        0 => b & 0x800F_FFFF_FFFF_FFFF,
        1 => b | 0x7FF0_0000_0000_0000,
        2 => b & 0x8000_0000_0000_0000,
        _ => b,
    };
    f64::from_bits(b)
}

/// A random finite nonzero `f64` with exponent in `lo..=hi`, so that no sum or product of
/// the cases overflows.
pub(crate) fn bounded_f64(rng: &mut Rng, lo: i64, hi: i64) -> f64 {
    let sign = rng.next_u64() & (1 << 63);
    let field = (rng.int(lo, hi) + 1023) as u64;
    f64::from_bits(sign | field << 52 | rng.next_u64() >> 12)
}

/// The tuple of the function `f` of the operands applied to each row of `rows`.
fn applied(params: &[&str], body: Term, rows: &[Vec<Term>]) -> Term {
    let calls = rows.iter().map(|r| app(var("f"), r.clone())).collect();
    let_("f", lam(params, body), prim(Prim::Tuple, calls))
}

/// The components of a tuple value.
fn components(v: &Value) -> Vec<Value> {
    match v {
        Value::Tuple(xs) => xs.to_vec(),
        other => panic!("{other} is no tuple"),
    }
}

#[test]
fn random_operands_give_the_same_bits_in_the_kernel_and_in_native_code() {
    let seed = zed_tests::seed::seed(
        "random_operands_give_the_same_bits_in_the_kernel_and_in_native_code",
    );
    let mut rng = Rng::new(seed);
    // 200 cases from a new seed each run (was 400 from a fixed one): the test took 0.13 s, against
    // 0.34 s at 400, as native code for one tuple of all the calls is built.
    let n = 200;
    // sqrt of operands of every class.
    let xs: Vec<f64> = (0..n).map(|_| any_f64(&mut rng)).collect();
    let rows: Vec<Vec<Term>> = xs.iter().map(|&x| vec![f64v(x.to_bits())]).collect();
    let roots = components(&agreed(&applied(&["a"], sqrt(var("a")), &rows), true));
    for (&x, r) in xs.iter().zip(&roots) {
        let r = f64::from_bits(bits(r));
        match () {
            _ if x.is_nan() || x < 0.0 || x == f64::NEG_INFINITY => {
                assert_eq!(r.to_bits(), NAN64, "{x:e}, seed {seed}")
            }
            _ if x == 0.0 || x == f64::INFINITY => {
                assert_eq!(r.to_bits(), x.to_bits(), "{x:e}, seed {seed}")
            }
            _ => assert!(
                nearest_root(x, r, r.next_down(), r.next_up()),
                "sqrt({x:e}) = {r:e}, seed {seed}"
            ),
        }
    }
    // fma of operands that cannot overflow, a third of them with the addend the negated
    // rounded product, where one rounding and two differ most.
    let abc: Vec<[f64; 3]> = (0..n)
        .map(|_| {
            let (a, b) = (
                bounded_f64(&mut rng, -500, 500),
                bounded_f64(&mut rng, -500, 500),
            );
            let c = match rng.below(3) {
                0 => -(a * b),
                _ => bounded_f64(&mut rng, -1000, 1000),
            };
            [a, b, c]
        })
        .collect();
    let rows: Vec<Vec<Term>> = (abc.iter())
        .map(|r| r.iter().map(|x| f64v(x.to_bits())).collect())
        .collect();
    let body = fma(var("a"), var("b"), var("c"));
    let fmas = components(&agreed(&applied(&["a", "b", "c"], body, &rows), true));
    let mut differ = 0;
    for ([a, b, c], r) in abc.iter().zip(&fmas) {
        let r = f64::from_bits(bits(r));
        let (ea, eb, ec) = (exact(*a).unwrap(), exact(*b).unwrap(), exact(*c).unwrap());
        let p = (&ea.0 * &eb.0, ea.1 + eb.1);
        let e = p.1.min(ec.1);
        let v = (at(&p, e) + at(&ec, e), e);
        let even = r.to_bits() & 1 == 0;
        assert!(
            nearest(&v, r, r.next_down(), r.next_up(), even),
            "fma({a:e}, {b:e}, {c:e}) = {r:e}, seed {seed}"
        );
        differ += usize::from(r.to_bits() != (a * b + c).to_bits());
    }
    // Over 8 seeds, 52 to 72 of the 200 cases differed, a third of all cases having the addend
    // the negated product; n / 10 lies about 7 standard deviations below, so no seed fails it
    // by chance.
    assert!(
        differ > n / 10,
        "one rounding and two differ on {differ} of {n}, seed {seed}"
    );
    // f32: both operations, on operands of every class.
    let rows: Vec<Vec<Term>> = (0..n / 4)
        .map(|_| (0..3).map(|_| f32v(rng.next_u64() as u32)).collect())
        .collect();
    let body = prim(
        Prim::Tuple,
        vec![sqrt(var("a")), fma(var("a"), var("b"), var("c"))],
    );
    let both = components(&agreed(&applied(&["a", "b", "c"], body, &rows), false));
    for (row, v) in rows.iter().zip(&both) {
        let [x, a, b, c] = [&row[0], &row[0], &row[1], &row[2]].map(|t| match t {
            Term::Lit(Value::Float32(x)) => x.get(),
            other => panic!("{other}"),
        });
        let [s, f] = <[Value; 2]>::try_from(components(v)).unwrap();
        let (s, f) = (
            f32::from_bits(bits(&s) as u32),
            f32::from_bits(bits(&f) as u32),
        );
        if x > 0.0 && x.is_finite() {
            let ok = nearest_root(x.into(), s.into(), s.next_down().into(), s.next_up().into());
            assert!(ok, "sqrt({x:e}) = {s:e}, seed {seed}");
        }
        if [a, b, c, f, f.next_down(), f.next_up()]
            .iter()
            .all(|x| x.is_finite())
        {
            let (ea, eb, ec) = [a, b, c].map(|x| exact(x.into()).unwrap()).into();
            let p = (&ea.0 * &eb.0, ea.1 + eb.1);
            let e = p.1.min(ec.1);
            let v = (at(&p, e) + at(&ec, e), e);
            let even = f.to_bits() & 1 == 0;
            let ok = nearest(&v, f.into(), f.next_down().into(), f.next_up().into(), even);
            assert!(ok, "fma({a:e}, {b:e}, {c:e}) = {f:e}, seed {seed}");
        }
    }
}

/// The line a program printing `exprs` after `defs` writes, run in the test directory `name`.
fn printed(name: &str, defs: &str, exprs: &[&str]) -> String {
    let line: Vec<String> = exprs.iter().map(|e| format!("${{{e}}}")).collect();
    let src = format!(
        "{defs}main(m: MainArgs) {{\n  m.stdout <- \"{}\\n\";\n}}\n",
        line.join(" ")
    );
    let o = run(name, &src, "", &[]);
    assert_eq!((o.status, o.stderr.as_str()), (0, ""), "{src}");
    o.stdout.trim_end().to_string()
}

#[test]
fn programs_write_sqrt_and_fma_as_calls_and_sqrt_as_a_method() {
    let defs = "r(positional x: f64) = sqrt(x);\ns(positional x: f32) = x.sqrt;\n\
                t(positional a: f64, positional b: f64, positional c: f64) = fma(a, b, c);\n\
                u(positional a: f64, positional b: f64, positional c: f64) = a * b + c;\n\
                v(positional a: f32, positional b: f32, positional c: f32) = fma(a, b, c);\n\
                w(positional a: f32, positional b: f32, positional c: f32) = a * b + c;\n";
    let got = printed(
        "sqrt_fma_calls",
        defs,
        &[
            "r(2.0)",
            "r(-0.0)",
            "r(-1.0)",
            "s(2.0)",
            "t(0.1, 10.0, -1.0)",
            "u(0.1, 10.0, -1.0)",
            "v(0.1, 10.0, -1.0)",
            "w(0.1, 10.0, -1.0)",
        ],
    );
    assert_eq!(
        got,
        "1.4142135623730951 -0.0 nan 1.4142135 5.551115123125783e-17 0.0 1.4901161e-8 0.0"
    );
}

#[test]
fn a_literal_operand_takes_f64_since_sqrt_and_fma_take_float_formats_alone() {
    // DESIGN.md L1.26b: "A decimal literal whose uses leave it float formats alone, `f64`
    // among them, takes `f64`"; an integer literal there, which no `int` arrow takes, does
    // the same, as it would were `f64` the one format.
    assert_eq!(
        printed(
            "sqrt_fma_literals",
            "f() = sqrt(2.0);\ng() = fma(2, 3, 4);\ny = sqrt(4);\n",
            &[
                "sqrt(2.0)",
                "f()",
                "g()",
                "y",
                "fma(0.1, 10.0, -1.0)",
                "sqrt(2.0f32)"
            ]
        ),
        "1.4142135623730951 1.4142135623730951 10.0 2.0 5.551115123125783e-17 1.4142135"
    );
    let s = sig("f(positional x) = sqrt(x);\n", "f");
    assert_eq!(s, "T -> T for T in f32 | f64");
}

/// The first line of the rejection of `src`, which declares a `main` of its own when it needs
/// one.
fn rejected(src: &str) -> String {
    let src = format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n");
    match load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.lines().next().unwrap_or_default().to_string(),
    }
}

#[test]
fn an_int_or_rat_operand_or_two_formats_are_rejected() {
    // No implicit conversion (DESIGN.md sec:domains): `sqrt(f64(n))` says where it rounds.
    let int = rejected("f(positional x: int) = sqrt(x);\n");
    assert!(int.ends_with("`sqrt` does not take (int): no arrow of `sqrt` takes these types."));
    let rat = rejected("f(positional x: rat) = sqrt(x);\n");
    assert!(rat.ends_with("`sqrt` does not take (rat): no arrow of `sqrt` takes these types."));
    let mixed = rejected("f(positional x: f64, positional y: f32) = fma(x, y, x);\n");
    // Every `f32` is an `f64`, so the cast of `y` is exact and is offered as the call rewritten.
    assert!(mixed.ends_with(
        "`fma` does not take (f64, f32, f64): no arrow of `fma` takes these types. \
         Try `fma(x, f64(y), x)` instead."
    ));
    let two = rejected("f(positional x: f64) = fma(x, x);\n");
    assert!(
        two.ends_with("`fma` takes 3 arguments, `fma(a, b, c)`, and `fma(x, x)` passes 2."),
        "{two}"
    );
}

/// The gap FLOAT-f32 left: a call that lists integer values, beside an `f32`, is read at
/// `f32` as it is beside an `f64` (DESIGN.md L1.26a: "each keeps its own value and is fixed
/// where the result is used").
#[test]
fn a_call_listing_integers_is_read_at_f32_as_at_f64() {
    let defs = "g(positional c: bool) = if c { 1 } else { 2 };\n\
                h(positional x: f32, positional c: bool) = x * g(c);\n\
                k(positional x: f32, positional c: bool) = fma(x, g(c), x);\n\
                e(positional x: f32, positional c: bool) = x == g(c);\n\
                d(positional x: f64, positional c: bool) = x * g(c);\n";
    assert_eq!(
        printed(
            "sqrt_fma_f32_reads",
            defs,
            &[
                "h(1.5f32, true)",
                "h(1.5f32, false)",
                "k(1.5f32, false)",
                "e(2.0f32, false)",
                "d(1.5, true)"
            ]
        ),
        "1.5 3.0 4.5 true 1.5"
    );
}
