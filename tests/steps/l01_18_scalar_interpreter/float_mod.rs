//! `floatMod(x, m)` at `f64` and `f32` (row FLOAT-floatMod; DESIGN.md sec:domains, "`floatMod`,
//! the remainder of a float"; QUESTIONS A174): for a finite `m > 0` the float of `[0.0, m)`
//! nearest the exact residue `x − m·⌊x/m⌋`, a tie to the even one; NaN for an infinite or NaN
//! `x`. The definition, its proof and its citations are at zed-kernel `num::float_mod`; the
//! survey that chose it is zed-impl `docs/mod-study.md`. The kernel, the counting machine and
//! native code at both of Cranelift's levels give the same bits; native code runs the word
//! through the kernel, since it has no inline form. The checker refuses a modulus it does not
//! show finite and greater than `0.0`. The expected bits are written out, and the random cases
//! are checked against exact integer arithmetic.

use num_bigint::BigInt;
use num_integer::Integer;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zed_tests::instances::Rng;

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_36_cranelift::{kernel, planned};
use zedc::run::load;
use zedc::zir::memory;

/// The canonical NaN of binary64 and of binary32 (DESIGN.md sec:reduction).
const NAN64: u64 = 0x7FF8_0000_0000_0000;
const NAN32: u64 = 0x7FC0_0000;

fn f64v(b: u64) -> Term {
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

pub(crate) fn float_mod(x: Term, m: Term) -> Term {
    prim(Prim::FloatMod, vec![x, m])
}

/// `floatMod` on literals, and on the parameters of a function applied to them, so that no
/// constant decides the result before the code runs.
fn both_forms(x: Term, m: Term) -> [Term; 2] {
    let body = float_mod(var("x"), var("m"));
    let called = let_(
        "f",
        lam(&["x", "m"], body),
        app(var("f"), vec![x.clone(), m.clone()]),
    );
    [float_mod(x, m), called]
}

/// The value of `t` by the kernel, by the counting machine and natively at both levels, all
/// equal bit for bit (a float value compares by its bits).
fn agreed(t: &Term) -> Value {
    let want = kernel(t).unwrap_or_else(|e| panic!("{t}: {e}"));
    let (g, p) = planned(t);
    let (m, _) = memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(m, want, "{t} by the counting machine");
    for level in [OptLevel::None, OptLevel::Speed] {
        let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("{t}: {e}"));
        assert_eq!(o.value, want, "{t} at {level:?}");
    }
    want
}

/// `floatMod` at `f64`: (x, m, result), as bits.
const PROBES64: [(u64, u64, u64); 20] = [
    // -1e-20 mod 360: the residue 360 − 1e-20 rounds to 360, so the result is the float below
    // it, 360 − 2^-44 (docs/mod-study.md; C's fmod-then-add gives 360 itself).
    (
        (-1e-20f64).to_bits(),
        0x4076_8000_0000_0000,
        0x4076_7FFF_FFFF_FFFF,
    ),
    // -0.5 mod 2 = 1.5.
    (
        0xBFE0_0000_0000_0000,
        0x4000_0000_0000_0000,
        0x3FF8_0000_0000_0000,
    ),
    // 5.5 mod 2 = 1.5, and -5.5 mod 2 = 0.5.
    (
        0x4016_0000_0000_0000,
        0x4000_0000_0000_0000,
        0x3FF8_0000_0000_0000,
    ),
    (
        0xC016_0000_0000_0000,
        0x4000_0000_0000_0000,
        0x3FE0_0000_0000_0000,
    ),
    // -0.0 mod 1 is +0.0, not -0.0.
    (
        0x8000_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    // 6 mod 3 and -6 mod 3 are +0.0.
    (
        0x4018_0000_0000_0000,
        0x4008_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    (
        0xC018_0000_0000_0000,
        0x4008_0000_0000_0000,
        0x0000_0000_0000_0000,
    ),
    // -2^-60 mod 1: 1 − 2^-60 rounds to 1, so the result is 1 − 2^-53.
    (
        0xBC30_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x3FEF_FFFF_FFFF_FFFF,
    ),
    // -2^-53 mod 1 = 1 − 2^-53 exactly, a float.
    (
        0xBCA0_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x3FEF_FFFF_FFFF_FFFF,
    ),
    // 1e17 mod 3 = 1 (1e17 is exactly 10^17, and 10 ≡ 1 mod 3); `x - trunc(x / m) * m`
    // evaluated in floats gives 0 (docs/mod-study.md, Local runs).
    (
        1e17f64.to_bits(),
        0x4008_0000_0000_0000,
        0x3FF0_0000_0000_0000,
    ),
    // 1 mod the least subnormal is 0; minus it mod twice it is it.
    (
        0x3FF0_0000_0000_0000,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0000,
    ),
    (
        0x8000_0000_0000_0001,
        0x0000_0000_0000_0002,
        0x0000_0000_0000_0001,
    ),
    // The greatest finite, (2^53 − 1)·2^971, mod 1.5 = 3/2: twice it is (2^53 − 1)·2^972,
    // and mod 3, 2^53 ≡ 2 and 2^972 ≡ 1, so twice it ≡ 1, and the residue is 1/2. The
    // longest exponent gap of the format, with no overflow.
    (
        0x7FEF_FFFF_FFFF_FFFF,
        0x3FF8_0000_0000_0000,
        0x3FE0_0000_0000_0000,
    ),
    // x below m: x itself; a negative x above -m: x + m.
    (
        0x3FD0_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x3FD0_0000_0000_0000,
    ),
    (
        0xBFD0_0000_0000_0000,
        0x3FF0_0000_0000_0000,
        0x3FE8_0000_0000_0000,
    ),
    // An infinite or NaN `x` gives NaN.
    (0x7FF0_0000_0000_0000, 0x3FF0_0000_0000_0000, NAN64),
    (0xFFF0_0000_0000_0000, 0x3FF0_0000_0000_0000, NAN64),
    (NAN64, 0x3FF0_0000_0000_0000, NAN64),
    // A modulus of 0 or below, or not finite, which a checked program never passes: NaN.
    (0x3FF0_0000_0000_0000, 0x0000_0000_0000_0000, NAN64),
    (0x3FF0_0000_0000_0000, 0x7FF0_0000_0000_0000, NAN64),
];

#[test]
fn float_mod_at_f64_gives_the_nearest_residue_in_zero_to_m() {
    for (x, m, want) in PROBES64 {
        for t in both_forms(f64v(x), f64v(m)) {
            assert_eq!(bits(&agreed(&t)), want, "floatMod({x:#018x}, {m:#018x})");
        }
    }
    // A negative modulus, and a NaN one.
    for m in [0xBFF0_0000_0000_0000, NAN64] {
        let t = float_mod(f64v(0x3FF0_0000_0000_0000), f64v(m));
        assert_eq!(bits(&agreed(&t)), NAN64, "floatMod(1, {m:#018x})");
    }
}

#[test]
fn float_mod_at_f32_gives_the_nearest_residue_in_zero_to_m() {
    for (x, m, want) in [
        // -1e-20 mod 360: 360 − 2^-15, the float below 360.
        ((-1e-20f32).to_bits(), 0x43B4_0000, 0x43B3_FFFF_u32),
        (0xBF00_0000, 0x4000_0000, 0x3FC0_0000), // -0.5 mod 2 = 1.5
        (0x8000_0000, 0x3F80_0000, 0x0000_0000), // -0.0 mod 1 = +0.0
        (0x8000_0001, 0x0000_0002, 0x0000_0001), // subnormals
        (0x7F80_0000, 0x3F80_0000, NAN32 as u32), // inf
        (0x3F80_0000, 0x0000_0000, NAN32 as u32), // m = 0
    ] {
        for t in both_forms(f32v(x), f32v(m)) {
            assert_eq!(
                bits(&agreed(&t)),
                u64::from(want),
                "floatMod({x:#010x}, {m:#010x})"
            );
        }
    }
}

/// A finite float as `m * 2^e`, `m` an integer with the float's sign.
fn exact(x: f64) -> (BigInt, i64) {
    let b = x.to_bits();
    let (field, frac) = ((b >> 52) & 0x7FF, b & ((1 << 52) - 1));
    let (m, e) = match field {
        0 => (frac, -1074),
        _ => (frac | (1 << 52), field as i64 - 1075),
    };
    let m = BigInt::from(m);
    (if x.is_sign_negative() { -m } else { m }, e)
}

/// Whether `r` is `floatMod(x, m)` for finite `x` and finite `m > 0`, all values of one format
/// given exactly as `f64`s, with `below` and `above` the neighbors of `r` in that format and
/// `even` whether `r`'s significand is even: `r` is `+0.0` or positive, below `m`, and no float
/// of `[0.0, m)` lies nearer the exact residue `ρ = x − m·⌊x/m⌋`, a tie only to an even `r`.
/// Exact integers of O(e_x − e_m) bits.
fn is_residue(x: f64, m: f64, r: f64, below: f64, above: f64, even: bool) -> bool {
    if r.is_sign_negative() || r >= m {
        return false;
    }
    let vals = [x, m, r, below, above].map(exact);
    let e = vals.iter().map(|v| v.1).min().unwrap();
    let at = |v: &(BigInt, i64)| &v.0 << (v.1 - e) as usize;
    let [xi, mi, ri, bi, ai] = vals.each_ref().map(at);
    let rho = xi.mod_floor(&mi);
    let d = |y: &BigInt| (&rho - y).magnitude().clone();
    let dr = d(&ri);
    // Only the neighbors inside `[0.0, m)` compete.
    let rivals = [(below >= 0.0, bi), (above < m, ai)];
    rivals.iter().filter(|(inside, _)| *inside).all(|(_, y)| {
        let dy = d(y);
        dr < dy || (dr == dy && even)
    })
}

/// A random finite nonzero `f64` with exponent in `lo..=hi`.
fn bounded_f64(rng: &mut Rng, lo: i64, hi: i64) -> f64 {
    let sign = rng.next_u64() & (1 << 63);
    let field = (rng.int(lo, hi) + 1023) as u64;
    f64::from_bits(sign | field << 52 | rng.next_u64() >> 12)
}

/// The tuple of `floatMod` applied, through a function, to each `(x, m)` of `rows`.
fn applied(rows: &[(Term, Term)]) -> Term {
    let calls = (rows.iter())
        .map(|(x, m)| app(var("f"), vec![x.clone(), m.clone()]))
        .collect();
    let body = float_mod(var("x"), var("m"));
    let_("f", lam(&["x", "m"], body), prim(Prim::Tuple, calls))
}

fn components(v: &Value) -> Vec<Value> {
    match v {
        Value::Tuple(xs) => xs.to_vec(),
        other => panic!("{other} is no tuple"),
    }
}

#[test]
fn random_operands_give_the_nearest_residue_in_the_kernel_and_in_native_code() {
    let seed = zed_tests::seed::seed(
        "random_operands_give_the_nearest_residue_in_the_kernel_and_in_native_code",
    );
    let mut rng = Rng::new(seed);
    let n = 300;
    // f64: exponents of `x` and `m` far apart and near, so both the long `fmod` and the
    // rounding of a small negative residue up to `m` come up, a third with `x` tiny and
    // negative, where `ρ` lies within half an ulp below `m`.
    let pairs: Vec<(f64, f64)> = (0..n)
        .map(|_| {
            let m = bounded_f64(&mut rng, -1022, 1023).abs();
            let x = match rng.below(3) {
                0 => -(bounded_f64(&mut rng, -1074, -900).abs()),
                1 => bounded_f64(&mut rng, -1022, 1023),
                _ => m * bounded_f64(&mut rng, -3, 3),
            };
            (x, m)
        })
        .filter(|(x, _)| x.is_finite())
        .collect();
    let rows: Vec<(Term, Term)> = (pairs.iter())
        .map(|(x, m)| (f64v(x.to_bits()), f64v(m.to_bits())))
        .collect();
    let got = components(&agreed(&applied(&rows)));
    for (&(x, m), r) in pairs.iter().zip(&got) {
        let r = f64::from_bits(bits(r));
        let even = r.to_bits() & 1 == 0;
        assert!(
            is_residue(x, m, r, r.next_down(), r.next_up(), even),
            "floatMod({x:e}, {m:e}) = {r:e}, seed {seed}"
        );
    }
    // f32: random bit patterns, the modulus made finite and positive.
    let pairs: Vec<(f32, f32)> = (0..n)
        .map(|_| {
            let x = f32::from_bits(rng.next_u64() as u32 & 0xFF7F_FFFF);
            let m = f32::from_bits(rng.next_u64() as u32 & 0x7F7F_FFFF);
            (x, if m == 0.0 { 1.0 } else { m })
        })
        .collect();
    let rows: Vec<(Term, Term)> = (pairs.iter())
        .map(|(x, m)| (f32v(x.to_bits()), f32v(m.to_bits())))
        .collect();
    let got = components(&agreed(&applied(&rows)));
    for (&(x, m), r) in pairs.iter().zip(&got) {
        let r = f32::from_bits(bits(r) as u32);
        let (lo, hi) = (r.next_down(), r.next_up());
        let even = r.to_bits() & 1 == 0;
        assert!(
            is_residue(x.into(), m.into(), r.into(), lo.into(), hi.into(), even),
            "floatMod({x:e}, {m:e}) = {r:e}, seed {seed}"
        );
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
fn programs_call_float_mod_with_a_literal_modulus() {
    let defs = "deg(positional a: f64) = floatMod(a, 360.0);\n\
                half(positional a: f32) = floatMod(a, 0.5f32);\n";
    let got = printed(
        "float_mod_calls",
        defs,
        &[
            "deg(-1e-20)",
            "deg(-90.0)",
            "deg(725.0)",
            "floatMod(-0.5, 2.0)",
            "floatMod(-0.0, 1.0)",
            "floatMod(5.5, 2)",
            "half(-0.75f32)",
        ],
    );
    assert_eq!(got, "359.99999999999994 270.0 5.0 1.5 0.0 1.5 0.25");
}

/// The first line of the rejection of `src`, which declares a `main` of its own.
fn rejected(src: &str) -> String {
    let src = format!("{src}main(m: MainArgs) {{\n  m.stdout <- \"\";\n}}\n");
    match load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.lines().next().unwrap_or_default().to_string(),
    }
}

#[test]
fn a_modulus_not_shown_finite_and_above_zero_is_rejected() {
    let zero = rejected("f(positional x: f64) = floatMod(x, 0.0);\n");
    assert!(
        zero.ends_with("`floatMod` takes `m` finite and greater than `0.0`: `floatMod(x, 0.0)`."),
        "{zero}"
    );
    let neg = rejected("f(positional x: f64) = floatMod(x, -1.5);\n");
    assert!(
        neg.ends_with("`floatMod` takes `m` finite and greater than `0.0`: `floatMod(x, -1.5)`."),
        "{neg}"
    );
    let int0 = rejected("f(positional x: f64) = floatMod(x, 0);\n");
    assert!(
        int0.ends_with("`floatMod` takes `m` finite and greater than `0.0`: `floatMod(x, 0)`."),
        "{int0}"
    );
    // A parameter: zedc has no intervals of floats yet (row FLOAT-interval), so it cannot show
    // `m` in range, and refuses it with its type.
    let var = rejected("f(positional x: f64, positional m: f64) = floatMod(x, m);\n");
    assert!(
        var.ends_with(
            "`floatMod` takes `m` finite and greater than `0.0`: `floatMod(x, m : f64)`."
        ),
        "{var}"
    );
    let two = rejected("f(positional x: f64) = floatMod(x);\n");
    assert!(
        two.ends_with(
            "`floatMod` takes 2 arguments, `floatMod(x, m)`, and `floatMod(x)` passes 1."
        ),
        "{two}"
    );
    let int = rejected("f(positional x: int) = floatMod(x, 3.0);\n");
    assert!(
        int.contains("no arrow of `floatMod` takes these types"),
        "{int}"
    );
}

/// `mod` on a float is a type error whose repair is `floatMod` (DESIGN.md sec:diagnostics, row
/// "`mod` on a float"; QUESTIONS A174; row MSG-float-mod-type-error), at each float format
/// zedc has (`f16` and `bf16` are not built yet), and `mod` on ints is unchanged.
#[test]
fn mod_on_a_float_is_a_type_error_whose_repair_is_float_mod() {
    let f64_lit = rejected("deg(positional a: f64) = a mod 360.0;\n");
    assert!(
        f64_lit
            .ends_with("`mod` takes ints: `a : f64 mod 360.0`. Try `floatMod(a, 360.0)` instead."),
        "{f64_lit}"
    );
    let f32_lit = rejected("deg(positional a: f32) = a mod 360.0;\n");
    assert!(
        f32_lit
            .ends_with("`mod` takes ints: `a : f32 mod 360.0`. Try `floatMod(a, 360.0)` instead."),
        "{f32_lit}"
    );
    let sum = rejected("f(positional a: f64, positional b: f64) = (a + b) mod 2.0;\n");
    assert!(
        sum.ends_with(
            "`mod` takes ints: `(a + b) : f64 mod 2.0`. Try `floatMod(a + b, 2.0)` instead."
        ),
        "{sum}"
    );
    // An int modulus with a float `x`.
    let int_m = rejected("deg(positional a: f64) = a mod 360;\n");
    assert!(
        int_m.ends_with("`mod` takes ints: `a : f64 mod 360`. Try `floatMod(a, 360)` instead."),
        "{int_m}"
    );
    // Two typed literals: they are refused at `mod`'s int parameters before the application
    // fails, and the error is still `mod` on a float.
    let lits = rejected("f(positional a: f64) = 7.5f64 mod 2.5f64;\n");
    assert!(
        lits.ends_with(
            "`mod` takes ints: `7.5f64 mod 2.5f64`. Try `floatMod(7.5f64, 2.5f64)` instead."
        ),
        "{lits}"
    );
    // The whole message: the carrier's derivation, the repair, the residue on `rat`, and no
    // narrowing cast.
    let src =
        "deg(positional a: f64) = a mod 360.0;\nmain(m: MainArgs) {\n  m.stdout <- \"\";\n}\n";
    let e = load(src.as_bytes()).err().expect("rejected");
    assert!(e.contains("`a` is declared `f64`"), "{e}");
    assert!(
        e.contains("repair: write `floatMod(a, 360.0)`; the checker accepts that"),
        "{e}"
    );
    assert!(
        e.contains("the exact residue is `rat(a) - 360r * rat(floor(rat(a) / 360r))`"),
        "{e}"
    );
    assert!(!e.contains("int(a)"), "{e}");
    // A modulus `floatMod` refuses, a parameter not shown finite and above `0.0`: no fix.
    let src = "f(positional a: f64, positional m: f64) = a mod m;\n\
               main(m: MainArgs) {\n  m.stdout <- \"\";\n}\n";
    let e = load(src.as_bytes()).err().expect("rejected");
    let head = e.lines().next().unwrap_or_default();
    assert!(
        head.ends_with("`mod` takes ints: `a : f64 mod m : f64`."),
        "{e}"
    );
    assert!(
        e.contains("the remainder of a float is `floatMod(a, m)`, for a modulus shown finite"),
        "{e}"
    );
    assert!(!e.contains("repair: write `floatMod"), "{e}");
    // `mod` on ints is accepted as before.
    let ints = "f(positional n: int) = n mod 360;\nmain(m: MainArgs) {\n  m.stdout <- \"\";\n}\n";
    assert!(load(ints.as_bytes()).is_ok(), "an int `mod` is rejected");
}

#[test]
fn the_rejection_of_a_variable_modulus_says_why_and_offers_a_literal() {
    let src = "f(positional x: f64, positional m: f64) = floatMod(x, m);\n\
               main(m: MainArgs) {\n  m.stdout <- \"\";\n}\n";
    let e = load(src.as_bytes()).err().expect("rejected");
    assert!(e.contains("`m` is this modulus, f64"), "{e}");
    assert!(
        e.contains("repair: write the modulus as a literal, such as `floatMod(x, 360.0)`"),
        "{e}"
    );
    assert!(
        e.contains("since zedc does not narrow a float by a test"),
        "{e}"
    );
}
