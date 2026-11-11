//! `*` through native code at the edges of the machine word, and native code against the
//! kernel on a seeded sample (test audit 2026-11-08, row 4).
//!
//! Integers: "semantic `int` widens its domain instead of overflowing" (DESIGN.md
//! sec:failure, item 1), so `a * b` is the exact product, a word when it fits in 64 bits and an
//! unbounded integer otherwise. Native code multiplies two words inline with
//! `smul_overflow` (codegen.rs, `Gen::inline`) and hands an overflow, or an operand that is not
//! a word, to the runtime, which runs the node in the kernel. So each product below must be the
//! exact one, the kernel's, and inline exactly when the operands and the product are words.
//!
//! Floats: "Every float operation with a NaN operand gives NaN" (sec:reduction, item 5), signed
//! zeros and the rounding are IEEE's, round to nearest even with no FMA contraction, and "NaN
//! [is] canonicalized to the quiet NaN with cleared sign and zero payload" (item 1, item 4). A
//! NaN result is therefore compared by its bits with that one NaN, as every other result is
//! compared by its bits; float `*` makes no kernel call.

use num_bigint::BigInt;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Pattern, Prim, Shared, Term, Value, World};
use zed_native::{OptLevel, run_at};
use zed_tests::instances::Rng;

use super::{kernel, planned};

const MIN: i128 = i64::MIN as i128;
const MAX: i128 = i64::MAX as i128;

/// The default seed of the sampled pairs; `ZED_MUL_SEED` replaces it, to rerun a failure.
const SEED: u64 = 0x6d75_6c5f_6564_6765;

fn seed() -> u64 {
    std::env::var("ZED_MUL_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(SEED)
}

/// The integer `n` as a value: a word when it fits in 64 bits.
fn int(n: i128) -> Value {
    Value::int(BigInt::from(n))
}

/// The product DESIGN.md gives: `a * b` exactly.
fn exact(a: i128, b: i128) -> Value {
    Value::int(BigInt::from(a) * BigInt::from(b))
}

/// Whether the inline code decides `a * b`: both operands and the product are words.
fn inline(a: i128, b: i128) -> bool {
    let word = |n: i128| i64::try_from(n).is_ok();
    word(a) && word(b) && a.checked_mul(b).is_some_and(word)
}

/// `t` run natively at `level`: its value and its count of kernel calls.
fn at(level: OptLevel, t: &Term) -> (Value, u64) {
    let (g, p) = planned(t);
    let o = run_at(level, &g, &p, &mut Evaluator::new(World::new()))
        .unwrap_or_else(|e| panic!("{t:?}: {e}"));
    (o.value, o.kernel_calls)
}

/// `x * y` on the literals, and in a function applied to them, so that no constant of the
/// term decides the product before the code runs.
fn both_forms(x: Value, y: Value) -> [Term; 2] {
    let mul = |a, b| prim(Prim::Mul, vec![a, b]);
    [
        mul(lit(x.clone()), lit(y.clone())),
        app(
            lam(&["a", "b"], mul(var("a"), var("b"))),
            vec![lit(x), lit(y)],
        ),
    ]
}

/// The named products of the audit and the products at the square root of the word's bound,
/// each with every neighbor of each operand: `(a + i) * (b + j)` for `i, j` in `-1..=1`.
/// Neighbors outside the word are unbounded integers, which the runtime multiplies.
const EDGES: [(i128, i128); 9] = [
    (MIN, -1),
    (-1, MIN),
    (MIN, MIN),
    (MAX, MAX),
    (MIN, 2),
    // `3037000499^2 = 2^63 - 5928526807` fits; `3037000500^2` does not.
    (3_037_000_499, 3_037_000_499),
    (-3_037_000_499, 3_037_000_500),
    // `-2^32 * 2^31` is `MIN` exactly, and `2^32 * 2^31` is one past `MAX`.
    (-(1 << 32), 1 << 31),
    (1 << 32, 1 << 31),
];

#[test]
fn the_edge_products_and_their_neighbors_are_exact_in_native_code() {
    let mut n = 0;
    let mut inlined = 0;
    for (a, b) in EDGES {
        for i in -1..=1 {
            for j in -1..=1 {
                let (x, y) = (a + i, b + j);
                let want = exact(x, y);
                assert_eq!(
                    kernel(&both_forms(int(x), int(y))[0]).unwrap(),
                    want,
                    "kernel {x} * {y}"
                );
                for t in both_forms(int(x), int(y)) {
                    for level in [OptLevel::None, OptLevel::Speed] {
                        let (got, calls) = at(level, &t);
                        assert_eq!(got, want, "{x} * {y} at {level:?}");
                        let calls_wanted = u64::from(!inline(x, y));
                        assert_eq!(calls, calls_wanted, "{x} * {y} at {level:?}: kernel calls");
                        n += 1;
                    }
                }
                inlined += usize::from(inline(x, y));
            }
        }
    }
    assert_eq!(n, EDGES.len() * 9 * 4);
    // The named cases themselves: each overflows but `MIN * 1`-like neighbors stay inline.
    for (x, y, want) in [
        (MIN, -1, 1i128 << 63),
        (-1, MIN, 1 << 63),
        (MIN, MIN, 1 << 126),
        (MAX, MAX, (1 << 126) - (1 << 64) + 1),
        (MIN, 2, -(1 << 64)),
        (-(1 << 32), 1 << 31, MIN),
        (MIN, 1, MIN),
        (MAX, -1, -MAX),
    ] {
        assert_eq!(exact(x, y), int(want), "{x} * {y}");
        assert_eq!(
            at(OptLevel::None, &both_forms(int(x), int(y))[1]).0,
            int(want)
        );
    }
    // Of the 81 pairs, 31 stay inline, counted by hand: 3 at `MIN * -1` (`MIN * 0`,
    // `(MIN + 1) * -1`, `(MIN + 1) * 0`), 3 at `-1 * MIN`, none at `MIN * MIN` or `MAX * MAX`,
    // 2 at `MIN * 2` (`MIN * 1`, `(MIN + 1) * 1`), 8 at `3037000499^2` (all but `3037000500^2`),
    // 6 at `-3037000499 * 3037000500`, 5 at `-2^32 * 2^31` and 4 at `2^32 * 2^31`.
    assert_eq!(inlined, 31);
}

/// An operand near an edge: within `2^8` of `MIN`, `MAX`, zero, `±2^31`, `±2^32` or
/// `±3037000499`, inside the word.
fn near_edge(r: &mut Rng) -> i128 {
    const CENTERS: [i128; 10] = [
        MIN,
        MAX,
        0,
        1 << 31,
        -(1 << 31),
        1 << 32,
        -(1 << 32),
        3_037_000_499,
        -3_037_000_499,
        0,
    ];
    let c = r.pick(&CENTERS);
    let d = r.int(-(1 << 8), 1 << 8) as i128;
    (c + d).clamp(MIN, MAX)
}

/// An operand of a random length: a word of random bits shifted right by `0..64`, of either
/// sign, so both short and long operands, and products that fit and that do not, are common.
fn any_length(r: &mut Rng) -> i128 {
    let bits = (r.next_u64() >> r.below(64)) as i64 as i128;
    let signed = if r.next_u64() & 1 == 0 { bits } else { -bits };
    signed.clamp(MIN, MAX)
}

/// The integer pairs: half within `2^8` of an edge, one operand or both, half of random length.
fn int_pairs(seed: u64, n: usize) -> Vec<(i128, i128)> {
    let mut r = Rng::new(seed);
    (0..n)
        .map(|k| {
            if k % 2 == 0 {
                match r.below(3) {
                    0 => (near_edge(&mut r), r.int(-(1 << 8), 1 << 8) as i128),
                    1 => (r.int(-(1 << 8), 1 << 8) as i128, near_edge(&mut r)),
                    _ => (near_edge(&mut r), near_edge(&mut r)),
                }
            } else {
                (any_length(&mut r), any_length(&mut r))
            }
        })
        .collect()
}

/// `a * b`.
fn product() -> Term {
    prim(Prim::Mul, vec![var("a"), var("b")])
}

/// `match a * b { NaN -> "NaN", p -> p }`. The literal pattern compares the product's word with
/// the canonical NaN by its bits (zed-rt `Heap::equals`), so a NaN with another sign or payload
/// in native code gives the float, not the string, where a value of the product alone would
/// not show it: making the word a value makes its NaN canonical.
fn nan_matched() -> Term {
    Term::Match(
        Shared::new(product()),
        vec![
            (Pattern::Lit(Value::float(f64::NAN)), lit("NaN")),
            (Pattern::Bind("p".into()), var("p")),
        ],
    )
}

/// `f = (a, b) -> body; (f(x0, y0), f(x1, y1), …)`: one compiled program for many pairs.
fn batch(pairs: &[(Value, Value)], body: &Term) -> Term {
    let calls = pairs
        .iter()
        .map(|(x, y)| app(var("f"), vec![lit(x.clone()), lit(y.clone())]))
        .collect();
    let_(
        "f",
        lam(&["a", "b"], body.clone()),
        prim(Prim::Tuple, calls),
    )
}

/// `body` on each of `pairs` by the kernel and natively at `level`, one program per `chunk`
/// pairs; each result equal in the three, by `same`, which also checks DESIGN.md's value.
/// Returns the native kernel calls.
fn differential(
    what: &str,
    seed: u64,
    pairs: &[(Value, Value)],
    body: &Term,
    chunk: usize,
    level: OptLevel,
    same: impl Fn(usize, &Value, &Value) -> Result<(), String>,
) -> u64 {
    let mut calls = 0;
    for (c, part) in pairs.chunks(chunk).enumerate() {
        let t = batch(part, body);
        let want = kernel(&t).unwrap_or_else(|e| panic!("{what}, seed {seed}: kernel: {e}"));
        let (got, k) = at(level, &t);
        calls += k;
        let (Value::Tuple(w), Value::Tuple(g)) = (&want, &got) else {
            panic!("{what}, seed {seed}: two tuples, got {want} and {got}")
        };
        assert_eq!(w.len(), part.len(), "{what}, seed {seed}");
        assert_eq!(g.len(), part.len(), "{what}, seed {seed}");
        for (i, (wv, gv)) in w.iter().zip(g.iter()).enumerate() {
            let k = c * chunk + i;
            let (x, y) = &pairs[k];
            if let Err(e) = same(k, wv, gv) {
                panic!(
                    "{what}, seed {seed} (rerun with ZED_MUL_SEED={seed}), pair {k}: {x} * {y}: {e}"
                );
            }
        }
    }
    calls
}

/// The pairs per compiled program. A program of 2,000 calls compiles in about 0.1 s at
/// `OptLevel::None`; the sample runs in 50 programs.
const CHUNK: usize = 2_000;

#[test]
fn a_hundred_thousand_integer_pairs_agree_with_the_kernel_and_are_exact() {
    let seed = seed();
    let pairs = int_pairs(seed, 100_000);
    let values: Vec<(Value, Value)> = pairs.iter().map(|&(x, y)| (int(x), int(y))).collect();
    let overflows = pairs.iter().filter(|&&(x, y)| !inline(x, y)).count();
    // The lowering keeps one node for equal nodes (CSE by content address, zir/lower.rs), so
    // a pair repeated in one program is multiplied once there.
    let distinct: usize = pairs
        .chunks(CHUNK)
        .map(|c| {
            let over: std::collections::HashSet<_> =
                c.iter().filter(|&&(x, y)| !inline(x, y)).collect();
            over.len()
        })
        .sum();
    let calls = differential(
        "integer *",
        seed,
        &values,
        &product(),
        CHUNK,
        OptLevel::None,
        |k, w, g| {
            let (x, y) = pairs[k];
            let want = exact(x, y);
            if w != &want {
                return Err(format!("the kernel gives {w}, the exact product is {want}"));
            }
            if g != &want {
                return Err(format!(
                    "native code gives {g}, the exact product is {want}"
                ));
            }
            Ok(())
        },
    );
    // Each distinct product that leaves the word is one call of the runtime, and no other is.
    assert_eq!(
        calls, distinct as u64,
        "seed {seed}: kernel calls against overflowing products"
    );
    // The sample reaches both sides of the edge often.
    assert!(
        overflows > 20_000 && overflows < 80_000,
        "seed {seed}: {overflows} overflows"
    );
}

/// One float of `class`, both signs: 0 zero, 1 subnormal, 2 normal, 3 infinity, 4 NaN with a
/// random payload, quiet or signaling.
fn of_class(r: &mut Rng, class: usize) -> f64 {
    const FRAC: u64 = (1 << 52) - 1;
    let sign = (r.next_u64() & 1) << 63;
    let bits = match class {
        0 => 0,
        1 => (r.next_u64() & FRAC).max(1),
        2 => (r.int(1, 2046) as u64) << 52 | (r.next_u64() & FRAC),
        3 => 0x7ff << 52,
        _ => 0x7ff << 52 | (r.next_u64() & FRAC).max(1),
    };
    f64::from_bits(sign | bits)
}

/// Floats of every class picked by hand: each sign of zero, the least and the greatest
/// subnormal, the least and greatest normal, one, the infinities, and NaNs with payloads.
const FLOAT_CORNERS: [u64; 18] = [
    0x0000_0000_0000_0000,
    0x8000_0000_0000_0000,
    0x0000_0000_0000_0001,
    0x8000_0000_0000_0001,
    0x000f_ffff_ffff_ffff,
    0x800f_ffff_ffff_ffff,
    0x0010_0000_0000_0000,
    0x8010_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0xffef_ffff_ffff_ffff,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
    0xfff8_0000_0000_0001,
    0x7ff0_0000_0000_0001,
    0xffff_ffff_ffff_ffff,
];

/// The bits of a float value.
fn bits(v: &Value) -> u64 {
    match v {
        Value::Float(x) => x.get().to_bits(),
        other => panic!("{other} is no float"),
    }
}

#[test]
fn a_hundred_thousand_float_pairs_over_every_class_agree_bit_for_bit() {
    let seed = seed();
    let mut r = Rng::new(seed);
    let mut pairs: Vec<(f64, f64)> = Vec::new();
    for x in FLOAT_CORNERS {
        for y in FLOAT_CORNERS {
            pairs.push((f64::from_bits(x), f64::from_bits(y)));
        }
    }
    while pairs.len() < 100_000 {
        let (cx, cy) = (r.below(5), r.below(5));
        pairs.push((of_class(&mut r, cx), of_class(&mut r, cy)));
    }
    // A NaN enters a program only as a value, which holds the canonical NaN whatever bits it was
    // made from: no literal, cast or operation gives a NaN with a payload (item 4).
    for &(x, y) in &pairs {
        for z in [x, y] {
            if z.is_nan() {
                assert_eq!(
                    bits(&Value::float(z)),
                    f64::NAN.to_bits(),
                    "{:#x}",
                    z.to_bits()
                );
            }
        }
    }
    let values: Vec<(Value, Value)> = pairs
        .iter()
        .map(|&(x, y)| (Value::float(x), Value::float(y)))
        .collect();
    let calls = differential(
        "float *",
        seed,
        &values,
        &nan_matched(),
        CHUNK,
        OptLevel::None,
        |k, w, g| float_same(floats_wanted(pairs[k]), w, g),
    );
    assert_eq!(calls, 0, "seed {seed}: float * runs inline");
}

/// What `nan_matched` gives on `(x, y)` by DESIGN.md: the string `NaN` for a NaN product, else
/// IEEE `x * y` by its bits.
fn floats_wanted((x, y): (f64, f64)) -> Option<u64> {
    let p = x * y;
    (!p.is_nan()).then_some(p.to_bits())
}

/// The kernel's result `w` and native code's `g` against `want` (`None` for the string `NaN`).
fn float_same(want: Option<u64>, w: &Value, g: &Value) -> Result<(), String> {
    let show = |v: &Value| match v {
        Value::Float(x) => format!("{v} ({:#018x})", x.get().to_bits()),
        _ => v.to_string(),
    };
    let wanted = match want {
        Some(b) => Value::float(f64::from_bits(b)),
        None => Value::str("NaN"),
    };
    let is = |v: &Value| match (v, want) {
        (Value::Float(x), Some(b)) => x.get().to_bits() == b,
        (Value::Str(_), None) => v == &wanted,
        _ => false,
    };
    match (is(w), is(g)) {
        (true, true) => Ok(()),
        (false, _) => Err(format!(
            "the kernel gives {}, IEEE {}",
            show(w),
            show(&wanted)
        )),
        (true, false) => Err(format!(
            "native code gives {}, IEEE {}",
            show(g),
            show(&wanted)
        )),
    }
}

/// One program per 2,000 pairs at `OptLevel::Speed` too, whose optimizer could fold or
/// reorder what `None` leaves alone: the first 2,000 integer pairs and float pairs.
#[test]
fn the_optimizing_level_agrees_on_a_sample() {
    let seed = seed();
    let pairs = int_pairs(seed, CHUNK);
    let values: Vec<(Value, Value)> = pairs.iter().map(|&(x, y)| (int(x), int(y))).collect();
    differential(
        "integer * at speed",
        seed,
        &values,
        &product(),
        CHUNK,
        OptLevel::Speed,
        |k, w, g| {
            let want = exact(pairs[k].0, pairs[k].1);
            match (w == &want, g == &want) {
                (true, true) => Ok(()),
                _ => Err(format!("kernel {w}, native {g}, exact {want}")),
            }
        },
    );
    let mut r = Rng::new(seed);
    let floats: Vec<(f64, f64)> = (0..CHUNK)
        .map(|_| {
            let (cx, cy) = (r.below(5), r.below(5));
            (of_class(&mut r, cx), of_class(&mut r, cy))
        })
        .collect();
    let values: Vec<(Value, Value)> = floats
        .iter()
        .map(|&(x, y)| (Value::float(x), Value::float(y)))
        .collect();
    differential(
        "float * at speed",
        seed,
        &values,
        &nan_matched(),
        CHUNK,
        OptLevel::Speed,
        |k, w, g| float_same(floats_wanted(floats[k]), w, g),
    );
}
