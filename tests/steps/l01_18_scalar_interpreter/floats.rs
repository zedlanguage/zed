//! How `String` writes a float, and the round trip `f64(String(x)) == x`, bit for bit.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{Prim, Value, eval};

use super::x;

#[test]
fn a_receipt_prints_floats_in_their_shortest_form() {
    assert_eq!(x("String(0.1 + 0.2)"), "\"0.30000000000000004\"");
    assert_eq!(x("\"total: ${19.99 * 3.0}\""), "\"total: 59.97\"");
    assert_eq!(x("String(2.0)"), "\"2.0\"", "a whole float keeps its point");
    assert_eq!(x("String(-0.0)"), "\"-0.0\"");
}

#[test]
fn fixed_notation_runs_from_one_millionth_to_below_ten_to_the_21() {
    let cases = [
        ("0.000001", "0.000001"),
        ("0.0000001", "1.0e-7"),
        ("123456789012345678901.0", "123456789012345680000.0"),
        ("1.0e21", "1.0e21"),
        ("6.02214076e23", "6.02214076e23"),
        ("5.0e-324", "5.0e-324"),
    ];
    for (lit, want) in cases {
        assert_eq!(x(&format!("String({lit})")), format!("\"{want}\""), "{lit}");
    }
}

#[test]
fn of_two_equally_near_shortest_forms_the_larger_magnitude_prints() {
    // The double is exactly 1666666666666669.25; .2 and .3 both read back to it.
    assert_eq!(x("String(1666666666666669.25)"), "\"1666666666666669.3\"");
    assert_eq!(x("String(-1666666666666669.25)"), "\"-1666666666666669.3\"");
    assert_eq!(
        x("f64(\"1666666666666669.3\") == 1666666666666669.25"),
        "true"
    );
    assert_eq!(
        x("f64(\"1666666666666669.2\") == 1666666666666669.25"),
        "true"
    );
}

/// `D * 10^-j` written with a point: `decimal_text(12, 3)` is `0.012`.
fn decimal_text(d: u128, j: u32) -> String {
    let digits = format!("{d:0>width$}", width = j as usize + 1);
    let (whole, frac) = digits.split_at(digits.len() - j as usize);
    format!("{whole}.{frac}")
}

/// A printed float as `(n, s)` with value `n * 10^s` and `n` not a multiple of 10.
fn decimal_value(text: &str) -> (u128, i32) {
    let (mantissa, exp) = text.split_once('e').unwrap_or((text, "0"));
    let (whole, frac) = mantissa.split_once('.').expect("a point");
    let mut n: u128 = format!("{whole}{frac}").parse().expect("digits");
    let mut s = exp.parse::<i32>().expect("an exponent") - frac.len() as i32;
    while n != 0 && n.is_multiple_of(10) {
        n /= 10;
        s += 1;
    }
    (n, s)
}

fn splitmix64(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn show(v: f64) -> String {
    match eval(&prim(Prim::Show, vec![lit(Value::float(v))])).unwrap() {
        Value::Str(s) => s.to_string(),
        other => panic!("String({v:e}) gave {other}"),
    }
}

fn read_f64(text: &str) -> f64 {
    match eval(&prim(Prim::CastF64, vec![lit(Value::str(text))])).unwrap() {
        Value::Float(f) => f.get(),
        other => panic!("f64({text:?}) gave {other}"),
    }
}

/// Every finite float with two shortest forms equally near it, sampled, prints the one of
/// larger magnitude (DESIGN.md sec:reduction, item 1: "Of two shortest digit strings equally
/// near the value, printing takes the one of larger magnitude").
///
/// Where ties are. Let `v = M * 2^-p` with `2^52 < M < 2^53`, so floats near `v` are `2^-p`
/// apart and a decimal reads back to `v` when it is within `2^-p / 2` of it. `v` is halfway
/// between `D * 10^-j` and `(D + 1) * 10^-j` exactly when `2 * 10^j * v = M * 5^j * 2^(j+1-p)`
/// is odd, that is when `M = K * 2^t` with `K` odd and `t = p - j - 1`; then
/// `2 * 10^j * v = K * 5^j`. Both decimals are `10^-j / 2` from `v`, so both read back when
/// `10^-j <= 2^-p`, and they are the shortest forms only if no multiple of `10^-(j-1)` reads
/// back, which needs `2^-p < 10^-(j-1)`. So `j` is the least `j` with `10^j >= 2^p`, and
/// `0 <= t <= 51` must hold. As `j` is about `0.301 p`, `t <= 51` fails for `p > 75`, and
/// `j >= 1` with `t >= 0` needs `p >= 2`: ties exist only for `2^-23 <= |v| < 2^51`. A float
/// at the bottom of its binade (`M = 2^52`) or subnormal has no tie: `t` would be at least 52.
/// In units of `10^-j / 2`, `v` is `K * 5^j`, an odd multiple of 5, so the nearest multiple of
/// `10^-(j-1)` (of 20 in these units) is always 5 units away, and it reads back exactly when
/// `5 * 2^p < 10^j`. So a binade with `0 <= t <= 51` either has no tie or every `v` in it with
/// `M = K * 2^t` is one, by whether `10^j < 5 * 2^p`: 52 of the 74 binades in that range.
/// This test draws `K` at random in every binade where `0 <= t <= 51`, and for each sample
/// checks in exact integers that `v` is halfway, that both neighbors read back, and whether
/// either multiple of `10^-(j-1)` nearest `v` does, which must agree with the binade's rule; a
/// sample whose coarser neighbor reads back is not a tie and is skipped. For each tie, both
/// texts read back through `f64(s)`, and `String` prints `D + 1`, with `-` before it for `-v`.
/// Its cost is linear in the samples: each is a fixed number of operations on at most 128 bits
/// and four evaluations.
///
/// Rust's `{:e}`, which `zed_kernel::num::show_f64` calls, takes `D + 1` this way (Rust 1.99.1,
/// `library/core/src/num/imp/flt2dec/strategy/`): `grisu::format_shortest` calls
/// `format_shortest_opt`, whose `round_and_weed` returns `None` (grisu.rs:442) when the digits
/// nearest `v` plus its error bound differ from those nearest `v` minus it, as they do at an
/// exact tie, and the fallback `dragon::format_shortest` rounds up when both the down and the
/// up condition hold and twice the remainder is at least the scale (dragon.rs:247,
/// `if up && (!down || *mant.mul_pow2(1) >= scale)`), so a remainder of exactly one half goes
/// up. Nothing pins the toolchain, so this test is what holds the rule.
#[test]
fn every_sampled_tie_prints_the_larger_magnitude() {
    const PER_BINADE: usize = 1000;
    let mut seed: u64 = 0x5eed_0f71_e5ed;
    let mut binades_with_ties = Vec::new();
    let mut ties = 0usize;
    for p in 1u32..=100 {
        let j = (0u32..)
            .find(|&j| 10u128.pow(j) >= 1u128 << p)
            .expect("a power of ten");
        if j == 0 || p < j + 1 || p - j - 1 > 51 {
            continue;
        }
        let t = p - j - 1;
        let e = 52 - p as i32; // 2^e <= v < 2^(e+1)
        let ten_j = 10u128.pow(j);
        let binade_has_ties = ten_j < 5u128 << p;
        let mut found = 0usize;
        for _ in 0..PER_BINADE {
            let low = 1u64 << (52 - t);
            let k = (low + splitmix64(&mut seed) % low) | 1;
            let m = k << t;
            let v = f64::from_bits((((e + 1023) as u64) << 52) | (m - (1 << 52)));
            // In units of 10^-j / 2: v is K * 5^j, and a decimal reads back to v when its
            // distance from v, times 2^p, is below 10^j, or equal to it with M even.
            let at = u128::from(k) * 5u128.pow(j);
            let reads_back = |distance: u128| {
                let scaled = distance << p;
                scaled < ten_j || (scaled == ten_j && m.is_multiple_of(2))
            };
            assert_eq!(
                at % 2,
                1,
                "{v:e} is halfway between two multiples of 10^-{j}"
            );
            assert!(reads_back(1), "{v:e}: both neighbors read back");
            let coarse = at / 20; // the multiples of 10^-(j-1) are the multiples of 20
            let coarser_reads_back =
                reads_back(at - 20 * coarse) || reads_back(20 * (coarse + 1) - at);
            assert_eq!(
                coarser_reads_back, !binade_has_ties,
                "{v:e}: the binade's rule"
            );
            if coarser_reads_back {
                continue;
            }
            let lower = (at - 1) / 2;
            let (lo_text, hi_text) = (decimal_text(lower, j), decimal_text(lower + 1, j));
            assert_eq!(lo_text.len(), hi_text.len(), "{v:e}: equally short");
            for text in [&lo_text, &hi_text] {
                assert_eq!(read_f64(text).to_bits(), v.to_bits(), "{text} reads back");
            }
            let printed = show(v);
            assert_eq!(
                decimal_value(&printed),
                (lower + 1, -(j as i32)),
                "{v:e} printed {printed}, not {hi_text}"
            );
            assert_eq!(show(-v), format!("-{printed}"));
            found += 1;
        }
        if found > 0 {
            binades_with_ties.push(e);
        }
        ties += found;
    }
    assert_eq!(binades_with_ties.len(), 52, "{binades_with_ties:?}");
    assert_eq!(binades_with_ties.first(), Some(&50));
    assert_eq!(binades_with_ties.last(), Some(&-23));
    assert_eq!(ties, 52 * PER_BINADE);
}

#[test]
fn infinities_and_nan_have_names() {
    assert_eq!(x("String(1.0 / 0.0)"), "\"inf\"");
    assert_eq!(x("String(-1.0 / 0.0)"), "\"-inf\"");
    assert_eq!(x("String(0.0 / 0.0)"), "\"nan\"");
    assert_eq!(x("f64(\"-inf\") < 0.0"), "true");
    assert_eq!(
        x("f64(\"nan\") == f64(\"nan\")"),
        "false",
        "NaN is not == itself"
    );
}

/// `f64(String(x))` by the kernel's own primitives.
fn round_trip(v: f64) -> Value {
    let shown = prim(Prim::Show, vec![lit(Value::float(v))]);
    eval(&prim(Prim::CastF64, vec![shown])).unwrap()
}

#[test]
fn every_float_reads_back_to_itself() {
    let mut edges = vec![
        0.0,
        -0.0,
        f64::MIN_POSITIVE,
        f64::MIN_POSITIVE / 3.0,
        f64::from_bits(1),
        f64::MAX,
        f64::MIN,
        f64::EPSILON,
        1e21,
        1e-7,
        123456.789,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ];
    // A fixed linear congruential sequence of bit patterns, every exponent among them.
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    for _ in 0..20_000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let v = f64::from_bits(state);
        if !v.is_nan() {
            edges.push(v);
        }
    }
    for v in edges {
        match round_trip(v) {
            Value::Float(back) => assert_eq!(back.get().to_bits(), v.to_bits(), "{v:e}"),
            other => panic!("{v:e} read back as {other}"),
        }
    }
    assert!(matches!(round_trip(f64::NAN), Value::Float(b) if b.get().is_nan()));
}
