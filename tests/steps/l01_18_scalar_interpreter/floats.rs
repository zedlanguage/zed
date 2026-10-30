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
