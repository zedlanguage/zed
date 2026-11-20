//! `f32` and `f64` of an `f64` keep the sign of a zero (row FAIL-values-cast-negzero, found by
//! TEST-complete-values, author P189): the kernel narrowed a float through its exact rational,
//! which has no sign of zero.

use zed_tests::step_helpers::l01_16_elaboration::value;

/// Functions that pass their argument on, so the checker does not read the operand.
const PASS: &str = "real(positional v: f64) = v;\ntext(positional v: String) = v;\n";

fn x(expr: &str) -> String {
    value(&format!("{PASS}x = {expr};\n"), "x")
}

/// DESIGN.md L1.18: `f32` of an `f64` is "the f32 equal to it", and a float cast that is exact
/// keeps the IEEE value, so `-0.0` stays `-0.0`, as `f64` of an `f32` already keeps it.
#[test]
fn a_float_cast_of_a_negative_zero_keeps_its_sign() {
    let cases = [
        ("f32(real(-0.0f64))", "-0.0f32"),
        ("f32(-0.0f64)", "-0.0f32"),
        ("f32(f64(text(\"-0\")))", "-0.0f32"),
        ("f64(real(-0.0f64))", "-0.0"),
        ("f64(-0.0f64)", "-0.0"),
        ("String(f32(real(-0.0f64)))", "\"-0.0\""),
        // Already right, for contrast.
        ("f64(f32(text(\"-0\")))", "-0.0"),
        ("f32(text(\"-0\"))", "-0.0f32"),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}

/// The neighbors of the case, through the same narrowing: a positive zero, the zeros equal
/// under IEEE `==`, a tiny float that rounds to the zero of its sign (IEEE 754 round to
/// nearest, step L1.18), the least `f32` subnormal, and `f64` of the infinities and the NaN.
/// IEEE Std 754-2019, doi:10.1109/IEEESTD.2019.8766229: comparisons, section 5.11 (full
/// comment in zed-kernel `value.rs`, `Value::surface_cmp`), and rounding, section 4.3 (full
/// comment in zed-kernel `num.rs`, enum `Rounding`); the narrowing is in zed-kernel
/// `words.rs`, at `Prim::CastF32` on a `Value::Float`.
#[test]
fn a_float_narrowed_to_f32_near_zero_and_f64_of_an_f64() {
    let cases = [
        ("f32(real(0.0f64))", "0.0f32"),
        ("f32(real(-0.0f64)) == f32(real(0.0f64))", "true"),
        ("f32(real(1.0e-46f64))", "0.0f32"),
        ("f32(real(-1.0e-46f64))", "-0.0f32"),
        ("f32(real(1.401298464324817e-45f64))", "1.0e-45f32"),
        ("f32(real(-1.401298464324817e-45f64))", "-1.0e-45f32"),
        ("f64(real(0.0f64))", "0.0"),
        ("f64(real(-2.5f64))", "-2.5"),
        ("String(f64(f64(text(\"-inf\"))))", "\"-inf\""),
        ("String(f64(f64(text(\"nan\"))))", "\"nan\""),
    ];
    for (e, want) in cases {
        assert_eq!(x(e), want, "{e}");
    }
}
