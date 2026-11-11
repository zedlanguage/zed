//! `f64Bits` of a NaN is the canonical NaN, in the kernel and in native code, whatever route
//! made the NaN. DESIGN.md step L1.39a: "`f64Bits(x)` is the IEEE 754 binary64 encoding of
//! `x`, an `int[0..<2 ^ 64]`, ... and the encoding of a NaN in each format is that format's
//! canonical NaN"; and sec:reduction, which defines it: "NaN canonicalized to the quiet NaN
//! with cleared sign and zero payload". For binary64 that is sign 0, exponent all ones, the
//! quiet bit (the highest fraction bit) 1 and the other 51 fraction bits 0: `0x7FF8000000000000`.
//! The expected values below are that constant, not what the code gives.
//!
//! On x86-64 the hardware does not give that NaN: `0.0 / 0.0`, `inf - inf`, `0.0 * inf` and
//! `inf / inf` give the default NaN `0xFFF8000000000000`, whose sign bit is set, and an
//! arithmetic operation with a NaN operand returns that operand's bits, sign and payload
//! included. So each program below makes its NaNs from operands it reads from its command
//! line, which the compiler cannot fold, and the executable's lines are compared with the
//! constant as well as with the interpreter's.

use std::ffi::OsString;
use std::path::Path;

use zed_kernel::{Prim, Value};
use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_36a_executables::{built, dir, executable, interpreter};

use super::x;

/// The canonical binary64 NaN: quiet, sign 0, payload 0 (DESIGN.md sec:reduction).
const CANONICAL: u64 = 0x7FF8_0000_0000_0000;

/// `f64Bits` of `f` in the kernel.
fn kernel_bits(f: f64) -> Value {
    zed_kernel::bits::word(Prim::F64Bits, &[Value::float(f)])
        .unwrap_or_else(|e| panic!("f64Bits({:#018x}): {e}", f.to_bits()))
}

#[test]
fn the_kernel_gives_the_canonical_nan_for_every_nan_encoding() {
    let want = Value::int(num_bigint::BigInt::from(CANONICAL));
    // Quiet and signaling NaNs of both signs, with the least, the greatest and a middle
    // payload, and the hardware's default NaN.
    let named = [
        0x7FF8_0000_0000_0000,
        0xFFF8_0000_0000_0000,
        0x7FF8_0000_0000_0001,
        0x7FFF_FFFF_FFFF_FFFF,
        0xFFFF_FFFF_FFFF_FFFF,
        0x7FF0_0000_0000_0001,
        0xFFF0_0000_0000_0001,
        0x7FF4_0000_0000_0000,
        0x7FF7_FFFF_FFFF_FFFF,
        0xFFF7_FFFF_FFFF_FFFF,
        0x7FFC_0000_DEAD_BEEF,
    ];
    for b in named {
        assert!(f64::from_bits(b).is_nan(), "{b:#018x}");
        assert_eq!(kernel_bits(f64::from_bits(b)), want, "{b:#018x}");
    }
    // Random NaNs: exponent all ones, sign and fraction random, the fraction not zero.
    let mut rng = Rng::new(0x7FF8);
    for _ in 0..10_000 {
        let r = rng.next_u64();
        let b = (r & 0x800F_FFFF_FFFF_FFFF) | 0x7FF0_0000_0000_0000;
        if b & 0x000F_FFFF_FFFF_FFFF == 0 {
            continue;
        }
        assert_eq!(kernel_bits(f64::from_bits(b)), want, "{b:#018x}");
    }
}

/// Checks that the interpreter (the kernel) and the executable `exe` built from `src` both
/// exit 0 and print `want` on `words`; one assertion shows both outputs, so a failure says
/// which side gives other bits.
fn both_print(src: &Path, exe: &Path, words: &[OsString], want: &str) {
    let run = interpreter(src, words, b"");
    let native = executable(exe, words, b"");
    assert_eq!(
        (
            (run.status, run.stdout.as_str()),
            (native.status, native.stdout.as_str())
        ),
        ((0, want), (0, want)),
        "(interpreter, executable)"
    );
}

/// The NaN routes the language has now (`sqrt` and `f64(#NaN)` come later; see the ignored tests
/// at the end), each made at run time from the operands
/// `z = 0.0`, `one = 1.0`, `m = -1.0` and `r`, a NaN read from the command line. Each fallback
/// after `else` is a value that makes no NaN, so a word the program fails to read shows as a
/// wrong line.
const ROUTES: &str = r#"
main(m: MainArgs) {
  z = f64(m.args[1] else "") else 1.0;
  one = f64(m.args[2] else "") else 0.0;
  m = f64(m.args[3] else "") else 0.0;
  r = f64(m.args[4] else "") else 0.0;
  nan = z / z;
  inf = one / z;
  m.stdout <- """
    zero over zero ${f64Bits(z / z)}
    inf minus inf ${f64Bits(inf - inf)}
    zero times inf ${f64Bits(z * inf)}
    inf over inf ${f64Bits(inf / inf)}
    negated ${f64Bits(-nan)}
    negated twice ${f64Bits(-(-nan))}
    nan plus one ${f64Bits(nan + one)}
    one plus nan ${f64Bits(one + nan)}
    one minus nan ${f64Bits(one - nan)}
    nan times minus one ${f64Bits(nan * m)}
    nan over minus one ${f64Bits(nan / m)}
    minus nan plus minus nan ${f64Bits(-nan + -nan)}
    min ${f64Bits(min(nan, one))}
    max ${f64Bits(max(one, -nan))}
    abs ${f64Bits(abs(-nan))}
    negative to the half ${f64Bits(m^0.5)}
    nan to the zero ${f64Bits(nan^z)}
    one to the nan ${f64Bits(one^nan)}
    nan to the nan ${f64Bits(nan^nan)}
    zero to the nan ${f64Bits(z^nan)}
    read ${f64Bits(r)}
    read negated ${f64Bits(-r)}
    read plus one ${f64Bits(r + one)}
    """;
}
"#;

/// The labels of [`ROUTES`]' lines, in order.
const LABELS: [&str; 23] = [
    "zero over zero",
    "inf minus inf",
    "zero times inf",
    "inf over inf",
    "negated",
    "negated twice",
    "nan plus one",
    "one plus nan",
    "one minus nan",
    "nan times minus one",
    "nan over minus one",
    "minus nan plus minus nan",
    "min",
    "max",
    "abs",
    "negative to the half",
    "nan to the zero",
    "one to the nan",
    "nan to the nan",
    "zero to the nan",
    "read",
    "read negated",
    "read plus one",
];

/// What [`ROUTES`] must print: every line the canonical NaN.
fn routes_expected() -> String {
    LABELS
        .iter()
        .map(|l| format!("{l} {CANONICAL}\n"))
        .collect()
}

#[test]
fn every_nan_route_gives_the_canonical_nan_in_the_interpreter_and_the_executable() {
    let d = dir("f64bits_nan_routes");
    let src = d.join("routes.zed");
    std::fs::write(&src, ROUTES).unwrap();
    let exe = d.join("routes");
    built(&src, &exe);
    let want = routes_expected();
    // `nan` is how a NaN prints, and `f64(s)` reads every string a float prints (DESIGN.md
    // sec:reduction); its sign comes from `-r`.
    let words: Vec<OsString> = ["--", "0.0", "1.0", "-1.0", "nan"]
        .iter()
        .map(OsString::from)
        .collect();
    both_print(&src, &exe, &words, &want);
}

/// The routes of [`ROUTES`] whose operands are literals, which the compiler may evaluate
/// before the program runs.
const FOLDED: &str = r#"
main(m: MainArgs) {
  m.stdout <- """
    zero over zero ${f64Bits(0.0 / 0.0)}
    inf minus inf ${f64Bits(1.0 / 0.0 - 1.0 / 0.0)}
    negated ${f64Bits(-(0.0 / 0.0))}
    nan plus one ${f64Bits(0.0 / 0.0 + 1.0)}
    negative to the half ${f64Bits((-1.0)^0.5)}
    nan to the zero ${f64Bits((0.0 / 0.0)^0.0)}
    one to the nan ${f64Bits(1.0^(0.0 / 0.0))}
    """;
}
"#;

#[test]
fn nans_of_literal_operands_give_the_canonical_nan_in_the_interpreter_and_the_executable() {
    let d = dir("f64bits_nan_folded");
    let src = d.join("folded.zed");
    std::fs::write(&src, FOLDED).unwrap();
    let exe = d.join("folded");
    built(&src, &exe);
    let want: String = [
        "zero over zero",
        "inf minus inf",
        "negated",
        "nan plus one",
        "negative to the half",
        "nan to the zero",
        "one to the nan",
    ]
    .iter()
    .map(|l| format!("{l} {CANONICAL}\n"))
    .collect();
    let words = [OsString::from("--")];
    both_print(&src, &exe, &words, &want);
}

/// The case whose NaN carries a sign bit into an addition: on x86-64, `z / z` with `z = 0.0`
/// gives `0xFFF8000000000000`, and `addsd` with a NaN operand returns that operand's bits, so
/// without canonicalization `f64Bits(z / z + 1.0)` would be `0xFFF8000000000000`
/// (18444492273895866368). The lines are compared with the constant, so the test fails if the
/// executable lets the sign or a payload through, whether or not the interpreter does too.
#[test]
fn a_nan_operand_of_an_addition_does_not_carry_its_sign_into_the_executable() {
    let src_text = r#"
main(m: MainArgs) {
  z = f64(m.args[1] else "") else 1.0;
  one = f64(m.args[2] else "") else 0.0;
  m.stdout <- "${f64Bits(z / z + one)} ${f64Bits(one + -(z / z))}";
}
"#;
    let d = dir("f64bits_nan_payload");
    let src = d.join("payload.zed");
    std::fs::write(&src, src_text).unwrap();
    let exe = d.join("payload");
    built(&src, &exe);
    let words: Vec<OsString> = ["--", "0.0", "1.0"].iter().map(OsString::from).collect();
    let native = executable(&exe, &words, b"");
    assert_eq!(
        (native.status, native.stdout.as_str()),
        (0, format!("{CANONICAL} {CANONICAL}\n").as_str())
    );
}

#[test]
#[ignore = "FLOAT-sqrt: `sqrt` is not yet defined"]
fn the_square_root_of_a_negative_is_the_canonical_nan() {
    assert_eq!(x("f64Bits(sqrt(-1.0))"), CANONICAL.to_string());
    assert_eq!(x("f64Bits(sqrt(-0.0 - 1e-300))"), CANONICAL.to_string());
}

#[test]
#[ignore = "NAN-cast-atoms: the float casts do not yet take `#NaN`"]
fn the_cast_of_the_nan_atom_is_the_canonical_nan() {
    // Outside `@fpwarn` code the cast gives the float with no atom (DESIGN.md sec:failure).
    assert_eq!(x("f64Bits(f64(#NaN))"), CANONICAL.to_string());
    assert_eq!(x("f64Bits(-f64(#NaN))"), CANONICAL.to_string());
    assert_eq!(x("f64Bits(f64(#inf) - f64(#inf))"), CANONICAL.to_string());
}

#[test]
#[ignore = "L1.18a: `f32Bits`, `f16Bits` and `bf16Bits` are not yet defined"]
fn the_other_formats_give_their_canonical_nan() {
    // The quiet NaN with cleared sign and zero payload of binary32, binary16 and bfloat16.
    assert_eq!(x("f32Bits(0.0f32 / 0.0f32)"), 0x7FC0_0000u32.to_string());
    assert_eq!(x("f16Bits(0.0f16 / 0.0f16)"), 0x7E00u16.to_string());
    assert_eq!(x("bf16Bits(0.0bf16 / 0.0bf16)"), 0x7FC0u16.to_string());
    assert_eq!(x("f32Bits(-(0.0f32 / 0.0f32))"), 0x7FC0_0000u32.to_string());
    assert_eq!(x("f16Bits(-(0.0f16 / 0.0f16))"), 0x7E00u16.to_string());
    assert_eq!(x("bf16Bits(-(0.0bf16 / 0.0bf16))"), 0x7FC0u16.to_string());
}
