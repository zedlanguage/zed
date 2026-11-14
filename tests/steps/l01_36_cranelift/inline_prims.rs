//! The primitives native code runs inline when their inputs allow, and gives to the kernel
//! otherwise: `sqrt` and `fma` of `f64` operands (IEEE 754-2019 section 5.4.1, one rounding),
//! and the code point of a string of one scalar, read in place. Each case gives the kernel's
//! value bit for bit, and the inline cases call no kernel.

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{F32, Prim, Term, Value};

use super::{float, kernel, native};

#[test]
fn sqrt_fma_and_code_point_run_inline_on_their_own_inputs_and_give_the_kernels_value() {
    let f32_ = |x: f32| lit(Value::Float32(F32::new(x)));
    let cat = |a: &str, b: &str| prim(Prim::Concat, vec![lit(a), lit(b)]);
    let sqrt = |x: Term| prim(Prim::Sqrt, vec![x]);
    let fma = |a: Term, b: Term, c: Term| prim(Prim::Fma, vec![a, b, c]);
    let cp = |x: Term| prim(Prim::CodePoint, vec![x]);
    // The case, the term, its value as the kernel prints it, and whether it runs inline.
    let cases: Vec<(&str, Term, &str, bool)> = vec![
        ("sqrt of a square", sqrt(float(2.25)), "1.5", true),
        ("sqrt of 2", sqrt(float(2.0)), "1.4142135623730951", true),
        ("sqrt of -0.0", sqrt(float(-0.0)), "-0.0", true),
        ("sqrt of a negative: NaN", sqrt(float(-1.0)), "nan", true),
        ("sqrt of infinity", sqrt(float(f64::INFINITY)), "inf", true),
        (
            "sqrt of an f32: the kernel",
            sqrt(f32_(2.25)),
            "1.5f32",
            false,
        ),
        (
            "fma, one rounding",
            fma(float(0.1), float(10.0), float(-1.0)),
            "5.551115123125783e-17",
            true,
        ),
        (
            "fma of an infinity and a zero: NaN",
            fma(float(f64::INFINITY), float(0.0), float(1.0)),
            "nan",
            true,
        ),
        (
            "fma with an f32 addend: the kernel",
            fma(float(2.0), float(3.0), f32_(1.0)),
            "",
            false,
        ),
        ("code point of a letter", cp(lit("a")), "97", true),
        ("code point of a two-byte scalar", cp(lit("é")), "233", true),
        (
            "code point of a four-byte scalar",
            cp(lit("😀")),
            "128512",
            true,
        ),
        (
            "code point of a fresh one-scalar string",
            cp(cat("", "z")),
            "122",
            true,
        ),
        (
            "code point of two scalars: the kernel",
            cp(lit("ab")),
            "#notScalar",
            false,
        ),
        (
            "code point of the empty string",
            cp(lit("")),
            "#notScalar",
            false,
        ),
        (
            "code point of a join",
            cp(cat("a", "b")),
            "#notScalar",
            false,
        ),
        ("code point of an int: the kernel", cp(lit(5)), "", false),
        (
            "code point of a string read twice",
            let_(
                "s",
                cat("q", ""),
                prim(Prim::Tuple, vec![cp(var("s")), cp(var("s"))]),
            ),
            "(113, 113)",
            true,
        ),
    ];
    for (case, t, want, inline) in cases {
        let k = kernel(&t);
        let n = native(&t);
        match (&k, &n) {
            (Ok(v), Ok(o)) => {
                assert_eq!(&o.value, v, "{case}: the kernel's value, bit for bit");
                if !want.is_empty() {
                    assert_eq!(v.to_string(), want, "{case}");
                }
                assert_eq!(
                    o.kernel_calls == 0,
                    inline,
                    "{case}: {} kernel calls",
                    o.kernel_calls
                );
            }
            (Err(a), Err(b)) => assert_eq!(a, b, "{case}"),
            _ => panic!("{case}: kernel {k:?}, native {:?}", n.map(|o| o.value)),
        }
    }
}
