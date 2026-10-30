//! Integer, float and boolean arithmetic and comparisons run inline: no kernel call, no
//! cell. Every edge case the inline code cannot decide (an overflow, `-` of the least
//! integer, division) goes to the runtime and gives the kernel's value, and every inline
//! result is the kernel's bit for bit, NaN and the signed zeros included.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};

use super::{float, kernel, native};

#[test]
fn a_loop_of_integer_arithmetic_calls_no_kernel() {
    // The sum of the squares below 10, by a closure applied to each.
    let sq = lam(&["x"], prim(Prim::Mul, vec![var("x"), var("x")]));
    let mut sum = lit(0i64);
    for i in 0..10i64 {
        sum = prim(Prim::Add, vec![sum, app(var("sq"), vec![lit(i)])]);
    }
    let t = let_("sq", sq, sum);
    let o = native(&t).unwrap();
    assert_eq!(o.value, kernel(&t).unwrap());
    assert_eq!(o.value.to_string(), "285");
    assert_eq!(o.kernel_calls, 0);
    assert_eq!(o.stats.allocations, 1, "the closure is the one cell");
}

#[test]
fn comparisons_and_branches_on_scalars_call_no_kernel() {
    let t = if_(
        prim(
            Prim::And,
            vec![
                prim(Prim::Lt, vec![lit(3i64), lit(4i64)]),
                prim(Prim::Ge, vec![float(2.5), float(-0.0)]),
            ],
        ),
        prim(Prim::Neg, vec![float(1.5)]),
        float(0.0),
    );
    let o = native(&t).unwrap();
    assert_eq!(o.value, kernel(&t).unwrap());
    assert_eq!(o.value.to_string(), "-1.5");
    assert_eq!((o.kernel_calls, o.stats.allocations), (0, 0));
}

#[test]
fn every_edge_case_gives_the_kernels_value() {
    let big = i64::MAX;
    let cases = vec![
        prim(Prim::Add, vec![lit(big), lit(1i64)]),
        prim(Prim::Sub, vec![lit(i64::MIN), lit(1i64)]),
        prim(Prim::Mul, vec![lit(big), lit(2i64)]),
        prim(Prim::Neg, vec![lit(i64::MIN)]),
        prim(Prim::Div, vec![lit(7i64), lit(2i64)]),
        prim(Prim::Div, vec![lit(1i64), lit(0i64)]),
        prim(Prim::Div, vec![float(1.0), float(0.0)]),
        prim(Prim::Div, vec![float(0.0), float(0.0)]),
        prim(Prim::Sub, vec![float(f64::INFINITY), float(f64::INFINITY)]),
        prim(Prim::Mul, vec![float(-0.0), float(5.0)]),
        prim(Prim::Neg, vec![float(0.0)]),
        prim(Prim::Add, vec![float(-0.0), float(-0.0)]),
        prim(Prim::Lt, vec![float(f64::NAN), float(1.0)]),
        prim(Prim::Ge, vec![float(f64::NAN), float(f64::NAN)]),
        prim(Prim::Eq, vec![float(0.0), float(-0.0)]),
        prim(Prim::Eq, vec![lit(3i64), lit(3i64)]),
        prim(Prim::Ne, vec![lit(3i64), lit(4i64)]),
        prim(Prim::Add, vec![lit(1i64), float(2.0)]),
        prim(Prim::Lt, vec![lit(1i64), float(2.0)]),
        prim(Prim::Add, vec![lit(true), lit(1i64)]),
        prim(Prim::Not, vec![lit(1i64)]),
        prim(Prim::Or, vec![lit(false), lit(true)]),
        prim(Prim::Not, vec![lit(false)]),
    ];
    for t in &cases {
        let want = kernel(t);
        let got = native(t).map(|o| o.value);
        match (&want, &got) {
            // Bit for bit: equality of floats compares their bits.
            (Ok(w), Ok(g)) => assert_eq!(w, g, "{t:?}"),
            (Err(w), Err(g)) => assert_eq!(w, g, "{t:?}"),
            _ => panic!("{t:?}: kernel {want:?}, native {got:?}"),
        }
    }
}

#[test]
fn a_canonical_nan_and_a_negative_zero_survive_inline_arithmetic() {
    let nan = native(&prim(Prim::Mul, vec![float(f64::INFINITY), float(0.0)])).unwrap();
    assert_eq!(nan.kernel_calls, 0);
    let zed_kernel::Value::Float(x) = nan.value else {
        panic!("a float")
    };
    assert_eq!(x.get().to_bits(), f64::NAN.to_bits());
    let z = native(&prim(Prim::Neg, vec![float(0.0)])).unwrap().value;
    let zed_kernel::Value::Float(x) = z else {
        panic!("a float")
    };
    assert_eq!(x.get().to_bits(), (-0.0f64).to_bits());
}

#[test]
fn an_overflow_goes_to_the_runtime_once() {
    let o = native(&prim(Prim::Add, vec![lit(i64::MAX), lit(1i64)])).unwrap();
    assert_eq!(o.kernel_calls, 1);
    let o = native(&prim(Prim::Add, vec![lit(i64::MAX - 1), lit(1i64)])).unwrap();
    assert_eq!(o.kernel_calls, 0);
}
