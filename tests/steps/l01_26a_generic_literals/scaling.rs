//! Generic literals at the rule of low complexity (DESIGN.md Part G): each joins its class
//! once, and each takes its carrier at run time by one `match` on the other operand.

use zed_tests::scaling;

use crate::l01_16_elaboration::elab;
use crate::l01_26_type_resolution::{info, sig};

/// A function of `n` untyped parameters, each added with a generic literal: `n` class
/// merges and `n` generic literals, nested `2n` deep.
fn sum(n: usize) -> String {
    let ps: Vec<String> = (0..n).map(|i| format!("positional x{i}")).collect();
    let body: Vec<String> = (0..n).map(|i| format!("x{i} + {}n", i + 1)).collect();
    format!("f({}) = {};\n", ps.join(", "), body.join(" + "))
}

#[test]
fn a_body_of_many_generic_literals_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&sum(2), "f"), "(T, T) -> T for T in int | f64 | rat");
            let n = 200;
            let srcs = [sum(n), sum(scaling::FACTOR * n)];
            scaling::check("a body of n generic literals and n class merges", n, |m| {
                let src = &srcs[usize::from(m != n)];
                let (info, _) = info(src);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
                assert_eq!(info.follows.len(), m);
                elab(src).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A function that calls a generic `mul` `n` times, each with a generic literal argument:
/// `n` literals that each take the carrier of the caller's parameter.
fn calls(n: usize) -> String {
    let body: Vec<String> = (0..n).map(|i| format!("mul(x, {}n)", i + 1)).collect();
    format!(
        "mul(positional x, positional k) = x * k;\nf(positional x) = {};\n",
        body.join(" + ")
    )
}

#[test]
fn a_body_of_many_generic_literal_arguments_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 29)
        .spawn(|| {
            assert_eq!(sig(&calls(2), "f"), "(T) -> T for T in int | f64 | rat");
            // At n = 200 a copy of the class's literals at each join stayed under the limit.
            let n = 1000;
            let srcs = [calls(n), calls(scaling::FACTOR * n)];
            scaling::check_order("a body of n generic literal arguments", n, 1, |m| {
                let src = &srcs[usize::from(m != n)];
                let (info, _) = info(src);
                assert!(info.errors.is_empty(), "{:?}", info.errors);
                assert_eq!(info.witness.len(), m);
                assert_eq!(info.follows.len(), m);
                elab(src).unwrap();
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
