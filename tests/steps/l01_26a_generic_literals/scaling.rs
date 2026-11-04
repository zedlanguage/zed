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
            scaling::check(
                "a body of n generic literals and n class merges",
                200,
                |n| {
                    let src = sum(n);
                    let (info, _) = info(&src);
                    assert!(info.errors.is_empty(), "{:?}", info.errors);
                    assert_eq!(info.follows.len(), n);
                    elab(&src).unwrap();
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
