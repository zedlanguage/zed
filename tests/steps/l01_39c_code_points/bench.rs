//! `utf8` and `fromUtf8` against the number of bytes: each reads the bytes once and builds or
//! reads a family of one entry per byte, keys in increasing order, so the work is of order n
//! (with the family's `log n` per entry, within the order `check_order` allows). The strings
//! and families are built before the timing.

use std::collections::HashMap;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;

/// A string of `n` bytes cycling through scalars of 1, 2, 3 and 4 bytes, so `n` is a multiple
/// of 10.
fn text(n: usize) -> String {
    "aé€😀".repeat(n / 10)
}

fn run(p: Prim, x: &Value) -> Value {
    zed_kernel::eval(&Term::Prim(p, vec![Term::Lit(x.clone())])).unwrap()
}

/// The inputs at sizes `n` and `8n`: each string and its bytes.
fn inputs(n: usize) -> HashMap<usize, (Value, Value)> {
    [n, scaling::FACTOR * n]
        .into_iter()
        .map(|m| {
            let s = Value::str(&text(m));
            let b = run(Prim::Utf8, &s);
            (m, (s, b))
        })
        .collect()
}

#[test]
fn utf8_is_linear_in_the_bytes() {
    let n = 10 * (1 << 16);
    let xs = inputs(n);
    scaling::check_order("utf8 of n bytes", n, 1, |m| {
        let (s, _) = &xs[&m];
        for _ in 0..4 {
            run(Prim::Utf8, s);
        }
    });
}

#[test]
fn from_utf8_is_linear_in_the_bytes() {
    let n = 10 * (1 << 19);
    let xs = inputs(n);
    assert_eq!(run(Prim::FromUtf8, &xs[&n].1), xs[&n].0);
    scaling::check_order("fromUtf8 of n bytes", n, 1, |m| {
        let (_, b) = &xs[&m];
        for _ in 0..4 {
            run(Prim::FromUtf8, b);
        }
    });
}
