//! Reading products and nested squares as powers, at `n` and `8n` factors or levels, on a
//! 2 MiB stack, as the `long` tests of [`super::scaling`] run; the terms are built before the
//! timing. `powers.rs` checks the same terms at small sizes and past 64 bits of count.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage::Domains;

use crate::doms;
use crate::powers::{alternating, at_most, fibonacci, pre, product, squares, var};

/// Checks the preimage of `make(k)` over `ds` at `n` and `8n`, to order 1, on a 2 MiB stack.
fn scales(what: &'static str, n: usize, ds: Domains, make: impl Fn(usize) -> Term + Send) {
    let measure = move || {
        let terms = scaling::inputs(n, make);
        scaling::check(what, n, |k| {
            pre(&terms[&k], &ds);
        });
    };
    scaling::on_a_thread(2 << 20, measure);
}

/// `i * i * … * i <= 1`, read as one power; and `i * i * j * i * j * … <= 1`, whose
/// products are read once each though the first factor of each lies as deep as the product.
/// The second stays at 512: at 4,096 and 32,768 it took 13.8 times the work and 22.8 times the
/// bytes (TEST-bench-move-l0125; plan row PERF-alternating-product-bytes).
#[test]
fn reading_a_product_as_a_power_is_linear_in_its_factors() {
    let ds = || doms(&[("i", Some(-50), Some(50)), ("j", Some(-50), Some(50))]);
    scales("`i * i * … * i <= 1` with n factors", 4096, ds(), |k| {
        at_most(product(&var("i"), k), 1)
    });
    scales(
        "`i * i * j * i * j * … <= 1` with n factors",
        512,
        ds(),
        |k| at_most(alternating(k), 1),
    );
}

/// `x1 = i * i; …; x<d> <= 0`, and the same over [`fibonacci`] counts: the count at depth
/// `d` has about `d` bits and is held exactly (COMPLEXITY.md S30b), so the counts take
/// `O(d^2)` bits in all, the `O(n log N)` of sec:constraints with `N` the largest count; its
/// time stays within the linear limit at these depths. At 6,000 and 48,000 the bytes of the
/// first grow 11.7 times, past the limit, so the depths stay (TEST-bench-move-l0125).
#[test]
fn reading_nested_squares_as_a_power_is_linear_in_their_depth() {
    let ds = || doms(&[("i", Some(-3), Some(3))]);
    scales("`x1 = i * i; …; x<n> <= 0`", 2048, ds(), |d| {
        squares(d, at_most(var(&format!("x{d}")), 0))
    });
    scales(
        "`x1 = i * i; x2 = x1 * i; …; x<n> <= 0`",
        2048,
        ds(),
        |d| fibonacci(d, at_most(var(&format!("x{d}")), 0)),
    );
}
