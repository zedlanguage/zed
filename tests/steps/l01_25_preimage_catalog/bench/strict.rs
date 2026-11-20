//! Grading a term in its binder (TONIC-strict) costs O(n) for n subterms: a chain of `n`
//! stages and a chain of `n` lets that each read the previous name twice, at `n` and `8n`, on
//! a 2 MiB stack, the terms built before the timing. `strict.rs` checks the grades of the same
//! terms at small sizes.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::axioms::Tonicity;
use zedc::store::grade::{Arith, grade};

use crate::doms;
use crate::strict::{chain, doubling};

/// Grades `make(n)` and `make(8n)` in `x` over `lo..`, on a 2 MiB stack.
fn scales(what: &'static str, n: usize, lo: Option<i64>, make: fn(usize) -> Term) {
    scaling::on_a_stack(2 << 20, || {
        let made = scaling::inputs(n, make);
        let d = doms(&[("x", lo, None)]);
        assert_eq!(
            grade(&made[&n], "x", &d, Arith::Int),
            Some(Tonicity::StrictUp)
        );
        scaling::check(what, n, |k| {
            std::hint::black_box(grade(&made[&k], "x", &d, Arith::Int));
        });
    });
}

#[test]
fn grading_scales_linearly() {
    scales("grading a chain over all integers", 12_500, None, chain);
}

/// Over `x >= 0` the ends of each stage's range are finite and grow with the chain's products.
#[test]
fn grading_with_growing_ends_scales_linearly() {
    scales("grading a chain over x >= 0", 12_500, Some(0), chain);
}

#[test]
fn grading_shared_lets_scales_linearly() {
    scales("grading a chain of shared lets", 6_250, Some(0), doubling);
}
