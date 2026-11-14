//! The chosen product of `Poly::mul` grows with its terms: the benchmark of `choice.rs`.

use zed_tests::scaling;

use crate::choice::{chosen, sum};

#[test]
fn the_chosen_product_of_n_dense_terms() {
    let ins = scaling::inputs(1000, |n| (sum(0..n as u128, 3), sum(0..n as u128, -5)));
    scaling::check(
        "the chosen product of two univariate sums of n terms",
        1000,
        |n| {
            let (a, b) = &ins[&n];
            assert_eq!(chosen(a, b).len(), 2 * n - 1);
        },
    );
}
