//! S22c at `n` and `8n`: the complement of `n` pieces at both ends of `i64`, and the preimage
//! of `y + 1 + … + 1 != MAX` with `k` ones. `overflow.rs` checks both at small sizes.

use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::interval::IntervalSet;
use zedc::store::preimage::{Demand, Domains, preimage};

use crate::overflow::{ones, spread};

#[test]
fn the_complement_at_the_ends_scales() {
    let sets: Vec<(usize, IntervalSet)> = [16384, 131_072].map(|n| (n, spread(n))).into();
    let top = IntervalSet::top();
    scaling::check(
        "the complement of n pieces at both ends of `i64`",
        16384,
        |n| {
            let s = &sets.iter().find(|(m, _)| *m == n).expect("a built set").1;
            std::hint::black_box(s.complement_in(&top));
        },
    );
    let terms: Vec<(usize, (Term, Domains))> = [1024, 8192].map(|k| (k, ones(k))).into();
    scaling::check("`y + 1 + … + 1 != MAX` with k ones", 1024, |k| {
        let (t, ds) = &terms.iter().find(|(m, _)| *m == k).expect("a built term").1;
        std::hint::black_box(preimage(t, ds, &Demand::Bool(true)));
    });
}
