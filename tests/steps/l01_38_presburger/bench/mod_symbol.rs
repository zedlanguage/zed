//! The benchmarks of `mod_symbol.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::mod_symbol::*;
use std::collections::BTreeMap;
use zed_kernel::Term;
use zed_tests::scaling;

#[test]
fn translating_symbolic_divisors_scales() {
    let n = 1750;
    let built: BTreeMap<usize, Term> = [n, n * scaling::FACTOR]
        .into_iter()
        .map(|k| (k, splits(k)))
        .collect();
    let measure = move || {
        scaling::check("splits by symbolic divisors translated", n, |k| {
            assert_splits_translated(&built[&k], k);
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}
