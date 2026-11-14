//! The benchmarks of `mod_symbol.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::mod_symbol::*;
use std::collections::BTreeMap;
use std::sync::Arc;
use zed_kernel::Term;
use zed_tests::scaling;
use zedc::store::preimage::relations;

#[test]
fn translating_symbolic_divisors_scales() {
    let n = 1750;
    let built: BTreeMap<usize, Term> = [n, n * scaling::FACTOR]
        .into_iter()
        .map(|k| (k, splits(k)))
        .collect();
    let inputs: [Arc<str>; 2] = ["x".into(), "n".into()];
    let measure = move || {
        scaling::check("splits by symbolic divisors translated", n, |k| {
            let rs = relations(&[&built[&k]], &inputs, true).expect("in the domain");
            assert_eq!(rs[0].defs.len(), 2 * k);
        });
    };
    let thread = std::thread::Builder::new().stack_size(8 << 20);
    thread.spawn(measure).unwrap().join().unwrap();
}
