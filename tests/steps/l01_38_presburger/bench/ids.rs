//! The benchmarks of `ids.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::ids::*;
use std::collections::BTreeMap;
use zed_tests::scaling;
use zedc::store::conjuncts::Conjuncts;
use zedc::store::presburger::{Formula, project_each};

#[test]
fn passes_over_shared_parts_take_time_linear_in_the_distinct_parts() {
    // A chain of d rules holds `a0` about 1.6^d times written out; each pass reads each rule
    // once. Two chains built apart share no part, so their comparison reads each pair once.
    let n = 3000;
    let built: BTreeMap<usize, [Formula; 3]> = [n, scaling::FACTOR * n]
        .map(|d| {
            let and = chain(d, true, &mut || {}).0;
            let apart = chain(d, true, &mut || {}).0;
            let or = chain(d, false, &mut || {}).0;
            (d, [and, apart, or])
        })
        .into();
    scaling::check(
        "conjuncts, folds, comparison and projection of a chain of d shared rules",
        n,
        |d| {
            let [and, apart, or] = &built[&d];
            let mut c = Conjuncts::default();
            c.and(and.clone());
            assert!(!c.set().is_empty());
            assert_eq!(and.atoms().len(), 2);
            assert_eq!(or.cons().len(), 2 * d + 2);
            assert!(and == apart);
            assert!(project_each(or, &[atom("x")]).is_ok());
        },
    );
}
