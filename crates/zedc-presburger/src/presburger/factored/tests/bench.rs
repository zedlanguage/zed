//! The benchmarks of `factored::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Each checks the measured work at n and 8n against the limit 10.5
//! (`crate::scaling`). Their negative control is the count of every pair (what `products`
//! listed before the factored solver), which grows 64 times on the same family
//! (`no_pair_of_the_star_is_listed_and_the_work_scales`), and the red run of
//! `entails::bench_entails_on_the_star`: the same file run on the code before the solver.
//! No bench runs the whole solver on `wlgrow`: its exact peel grows 47 times there
//! (exception 3 of the design, COMPLEXITY.md, the A225 entry).

use super::*;

mod entails;

/// `products`' pair search end to end on [`star`]: k rows on each factor, no pair kept.
#[test]
fn bench_factored_star() {
    crate::scaling::check_inputs(
        "factored kept_pairs on the star",
        2000,
        star,
        |(rows, on, wanted, partners)| {
            let rows: Vec<&Lin> = rows.iter().collect();
            assert!(super::super::kept_pairs(&rows, on, wanted, partners).is_empty());
        },
    );
}
