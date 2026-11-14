//! Benchmarks of `loops`: each times the work at a size and at 8 times it, run apart from
//! the correctness tests (`tools/run_tests.sh --bench`).

use super::*;

#[test]
fn classifying_a_chain_of_choices_scales() {
    for (closed, outcome) in [(false, true), (true, true), (true, false)] {
        let built = scaling::inputs(200, |k| (chain_scope(k), chain(k, closed)));
        let what = match (closed, outcome) {
            (false, _) => "an open chain of choices classified",
            (true, true) => "a closed chain of choices classified, with its message",
            (true, false) => "the opposite of a closed chain, one choice, classified",
        };
        scaling::check_order(what, 200, 1, |k| {
            let (s, t) = &built[&k];
            assert_eq!(s.looped_test(t, outcome).is_some(), closed && outcome);
        });
    }
}
