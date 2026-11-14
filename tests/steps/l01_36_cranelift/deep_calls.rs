//! Native code as deep as a program recurses (COMPLEXITY.md R10): a list built by nested calls
//! gives the kernel's value. The generated code runs on a stack the runtime maps for the run, as
//! large as the machine's memory, so no depth is refused before memory runs out. The test here
//! runs a few small depths on the test's own stack; the lists built by 10,000 and by 80,000
//! nested calls on the 2 MiB stack of a spawned thread are benchmarks, in `bench/deep_calls.rs`
//! (author P178: a test that needs an unusual size is a benchmark). The wide function of the
//! same row is in `deep_heap.rs`, a binary of its own.

use zed_kernel::{Evaluator, Value, World};
use zed_tests::deep::linked_list;
use zedc::zir::legalize::Legalized;
use zedc::zir::memory::Plan;

use super::planned;

/// `g` under `p` run natively.
pub(crate) fn native(g: &Legalized, p: &Plan) -> Value {
    zed_native::run(g, p, &mut Evaluator::new(World::new()))
        .unwrap()
        .value
}

#[test]
fn a_list_built_by_nested_calls_runs_natively_as_in_the_kernel() {
    for k in [0, 1, 2, 10] {
        let t = linked_list(k);
        let want = Evaluator::new(World::new()).run(&t).unwrap();
        let (g, p) = planned(&t);
        assert_eq!(native(&g, &p), want, "linked_list({k})");
    }
}
