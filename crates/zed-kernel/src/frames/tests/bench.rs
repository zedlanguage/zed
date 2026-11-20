//! The benchmark of [`Stack`], run by `tools/run_tests.sh --bench` and left out of its default
//! run (TEST-bench-move-crates, author P178: a deep recursion on a thread stack smaller than
//! the default). Its small instance among the correctness tests is
//! `calls_run_in_the_order_of_plain_recursion`, 100 calls deep on the default stack.

use super::*;

fn on_small_stack(f: impl FnOnce() + Send + 'static) {
    crate::scaling::on_a_stack(64 << 10, f);
}

#[test]
fn a_million_calls_deep_need_no_more_of_the_threads_stack() {
    on_small_stack(|| {
        let t = Trace {
            stack: Stack::default(),
            seen: Cell::new(0),
        };
        assert_eq!(t.stack.run(t.sum(1_000_000)), 500_000_500_000);
    });
}
