//! Native code as deep as a program recurses (COMPLEXITY.md R10): a list built by nested calls
//! runs in time linear in the depth of the calls, and gives the kernel's value 10,000 and 80,000
//! calls deep on the 2 MiB stack of a spawned thread. The small instance is in `deep_calls.rs`.

use std::cmp::Ordering;

use zed_kernel::{Evaluator, Term, Value, World};
use zed_tests::deep::{linked_list, on_main_sized_stack};
use zed_tests::scaling;

use crate::deep_calls::native;
use crate::planned;

/// The depth of calls of the smaller run.
const CALLS: usize = 300_000;

/// Runs `f` on a thread with a 2 MiB stack, the default of a spawned Rust thread.
fn on_2_mib_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(2 << 20);
        thread.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

#[test]
fn deep_recursion_runs_in_time_linear_in_its_depth() {
    let programs = [CALLS, scaling::FACTOR * CALLS].map(|n| (n, planned(&linked_list(n as i64))));
    on_2_mib_stack(|| {
        scaling::check("native linked_list by its depth of calls", CALLS, |n| {
            let (g, p) = &programs.iter().find(|(m, _)| *m == n).unwrap().1;
            drop(native(g, p));
        })
    });
}

/// The kernel's value of `t`, on the stack of a main thread for the deep value it builds.
fn kernel(t: &Term) -> Value {
    on_main_sized_stack(|| Evaluator::new(World::new()).run(t).unwrap())
}

/// The depth of calls of the test below, which also runs 8 times as deep.
const DEEP_CALLS: usize = 10_000;

/// Small instance: `deep_calls::a_list_built_by_nested_calls_runs_natively_as_in_the_kernel`.
#[test]
fn a_list_built_by_10000_nested_calls_runs_on_a_2_mib_stack() {
    for k in [DEEP_CALLS, scaling::FACTOR * DEEP_CALLS] {
        let t = linked_list(k as i64);
        let want = kernel(&t);
        let (g, p) = planned(&t);
        let got = on_2_mib_stack(|| native(&g, &p));
        // `cmp` walks the two values on an explicit stack.
        assert!(
            got.cmp(&want) == Ordering::Equal,
            "linked_list({k}) run natively differs from the kernel's value"
        );
    }
}
