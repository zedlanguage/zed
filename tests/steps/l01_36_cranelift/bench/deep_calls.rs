//! Native code as deep as a program recurses (COMPLEXITY.md R10): a list built by nested calls
//! runs in time linear in the depth of the calls. The correctness test is in `deep_calls.rs`.

use zed_tests::deep::linked_list;
use zed_tests::scaling;

use crate::deep_calls::{native, on_2_mib_stack};

/// The depth of calls of the smaller run.
const CALLS: usize = 300_000;
use crate::planned;

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
