//! An edit script runs in time linear in its steps: the benchmark of `reuse.rs`, whose test runs
//! a script of a few steps.

use zed_tests::scaling::check;

use crate::reuse::{rates, run};

#[test]
fn a_script_runs_in_time_linear_in_its_steps() {
    let n = 8;
    let scripts = zed_tests::scaling::inputs(n, rates);
    check("an edit script of n steps", n, |k| {
        std::hint::black_box(run(&scripts[&k]));
    });
}
