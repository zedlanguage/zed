//! Resolving a fence of many programs one at a time is linear in the programs: the benchmark of
//! `fences.rs`, whose test resolves the same fence at small sizes.

use crate::fences::{each_program_resolves, fence_of};

#[test]
fn a_fence_of_many_programs_scales() {
    // Each program is a slice of the fence's statements; a program that held every statement
    // before its `main` would read k² statements for k programs.
    let inputs = zed_tests::scaling::inputs(200, fence_of);
    zed_tests::scaling::check("a fence of k programs, resolved one at a time", 200, |k| {
        let (text, s) = &inputs[&k];
        each_program_resolves(text, s, k);
    });
}
