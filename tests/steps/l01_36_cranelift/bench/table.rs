//! The heap's table of uncounted values and its cells against the number of runs of a match
//! or a read (COMPLEXITY.md R12): matches of a function and reads and drops of bare values run
//! in time linear in their number. The small instances are in `table.rs`.

use zed_kernel::World;

use super::scaling::check_run;
use crate::table::{bare, bare_world, fun_is, fun_wild};

#[test]
fn matches_of_a_function_by_is_scale() {
    check_run("n matches of a function by is", 1_250, fun_is, |_| {
        World::new()
    });
}

#[test]
fn matches_of_a_function_by_wild_scale() {
    check_run("n matches of a function by _", 1_250, fun_wild, |_| {
        World::new()
    });
}

#[test]
fn bare_values_made_and_dropped_scale() {
    check_run("n reads and drops of bare values", 1_200, bare, bare_world);
}
