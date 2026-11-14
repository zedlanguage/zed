//! Checking `n` powers and their repairs, at `n` and `8n` (`power_repairs.rs`).

use zed_tests::scaling;

use crate::power_repairs::*;

/// Checks the program of `make(n)` and `make(8n)` with `verdict`.
fn checking(what: &str, make: fn(usize) -> String, verdict: fn(&str)) {
    let n = 64;
    let made = scaling::inputs(n, |k| program(&make(k)));
    scaling::check(what, n, |k| verdict(&made[&k]));
}

#[test]
fn checking_bound_powers_to_negative_literals_scales() {
    checking(
        "checking n bound powers to negative literals and n powers in one class",
        negative_bound,
        is_rejected,
    );
}

#[test]
fn checking_repairs_at_uses_scales() {
    checking(
        "checking repairs at the uses of n names and n uses of a name",
        bound_uses,
        is_rejected,
    );
}

#[test]
fn a_chain_of_powers_scales() {
    checking(
        "checking a chain of n powers of powers",
        tower,
        checks_whole,
    );
}

#[test]
fn a_tower_of_powers_under_a_test_scales() {
    checking(
        "checking a tower of n powers under a test",
        narrowed_tower,
        checks_whole,
    );
}

#[test]
fn a_tower_at_its_least_power_checks_and_scales() {
    checking(
        "checking a tower of n powers, each at its least power",
        |n| least_power_tower(n, 2),
        checks_whole,
    );
}
