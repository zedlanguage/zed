//! The repairs of `domain_repairs.rs` at `n` and `8n`.

use zed_tests::scaling;

use crate::domain_repairs::*;

#[test]
fn a_pushed_chain_of_names_of_literals_is_rejected_in_linear_time() {
    let n = 1000;
    let srcs = scaling::inputs(n, a_pushed_chain);
    scaling::check("rejecting the push of a chain of n names", n, |k| {
        a_pushed_chain_rejected(&srcs[&k], k);
    });
}

#[test]
fn naming_the_repairs_value_takes_time_linear_in_the_call() {
    let n = 1000;
    let srcs = scaling::inputs(n, crowded);
    scaling::check("the name of a repair among n names the call writes", n, |k| {
        the_repairs_value_named(&srcs[&k], k);
    });
}

#[test]
fn a_width_repair_takes_time_linear_in_the_call() {
    let n = 1000;
    let srcs = scaling::inputs(n, a_wide_bit_not);
    scaling::check("the width repair of a call of n terms", n, |k| {
        a_width_repair(&srcs[&k], k);
    });
}
