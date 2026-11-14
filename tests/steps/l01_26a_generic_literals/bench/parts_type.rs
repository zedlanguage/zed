use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::checked;

use super::super::parts_type::{calls, parts};

#[test]
fn a_call_that_reads_many_parts_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 1600;
        let srcs = [parts(n), parts(scaling::FACTOR * n)];
        scaling::check("checking a call that reads n parts of its tuple", n, |m| {
            checked(&srcs[usize::from(m != n)]);
        });
    });
}

#[test]
fn many_calls_through_a_bounded_variable_check_in_linear_time() {
    let n = 1000;
    let srcs = [calls(n), calls(scaling::FACTOR * n)];
    scaling::check("checking n calls through a bounded variable", n, |m| {
        checked(&srcs[usize::from(m != n)]);
    });
}
