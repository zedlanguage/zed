use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::tuples::{deep, wide};

#[test]
fn a_deeply_nested_tuple_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 10_000;
        let units = scaling::inputs(n, |m| Resolved::new(&deep(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert!(e.contains(&format!("{} is 0.5\n", "[1]".repeat(*m))), "{e}");
        }
        scaling::check_order("rejecting a division n tuples deep", n, 1, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// Checks the rejection of the division of `wide(m, call)` at `n = 7300` and `8n`.
fn a_wide_tuple(call: bool) {
    scaling::on_a_thread(1 << 29, || {
        let n = 7300;
        // Each program is resolved only in the process that checks it, and the rejection is
        // asserted on what each run finds (`scaling::check_inputs`;
        // FAIL-bench-first-phase-past-20s-l0126-l0129). The text the message must hold is
        // made with the input, outside the run.
        let unit = |m: usize| {
            let named = format!("y[{m}] is 0.5\n");
            (Resolved::new(&wide(m, call)), named)
        };
        let what = match call {
            false => "rejecting the division of a tuple of n components",
            true => "rejecting the division of a tuple of n components passed to `id`",
        };
        scaling::check_inputs(what, n, unit, |(u, named)| {
            let errors = u.type_errors();
            let [e] = &errors[..] else {
                panic!("one rejection")
            };
            assert!(call || e.contains(named.as_str()), "{e}");
            std::hint::black_box(errors);
        });
    });
}

/// Besides its ratio: one rejection, naming the component that holds the division. Small instance:
/// `tuples::the_division_of_a_wide_tuple_is_one_rejection_naming_its_component`.
#[test]
fn a_wide_tuple_checks_in_linear_time() {
    a_wide_tuple(false);
}

/// Besides its ratio: one rejection. Small instance, passed to a call and not:
/// `tuples::the_division_of_a_wide_tuple_is_one_rejection_naming_its_component`.
#[test]
fn a_wide_tuple_checks_in_linear_time_passed_to_a_call() {
    a_wide_tuple(true);
}
