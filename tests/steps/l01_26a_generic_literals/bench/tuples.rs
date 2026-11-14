use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::tuples::{deep, wide};

#[test]
fn a_deeply_nested_tuple_checks_in_linear_time() {
    scaling::on_a_thread(1 << 29, || {
        let n = 2000;
        let units = scaling::inputs(n, |m| Resolved::new(&deep(m)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert!(e.contains(&format!("{} is 0.5\n", "[1]".repeat(*m))), "{e}");
        }
        scaling::check_order("rejecting a decimal n tuples deep", n, 1, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

/// Checks the rejection of the decimal of `wide(m, call)` at `n = 1000` and `8n`.
fn a_wide_tuple(call: bool) {
    scaling::on_a_thread(1 << 29, || {
        let n = 1000;
        let units = scaling::inputs(n, |m| Resolved::new(&wide(m, call)));
        for (m, u) in &units {
            let [e] = &u.type_errors()[..] else {
                panic!("one rejection")
            };
            assert!(call || e.contains(&format!("y[{m}] is 0.5\n")), "{e}");
        }
        let what = match call {
            false => "rejecting the decimal of a tuple of n components",
            true => "rejecting the decimal of a tuple of n components passed to `id`",
        };
        scaling::check_order(what, n, 1, |m| {
            std::hint::black_box(units[&m].type_errors());
        });
    });
}

#[test]
fn a_wide_tuple_checks_in_linear_time() {
    a_wide_tuple(false);
}

#[test]
fn a_wide_tuple_checks_in_linear_time_passed_to_a_call() {
    a_wide_tuple(true);
}
