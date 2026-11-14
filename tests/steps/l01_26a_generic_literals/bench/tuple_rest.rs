use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::tuple_rest::{chain, decimals, printed};

#[test]
fn many_decimals_on_one_line_print_the_line_once() {
    // Negative control (run once, not committed): one message for each decimal, each quoting
    // the line, as before this item, printed 16.2 times the bytes for 4 times the decimals
    // (964335 bytes for n = 200, 15605535 for 800), and failed the bound below. One message
    // prints 4.0 times (zedc: 51340 bytes for 200, 207641 for 800). Held at 200 and 1,600
    // decimals since the limit of 13 (TESTS-scaling-limit-13).
    scaling::on_a_thread(1 << 28, || {
        let n = 6600;
        let bytes = |m: usize| printed(&decimals(m)).len() as u64;
        scaling::hold_linear(
            &format!(
                "{n} and {} decimals on one line, rejected",
                scaling::FACTOR * n
            ),
            "bytes printed",
            bytes(n),
            bytes(scaling::FACTOR * n),
        );
        assert_eq!(
            printed(&decimals(n)).matches(&decimals(n)[..20]).count(),
            1,
            "the line is printed once"
        );
        let units = scaling::inputs(n, decimals);
        scaling::check_order(
            "printing the rejection of n decimals on one line",
            n,
            1,
            |m| {
                std::hint::black_box(printed(&units[&m]));
            },
        );
    });
}

#[test]
fn many_calls_of_a_long_chain_check_in_linear_time() {
    scaling::on_a_thread(1 << 28, || {
        let n = 2800;
        let units = scaling::inputs(n, |m| Resolved::new(&chain(m)));
        scaling::check(
            "checking n calls of a chain of n functions that returns a decimal",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
