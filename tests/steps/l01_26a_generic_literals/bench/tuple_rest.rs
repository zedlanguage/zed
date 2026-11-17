use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::tuple_rest::{chain, divisions, printed};

#[test]
fn many_divisions_on_one_line_print_the_line_once() {
    // Written with decimals before they took `f64` (author decision 2026-11-12); a `/` of
    // integer literals is what stays rejected, so the line now holds divisions. Negative
    // control (run once, not committed, with decimals): one message for each decimal, each
    // quoting the line, as before this item, printed 16.2 times the bytes for 4 times the
    // decimals (964335 bytes for n = 200, 15605535 for 800), and failed the bound below. One
    // message prints 4.0 times (zedc: 51340 bytes for 200, 207641 for 800). The decimals were
    // held at 6,600 and 52,800. A division costs about 0.4 ms to check and print here, 1.36 s
    // for 3,200 on 2026-11-16, so 6,600 and 52,800 divisions ran past the 60 s a test may take;
    // they are held at 800 and 6,400, which print 285978 and 2439956 bytes, 8.53 times, in about
    // 6 s.
    scaling::on_a_thread(1 << 28, || {
        let n = 800;
        let bytes = |m: usize| printed(&divisions(m)).len() as u64;
        scaling::hold_linear(
            &format!(
                "{n} and {} divisions on one line, rejected",
                scaling::FACTOR * n
            ),
            "bytes printed",
            bytes(n),
            bytes(scaling::FACTOR * n),
        );
        assert_eq!(
            printed(&divisions(n)).matches(&divisions(n)[..20]).count(),
            1,
            "the line is printed once"
        );
        let units = scaling::inputs(n, divisions);
        scaling::check_order(
            "printing the rejection of n divisions on one line",
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
        let units = scaling::inputs(n, |m| Resolved::new(&chain(m, "1 / 2")));
        scaling::check(
            "checking n calls of a chain of n functions that returns a division",
            n,
            |m| {
                units[&m].check();
            },
        );
    });
}
