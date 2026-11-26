//! The form rule of `ids.rs` at `d` and `8d` levels. Each term is built before the timing.

use zed_kernel::{Shared, Term};
use zed_tests::scaling;
use zedc::stage::ends;

use crate::ids::{random_build_orders_read_and_stage_alike, same_arms};

#[test]
fn a_part_held_by_both_arms_of_nested_ifs_is_read_once() {
    // The two arms of each `if` are one node: read by the place it is reached from, the walk
    // would take 2^d steps.
    let n = 1000;
    let terms = scaling::inputs(n, same_arms);
    scaling::check_order(
        "stage::ends on d nested ifs whose two arms are one part",
        n,
        1,
        |d| {
            assert!(ends(&terms[&d]));
        },
    );
    // Under a binder of `n` the chain still ends.
    let under = Term::Lam(vec!["n".into()], Shared::new(same_arms(n)));
    assert!(ends(&under));
}

/// The terms of one piece of the 200,000 the TERM-id probe compared (plan row
/// TESTS-random-batteries-to-size). Correctness test:
/// `ids::random_terms_built_in_two_orders_read_and_stage_alike`, 100 terms.
const PIECE: usize = 10_000;

fn piece(k: usize) {
    let name = format!("200,000 random terms built in two orders, piece {k}");
    scaling::timed(&name, || {
        random_build_orders_read_and_stage_alike(&name, PIECE)
    });
}

/// The 20 pieces, one test each.
macro_rules! pieces {
    ($($test:ident = $k:literal;)*) => {
        $(
            #[test]
            fn $test() {
                piece($k);
            }
        )*
    };
}

pieces! {
    random_terms_built_in_two_orders_read_and_stage_alike_0 = 0;
    random_terms_built_in_two_orders_read_and_stage_alike_1 = 1;
    random_terms_built_in_two_orders_read_and_stage_alike_2 = 2;
    random_terms_built_in_two_orders_read_and_stage_alike_3 = 3;
    random_terms_built_in_two_orders_read_and_stage_alike_4 = 4;
    random_terms_built_in_two_orders_read_and_stage_alike_5 = 5;
    random_terms_built_in_two_orders_read_and_stage_alike_6 = 6;
    random_terms_built_in_two_orders_read_and_stage_alike_7 = 7;
    random_terms_built_in_two_orders_read_and_stage_alike_8 = 8;
    random_terms_built_in_two_orders_read_and_stage_alike_9 = 9;
    random_terms_built_in_two_orders_read_and_stage_alike_10 = 10;
    random_terms_built_in_two_orders_read_and_stage_alike_11 = 11;
    random_terms_built_in_two_orders_read_and_stage_alike_12 = 12;
    random_terms_built_in_two_orders_read_and_stage_alike_13 = 13;
    random_terms_built_in_two_orders_read_and_stage_alike_14 = 14;
    random_terms_built_in_two_orders_read_and_stage_alike_15 = 15;
    random_terms_built_in_two_orders_read_and_stage_alike_16 = 16;
    random_terms_built_in_two_orders_read_and_stage_alike_17 = 17;
    random_terms_built_in_two_orders_read_and_stage_alike_18 = 18;
    random_terms_built_in_two_orders_read_and_stage_alike_19 = 19;
}
