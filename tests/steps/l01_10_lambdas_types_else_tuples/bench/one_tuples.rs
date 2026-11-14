//! A one-tuple nested n deep is parsed, printed back and evaluated in time of order n: the
//! benchmark of `one_tuples.rs`, whose test runs the same checks at small depths.

use zed_tests::scaling;

use crate::one_tuples::{evaluates, nested, prints_back};

#[test]
fn nested_one_tuples_scale() {
    let texts = scaling::inputs(250, nested);
    // Printing back and evaluating are timed apart, so that the cheaper one, printing,
    // cannot hide a quadratic under the cost of the other.
    scaling::check(
        "a one-tuple nested n deep, parsed and printed back",
        250,
        |n| prints_back(&texts[&n]),
    );
    scaling::check(
        "a one-tuple nested n deep, evaluated and its value printed",
        250,
        |n| evaluates(&texts[&n], n),
    );
}
