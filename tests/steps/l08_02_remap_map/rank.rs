//! `map` composed with rank insertion (sec:remap_law, "Ranking: order is a key you add"), the
//! widen `k -> (rank(f(v)), k)`, on the M0 model. The source form, `into (desc v -> k -> v)`,
//! waits for step L8.2 (its cases, with this composition, are parked in
//! /home/luke/Work/wt/failing-tests/L8.2.rs). A `map` by a function that keeps the order of
//! the values commutes with the rank; one that reverses it reverses the ranks; a constant puts
//! every entry under rank 0.

use zed_kernel::term::build::lit;
use zed_kernel::{Family, Prim, Term, Value, eval};
use zed_tests::kernel::*;

/// `{ "ann" -> 3, "bob" -> 5, "cy" -> 3 }`.
fn scores() -> Term {
    lit(Value::Family(Family::of([
        ("ann", 3i64),
        ("bob", 5),
        ("cy", 3),
    ])))
}

fn show(t: &Term) -> String {
    eval(t)
        .map(|v| v.to_string())
        .unwrap_or_else(|e| format!("error: {e:?}"))
}

/// `F into (desc v -> k -> v)`.
fn desc(f: Term) -> Term {
    let gt = |a, b| bin(Prim::Gt, a, b);
    rank_widen(f, &|v| v, &gt)
}

#[test]
fn a_map_that_keeps_the_order_commutes_with_the_rank() {
    let before = desc(map(scores(), |v| mul(v, lit(2))));
    let after = map(desc(scores()), |v| mul(v, lit(2)));
    let want = r#"{0 -> {"bob" -> 10}, 1 -> {"ann" -> 6, "cy" -> 6}}"#;
    assert_eq!(show(&before), want);
    assert_eq!(show(&after), want);
}

#[test]
fn a_map_that_reverses_the_order_reverses_the_ranks() {
    let before = desc(map(scores(), |v| sub(lit(0), v)));
    let after = map(desc(scores()), |v| sub(lit(0), v));
    assert_eq!(
        show(&before),
        r#"{0 -> {"ann" -> -3, "cy" -> -3}, 1 -> {"bob" -> -5}}"#
    );
    assert_eq!(
        show(&after),
        r#"{0 -> {"bob" -> -5}, 1 -> {"ann" -> -3, "cy" -> -3}}"#
    );
}

#[test]
fn a_constant_map_puts_every_entry_under_one_rank() {
    let before = desc(map(scores(), |_| lit(0)));
    assert_eq!(
        show(&before),
        r#"{0 -> {"ann" -> 0, "bob" -> 0, "cy" -> 0}}"#
    );
}
