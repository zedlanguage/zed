//! The derived forms the laws are stated over, checked on hand-computed examples before the
//! laws use them.

use zed_kernel::term::build::{lit, prim};
use zed_kernel::{KernelError, Prim, Term, Value, eval};
use zed_tests::kernel::*;

use super::{ints, seq};

fn run(t: Term) -> String {
    eval(&t).unwrap().to_string()
}

#[test]
fn map_applies_to_every_value_and_keeps_the_keys() {
    let prices = ints(&[(101, 250), (102, 1200), (105, 75)]);
    let doubled = map(prices, |v| mul(v, lit(2)));
    assert_eq!(run(doubled), "{101 -> 500, 102 -> 2400, 105 -> 150}");
}

#[test]
fn scan_gives_running_totals() {
    let daily_sales = seq(&[3i64, 1, 4, 1]);
    let totals = scan(daily_sales, Term::PrimFn(Prim::Add));
    assert_eq!(run(totals), "{0 -> 3, 1 -> 4, 2 -> 8, 3 -> 9}");
}

#[test]
fn foldl_and_foldr_apply_the_operator_in_sequence() {
    // A balance of 100 less three withdrawals, left to right.
    let withdrawals = seq(&[10i64, 3, 2]);
    let minus = Term::PrimFn(Prim::Sub);
    assert_eq!(
        run(foldl(withdrawals.clone(), lit(100), minus.clone())),
        "85"
    );
    // 10 - (3 - (2 - 0)), right to left.
    assert_eq!(run(foldr(withdrawals, minus.clone(), lit(0))), "9");
    let none = seq::<i64>(&[]);
    assert_eq!(run(foldl(none.clone(), lit(100), minus.clone())), "100");
    assert_eq!(run(foldr(none, minus, lit(7))), "7");
}

#[test]
fn flip_swaps_the_arguments() {
    let minus = Term::PrimFn(Prim::Sub);
    let t = zed_kernel::term::build::app(flip(minus), vec![lit(3), lit(10)]);
    assert_eq!(run(t), "7");
}

#[test]
fn rank_widen_puts_tied_scores_under_one_dense_rank() {
    let scores = lit(Value::Family(zed_kernel::Family::of([
        ("ann", 90i64),
        ("bob", 85),
        ("cy", 90),
        ("dee", 70),
    ])));
    let ranked = rank_widen(scores, &|v| v, &lt);
    assert_eq!(
        run(ranked),
        r#"{0 -> {"dee" -> 70}, 1 -> {"bob" -> 85}, 2 -> {"ann" -> 90, "cy" -> 90}}"#
    );
}

#[test]
fn refine_keeps_passes_rejects_and_lets_failures_through() {
    let positive = func(|[v]| lt(lit(0), v));
    assert_eq!(eval(&refine(lit(5), positive.clone())), Ok(Value::Int(5)));
    assert_eq!(
        eval(&refine(lit(-1), positive.clone())),
        Ok(Value::atom("invalid"))
    );
    // A failure in the input flows out unchanged, and `p` is never asked about it.
    assert_eq!(
        eval(&refine(idiv(lit(12), lit(0)), positive)),
        Ok(Value::atom("divByZero"))
    );
}

#[test]
fn disjoint_union_merges_disjoint_families_and_rejects_overlap() {
    let morning = ints(&[(1, 30), (2, 45)]);
    let evening = ints(&[(7, 20)]);
    assert_eq!(
        run(disjoint_union(morning.clone(), evening, 1)),
        "{1 -> 30, 2 -> 45, 7 -> 20}"
    );
    // The kernel's `Union` merges two equal leaves; `⊎` rejects them.
    let again = ints(&[(2, 45)]);
    assert_eq!(
        run(prim(Prim::Union, vec![morning.clone(), again.clone()])),
        "{1 -> 30, 2 -> 45}"
    );
    assert!(matches!(
        eval(&disjoint_union(morning, again, 1)),
        Err(KernelError::Collision { .. })
    ));
}

#[test]
fn fresh_names_never_repeat() {
    assert_ne!(fresh("x"), fresh("x"));
}
