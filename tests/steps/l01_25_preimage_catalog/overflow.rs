//! S22c: a comparison with a constant at an end of `i64`, read backward through a sum whose
//! values pass that end. Kernel integers are unbounded, so `y + (MAX - 3)` at `y = 4` is
//! `MAX + 1`, an integer that differs from `MAX`; the preimage must keep such inputs.

use zed_kernel::{Prim, Term, Value};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{Demand, Domains, preimage};

use super::{check, doms, shown};

const MAX: i64 = i64::MAX;
const MIN: i64 = i64::MIN;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

/// The preimage of `d` under `t` over `ds`, checked against the interpreter on the points of
/// `window`, printed.
fn checked(t: &Term, ds: &Domains, d: &Demand, window: (i64, i64)) -> String {
    let p = preimage(t, ds, d);
    check(t, ds, d, &p, window);
    shown(&p)
}

/// `y + (MAX - 3) == MAX` is false for every `y` in `[-10, 10]` but 3: from 4 up the sum
/// passes `MAX`. The transfer read `!= MAX` as `<= MAX - 1`, which drops every integer above
/// `MAX`, and returned `[-10, 2]` as exact.
#[test]
fn a_sum_past_max_is_not_equal_to_max() {
    let sum = prim(Prim::Add, var("y"), int(MAX - 3));
    let ds = doms(&[("y", Some(-10), Some(10))]);
    let eq = prim(Prim::Eq, sum.clone(), int(MAX));
    let ne = prim(Prim::Ne, sum, int(MAX));
    for (t, d) in [(&eq, Demand::Bool(false)), (&ne, Demand::Bool(true))] {
        assert_eq!(
            checked(t, &ds, &d, (-10, 10)),
            "y [-10..=2, 4..=10]; exact",
            "{t}"
        );
    }
    assert_eq!(
        checked(&eq, &ds, &Demand::Bool(true), (-10, 10)),
        "y [3..=3]; exact"
    );
}

/// The mirror at `i64::MIN`: `y + (MIN + 3)` at `y = -4` is `MIN - 1`.
#[test]
fn a_sum_past_min_is_not_equal_to_min() {
    let sum = prim(Prim::Add, var("y"), int(MIN + 3));
    let ds = doms(&[("y", Some(-10), Some(10))]);
    let t = prim(Prim::Eq, sum, int(MIN));
    assert_eq!(
        checked(&t, &ds, &Demand::Bool(false), (-10, 10)),
        "y [-10..=-4, -2..=10]; exact"
    );
    // `y - 3 != MIN` on inputs at the bottom of `i64`, where `y - 3` leaves it.
    let t = prim(Prim::Ne, prim(Prim::Sub, var("y"), int(3)), int(MIN));
    let ds = doms(&[("y", Some(MIN), Some(MIN + 10))]);
    assert_eq!(
        checked(&t, &ds, &Demand::Bool(true), (MIN, MIN + 10)),
        format!("y [{MIN}..={}, {}..={}]; exact", MIN + 2, MIN + 4, MIN + 10)
    );
}

/// The same test on an `if` whose one arm passes `MAX`, and on two inputs.
#[test]
fn an_arm_or_a_second_input_past_max() {
    let arm = prim(Prim::Add, var("y"), int(MAX - 3));
    let t = Term::If(
        std::sync::Arc::new(prim(Prim::Gt, var("y"), int(0))),
        std::sync::Arc::new(arm),
        std::sync::Arc::new(var("y")),
    );
    let t = prim(Prim::Eq, t, int(MAX));
    let ds = doms(&[("y", Some(-10), Some(10))]);
    // Exact: the arm at `y = 3` is `MAX`, and past it `MAX + 1` and more differ from `MAX`.
    assert_eq!(
        checked(&t, &ds, &Demand::Bool(false), (-10, 10)),
        "y [-10..=2, 4..=10]; exact"
    );
    let sum = prim(Prim::Add, prim(Prim::Add, var("x"), var("y")), int(MAX - 3));
    let t = prim(Prim::Eq, sum, int(MAX));
    let ds = doms(&[("x", Some(0), Some(5)), ("y", Some(0), Some(5))]);
    assert_eq!(
        checked(&t, &ds, &Demand::Bool(false), (0, 5)),
        "x [0..=5]; y [0..=5]; necessary"
    );
}

/// The complement keeps the integers past an end of `i64` exactly when the set it is taken in
/// holds them.
#[test]
fn the_complement_at_the_ends_of_i64() {
    use End::{NegInf, PosInf};
    let at = |v: i128| End::from(v);
    let top = IntervalSet::top();
    let max = IntervalSet::single(MAX);
    assert_eq!(
        max.complement_in(&top),
        IntervalSet::from_pieces(vec![
            (NegInf, at(MAX as i128 - 1)),
            (at(MAX as i128 + 1), PosInf)
        ])
    );
    assert_eq!(
        max.complement_in(&IntervalSet::of(0, MAX)),
        IntervalSet::of(0, MAX - 1)
    );
    let low = IntervalSet::range(End::of(MIN), End::of(5));
    assert_eq!(
        low.complement_in(&top),
        IntervalSet::from_pieces(vec![(NegInf, at(MIN as i128 - 1)), (at(6), PosInf)])
    );
    assert_eq!(
        low.complement_in(&IntervalSet::of(MIN, 9)),
        IntervalSet::of(6, 9)
    );
    assert_eq!(
        IntervalSet::of(1, 2).complement_in(&IntervalSet::of(0, 4)),
        IntervalSet::from_pieces(vec![(at(0), at(0)), (at(3), at(4))])
    );
}

/// `n` pieces from `i64::MIN` to `i64::MAX`, one integer each with gaps of one between them
/// except a wide gap in the middle.
fn spread(n: usize) -> IntervalSet {
    let n = n as i64;
    let low = (0..n / 2).map(|i| (End::of(MIN + 2 * i), End::of(MIN + 2 * i)));
    let high = (0..n - n / 2).map(|i| (End::of(MAX - 2 * i), End::of(MAX - 2 * i)));
    IntervalSet::from_pieces(low.chain(high).collect())
}

/// `y + 1 + 1 + … + 1` (`k` ones) `!= MAX` over `y` in `[MAX - k - 5, MAX]`.
fn ones(k: usize) -> (Term, Domains) {
    let sum = (0..k).fold(var("y"), |t, _| prim(Prim::Add, t, int(1)));
    let lo = MAX - k as i64 - 5;
    (
        prim(Prim::Ne, sum, int(MAX)),
        doms(&[("y", Some(lo), None)]),
    )
}

#[test]
fn the_complement_at_the_ends_scales() {
    let sets: Vec<(usize, IntervalSet)> = [1024, 8192].map(|n| (n, spread(n))).into();
    let top = IntervalSet::top();
    zed_tests::scaling::check(
        "the complement of n pieces at both ends of `i64`",
        1024,
        |n| {
            let s = &sets.iter().find(|(m, _)| *m == n).expect("a built set").1;
            std::hint::black_box(s.complement_in(&top));
        },
    );
    let terms: Vec<(usize, (Term, Domains))> = [64, 512].map(|k| (k, ones(k))).into();
    zed_tests::scaling::check("`y + 1 + … + 1 != MAX` with k ones", 64, |k| {
        let (t, ds) = &terms.iter().find(|(m, _)| *m == k).expect("a built term").1;
        std::hint::black_box(preimage(t, ds, &Demand::Bool(true)));
    });
    // Every `y` meets it but `MAX - 64`; from `MAX - 63` up the sum passes `MAX`.
    let (t, ds) = ones(64);
    assert_eq!(
        checked(&t, &ds, &Demand::Bool(true), (MAX - 69, MAX)),
        format!("y [{}..={}, {}..]; exact", MAX - 69, MAX - 65, MAX - 63)
    );
}
