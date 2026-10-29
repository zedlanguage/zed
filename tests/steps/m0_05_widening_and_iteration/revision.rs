//! The tonicity table, interval revision and the reductions, on constraints from ordinary
//! programs, and checked for soundness by brute force over every operand interval with
//! endpoints in a small range.

use zedc::store::interval::{End, IntervalSet};
use zedc::store::lattice::{Congruence, FiniteSet};
use zedc::store::revision::{
    Op, Tonicity, arity, backward, forward, reduce_congruence, reduce_finite, tonicity,
};

use super::iv;

fn top() -> IntervalSet {
    IntervalSet::top()
}

#[test]
fn the_tonicity_table_follows_the_sign_of_the_other_argument() {
    use Tonicity::*;
    assert_eq!(tonicity(Op::Add, 1), Up);
    assert_eq!(tonicity(Op::Sub, 0), Up);
    assert_eq!(tonicity(Op::Sub, 1), Down);
    assert_eq!(tonicity(Op::Mul, 0), UpWhereOtherNonneg);
    assert_eq!(tonicity(Op::Abs, 0), DownThenUp);
    assert_eq!(tonicity(Op::Pow(2), 0), DownThenUp);
    assert_eq!(tonicity(Op::Pow(3), 0), Up);
    assert_eq!(tonicity(Op::Mod, 0), Tonicity::None);
    // A product whose factors straddle 0 is split at 0 and the parts' images joined:
    // (-3..=2) * (-1..=4) has extremes -3*4 and 2*4.
    assert_eq!(
        forward(Op::Mul, &IntervalSet::of(-3, 2), &IntervalSet::of(-1, 4)),
        IntervalSet::of(-12, 8)
    );
    // 0 times an unbounded factor is 0, not undefined.
    assert_eq!(
        forward(Op::Mul, &IntervalSet::single(0), &top()),
        IntervalSet::single(0)
    );
}

#[test]
fn an_order_total_bounds_the_quantity() {
    // `total = price * qty` with prices from 10 to 20 cents and a total of at most 50: the
    // quantity is at most 5, and is unchanged where it was already smaller.
    let (price, qty) = (IntervalSet::of(10, 20), IntervalSet::of(0, 100));
    let total = forward(Op::Mul, &price, &qty).meet(&iv(None, Some(50)));
    assert_eq!(
        backward(Op::Mul, 1, &price, &qty, &total),
        IntervalSet::of(0, 5)
    );
    // A free price that may be 0 gives the quantity no bound.
    let free = IntervalSet::of(0, 20);
    assert_eq!(backward(Op::Mul, 1, &free, &qty, &total), qty);
}

#[test]
fn a_minute_count_bounds_the_seconds() {
    // `minutes = seconds div 60` with 2 or 3 minutes: 120 to 239 seconds.
    let sixty = IntervalSet::single(60);
    let got = backward(
        Op::Div,
        0,
        &iv(Some(0), None),
        &sixty,
        &IntervalSet::of(2, 3),
    );
    assert_eq!(got, IntervalSet::of(120, 239));
    // `hour = t mod 24`: any hour without more, and the shifted range when t spans no wrap.
    assert_eq!(
        forward(Op::Mod, &top(), &IntervalSet::single(24)),
        IntervalSet::of(0, 23)
    );
    assert_eq!(
        forward(Op::Mod, &IntervalSet::of(25, 30), &IntervalSet::single(24)),
        IntervalSet::of(1, 6)
    );
    assert_eq!(
        forward(Op::Mod, &IntervalSet::of(20, 30), &IntervalSet::single(24)),
        IntervalSet::of(0, 23)
    );
}

#[test]
fn a_tolerance_on_a_difference_gives_one_or_two_pieces() {
    // `abs(delta) <= 5` and `abs(delta) >= 3`.
    assert_eq!(
        backward(Op::Abs, 0, &top(), &top(), &IntervalSet::of(0, 5)),
        IntervalSet::of(-5, 5)
    );
    assert_eq!(
        backward(Op::Abs, 0, &top(), &top(), &iv(Some(3), None)).to_string(),
        "[..=-3, 3..]"
    );
    // `x ** 2` between 10 and 50: x is 4 to 7 in either sign.
    assert_eq!(
        backward(Op::Pow(2), 0, &top(), &top(), &IntervalSet::of(10, 50)).to_string(),
        "[-7..=-4, 4..=7]"
    );
    // `x ** 3` up to -8: x at most -2.
    assert_eq!(
        backward(Op::Pow(3), 0, &top(), &top(), &iv(None, Some(-8))),
        iv(None, Some(-2))
    );
}

#[test]
fn a_minimum_bounds_both_arguments_from_below_and_one_from_above() {
    // `min(stock, ordered) >= 3`: both are at least 3.
    let (stock, ordered) = (IntervalSet::of(0, 50), IntervalSet::of(0, 9));
    let z = iv(Some(3), None);
    assert_eq!(
        backward(Op::Min, 0, &stock, &ordered, &z),
        IntervalSet::of(3, 50)
    );
    // `min(stock, ordered) <= 2` with at least 5 ordered: the stock is at most 2.
    let ordered = IntervalSet::of(5, 9);
    let z = IntervalSet::of(0, 2);
    assert_eq!(
        backward(Op::Min, 0, &stock, &ordered, &z),
        IntervalSet::of(0, 2)
    );
    // `max(a, b) <= 10` bounds both from above.
    assert_eq!(
        backward(Op::Max, 1, &top(), &top(), &IntervalSet::of(0, 10)),
        iv(None, Some(10))
    );
}

#[test]
fn an_aligned_index_moves_its_bounds_to_the_alignment() {
    // An index into an array of 100 that is a multiple of 4 and at least 1: 4 to 96.
    let (x, _) = reduce_congruence(&IntervalSet::of(1, 99), &Congruence::new(4, 0));
    assert_eq!(x, IntervalSet::of(4, 96));
    // An index fixed to 8 fixes the congruence to that value.
    let (_, c) = reduce_congruence(&IntervalSet::of(5, 10), &Congruence::new(8, 0));
    assert_eq!(c, Congruence::single(8));
    // The examples of sec:constraints: `int[0..=10]` with `1 mod 4` is `int[1..=9]`, and
    // `int[2..=4]` with `1 mod 4` is empty.
    let one_mod_four = Congruence::new(4, 1);
    assert_eq!(
        reduce_congruence(&IntervalSet::of(0, 10), &one_mod_four).0,
        IntervalSet::of(1, 9)
    );
    assert_eq!(
        reduce_congruence(&IntervalSet::of(2, 4), &one_mod_four),
        (IntervalSet::empty(), Congruence::Bottom)
    );
    // A status in 400..=499 out of the known codes {200, 404, 500}: just 404.
    let (x, s) = reduce_finite(&IntervalSet::of(400, 499), &FiniteSet::of([200, 404, 500]));
    assert_eq!((x, s), (IntervalSet::single(404), FiniteSet::of([404])));
}

/// The operand intervals of the brute-force checks: every interval with endpoints in
/// -3..=3 or infinite, the empty set, and a two-piece union.
fn operands() -> Vec<IntervalSet> {
    let ends: Vec<End> = std::iter::once(End::NegInf)
        .chain((-3..=3).map(End::Fin))
        .chain(std::iter::once(End::PosInf))
        .collect();
    let mut out = vec![
        IntervalSet::empty(),
        IntervalSet::of(-3, -2).join(&IntervalSet::of(2, 3)),
    ];
    for &lo in &ends {
        for &hi in &ends {
            if lo <= hi && lo != End::PosInf && hi != End::NegInf {
                out.push(IntervalSet::range(lo, hi));
            }
        }
    }
    out
}

fn apply(op: Op, x: i64, y: i64) -> Option<i64> {
    match op {
        Op::Add => Some(x + y),
        Op::Sub => Some(x - y),
        Op::Neg => Some(-x),
        Op::Mul => Some(x * y),
        Op::Pow(k) => Some(x.pow(k)),
        Op::Div => (y != 0).then(|| x.div_euclid(y)),
        Op::Mod => (y != 0).then(|| x.rem_euclid(y)),
        Op::Abs => Some(x.abs()),
        Op::Min => Some(x.min(y)),
        Op::Max => Some(x.max(y)),
    }
}

const OPS: [Op; 11] = [
    Op::Add,
    Op::Sub,
    Op::Neg,
    Op::Mul,
    Op::Pow(2),
    Op::Pow(3),
    Op::Div,
    Op::Mod,
    Op::Abs,
    Op::Min,
    Op::Max,
];

#[test]
fn one_round_of_revision_never_loses_a_solution() {
    // For every operator, operand intervals and demanded result: a forward pass then a
    // backward pass to each operand keeps every pair of members whose result is demanded.
    // Members are taken from -9..=9, which every finite endpoint lies inside.
    let window = -9..=9i64;
    let mut kept = 0usize;
    for op in OPS {
        for x in operands() {
            for y in operands() {
                for z in operands().into_iter().step_by(4) {
                    let z = z.meet(&forward(op, &x, &y));
                    let x2 = backward(op, 0, &x, &y, &z);
                    let y2 = if arity(op) == 2 {
                        backward(op, 1, &x2, &y, &z)
                    } else {
                        y.clone()
                    };
                    let ys: Vec<i64> = if arity(op) == 1 {
                        vec![0]
                    } else {
                        window.clone().filter(|&b| y.contains(b)).collect()
                    };
                    for a in window.clone().filter(|&a| x.contains(a)) {
                        for &b in &ys {
                            if apply(op, a, b).is_some_and(|r| z.contains(r)) {
                                assert!(
                                    x2.contains(a) && (arity(op) == 1 || y2.contains(b)),
                                    "{op:?} {x} {y} {z}: lost ({a}, {b})"
                                );
                                kept += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert!(kept > 1_000_000, "only {kept} solutions checked");
}
