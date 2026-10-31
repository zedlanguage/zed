//! The interval-union operations at the rule of low complexity (DESIGN.md Part G): `cap`
//! merges neighbors by a heap rather than by a scan per merge, `join` merges two sorted lists,
//! `contains` searches, and the forward transfer does work linear in its operands and gives
//! no sign region more pieces than an operand has in one, so piece counts do not multiply
//! along a chain of operators. No constant bounds the pieces.

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::revision::{self, Op};

use End::{Fin, NegInf, PosInf};

/// `n` pieces with random gaps, the outer ones infinite when `open`.
fn pieces(rng: &mut Rng, n: usize, open: bool) -> IntervalSet {
    let mut at = 0i64;
    let mut out = Vec::new();
    for _ in 0..n {
        let lo = at + rng.int(2, 9);
        let hi = lo + rng.int(0, 5);
        out.push((Fin(lo), Fin(hi)));
        at = hi;
    }
    if open && n > 0 {
        out[0].0 = NegInf;
        out[n - 1].1 = PosInf;
    }
    IntervalSet::from_pieces(out)
}

/// The rule `cap` must follow, as step M0.5 states it: while there are too many pieces, merge
/// the two neighbors with the fewest integers between them, the lower pair on a tie.
fn cap_by_rule(s: &IntervalSet, limit: usize) -> IntervalSet {
    let mut p = s.pieces().to_vec();
    while p.len() > limit.max(1) {
        let gap = |i: usize| match (p[i].1, p[i + 1].0) {
            (Fin(hi), Fin(lo)) => lo - hi,
            _ => unreachable!(),
        };
        let at = (0..p.len() - 1).min_by_key(|&i| (gap(i), i)).unwrap();
        p[at].1 = p[at + 1].1;
        p.remove(at + 1);
    }
    IntervalSet::from_pieces(p)
}

#[test]
fn cap_follows_the_merge_rule() {
    let mut rng = Rng::new(24);
    let mut tried = 0;
    for _ in 0..2000 {
        let n = rng.below(30);
        let open = rng.below(2) == 0;
        let s = pieces(&mut rng, n, open);
        let limit = rng.below(12);
        assert_eq!(
            s.cap(limit),
            cap_by_rule(&s, limit),
            "{s} capped to {limit}"
        );
        tried += 1;
    }
    assert_eq!(tried, 2000);
}

#[test]
fn join_and_contains_agree_with_membership() {
    let mut rng = Rng::new(7);
    for _ in 0..500 {
        let (n, m) = (rng.below(12), rng.below(12));
        let (a, b) = (pieces(&mut rng, n, false), pieces(&mut rng, m, false));
        let j = a.join(&b);
        for v in -2..=120 {
            assert_eq!(
                j.contains(v),
                a.contains(v) || b.contains(v),
                "{a} ∪ {b} at {v}"
            );
        }
        assert_eq!(
            j,
            IntervalSet::from_pieces([a.pieces(), b.pieces()].concat())
        );
    }
}

/// Eight single integers far apart, so that a sum of two has up to 64 distinct members.
fn sparse(rng: &mut Rng) -> IntervalSet {
    let mut at = 0i64;
    IntervalSet::from_pieces(
        (0..8)
            .map(|_| {
                at += rng.int(1_000, 1_000_000);
                (Fin(at), Fin(at))
            })
            .collect(),
    )
}

/// A sum of `k` operands of eight sparse pieces each, the way a chain of `+` builds one: each
/// image keeps to its operands' eight pieces, so the chain's cost is linear in `k`.
fn sum_chain(k: usize) -> IntervalSet {
    let mut rng = Rng::new(k as u64);
    let mut acc = sparse(&mut rng);
    for _ in 0..k {
        let next = sparse(&mut rng);
        acc = revision::forward(Op::Add, &acc, &next);
        assert!(acc.pieces().len() <= 8, "{acc}");
    }
    acc
}

#[test]
fn a_chain_of_operators_keeps_to_its_operands_pieces() {
    // Each step's image contains every sum of members, so the members are kept.
    let a = IntervalSet::from_pieces(vec![(Fin(0), Fin(0)), (Fin(10), Fin(10))]);
    let mut acc = a.clone();
    for _ in 0..6 {
        acc = revision::forward(Op::Add, &acc, &a);
    }
    for v in (0..=70).step_by(10) {
        assert!(acc.contains(v), "{acc} has {v}");
    }
    assert!(acc.pieces().len() <= 2, "{acc}");
    scaling::check("a chain of `+` over eight-piece operands", 200, |k| {
        sum_chain(k);
    });
}

/// The pieces of `s` in each sign region: negative, zero, positive.
fn per_region(s: &IntervalSet) -> [usize; 3] {
    let mut n = [0; 3];
    for p in s.sign_parts() {
        n[if p.1 < Fin(0) {
            0
        } else if p.0 > Fin(0) {
            2
        } else {
            1
        }] += 1;
    }
    n
}

/// Up to six pieces within `-40..=40`.
fn small(rng: &mut Rng) -> IntervalSet {
    let n = rng.int(1, 6) as usize;
    IntervalSet::from_pieces(
        (0..n)
            .map(|_| {
                let lo = rng.int(-40, 40);
                (Fin(lo), Fin(lo + rng.int(0, 4)))
            })
            .collect(),
    )
}

const OPS: [Op; 6] = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Min, Op::Max];

fn apply(op: Op, a: i64, b: i64) -> Option<i64> {
    Some(match op {
        Op::Add => a + b,
        Op::Sub => a - b,
        Op::Mul => a * b,
        Op::Div if b == 0 => return None,
        Op::Div => a.div_euclid(b),
        Op::Min => a.min(b),
        _ => a.max(b),
    })
}

#[test]
fn an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region() {
    let mut rng = Rng::new(325);
    let mut checked = 0;
    for _ in 0..600 {
        let (a, b) = (small(&mut rng), small(&mut rng));
        for op in OPS {
            let z = revision::forward(op, &a, &b);
            for x in -44..=44 {
                for y in -44..=44 {
                    if a.contains(x)
                        && b.contains(y)
                        && let Some(r) = apply(op, x, y)
                    {
                        assert!(
                            z.contains(r),
                            "{op:?} {a} {b}: {x}, {y} gives {r}, not in {z}"
                        );
                        checked += 1;
                    }
                }
            }
            let most = per_region(&a)
                .into_iter()
                .chain(per_region(&b))
                .max()
                .unwrap();
            assert!(
                per_region(&z).into_iter().all(|n| n <= most),
                "{op:?} {a} {b} gives {z}"
            );
        }
    }
    assert!(checked > 100_000, "{checked}");
}

#[test]
fn an_image_with_a_one_piece_operand_is_the_join_of_the_pieces_images() {
    // With one operand of one piece nothing is merged before the image is taken, so when the
    // join of each piece's image keeps to the region bound, the image is that join.
    let mut rng = Rng::new(326);
    let mut equal = 0;
    for _ in 0..2000 {
        let a = small(&mut rng);
        let lo = rng.int(-40, 40);
        let b = IntervalSet::range(Fin(lo), Fin(lo + rng.int(0, 9)));
        for op in OPS {
            let join = a.pieces().iter().fold(IntervalSet::empty(), |j, &p| {
                j.join(&revision::forward(
                    op,
                    &IntervalSet::from_pieces(vec![p]),
                    &b,
                ))
            });
            let most = per_region(&a)
                .into_iter()
                .chain(per_region(&b))
                .max()
                .unwrap();
            if per_region(&join).into_iter().all(|n| n <= most) {
                assert_eq!(revision::forward(op, &a, &b), join, "{op:?} {a} {b}");
                equal += 1;
            }
        }
    }
    assert!(equal > 6000, "{equal}");
}

#[test]
fn the_interval_operations_scale() {
    let sets = |n: usize| {
        let mut rng = Rng::new(n as u64);
        (pieces(&mut rng, n, true), pieces(&mut rng, n, false))
    };
    scaling::check("capping n pieces to 8", 4000, |n| {
        let (a, _) = sets(n);
        assert_eq!(a.cap(8).pieces().len(), 8.min(n));
    });
    scaling::check("the forward `*` of two sets of n pieces", 4000, |n| {
        let (a, b) = sets(n);
        let z = revision::forward(Op::Mul, &a, &b.neg());
        assert!(!z.is_empty());
    });
    scaling::check("joining two sets of n pieces", 4000, |n| {
        let (a, b) = sets(n);
        assert!(!a.join(&b).is_empty());
    });
    scaling::check("n membership tests in a set of n pieces", 4000, |n| {
        let (_, b) = sets(n);
        let hits = (0..n as i64).filter(|&v| b.contains(v * 7)).count();
        assert!(hits <= n);
    });
}

/// `k` lower and `k` upper bounds, each on a symbol of its own and each with a floor.
fn many(k: usize, shift: i64) -> zedc::store::affine::Bounds {
    use zedc::store::affine::{Affine, Bound, Bounds};
    let side = |c: i64, floor: End| {
        (0..k)
            .map(move |i| Bound {
                affine: Affine::sym(&format!("s{i}")).plus(c).expect("small"),
                floor,
            })
            .collect::<Vec<_>>()
    };
    Bounds::from_bounds(
        IntervalSet::top(),
        side(shift, Fin(-1)),
        side(shift + 10, Fin(1)),
    )
}

#[test]
fn bounds_on_many_symbols_scale() {
    use zedc::store::lattice::Lattice;
    scaling::check("symbolic bounds on distinct symbols", 200, |k| {
        let (a, b) = (many(k, 0), many(k, 1));
        let j = a.join(&b);
        assert_eq!(j.bounds(zedc::store::affine::Side::Lower).len(), k);
        a.meet(&b);
    });
}
