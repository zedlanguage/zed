//! Completeness cases for step M0.5 (DESIGN.md, that step's paragraph): the interval-union
//! widening, narrowing and snapping on the bottom, the top, equal operands, infinite ends and
//! sets with no landmark on a side; the interval set as a lattice and its ends; the order
//! keys of the traversal; the scheduler's empty state; and the backward table for `^` with an
//! exponent past `2 ^ 127`. COMPLETENESS.md lists each case with the test that covers it.

use std::cmp::Ordering;

use num_bigint::BigInt;
use zedc::address::ContentAddress;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::landmarks::Landmarks;
use zedc::store::lattice::Lattice;
use zedc::store::revision::{Exponent, Op, backward, forward};
use zedc::store::schedule::Schedule;
use zedc::store::wto::VertexKey;

use super::iv;

fn marks(ks: &[i64]) -> Landmarks {
    Landmarks::of(ks.iter().copied(), [])
}

#[test]
fn an_interval_set_is_a_lattice_with_the_empty_set_and_every_integer() {
    let a = IntervalSet::of(1, 4);
    assert_eq!(<IntervalSet as Lattice>::bottom(), IntervalSet::empty());
    assert_eq!(<IntervalSet as Lattice>::top(), IntervalSet::top());
    assert_eq!(Lattice::join(&a, &IntervalSet::of(6, 7)).len(), 2);
    assert_eq!(
        Lattice::meet(&a, &IntervalSet::of(3, 9)),
        IntervalSet::of(3, 4)
    );
    // The order read off the meet.
    assert!(a.leq(&IntervalSet::of(0, 4)) && !IntervalSet::of(0, 4).leq(&a));
    assert!(IntervalSet::empty().leq(&a) && a.leq(&IntervalSet::top()));
    assert!(IntervalSet::empty().leq(&IntervalSet::empty()));
    assert!(IntervalSet::top().leq(&IntervalSet::top()));
    // The trait's widening and narrowing are the set's.
    let none = Landmarks::none();
    assert_eq!(
        Lattice::widen(&a, &IntervalSet::of(1, 5), &none),
        IntervalSet::widen(&a, &IntervalSet::of(1, 5), &none)
    );
    assert_eq!(
        Lattice::narrow(&IntervalSet::top(), &a, &none),
        IntervalSet::narrow(&IntervalSet::top(), &a, &none)
    );
}

#[test]
fn an_end_from_each_integer_type_and_back() {
    assert_eq!(End::from(5i64), End::of(5));
    assert_eq!(End::from(-5i128), End::of(-5));
    assert_eq!(End::from(i128::MAX), End::Fin(Num::from(i128::MAX)));
    assert_eq!(End::of(7).to_i64(), Some(7));
    assert_eq!(End::of(i64::MIN).to_i64(), Some(i64::MIN));
    assert_eq!(End::from(i128::from(i64::MAX) + 1).to_i64(), None);
    assert_eq!(End::PosInf.to_i64(), None);
    assert_eq!(End::NegInf.to_i64(), None);
}

/// DESIGN.md step M0.5: the widening moves each finite endpoint of `b` outward to the nearest
/// of `a`'s endpoints and the landmarks, or to infinity when there is none on that side.
#[test]
fn interval_widening_on_the_bottom_equal_operands_and_infinite_ends() {
    let none = Landmarks::none();
    // From the bottom: `next`, its ends kept.
    assert_eq!(
        IntervalSet::empty().widen(&IntervalSet::of(3, 5), &none),
        IntervalSet::of(3, 5)
    );
    assert_eq!(
        IntervalSet::empty().widen(&IntervalSet::empty(), &none),
        IntervalSet::empty()
    );
    // Equal operands: unchanged, though no end is a landmark.
    let s = IntervalSet::from_pieces(vec![(End::of(0), End::of(1)), (End::of(5), End::of(6))]);
    assert_eq!(s.widen(&s, &none), s);
    // Infinite ends stay infinite.
    assert_eq!(
        iv(Some(0), None).widen(&iv(Some(-3), None), &none),
        IntervalSet::top()
    );
    assert_eq!(
        IntervalSet::top().widen(&IntervalSet::top(), &none),
        IntervalSet::top()
    );
    // A new piece between old pieces: its ends go out to the old ends around it, and the
    // pieces that then touch merge.
    let grown = s.join(&IntervalSet::single(3));
    assert_eq!(s.widen(&grown, &none), IntervalSet::of(0, 6));
    // A new piece above every old end, with a landmark above it: from its lower end down to
    // the old end 6 and from its upper end up to the landmark.
    let up = s.join(&IntervalSet::of(9, 10));
    assert_eq!(
        s.widen(&up, &marks(&[20])),
        IntervalSet::from_pieces(vec![(End::of(0), End::of(1)), (End::of(5), End::of(19))])
    );
    assert_eq!(
        s.widen(&up, &none),
        IntervalSet::from_pieces(vec![(End::of(0), End::of(1)), (End::of(5), End::PosInf)])
    );
}

/// DESIGN.md step M0.5: the narrowing moves each finite endpoint of `b` outward to the nearest
/// of `a`'s endpoints and the landmarks, and leaves it where it is when there is none.
#[test]
fn interval_narrowing_on_the_bottom_equal_operands_and_infinite_ends() {
    let none = Landmarks::none();
    let s = IntervalSet::of(0, 9);
    assert_eq!(s.narrow(&IntervalSet::empty(), &none), IntervalSet::empty());
    assert_eq!(s.narrow(&s, &none), s);
    assert_eq!(
        IntervalSet::top().narrow(&IntervalSet::top(), &none),
        IntervalSet::top()
    );
    // Both ends of `self` infinite: `next`'s finite ends stay, or move to landmarks.
    assert_eq!(
        IntervalSet::top().narrow(&IntervalSet::of(2, 5), &none),
        IntervalSet::of(2, 5)
    );
    assert_eq!(
        IntervalSet::top().narrow(&IntervalSet::of(2, 5), &marks(&[0, 8])),
        IntervalSet::of(1, 7)
    );
    // One infinite end in `next` is kept.
    assert_eq!(
        IntervalSet::top().narrow(&iv(None, Some(4)), &none),
        iv(None, Some(4))
    );
    // Pieces of `next` inside one piece of `self` move out to its ends and merge.
    let two = IntervalSet::from_pieces(vec![(End::of(2), End::of(3)), (End::of(6), End::of(7))]);
    assert_eq!(s.narrow(&two, &none), s);
}

#[test]
fn snapping_moves_each_end_to_a_landmark_or_to_infinity() {
    // No landmark below or above: both ends go to infinity.
    assert_eq!(
        IntervalSet::of(3, 5).snap(&Landmarks::none()),
        IntervalSet::top()
    );
    // A landmark on one side only.
    assert_eq!(IntervalSet::of(3, 5).snap(&marks(&[10])), iv(None, Some(9)));
    assert_eq!(IntervalSet::of(3, 5).snap(&marks(&[0])), iv(Some(1), None));
    // Infinite ends stay infinite; a finite end on a landmark stays.
    assert_eq!(iv(Some(4), None).snap(&marks(&[0])), iv(Some(1), None));
    assert_eq!(iv(None, Some(4)).snap(&marks(&[9])), iv(None, Some(8)));
    assert_eq!(
        IntervalSet::of(1, 8).snap(&marks(&[0, 9])),
        IntervalSet::of(1, 8)
    );
    assert_eq!(
        IntervalSet::empty().snap(&marks(&[0])),
        IntervalSet::empty()
    );
    assert_eq!(IntervalSet::top().snap(&marks(&[0])), IntervalSet::top());
    // Two pieces with no landmark between or below them snap to one range: `..=8` each.
    let s = IntervalSet::from_pieces(vec![(End::of(0), End::of(1)), (End::of(5), End::of(6))]);
    assert_eq!(s.snap(&marks(&[9])), iv(None, Some(8)));
}

#[test]
fn interval_sets_print_their_pieces_for_debugging_and_compare_by_members() {
    assert_eq!(
        format!("{:?}", IntervalSet::empty()),
        "IntervalSet { pieces: [] }"
    );
    let a = format!("{:?}", IntervalSet::of(1, 2));
    assert!(
        a.starts_with("IntervalSet { pieces: [") && a != format!("{:?}", IntervalSet::of(1, 3))
    );
    // Equal sets built apart, with one and with many pieces; and sets of equal piece counts
    // that differ in one piece.
    let many = |shift: i64| {
        IntervalSet::from_pieces(
            (0..6)
                .map(|i| {
                    (
                        End::of(10 * i),
                        End::of(10 * i + 1 + shift * i64::from(i == 3)),
                    )
                })
                .collect(),
        )
    };
    assert_eq!(many(0), many(0));
    assert_ne!(many(0), many(1));
    assert_eq!(IntervalSet::of(1, 2), IntervalSet::of(1, 2));
    assert_ne!(IntervalSet::of(1, 2), IntervalSet::of(1, 3));
    assert_ne!(IntervalSet::empty(), IntervalSet::of(1, 2));
    assert_ne!(IntervalSet::of(1, 2), IntervalSet::empty());
    assert_eq!(IntervalSet::empty(), IntervalSet::empty());
    // A set built by joining equals the one built from its pieces.
    let joined = (0..6).fold(IntervalSet::empty(), |s, i| {
        s.join(&IntervalSet::of(10 * i, 10 * i + 1))
    });
    assert_eq!(joined, many(0));
}

fn key<'a, F: Ord, P: Ord>(
    name: &'a str,
    a: u8,
    form: &'a F,
    keypath: &'a P,
) -> VertexKey<'a, F, P> {
    VertexKey {
        name,
        address: ContentAddress([a; 32]),
        form,
        keypath,
    }
}

/// DESIGN.md step M0.5: the order is by name, then content address, then canonical form, then
/// keypath; two keys holding the same form and keypath are equal.
#[test]
fn vertex_keys_compare_part_by_part() {
    let (f, g) = (String::from("f"), String::from("g"));
    let (p, q) = (vec![0u32], vec![0u32, 1]);
    let k = key("x", 0, &f, &p);
    // The same form and keypath, by reference.
    assert_eq!(k.cmp(&k), Ordering::Equal);
    assert_eq!(k.partial_cmp(&key("x", 0, &f, &p)), Some(Ordering::Equal));
    assert!(k == key("x", 0, &f, &p));
    // Equal forms held apart.
    let f2 = f.clone();
    assert_eq!(k.cmp(&key("x", 0, &f2, &p)), Ordering::Equal);
    // Each part decides when those before it are equal.
    assert_eq!(k.partial_cmp(&key("y", 0, &f, &p)), Some(Ordering::Less));
    assert_eq!(
        key("y", 0, &f, &p).cmp(&key("x", 9, &g, &q)),
        Ordering::Greater
    );
    assert_eq!(k.cmp(&key("x", 1, &f, &p)), Ordering::Less);
    assert_eq!(
        key("x", 1, &f, &p).cmp(&key("x", 0, &g, &q)),
        Ordering::Greater
    );
    assert_eq!(k.cmp(&key("x", 0, &g, &p)), Ordering::Less);
    assert_eq!(
        key("x", 0, &g, &p).cmp(&key("x", 0, &f, &q)),
        Ordering::Greater
    );
    // A keypath before a longer one it begins.
    assert_eq!(k.cmp(&key("x", 0, &f, &q)), Ordering::Less);
    assert!(k != key("x", 0, &f, &q));
    // A local binder's level name sorts before every written name.
    assert_eq!(key("\u{0}0", 9, &g, &q).cmp(&k), Ordering::Less);
}

#[test]
fn a_new_scheduler_has_no_value() {
    let s: Schedule<i64> = Schedule::default();
    assert_eq!(s.values().get(0), None);
    assert_eq!(s.values().get(5), None);
}

fn pow_kept() -> Op {
    // `2 ^ 200`, a kept exponent with no exact form for a root or a power.
    Op::Pow(Exponent::Num(Num::from(2).pow(200)))
}

/// DESIGN.md step M0.5, the backward table: `^` with an even exponent gives two pieces of
/// opposite sign. With an exponent past `2 ^ 127` the roots are bounded outward
/// (COMPLEXITY.md S36), so the result must hold every member that gives a result in `z`, and
/// lie in the operand.
#[test]
fn backward_powers_with_a_kept_exponent_hold_every_root() {
    let all = IntervalSet::top();
    let k = pow_kept();
    // `x ^ (2 ^ 200)` in `0..=1`: exactly `x` in `-1..=1`.
    assert_eq!(
        backward(&k, 0, &all, &all, &IntervalSet::of(0, 1)),
        IntervalSet::of(-1, 1)
    );
    // `x ^ (2 ^ 200) == 0`: `x == 0`.
    assert_eq!(
        backward(&k, 0, &all, &all, &IntervalSet::single(0)),
        IntervalSet::single(0)
    );
    // Negative results: no `x`.
    assert!(backward(&k, 0, &all, &all, &IntervalSet::of(-5, -1)).is_empty());
    // A bound past `2 ^ u32::MAX`: `x` in `-1..=1` at least, and within the operand.
    let huge = IntervalSet::range(End::of(0), End::Fin(Num::from(2).pow(u32::MAX)));
    let r = backward(&k, 0, &all, &all, &huge);
    assert!(IntervalSet::of(-1, 1).is_subset(&r), "{r}");
    let operand = IntervalSet::of(-100, 100);
    let r = backward(&k, 0, &operand, &all, &huge);
    assert!(
        IntervalSet::of(-1, 1).is_subset(&r) && r.is_subset(&operand),
        "{r}"
    );
    // The forward image agrees: `0`, `1` and `-1` are exact by parity.
    for b in [-1i64, 0, 1] {
        let want = IntervalSet::single(b.abs());
        assert_eq!(forward(&k, &IntervalSet::single(b), &all), want, "{b}");
    }
    // An odd kept exponent, `2 ^ 200 + 1`: signed roots; `x ^ k` in `-1..=1` is `x` in `-1..=1`.
    let odd = Op::Pow(Exponent::Num(&Num::from(2).pow(200) + &Num::ONE));
    assert_eq!(
        backward(&odd, 0, &all, &all, &IntervalSet::of(-1, 1)),
        IntervalSet::of(-1, 1)
    );
    assert_eq!(
        forward(&odd, &IntervalSet::single(-1), &all),
        IntervalSet::single(-1)
    );
    // A kept exponent written out as a big integer is the same exponent.
    let written = Op::Pow(Exponent::Num(Num::from(BigInt::from(2).pow(200))));
    assert_eq!(
        backward(&written, 0, &all, &all, &IntervalSet::of(0, 1)),
        IntervalSet::of(-1, 1)
    );
}

/// Union, intersection and difference of two sets that share most of their pieces, as a set
/// and the same set with one piece removed and one added: the operations meet subtrees held
/// by both, which they may return shared, and must still give the sets of members.
#[test]
fn set_operations_on_sets_that_share_most_pieces() {
    let piece = |i: i64| (End::of(10 * i), End::of(10 * i + 1));
    let pieces = |skip: Option<i64>, far: bool| {
        let mut ps: Vec<(End, End)> = (0..64).filter(|&i| Some(i) != skip).map(piece).collect();
        if far {
            ps.push((End::of(10_000), End::of(10_000)));
        }
        IntervalSet::from_pieces(ps)
    };
    let a = (0..64).fold(IntervalSet::empty(), |s, i| {
        s.join(&IntervalSet::of(10 * i, 10 * i + 1))
    });
    assert_eq!(a, pieces(None, false));
    let far = IntervalSet::single(10_000);
    for skip in [0, 1, 31, 32, 62, 63] {
        let gone = IntervalSet::of(10 * skip, 10 * skip + 1);
        let b = a.join(&far).minus(&gone);
        assert_eq!(b, pieces(Some(skip), true), "{skip}");
        assert_eq!(a.join(&b), pieces(None, true), "{skip}");
        assert_eq!(b.join(&a), pieces(None, true), "{skip}");
        assert_eq!(a.meet(&b), pieces(Some(skip), false), "{skip}");
        assert_eq!(b.meet(&a), pieces(Some(skip), false), "{skip}");
        assert_eq!(a.minus(&b), gone, "{skip}");
        assert_eq!(b.minus(&a), far, "{skip}");
    }
    // A set less itself, held once or twice.
    assert!(a.minus(&a).is_empty());
    assert!(a.minus(&a.clone()).is_empty());
    assert_eq!(a.minus(&IntervalSet::empty()), a);
    assert!(IntervalSet::empty().minus(&a).is_empty());
}
