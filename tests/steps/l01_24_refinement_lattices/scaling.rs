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
        out.push((End::of(lo), End::of(hi)));
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
    let mut p = s.clone().into_pieces();
    while p.len() > limit.max(1) {
        let gap = |i: usize| match (&p[i].1, &p[i + 1].0) {
            (Fin(hi), Fin(lo)) => lo - hi,
            _ => unreachable!(),
        };
        let at = (0..p.len() - 1).min_by_key(|&i| (gap(i), i)).unwrap();
        p[at].1 = p[at + 1].1.clone();
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
            IntervalSet::from_pieces(a.pieces().chain(b.pieces()).cloned().collect())
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
                (End::of(at), End::of(at))
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
        acc = revision::forward(&Op::Add, &acc, &next);
        assert!(acc.len() <= 8, "{acc}");
    }
    acc
}

/// The pieces of `s` in each sign region: negative, zero, positive.
fn per_region(s: &IntervalSet) -> [usize; 3] {
    let mut n = [0; 3];
    for p in s.sign_parts() {
        n[if p.1 < End::of(0) {
            0
        } else if p.0 > End::of(0) {
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
                (End::of(lo), End::of(lo + rng.int(0, 4)))
            })
            .collect(),
    )
}

const OPS: [Op; 6] = [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Min, Op::Max];

fn apply(op: &Op, a: i64, b: i64) -> Option<i64> {
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
        for op in &OPS {
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
        let b = IntervalSet::range(End::of(lo), End::of(lo + rng.int(0, 9)));
        for op in &OPS {
            let join = a.pieces().fold(IntervalSet::empty(), |j, p| {
                j.join(&revision::forward(
                    op,
                    &IntervalSet::from_pieces(vec![p.clone()]),
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

/// `k` lower and `k` upper bounds, each on a symbol of its own and each with a floor.
fn many(k: usize, shift: i64) -> zedc::store::affine::Bounds {
    use zedc::store::affine::{Affine, Bound, Bounds};
    let side = |c: i64, floor: End| {
        (0..k)
            .map(move |i| Bound {
                affine: Affine::sym(&format!("s{i}")).plus(c),
                floor: floor.clone(),
            })
            .collect::<Vec<_>>()
    };
    Bounds::from_bounds(
        IntervalSet::top(),
        side(shift, End::of(-1)),
        side(shift + 10, End::of(1)),
    )
}

/// The work of the ends: the forward transfer and the joins over `n` pieces whose ends lie
/// near `base`, and the hull of `x` under `n` lower bounds `x >= base + 3i` and one upper
/// bound. With `base` 0 every end is one machine word; with `base` 2^200 every end is a big
/// integer of the same size at `n` and `8n`, so the work grows with `n` alone.
struct EndsWork {
    set: IntervalSet,
    shifted: IntervalSet,
    hull: zedc::store::presburger::Formula,
}

fn ends_work(n: usize, base: &num_bigint::BigInt) -> EndsWork {
    use zedc::store::interval::Num;
    use zedc::store::presburger::{Atom, Con, Formula, Lin};
    let at = |k: usize| Num::from(base + num_bigint::BigInt::from(k));
    let set = |shift: usize| {
        IntervalSet::from_pieces(
            (0..n)
                .map(|i| (Fin(at(10 * i + shift)), Fin(at(10 * i + shift + 4))))
                .collect(),
        )
    };
    let x = || Lin::atom(Atom::Sym("x".into()));
    let mut cons: Vec<Formula> = (0..n)
        .map(|i| Formula::Con(Con::ge(&x(), &Lin::constant(base + 3 * i))))
        .collect();
    cons.push(Formula::Con(Con::ge(
        &Lin::constant(base + 3 * n + 5),
        &x(),
    )));
    EndsWork {
        set: set(0),
        shifted: set(3),
        hull: Formula::and(cons),
    }
}

fn run_ends(w: &EndsWork) {
    use zedc::store::presburger::{Atom, project};
    let three = IntervalSet::single(3);
    let moved = revision::forward(&Op::Add, &w.set, &three);
    let scaled = revision::forward(&Op::Mul, &w.set, &IntervalSet::single(-2));
    std::hint::black_box(moved.join(&w.shifted).meet(&scaled.neg()));
    std::hint::black_box(project(&w.hull, &Atom::Sym("x".into())).unwrap());
}

fn check_ends(what: &str, base: num_bigint::BigInt) {
    let n = 200;
    let (small, large) = (ends_work(n, &base), ends_work(scaling::FACTOR * n, &base));
    for (w, m) in [(&small, n), (&large, scaling::FACTOR * n)] {
        let hull = zedc::store::presburger::project(
            &w.hull,
            &zedc::store::presburger::Atom::Sym("x".into()),
        )
        .unwrap();
        let lo = zedc::store::interval::Num::from(&base + 3 * (m - 1));
        let hi = zedc::store::interval::Num::from(&base + 3 * m + 5);
        assert_eq!(hull, IntervalSet::range(Fin(lo), Fin(hi)), "{what} at {m}");
    }
    scaling::check(what, n, |m| run_ends(if m == n { &small } else { &large }));
}

/// The bound of `x ^ k` for x in 2..=3, its demand back on x, and its order against another
/// power: kept as powers, so the work grows with the bits of `k`, not with the `k` bits of
/// the bound.
fn power_bounds(k: usize) {
    use zedc::store::interval::Num;
    let k = u32::try_from(k).unwrap();
    let x = IntervalSet::of(2, 3);
    let image = revision::forward(&Op::Pow(k.into()), &x, &x);
    let back = revision::backward(
        &Op::Pow(k.into()),
        0,
        &IntervalSet::top(),
        &IntervalSet::top(),
        &image,
    );
    assert_eq!(back, IntervalSet::of(-3, -2).join(&x));
    assert!(Num::from(2).pow(k + k / 2) < Num::from(3).pow(k));
}

/// The forward sum, product and negation, the join and the meet over `n` pieces whose ends lie
/// a little past 2^(10^8): kept forms of one core, so each end costs the same at `n` and `8n`
/// and the work grows with `n` alone.
fn kept_ends(n: usize) -> (IntervalSet, IntervalSet) {
    use zedc::store::interval::Num;
    let base = Num::from(2).pow(100_000_000);
    let at = |k: usize| &base + &Num::from(i64::try_from(k).unwrap());
    let set = |shift: usize| {
        IntervalSet::from_pieces(
            (0..n)
                .map(|i| (Fin(at(10 * i + shift)), Fin(at(10 * i + shift + 4))))
                .collect(),
        )
    };
    (set(0), set(3))
}

fn run_kept_ends((set, shifted): &(IntervalSet, IntervalSet)) {
    let moved = revision::forward(&Op::Add, set, &IntervalSet::single(3));
    let scaled = revision::forward(&Op::Mul, set, &IntervalSet::single(-2));
    std::hint::black_box(moved.join(shifted).meet(&scaled.neg()));
    std::hint::black_box(moved.meet(shifted));
}

/// `x ^ k + 1`, `k * x ^ k - 1` and the cube root of `2 ^ k`, with their order: kept forms,
/// so the work grows with the bits of `k`, not with the `k` bits of the values.
fn kept_arithmetic(k: usize) {
    use zedc::store::interval::Num;
    let k = u32::try_from(k).unwrap();
    let x = IntervalSet::of(2, 3);
    let image = revision::forward(&Op::Pow(k.into()), &x, &x);
    let plus = revision::forward(&Op::Add, &image, &IntervalSet::single(1));
    let times = revision::forward(&Op::Mul, &IntervalSet::single(i64::from(k)), &image);
    let less = revision::forward(&Op::Sub, &times, &IntervalSet::single(1));
    assert!(plus.bounds().unwrap().1 < less.bounds().unwrap().1);
    let two = Num::from(2).pow(k);
    let root = two.floor_root(3);
    assert!(root.pow(3) <= two && two < Num::from(2).pow(k + 1));
    assert_eq!(two.ceil_root(3), &root + &Num::ONE);
    // Sums of powers of different integers, a difference that folds, and a power of a sum.
    let (three, five) = (Num::from(3).pow(k), Num::from(5).pow(k));
    let s = &three + &five;
    assert!(five < s && &s - &five == three);
    assert_eq!(&Num::from(3).pow(k + 1) - &three, &three * &Num::from(2));
    assert!(s.mod_floor(&Num::from(1_000_003)) < Num::from(1_000_003));
    let cube = (&two + &Num::ONE).pow(3);
    let expanded = &(&(&Num::from(2).pow(3 * k) + &(&Num::from(2).pow(2 * k) * &Num::from(3)))
        + &(&two * &Num::from(3)))
        + &Num::ONE;
    assert!((&cube - &expanded).is_zero());
}

/// `3 ^ e * 9 ^ (e + 1) - 3 ^ (3e + 2)` and `6 ^ e * 5 ^ (e + 1) - 2 ^ e * 3 ^ e *
/// 5 ^ (e + 1)`: integer bases reduced to their least roots and cores compared over a coprime
/// base, so each difference cancels with work of order the bits of `e`.
fn equal_cores(e: usize) {
    use zedc::store::interval::Num;
    let e = u32::try_from(e).unwrap();
    let pow = |b: i64, k: u32| Num::from(b).pow(k);
    let product = &pow(3, e) * &pow(9, e + 1);
    assert!((&product - &pow(3, 3 * e + 2)).is_zero());
    let six = &pow(6, e) * &pow(5, e + 1);
    let apart = &pow(2, e) * &(&pow(3, e) * &pow(5, e + 1));
    assert_eq!(&(&six + &Num::from(7)) - &apart, Num::from(7));
}

/// The bound of `x^3` for `x` in `[0, 2^n + 3]`, and the cube of the end itself: the end is
/// kept as a power of its least root, found by a 2-adic root per prime index below its bits,
/// at the cost of a few products of its bits, not of a root of all its bits per index. An
/// index whose root is wider than a word is first tested modulo the least prime that is 1
/// modulo it, all such residues coming from one remainder tree, so `2^n + 3`, which is no
/// power, takes almost no wide root.
fn cube_of_a_wide_end(base: &num_bigint::BigInt) {
    use zedc::store::interval::Num;
    let end = Num::from(base.clone());
    let cube = end.pow(3);
    assert!(cube > end);
    let x = IntervalSet::range(Fin(Num::ZERO), Fin(end));
    let image = revision::forward(&Op::Pow(3u32.into()), &x, &x);
    assert_eq!(image.bounds().map(|(_, hi)| hi), Some(&Fin(cube)));
}

/// `(2^n * 3) ^ 1000` against `2 ^ (1000 n) * 3 ^ 1000`: the cores are written over the
/// coprime base 2, 3, found by taking every power of a shared factor out at once, so the
/// equality costs a few products of `n` bits, not `n` divisions.
fn equal_over_a_wide_base((x, y): &(zedc::store::interval::Num, zedc::store::interval::Num)) {
    assert_eq!(x, y);
}

mod bench;
