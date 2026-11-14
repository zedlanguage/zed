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
/// The operands come from `rng`; the callers draw its seed afresh each run and print it
/// (`ZED_TEST_SEED=<seed>` repeats the run). It was `Rng::new(k)` (TEST-l0123-leftovers).
fn sum_chain(rng: &mut Rng, k: usize) -> IntervalSet {
    let mut acc = sparse(rng);
    for _ in 0..k {
        let next = sparse(rng);
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

/// Each of the six operators on `draws` pairs of small sets drawn with the fixed seed 325:
/// the image holds every result of members, and keeps to the most pieces any region of an
/// operand has. `checked` counts the member pairs, at least `at_least`.
///
/// TEST-bench-move-l0123, author P178 (many cases are a benchmark): the test drew 600 pairs
/// (0.64 s alone at load 25); it now draws 60, and the 600 run as
/// `bench::an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region`.
fn image_holds(draws: usize, at_least: usize) {
    let mut rng = Rng::new(325);
    let mut checked = 0;
    for _ in 0..draws {
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
    assert!(checked > at_least, "{checked}");
}

#[test]
fn an_image_holds_every_result_and_keeps_to_the_most_pieces_of_a_region() {
    image_holds(60, 10_000);
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

fn check_ends(what: &str, base: num_bigint::BigInt, n: usize) {
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

/// Small instance of `bench::a_chain_of_operators_keeps_to_its_operands_pieces`: a chain of six
/// `+` of `{0, 10}` holds every sum of members in two pieces, and a chain of one to four `+`
/// over operands of eight sparse pieces keeps to eight pieces at every step (`sum_chain`
/// asserts it at each step).
#[test]
fn a_short_chain_of_sums_keeps_its_members_in_few_pieces() {
    let a = IntervalSet::from_pieces(vec![(End::of(0), End::of(0)), (End::of(10), End::of(10))]);
    let mut acc = a.clone();
    for _ in 0..6 {
        acc = revision::forward(&Op::Add, &acc, &a);
    }
    for v in (0..=70).step_by(10) {
        assert!(acc.contains(v), "{acc} has {v}");
    }
    assert!(acc.len() <= 2, "{acc}");
    let (mut rng, seed) = Rng::fresh("a short chain of sums");
    for k in 1..=4 {
        assert!(
            sum_chain(&mut rng, k).len() <= 8,
            "{k} (ZED_TEST_SEED={seed})"
        );
    }
}

/// Small instance of the six tests `bench::capping_n_pieces_scales` to
/// `bench::membership_tests_in_a_set_scale`, once `the_interval_operations_scale`: on an open
/// set and a closed set of 1, 2, 5 and 12 pieces, the negation and the join agree with
/// membership, the sign parts number at least the pieces, and the forward `*` and `/` by the
/// negated closed set hold every product and quotient of members in a window.
#[test]
fn products_quotients_sign_parts_and_joins_of_open_sets_hold_their_members() {
    let (mut rng, seed) = Rng::fresh("open and closed sets");
    for n in [1usize, 2, 5, 12] {
        let (a, b) = (pieces(&mut rng, n, true), pieces(&mut rng, n, false));
        let nb = b.neg();
        let joined = a.join(&b);
        let w = 14 * n as i64 + 10;
        for v in -w..=w {
            assert_eq!(
                nb.contains(v),
                b.contains(-v),
                "-({b}) at {v}, ZED_TEST_SEED={seed}"
            );
            assert_eq!(
                joined.contains(v),
                a.contains(v) || b.contains(v),
                "{a} join {b} at {v}, ZED_TEST_SEED={seed}"
            );
        }
        assert!(a.sign_parts().len() >= n, "{a}, ZED_TEST_SEED={seed}");
        for op in [Op::Mul, Op::Div] {
            let z = revision::forward(&op, &a, &nb);
            for x in (-w..=w).filter(|&x| a.contains(x)) {
                for y in (-w..=w).filter(|&y| nb.contains(y)) {
                    if let Some(r) = apply(&op, x, y) {
                        assert!(
                            z.contains(r),
                            "{op:?} {a} {nb}: {x}, {y}, ZED_TEST_SEED={seed}"
                        );
                    }
                }
            }
        }
    }
}

/// Small instance of `bench::interval_set_operations_scale`: the meet, the complement within a
/// set and the subset test of one-piece sets against a set of 1 to 40 pieces agree with
/// membership; a join with a member gives the set back; a set grown by one-point joins has
/// those points, nothing between them, and their bounds.
#[test]
fn one_piece_updates_and_queries_agree_with_membership() {
    let (mut rng, seed) = Rng::fresh("one-piece updates");
    for n in [1usize, 2, 5, 40] {
        let b = pieces(&mut rng, n, false);
        let mut grown = IntervalSet::empty();
        let w = 15 * n as i64 + 10;
        for i in 0..n as i64 {
            let v = 7 * i;
            let one = IntervalSet::of(v, v + 3);
            let meet = b.meet(&one);
            let rest = one.complement_in(&b);
            for x in -2..=w {
                let (inb, inone) = (b.contains(x), one.contains(x));
                assert_eq!(
                    meet.contains(x),
                    inb && inone,
                    "{b} meet {one} at {x}, ZED_TEST_SEED={seed}"
                );
                assert_eq!(
                    rest.contains(x),
                    inb && !inone,
                    "{b} minus {one} at {x}, ZED_TEST_SEED={seed}"
                );
            }
            let inside = (v..=v + 3).all(|x| b.contains(x));
            assert_eq!(
                one.is_subset(&b),
                inside,
                "{one} in {b}, ZED_TEST_SEED={seed}"
            );
            assert!(
                b.is_subset(&b.join(&one)),
                "{b} join {one}, ZED_TEST_SEED={seed}"
            );
            if b.contains(v) {
                assert_eq!(
                    b.join(&IntervalSet::single(v)),
                    b,
                    "{b} join {v}, ZED_TEST_SEED={seed}"
                );
            }
            grown = grown.join(&IntervalSet::single(3 * v));
        }
        for i in 0..n as i64 {
            assert!(grown.contains(21 * i), "{grown} has {}", 21 * i);
            assert!(!grown.contains(21 * i + 1), "{grown} lacks {}", 21 * i + 1);
        }
        assert_eq!(
            grown.bounds().map(|(lo, hi)| (lo.clone(), hi.clone())),
            Some((End::of(0), End::of(21 * (n as i64 - 1)))),
            "{grown}"
        );
    }
}

/// Small instance of `bench::bounds_on_many_symbols_scale`: the join of two sets of `k` bounds
/// on `k` symbols, one shifted by 1, keeps a lower and an upper bound for each symbol and holds
/// both sides; their meet lies under both.
#[test]
fn a_join_of_bounds_on_distinct_symbols_keeps_one_per_symbol() {
    use zedc::store::affine::Side;
    use zedc::store::lattice::Lattice;
    for k in 1..=4 {
        let (a, b) = (many(k, 0), many(k, 1));
        let j = a.join(&b);
        assert_eq!(j.bounds(Side::Lower).len(), k, "lower, {k}");
        assert_eq!(j.bounds(Side::Upper).len(), k, "upper, {k}");
        assert!(a.leq(&j) && b.leq(&j), "{k}");
        let m = a.meet(&b);
        assert!(m.leq(&a) && m.leq(&b), "{k}");
    }
}

/// Small instance of `bench::ends_in_one_word_scale_linearly` and
/// `bench::ends_of_2_to_the_200_scale_linearly`: with ends at 0 and near 2^200, the hull of
/// `n` lower bounds and one upper bound is exact, the set moved by 3 is the shifted set, and
/// the set times -2, negated, meets the shifted set by membership near 0 and not at all near
/// 2^200.
#[test]
fn ends_near_0_and_2_to_the_200_move_scale_and_project_exactly() {
    use zedc::store::interval::Num;
    use zedc::store::presburger::{Atom, project};
    for base in [
        num_bigint::BigInt::from(0),
        num_bigint::BigInt::from(1) << 200,
    ] {
        for n in [1usize, 3] {
            let w = ends_work(n, &base);
            let hull = project(&w.hull, &Atom::Sym("x".into())).unwrap();
            let lo = Num::from(&base + 3 * (n - 1));
            let hi = Num::from(&base + 3 * n + 5);
            assert_eq!(hull, IntervalSet::range(Fin(lo), Fin(hi)), "{base} {n}");
            let moved = revision::forward(&Op::Add, &w.set, &IntervalSet::single(3));
            assert_eq!(moved, w.shifted, "{base} {n}");
            assert_eq!(moved.join(&w.shifted), w.shifted, "{base} {n}");
            let scaled = revision::forward(&Op::Mul, &w.set, &IntervalSet::single(-2)).neg();
            let met = moved.join(&w.shifted).meet(&scaled);
            if base == num_bigint::BigInt::from(0) {
                for v in -5..=20 * n as i64 + 10 {
                    assert_eq!(
                        met.contains(v),
                        w.shifted.contains(v) && scaled.contains(v),
                        "{n} at {v}"
                    );
                }
                assert!(!met.is_empty(), "{n}");
            } else {
                assert!(met.is_empty(), "{n}");
            }
        }
    }
}

/// Small instance of `bench::kept_ends_scale_linearly`: on 1 and 3 pieces with kept ends past
/// 2^(10^8), the set moved by 3 is the shifted set, and the set times -2, negated, keeps its
/// pieces apart and meets nothing of the shifted set.
#[test]
fn kept_ends_past_2_to_the_10_to_the_8_move_and_scale_exactly() {
    for n in [1usize, 3] {
        let (set, shifted) = kept_ends(n);
        let moved = revision::forward(&Op::Add, &set, &IntervalSet::single(3));
        assert_eq!(moved.meet(&shifted), shifted, "{n}");
        assert_eq!(moved, shifted, "{n}");
        let scaled = revision::forward(&Op::Mul, &set, &IntervalSet::single(-2)).neg();
        assert_eq!(scaled.len(), n, "{n}");
        assert!(moved.join(&shifted).meet(&scaled).is_empty(), "{n}");
    }
}

/// Small instance of `bench::kept_arithmetic_scales_with_the_bits_of_the_exponent`: the kept
/// arithmetic and the cube root of `2^k` for `k` of both residues 1 and 2 modulo 3, at about
/// 300 and 10^6 bits.
#[test]
fn kept_arithmetic_holds_for_both_irrational_cube_roots() {
    for k in [301, 302, 1_000_001, 1_000_003] {
        kept_arithmetic(k);
    }
}

/// Small instance of `bench::the_cube_of_a_wide_end_scales_with_its_bits`: at 40,000 bits,
/// where indices above 511 have roots wider than a word, and at 131,072 bits, where the
/// remainder tree's first division is past `DIV_LEAF`, the cube of `2^n + 3` is the cube
/// written out and the image of `x^3` up to the end ends at it.
#[test]
fn the_cube_of_a_wide_end_is_its_cube_written_out() {
    use zedc::store::interval::Num;
    for n in [40_000, 131_072] {
        let base = (num_bigint::BigInt::from(1) << n) + 3;
        cube_of_a_wide_end(&base);
        assert_eq!(
            Num::from(base.clone()).pow(3),
            Num::from(base.pow(3)),
            "{n}"
        );
    }
}

/// Small instance of `bench::equality_over_a_wide_base_scales_with_its_bits`: a power of
/// `2^n 3` written out equals the product of the powers of its factors, at widths on either
/// side of a word and past 64 words, and differs from a value of the same bits with another
/// split of the factors.
#[test]
fn a_power_of_a_wide_even_base_equals_the_powers_of_its_factors() {
    use zedc::store::interval::Num;
    for n in [1u32, 63, 64, 65, 200, 4096] {
        let wide = Num::from((num_bigint::BigInt::from(1) << n) * 3);
        let x = wide.pow(1000);
        let want = &Num::from(2).pow(1000 * n) * &Num::from(3).pow(1000);
        equal_over_a_wide_base(&(x.clone(), want));
        let off = &Num::from(2).pow(1000 * n + 1) * &Num::from(3).pow(999);
        assert_ne!(x, off, "{n}");
    }
}

/// Small instance of `bench::equality_over_a_wide_odd_base_scales_with_its_bits`: a power of
/// `3^n 2` written out equals the product of the powers of its factors, below and past the
/// width where the division that takes out the factor 3 passes `DIV_LEAF`, and differs from a
/// value with another split of the factors.
#[test]
fn a_power_of_a_wide_odd_base_equals_the_powers_of_its_factors() {
    use zedc::store::interval::Num;
    for n in [1u32, 41, 300, 4000] {
        let wide = Num::from(num_bigint::BigInt::from(3).pow(n) * 2);
        let x = wide.pow(1000);
        let three = |k: u64| Num::from(3).pow_by(&Num::from(k)).expect("a power");
        let want = &three(1000 * u64::from(n)) * &Num::from(2).pow(1000);
        equal_over_a_wide_base(&(x.clone(), want));
        let off = &three(1000 * u64::from(n) - 1) * &Num::from(2).pow(1001);
        assert_ne!(x, off, "{n}");
    }
}

mod bench;
