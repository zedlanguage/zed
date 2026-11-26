//! The threshold-implication component (DESIGN.md sec:domains, item (2) of the tests that hold
//! disjunctions; QUESTIONS A57, resolved at zed 5859622): parts `x + k*w <= a || y - m*w >= b`
//! and base atoms of the same two shapes, solved exactly by two propagations at the hub's least
//! value and a binary search for its greatest value that passes ([`threshold::solve`]).
//!
//! Ported from the reference model `/home/luke/Work/wt/s4-analysis/a57/a57.mjs`, which matched
//! enumeration on 160,000 components, and from `red.mjs`, the reduction from reachability that
//! shows why a part of two lower bounds has no such method. The model's two variants broken on
//! purpose (`a57_ctl1.mjs`: bounds at `c*` in place of `p`; `a57_ctl2.mjs`: a part firing only
//! above `a + k*c`) were run as negative controls against this port and are not committed.

use std::collections::BTreeSet;

use zed_tests::scaling;
use zedc::store::int::{Int, Num};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::threshold::{self, Answer, Lower, System, Upper};

/// The model's generator: a linear congruential sequence, so a seed names a corpus.
///
/// The step wraps: 2^31 divides 2^64, so the wrapped `seed * 1103515245 + 12345` mod 2^31 is
/// the exact one for every seed. It multiplied without wrapping until DRY-test-helpers, which
/// panicked in a debug build for a seed above `(2^64 - 12345) / 1103515245`, 16,716,347,288;
/// every seed below that draws the stream it drew then (`a_large_seed_steps_exactly`).
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: i64) -> i64 {
        self.0 = self.0.wrapping_mul(1_103_515_245).wrapping_add(12_345) % 2_147_483_648;
        (self.0 % n as u64) as i64
    }
}

/// [`Rng::below`] steps a seed of any size to the exact `(seed * 1103515245 + 12345) mod 2^31`,
/// without the overflow of the unwrapped multiply it had.
#[test]
fn a_large_seed_steps_exactly() {
    // 16,716,347,288 is the last seed whose unwrapped step fits in 64 bits; 16,716,347,289 the
    // first that overflowed.
    for seed in [
        0,
        1,
        2_147_483_647,
        16_716_347_288,
        16_716_347_289,
        u64::MAX,
    ] {
        let mut r = Rng(seed);
        r.below(1);
        let exact = (u128::from(seed) * 1_103_515_245 + 12_345) % 2_147_483_648;
        assert_eq!(u128::from(r.0), exact, "seed {seed}");
    }
}

fn upper(x: usize, k: i64, a: i64) -> Upper {
    Upper {
        x,
        k: Int::from(k),
        a: Int::from(a),
    }
}

fn lower(y: usize, m: i64, b: i64) -> Lower {
    Lower {
        y,
        m: Int::from(m),
        b: Int::from(b),
    }
}

/// Each name's least and greatest value that pass, and the hub's values that pass.
type Passing = (Vec<(i64, i64)>, Vec<i64>);

/// The values of each name and of the hub that pass, by enumeration over finite sets: each
/// name's least and greatest value, and the hub's values; `None` when none pass.
fn enumerate(sys: &System) -> Option<Passing> {
    enumerate_values(sys).0
}

/// [`enumerate`], and each name's values that pass, every one.
fn enumerate_values(sys: &System) -> (Option<Passing>, Vec<BTreeSet<i64>>) {
    let values = |d: &IntervalSet| -> Vec<i64> {
        d.pieces()
            .flat_map(|(lo, hi)| lo.to_i64().expect("finite")..=hi.to_i64().expect("finite"))
            .collect()
    };
    let doms: Vec<Vec<i64>> = sys.names.iter().map(values).collect();
    let i = |v: &Int| Num::from(v).to_i64().expect("small");
    let n = doms.len();
    let mut out: Option<Passing> = None;
    let mut sets: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); n];
    let mut x = vec![0i64; n];
    fn rec(
        i: usize,
        c: i64,
        x: &mut Vec<i64>,
        doms: &[Vec<i64>],
        ok: &dyn Fn(&[i64], i64) -> bool,
        out: &mut Option<Passing>,
        sets: &mut [BTreeSet<i64>],
    ) {
        if i == doms.len() {
            if ok(x, c) {
                let o = out.get_or_insert_with(|| (vec![(i64::MAX, i64::MIN); x.len()], vec![]));
                for (b, v) in o.0.iter_mut().zip(x.iter()) {
                    *b = (b.0.min(*v), b.1.max(*v));
                }
                if o.1.last() != Some(&c) {
                    o.1.push(c);
                }
                for (s, v) in sets.iter_mut().zip(x.iter()) {
                    s.insert(*v);
                }
            }
            return;
        }
        for &v in &doms[i] {
            x[i] = v;
            rec(i + 1, c, x, doms, ok, out, sets);
        }
    }
    let up = |u: &Upper, x: &[i64], c: i64| x[u.x] + i(&u.k) * c <= i(&u.a);
    let low = |l: &Lower, x: &[i64], c: i64| x[l.y] - i(&l.m) * c >= i(&l.b);
    let ok = |x: &[i64], c: i64| {
        sys.uppers.iter().all(|u| up(u, x, c))
            && sys.lowers.iter().all(|l| low(l, x, c))
            && sys.parts.iter().all(|(u, l)| up(u, x, c) || low(l, x, c))
    };
    for c in values(&sys.hub) {
        rec(0, c, &mut x, &doms, &ok, &mut out, &mut sets);
    }
    (out, sets)
}

/// The answer of [`threshold::solve`] in the form [`enumerate`] gives.
fn solved(sys: &System) -> Option<Option<Passing>> {
    let fin = |e: &End| e.to_i64().expect("finite");
    match threshold::solve(sys) {
        Answer::Empty => Some(None),
        Answer::MixedHub => None,
        Answer::Bounds { names, hub, .. } => Some(Some((
            names.iter().map(|(l, h)| (fin(l), fin(h))).collect(),
            hub.pieces()
                .flat_map(|(lo, hi)| fin(lo)..=fin(hi))
                .collect(),
        ))),
    }
}

/// A random component: `n` names with values from `-2..=2` up to a width of 5, some with a
/// value left out; a hub of 1 to `hub` values from `-2..=2`; up to 5 parts and some base atoms,
/// with coefficients from `ks`.
fn random(r: &mut Rng, hub: i64, ks: &[i64]) -> System {
    let n = 2 + r.below(3) as usize;
    let names: Vec<IntervalSet> = (0..n)
        .map(|_| {
            let lo = r.below(5) - 2;
            let hi = lo + r.below(6);
            let d = IntervalSet::of(lo, hi);
            if hi - lo >= 2 && r.below(3) == 0 {
                let gap = lo + 1 + r.below(hi - lo - 1);
                d.meet(&IntervalSet::from_pieces(vec![
                    (End::NegInf, End::of(gap - 1)),
                    (End::of(gap + 1), End::PosInf),
                ]))
            } else {
                d
            }
        })
        .collect();
    let p = r.below(5) - 2;
    let hub_set = IntervalSet::of(p, p + r.below(hub));
    let k = |r: &mut Rng| ks[r.below(ks.len() as i64) as usize];
    let parts = (0..1 + r.below(5))
        .map(|_| {
            let x = r.below(n as i64) as usize;
            let y = (x + 1 + r.below(n as i64 - 1) as usize) % n;
            (
                upper(x, k(r), r.below(5) - 2),
                lower(y, k(r), r.below(5) - 2),
            )
        })
        .collect();
    let mut uppers = Vec::new();
    let mut lowers = Vec::new();
    for x in 0..n {
        if r.below(4) == 0 {
            uppers.push(upper(x, k(r), r.below(5) - 1));
        }
        if r.below(3) == 0 {
            lowers.push(lower(x, k(r), r.below(5) - 2));
        }
    }
    System {
        names,
        hub: hub_set,
        parts,
        uppers,
        lowers,
    }
}

/// Runs `count` random components of [`random`] and asserts each answer is the enumerated
/// one; returns how many were solved (not left to S4-hub-mixed) and how many had no value.
fn corpus(seed: u64, count: usize, hub: i64, ks: &[i64]) -> (usize, usize) {
    let mut r = Rng(seed);
    let (mut solved_n, mut empty) = (0, 0);
    for it in 0..count {
        let sys = random(&mut r, hub, ks);
        let Some(none) = component_checked(&sys, &format!("seed {seed}, component {it}")) else {
            continue;
        };
        solved_n += 1;
        empty += usize::from(none);
    }
    (solved_n, empty)
}

/// Asserts that [`threshold::solve`]'s answer on `sys` is the enumerated one (`at` names the
/// component in a failure): `None` when the component is left to S4-hub-mixed, else whether no
/// value passes.
///
/// An answer marked `filled` is also checked value by value: each name's values that pass are
/// then every one of its own values between its bounds (FAIL-preimage-threshold-hull-unrefused).
fn component_checked(sys: &System, at: &str) -> Option<bool> {
    let got = solved(sys)?;
    let (want, sets) = enumerate_values(sys);
    assert_eq!(got, want, "{at}: {sys:?}");
    if let (Answer::Bounds { filled: true, .. }, Some((ends, _))) = (threshold::solve(sys), &want) {
        for (i, ((lo, hi), d)) in ends.iter().zip(&sys.names).enumerate() {
            let between: BTreeSet<i64> = (*lo..=*hi).filter(|v| d.contains(*v)).collect();
            assert_eq!(sets[i], between, "{at}, name {i}, filled: {sys:?}");
        }
    }
    Some(want.is_none())
}

/// A cycle of parts can leave a hole between a name's bounds, so the answer is not `filled`:
/// with the hub at 0, `x <= 0 || z >= 1` and `z <= 0 || x >= 2` on x in `0..=2` and z in
/// `0..=1` leave x {0, 2}. And a hub of two values with both signs: `x + 1 <= 3w <= x + 2` on
/// x in `0..=4`, w in `1..=2`, leaves x {1, 2} at w = 1 and {4} at w = 2. Both gave `filled`
/// answers before FAIL-preimage-threshold-hull-unrefused, which kept the hull.
#[test]
fn a_cycle_of_parts_is_not_filled() {
    let cycle = System {
        names: vec![IntervalSet::of(0, 2), IntervalSet::of(0, 1)],
        hub: IntervalSet::of(0, 0),
        parts: vec![
            (upper(0, 0, 0), lower(1, 0, 1)),
            (upper(1, 0, 0), lower(0, 0, 2)),
        ],
        uppers: vec![],
        lowers: vec![],
    };
    assert_eq!(
        threshold::solve(&cycle),
        Answer::Bounds {
            names: vec![(fin(0), fin(2)), (fin(0), fin(1))],
            hub: IntervalSet::of(0, 0),
            filled: false,
        }
    );
    assert_eq!(enumerate_values(&cycle).1[0], BTreeSet::from([0, 2]));
    let mixed = System {
        names: vec![IntervalSet::of(0, 4)],
        hub: IntervalSet::of(1, 2),
        parts: vec![],
        uppers: vec![upper(0, -3, -1)],
        lowers: vec![lower(0, 3, -2)],
    };
    assert_eq!(
        threshold::solve(&mixed),
        Answer::Bounds {
            names: vec![(fin(1), fin(4))],
            hub: IntervalSet::of(1, 2),
            filled: false,
        }
    );
    assert_eq!(enumerate_values(&mixed).1[0], BTreeSet::from([1, 2, 4]));
}

/// A new seed for [`Rng`] ([`zed_tests::instances::Rng::fresh`], printed with `what`), below
/// `2^31`, the range of the generator's states. A seed and its value mod `2^31` draw the same
/// stream, so the reduced seed the failure messages print repeats the run.
fn fresh(what: &str) -> u64 {
    zed_tests::instances::Rng::fresh(what).1 % 2_147_483_648
}

/// Components of each corpus test: 5,000 for each of the seeds 1 to 4 before random tests took
/// a new seed each run (about 0.4 s each at load 27); 5,000 for one seed now.
const COUNT: usize = 5_000;

/// The model's corpus: every coefficient 1 (the model's parts `v + w <= 0 || u - w >= 1`), with
/// every constant, interval and hub at random.
#[test]
fn components_of_unit_coefficients_equal_enumeration() {
    let seed = fresh("components of unit coefficients");
    let (n, empty) = corpus(seed, COUNT, 4, &[1]);
    assert_eq!(n, COUNT, "seed {seed}");
    eprintln!("seed {seed}: {empty} of {n} empty");
    // A component with no value and one with values are compared in every run, whatever the
    // draws gave (PROOF-test-count-thresholds; until 2026-11-15 the test asserted that both
    // occurred among its 5,000). At the hub's one value 0, the part reads `x0 <= 0 || x1 >= 1`
    // and the base `x0 >= 1`, so `x1 >= 1`; the base `x1 <= 0` then leaves no value, and
    // without it `x0 = x1 = 1` passes.
    let mut sys = System {
        names: vec![IntervalSet::of(0, 1), IntervalSet::of(0, 1)],
        hub: IntervalSet::of(0, 0),
        parts: vec![(upper(0, 1, 0), lower(1, 1, 1))],
        uppers: vec![upper(1, 1, 0)],
        lowers: vec![lower(0, 1, 1)],
    };
    assert_eq!(component_checked(&sys, "built, x1 <= 0"), Some(true));
    sys.uppers.clear();
    assert_eq!(component_checked(&sys, "built"), Some(false));
}

/// Coefficients from 0 to 2: `k` and `m` of one sign, zero allowed.
#[test]
fn components_of_coefficients_at_least_zero_equal_enumeration() {
    corpus(
        fresh("components of coefficients at least 0"),
        COUNT,
        4,
        &[0, 1, 2],
    );
}

/// Coefficients from -2 to 0: the hub's values that pass run from some value up to its
/// greatest.
#[test]
fn components_of_coefficients_at_most_zero_equal_enumeration() {
    corpus(
        fresh("components of coefficients at most 0"),
        COUNT,
        4,
        &[-2, -1, 0],
    );
}

/// Coefficients of both signs and a hub of one or two values: the join of the answers at each
/// value.
#[test]
fn components_with_both_signs_and_a_hub_of_two_values_equal_enumeration() {
    let seed = fresh("components with both signs");
    let (n, _) = corpus(seed, COUNT, 2, &[-1, 0, 1]);
    assert_eq!(n, COUNT, "seed {seed}: every hub of two values is solved");
}

/// A hub of three or more values with coefficients of both signs is not solved as a whole
/// (study S4-hub-mixed, `docs/studies/s4-hub-mixed.md`: such a solve would multiply Boolean
/// matrices, [`the_least_values_under_a_mixed_hub_are_a_boolean_product`]).
#[test]
fn a_hub_of_three_values_with_both_signs_is_left_open() {
    let sys = System {
        names: vec![IntervalSet::of(0, 3), IntervalSet::of(0, 3)],
        hub: IntervalSet::of(0, 2),
        parts: vec![(upper(0, 1, 0), lower(1, -1, 1))],
        uppers: vec![],
        lowers: vec![],
    };
    assert_eq!(threshold::solve(&sys), Answer::MixedHub);
}

/// The exact answer of a component, found by solving it with the hub fixed at each of its
/// values in turn and joining the answers: the points that pass are the union over the hub's
/// values `c` of those that pass at `c` (the proof at `threshold::mixed`), and each solve at
/// one value is exact (the corpora above). O(W) solves for a hub of W values.
fn joined_over_hub(sys: &System) -> Option<Passing> {
    let fin = |e: &End| e.to_i64().expect("finite");
    let hub: Vec<i64> = (sys.hub.pieces())
        .flat_map(|(lo, hi)| fin(lo)..=fin(hi))
        .collect();
    let mut out: Option<Passing> = None;
    for c in hub {
        let one = System {
            hub: IntervalSet::of(c, c),
            ..sys.clone()
        };
        let Some(Some((names, _))) = solved(&one) else {
            continue;
        };
        let o = out.get_or_insert_with(|| (vec![(i64::MAX, i64::MIN); names.len()], vec![]));
        for (b, (lo, hi)) in o.0.iter_mut().zip(names) {
            *b = (b.0.min(lo), b.1.max(hi));
        }
        o.1.push(c);
    }
    out
}

/// Name 0 of [`product_gadget`] and [`steep_lines`]: `t` in `1..=1`.
const ONE: usize = 0;

/// Adds to `sys` a name `y` in `0..=top` and the two parts `t + w <= l || y + w >= l + 1` and
/// `y <= 0 || target >= 1`: the first fires when `w >= l` and then sets `y >= l + 1 - w`, which
/// fires the second when `w <= l`, so `target >= 1` is forced exactly when `w = l`. The first
/// part's coefficients are 1 and -1, both signs.
fn edge_at(sys: &mut System, l: i64, top: i64, target: usize) {
    let y = sys.names.len();
    sys.names.push(IntervalSet::of(0, top));
    sys.parts.push((upper(ONE, 1, l), lower(y, -1, l + 1)));
    sys.parts.push((upper(y, 0, 0), lower(target, 0, 1)));
}

/// The reduction of study S4-hub-mixed from the Boolean product of two k×k matrices `a` and
/// `b`: the hub `w` in `1..=k`; names `u_i`, `v_j`, `x_ij` in `0..=1`; an edge of [`edge_at`]
/// to `u_i` at `w = l` for each `a[i][l-1]` false and to `v_j` at `w = l` for each
/// `b[l-1][j]` false; and the parts `u_i <= 0 || x_ij >= 1`, `v_j <= 0 || x_ij >= 1`. At
/// `w = l` the least value of `x_ij` is 1 exactly when `a[i][l-1]` or `b[l-1][j]` is false;
/// every value of `w` passes, so the exact least value of `x_ij` is 1 exactly when that holds
/// at every `l`, that is when entry `(i, j)` of the product is false. Returns the component and
/// the index of `x_ij` at `i * k + j`. Its size: at most 4k² + 2k² parts and 3k² + 2k + 1
/// names, the hub's width k, every coefficient in `-1..=1`.
fn product_gadget(a: &[Vec<bool>], b: &[Vec<bool>]) -> (System, Vec<usize>) {
    let k = a.len();
    let kk = k as i64;
    let u = |i: usize| 1 + i;
    let v = |j: usize| 1 + k + j;
    let x = |i: usize, j: usize| 1 + 2 * k + i * k + j;
    let mut sys = System {
        names: [
            vec![IntervalSet::of(1, 1)],
            vec![IntervalSet::of(0, 1); 2 * k + k * k],
        ]
        .concat(),
        hub: IntervalSet::of(1, kk),
        parts: vec![],
        uppers: vec![],
        lowers: vec![],
    };
    for i in 0..k {
        for j in 0..k {
            sys.parts.push((upper(u(i), 0, 0), lower(x(i, j), 0, 1)));
            sys.parts.push((upper(v(j), 0, 0), lower(x(i, j), 0, 1)));
        }
    }
    for l in 0..k {
        for i in 0..k {
            if !a[i][l] {
                edge_at(&mut sys, l as i64 + 1, kk, u(i));
            }
            if !b[l][i] {
                edge_at(&mut sys, l as i64 + 1, kk, v(i));
            }
        }
    }
    let xs = (0..k * k).map(|ij| x(ij / k, ij % k)).collect();
    (sys, xs)
}

/// The Boolean product of two square matrices.
fn boolean_product(a: &[Vec<bool>], b: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let k = a.len();
    (0..k)
        .map(|i| (0..k).map(|j| (0..k).any(|l| a[i][l] && b[l][j])).collect())
        .collect()
}

/// Study S4-hub-mixed: the exact least values of a threshold-implication component whose hub
/// has k values and coefficients of both signs give the Boolean product of two k×k matrices
/// ([`product_gadget`]), from a component of O(k²) parts. So a solve in O(N log N log W) for
/// N parts and a hub of width W would multiply k×k Boolean matrices in O(k² log³ k); the proof
/// and the citations are at `threshold::mixed`. Checked here on random matrices of k from 1 to
/// 6 against [`boolean_product`], through [`joined_over_hub`]; at k = 2, where the hub has two
/// values and [`threshold::solve`] answers, against its answer, and against enumeration when
/// the component has at most 4 edges (its points then number at most 3^4 · 2^8 per hub value).
/// Negative control, run once and not committed: with the first part of [`edge_at`] written
/// `t + w <= l || y - w >= 1 - l` (one sign, so the edge holds at every `w >= l`), the test
/// failed on all 20 seeds tried (`ZED_TEST_SEED` 1 to 20), 19 of them at an entry of the
/// product and one at the check that the component is refused.
#[test]
fn the_least_values_under_a_mixed_hub_are_a_boolean_product() {
    let seed = fresh("boolean product under a mixed hub");
    let mut r = Rng(seed);
    let mut enumerated = 0;
    for it in 0..300 {
        let k = 1 + r.below(6) as usize;
        let mut matrix = || -> Vec<Vec<bool>> {
            (0..k)
                .map(|_| (0..k).map(|_| r.below(3) != 0).collect())
                .collect()
        };
        let (a, b) = (matrix(), matrix());
        let (sys, xs) = product_gadget(&a, &b);
        let at = format!("seed {seed}, draw {it}, a {a:?}, b {b:?}");
        let want = boolean_product(&a, &b);
        let (names, hub) = joined_over_hub(&sys).expect("every hub value passes");
        assert_eq!(hub, (1..=k as i64).collect::<Vec<_>>(), "{at}");
        for (ij, &x) in xs.iter().enumerate() {
            let zero = !want[ij / k][ij % k];
            assert_eq!(names[x], (i64::from(zero), 1), "{at}, entry {ij}");
        }
        // With no false entry there is no edge and no coefficient of the hub.
        if k >= 3 && sys.names.len() > 1 + 2 * k + k * k {
            assert_eq!(threshold::solve(&sys), Answer::MixedHub, "{at}");
        }
        if k == 2 {
            assert_eq!(
                solved(&sys),
                Some(Some((names.clone(), hub.clone()))),
                "{at}"
            );
            if sys.parts.len() <= 2 * 4 + 2 * 4 {
                enumerated += 1;
                assert_eq!(enumerate(&sys), Some((names, hub)), "{at}");
            }
        }
    }
    eprintln!("seed {seed}: {enumerated} components of k = 2 enumerated");
    // A fixed pair, so a component of k = 2 is enumerated on every run: three edges, to `u_0`
    // at `w = 2` and to `v_0` and `v_1` at `w = 1`.
    let a = vec![vec![true, false], vec![true, true]];
    let b = vec![vec![false, false], vec![true, true]];
    let (sys, xs) = product_gadget(&a, &b);
    let (names, hub) = enumerate(&sys).expect("every hub value passes");
    let lows: Vec<i64> = xs.iter().map(|&x| names[x].0).collect();
    // The product: row 0 is a[0][0] b[0][j] or a[0][1] b[1][j] = false or false: [0, 0]; row
    // 1 is a[1][1] b[1][j] = true: [1, 1]. A false entry has least value 1.
    assert_eq!(lows, [1, 1, 0, 0]);
    assert_eq!(hub, [1, 2]);
}

/// The component of study S4-hub-mixed's second family, `n` blocks of `m` hub values: the hub
/// `w` in `0..=n*m - 1`; `y` in `0..=m`; for each block `i` a name `p_i` in `0..=n*m` and the
/// parts `t + w <= i*m || p_i + w >= (i+1)*m` and `p_i <= 0 || y - w >= -i*m`, so that
/// `y >= w - i*m` holds exactly when `w` is in block `i` (`i*m <= w < (i+1)*m`); and for each
/// `j` in `1..m` a name `x_j` in `0..=1` with the part `y <= j - 1 || x_j >= 1`. With the hub
/// at `c` the least value of `x_j` is 1 exactly when `c mod m >= j`. Returns the component and
/// the indices of the `x_j`.
fn steep_lines(n: usize, m: usize) -> (System, Vec<usize>) {
    let (ni, mi) = (n as i64, m as i64);
    let y = 1;
    let xs: Vec<usize> = (2..m + 1).collect();
    let mut sys = System {
        names: [
            vec![IntervalSet::of(1, 1), IntervalSet::of(0, mi)],
            vec![IntervalSet::of(0, 1); m - 1],
        ]
        .concat(),
        hub: IntervalSet::of(0, ni * mi - 1),
        parts: vec![],
        uppers: vec![],
        lowers: vec![],
    };
    for (j, &x) in xs.iter().enumerate() {
        sys.parts.push((upper(y, 0, j as i64), lower(x, 0, 1)));
    }
    for i in 0..ni {
        let p = sys.names.len();
        sys.names.push(IntervalSet::of(0, ni * mi));
        sys.parts
            .push((upper(ONE, 1, i * mi), lower(p, -1, (i + 1) * mi)));
        sys.parts.push((upper(p, 0, 0), lower(y, 1, -i * mi)));
    }
    (sys, xs)
}

/// Study S4-hub-mixed: the least values at each hub value change Θ(N²) times in all as the
/// hub runs over its values, for N parts ([`steep_lines`], N = 2n + m - 1): `x_j` changes
/// 2n - 1 times (up at `c = i*m + j` for each block, down at each block's start but the
/// first), so (m - 1)(2n - 1) changes in all, 465 at n = m = 16 with 47 parts. So a method that
/// walks the hub values where the answer changes and updates the names that change does
/// Θ(N²) updates on this family. Checked here at n = m = 4, 8, 16 against the formula, each
/// value solved by [`threshold::solve`] with the hub fixed.
#[test]
fn the_answer_at_each_hub_value_changes_quadratically_often() {
    for s in [4usize, 8, 16] {
        let (sys, xs) = steep_lines(s, s);
        assert_eq!(threshold::solve(&sys), Answer::MixedHub, "n = m = {s}");
        let mut was: Option<Vec<i64>> = None;
        let mut changes = 0;
        for c in 0..(s * s) as i64 {
            let one = System {
                hub: IntervalSet::of(c, c),
                ..sys.clone()
            };
            let Some(Some((names, _))) = solved(&one) else {
                panic!("n = m = {s}: hub value {c} passes");
            };
            let lows: Vec<i64> = xs.iter().map(|&x| names[x].0).collect();
            let want: Vec<i64> = (1..s as i64)
                .map(|j| i64::from(c % s as i64 >= j))
                .collect();
            assert_eq!(lows, want, "n = m = {s}, hub value {c}");
            if let Some(w) = &was {
                changes += w.iter().zip(&lows).filter(|(a, b)| a != b).count();
            }
            was = Some(lows);
        }
        assert_eq!(sys.parts.len(), 3 * s - 1, "n = m = {s}");
        assert_eq!(changes, (s - 1) * (2 * s - 1), "n = m = {s}");
    }
}

fn fin(v: i64) -> End {
    End::Fin(Num::from(v))
}

/// The walk of `s4.rs` (Claude round 3): `v_i + w <= 0 || v_(i+1) - w >= 1` and `v0 - w >= 1`,
/// `v_i` in `0..=3`, `w` in `0..=1`. At `w = 0` the start gives `v0 >= 1`, which passes the
/// threshold of each part in turn: every `v_i` in `1..=3`; at `w = 1` every `v_i` is at least 2
/// and at most 3, so `w` keeps both values.
#[test]
fn the_walk_is_exact() {
    for n in [2, 5, 40] {
        let sys = System {
            names: vec![IntervalSet::of(0, 3); n],
            hub: IntervalSet::of(0, 1),
            parts: (0..n - 1)
                .map(|i| (upper(i, 1, 0), lower(i + 1, 1, 1)))
                .collect(),
            uppers: vec![],
            lowers: vec![lower(0, 1, 1)],
        };
        assert_eq!(
            threshold::solve(&sys),
            Answer::Bounds {
                names: vec![(fin(1), fin(3)); n],
                hub: IntervalSet::of(0, 1),
                filled: true,
            }
        );
    }
}

/// Unbounded names and hub: at a hub value past every integer the propagation compares terms
/// in the hub, so the answer is the limit there. `x - w >= 0` and `x + w <= 10 || y - w >= 5`
/// with `y <= 7`: the part fires when `x`, whose least value is `c`, reaches `11 - c`, so from
/// `c = 6`, and then asks `y >= 5 + c`, past 7. So the hub stops at 5, and `x` is unbounded.
#[test]
fn an_unbounded_hub_is_searched_by_doubling() {
    let sys = System {
        names: vec![IntervalSet::top(), IntervalSet::range(End::NegInf, fin(7))],
        hub: IntervalSet::top(),
        parts: vec![(upper(0, 1, 10), lower(1, 1, 5))],
        uppers: vec![],
        lowers: vec![lower(0, 1, 0)],
    };
    // The least value of x at hub value c is c. The part fires when x reaches 10 - c + 1, which
    // x = c does once c >= 6, and then asks y >= 5 + c >= 11, past 7. So c* = 5, and at a hub
    // far below every constant x is unbounded on both sides.
    assert_eq!(
        threshold::solve(&sys),
        Answer::Bounds {
            names: vec![(End::NegInf, End::PosInf), (End::NegInf, fin(7))],
            hub: IntervalSet::range(End::NegInf, fin(5)),
            filled: true,
        }
    );
    // With no bound on y every hub value passes.
    let free = System {
        names: vec![IntervalSet::top(), IntervalSet::top()],
        ..sys
    };
    assert_eq!(
        threshold::solve(&free),
        Answer::Bounds {
            names: vec![(End::NegInf, End::PosInf), (End::NegInf, End::PosInf)],
            hub: IntervalSet::top(),
            filled: true,
        }
    );
}

/// A hub bounded above only, with coefficients at most 0: the mirror of the last test.
#[test]
fn an_unbounded_hub_below_is_searched_by_doubling() {
    let sys = System {
        names: vec![IntervalSet::top(), IntervalSet::range(End::NegInf, fin(7))],
        hub: IntervalSet::range(End::NegInf, fin(100)),
        parts: vec![(upper(0, -1, 10), lower(1, -1, 5))],
        uppers: vec![],
        lowers: vec![lower(0, -1, 0)],
    };
    // The last test with w = -c: c >= -5, and up to 100; x + w >= 0 with w <= 100 gives x >= -100.
    assert_eq!(
        threshold::solve(&sys),
        Answer::Bounds {
            names: vec![(fin(-100), End::PosInf), (End::NegInf, fin(7))],
            hub: IntervalSet::of(-5, 100),
            filled: true,
        }
    );
}

/// `red.mjs`: the exact bounds of parts with two upper bounds answer reachability. Each name in
/// `0..=1`; each edge `a -> b` of a graph is `ha <= 0 || hb >= 1`, and each query "does `a`
/// reach `b`" a name `q` with `q <= 0 || ha >= 1` and `hb <= 0 || q <= 0`. Then `q`'s greatest
/// value is 0 exactly when `a` reaches `b`. The parts `hb <= 0 || q <= 0` are two upper bounds,
/// outside the threshold-implication shape, which is why that shape is refused there.
#[test]
fn the_greatest_value_of_a_query_name_is_reachability() {
    let seed = fresh("reachability by greatest values");
    let mut r = Rng(seed);
    let (mut total, mut zeros) = (0, 0);
    for _ in 0..3_000 {
        let n = 2 + r.below(5) as usize;
        let edges: Vec<(usize, usize)> = (0..r.below(2 * n as i64))
            .filter_map(|_| {
                let (a, b) = (r.below(n as i64) as usize, r.below(n as i64) as usize);
                (a < b).then_some((a, b))
            })
            .collect();
        let queries: Vec<(usize, usize)> = (0..1 + r.below(3))
            .map(|_| (r.below(n as i64) as usize, r.below(n as i64) as usize))
            .collect();
        let reached = queries_checked(n, &edges, &queries, &format!("seed {seed}"));
        total += reached.len();
        zeros += reached.iter().filter(|r| **r).count();
    }
    eprintln!("seed {seed}: {zeros} of {total} queries reached");
    // A query that reaches and one that does not are compared in every run, whatever the
    // draws gave (PROOF-test-count-thresholds; until 2026-11-15 the test asserted that both
    // occurred). Over the one edge `0 -> 1`: with `q` at 1 for the query `0 -> 1`, `x0` is 1,
    // so the edge sets `x1` to 1, and then `x1 <= 0 || q <= 0` fails, so `q`'s greatest value
    // is 0; for `1 -> 0`, `q = x1 = 1` and `x0 = 0` meet every test, so it is 1.
    assert_eq!(
        queries_checked(2, &[(0, 1)], &[(0, 1), (1, 0)], "built"),
        [true, false]
    );
}

/// Asserts that the greatest value of each query name of `queries` over the edges `edges` on
/// `n` names, by enumeration, is 0 exactly when the query's start reaches its end (`at` names
/// the case in a failure): for each query, whether it reaches.
fn queries_checked(
    n: usize,
    edges: &[(usize, usize)],
    queries: &[(usize, usize)],
    at: &str,
) -> Vec<bool> {
    let mut out = Vec::new();
    let v = n + queries.len();
    let mut best = vec![-1i64; queries.len()];
    for bits in 0u32..1 << v {
        let x = |i: usize| i64::from((bits >> i) & 1);
        let ok = edges.iter().all(|&(a, b)| x(a) <= 0 || x(b) >= 1)
            && queries.iter().enumerate().all(|(j, &(a, b))| {
                let q = x(n + j);
                (q <= 0 || x(a) >= 1) && (x(b) <= 0 || q <= 0)
            });
        if ok {
            for (j, b) in best.iter_mut().enumerate() {
                *b = (*b).max(x(n + j));
            }
        }
    }
    for (j, &(a, b)) in queries.iter().enumerate() {
        let mut seen = vec![false; n];
        zed_graph::reach(
            [a],
            |&t| !std::mem::replace(&mut seen[t], true),
            |&u| {
                (edges.iter())
                    .filter(move |&&(s, _)| s == u)
                    .map(|&(_, t)| t)
            },
        );
        out.push(seen[b]);
        assert_eq!(
            best[j] == 0,
            seen[b],
            "{at}, query {a} -> {b} over {edges:?}"
        );
    }
    out
}

/// The walk of [`the_walk_is_exact`] over `n` names with the hub in `0..=w`.
fn walk(n: usize, w: i64) -> System {
    System {
        names: vec![IntervalSet::of(0, 3 * w + 3); n],
        hub: IntervalSet::of(0, w),
        parts: (0..n - 1)
            .map(|i| (upper(i, 1, 0), lower(i + 1, 1, 1)))
            .collect(),
        uppers: vec![],
        lowers: vec![lower(0, 1, 1)],
    }
}

/// A walk whose last name is bounded above by `w + 1 - c`: the hub's values that pass are
/// `0..=w/2`, found by a search over the hub. Small widths against enumeration; wide ones,
/// the answer itself.
#[test]
fn a_wide_finite_hub_is_searched() {
    for (n, w) in [(2, 2), (3, 4), (3, 5)] {
        let mut sys = walk(n, w);
        sys.uppers.push(upper(n - 1, 1, w + 1));
        assert_eq!(solved(&sys), Some(enumerate(&sys)), "n = {n}, w = {w}");
    }
    for w in [100i64, 10i64.pow(16)] {
        let mut sys = walk(50, w);
        sys.uppers.push(upper(49, 1, w + 1));
        let mut names = vec![(fin(1), fin(3 * w + 3)); 49];
        names.push((fin(1), fin(w + 1)));
        assert_eq!(
            threshold::solve(&sys),
            Answer::Bounds {
                names,
                hub: IntervalSet::of(0, w / 2),
                filled: true,
            },
            "w = {w}"
        );
    }
}

mod bench;
