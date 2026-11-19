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
    let values = |d: &IntervalSet| -> Vec<i64> {
        d.pieces()
            .flat_map(|(lo, hi)| lo.to_i64().expect("finite")..=hi.to_i64().expect("finite"))
            .collect()
    };
    let doms: Vec<Vec<i64>> = sys.names.iter().map(values).collect();
    let i = |v: &Int| Num::from(v).to_i64().expect("small");
    let n = doms.len();
    let mut out: Option<Passing> = None;
    let mut x = vec![0i64; n];
    fn rec(
        i: usize,
        c: i64,
        x: &mut Vec<i64>,
        doms: &[Vec<i64>],
        ok: &dyn Fn(&[i64], i64) -> bool,
        out: &mut Option<Passing>,
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
            }
            return;
        }
        for &v in &doms[i] {
            x[i] = v;
            rec(i + 1, c, x, doms, ok, out);
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
        rec(0, c, &mut x, &doms, &ok, &mut out);
    }
    out
}

/// The answer of [`threshold::solve`] in the form [`enumerate`] gives.
fn solved(sys: &System) -> Option<Option<Passing>> {
    let fin = |e: &End| e.to_i64().expect("finite");
    match threshold::solve(sys) {
        Answer::Empty => Some(None),
        Answer::MixedHub => None,
        Answer::Bounds { names, hub } => Some(Some((
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
fn component_checked(sys: &System, at: &str) -> Option<bool> {
    let got = solved(sys)?;
    let want = enumerate(sys);
    assert_eq!(got, want, "{at}: {sys:?}");
    Some(want.is_none())
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

/// A hub of three or more values with coefficients of both signs is left to plan row
/// S4-hub-mixed.
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
        let mut stack = vec![a];
        seen[a] = true;
        while let Some(u) = stack.pop() {
            for &(s, t) in edges {
                if s == u && !seen[t] {
                    seen[t] = true;
                    stack.push(t);
                }
            }
        }
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
            },
            "w = {w}"
        );
    }
}

mod bench;
