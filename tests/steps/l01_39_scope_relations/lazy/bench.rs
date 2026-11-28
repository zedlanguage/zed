//! Benchmarks of `lazy`: each times the work at a size and at 8 times it, run apart from the
//! correctness tests (`tools/run_tests.sh --bench`).

use super::*;

/// A constraint written after a kept test whose case fixes one of its names and leaves
/// another open is asked at the case's point (`Scope::written_dead`, `Scope::no_point_at`):
/// k groups of [`points_asked`], eager and lazy, at k and 8k, the answers checked at each size
/// as in `points_asked_after_a_disjunction_are_answered`. Moved here from the correctness
/// tests, whose piece it took past 20 s (TEST-vm-pieces-over-20s, 2026-11-22).
#[test]
fn points_asked_after_a_disjunction_scale() {
    let made = zed_tests::scaling::inputs(64, |k| (points_asked_scope(k), points_asked(k)));
    for lazy in [false, true] {
        let what = format!("constraints asked at kept points, lazy: {lazy}");
        zed_tests::scaling::check(&what, 64, |k| {
            let (s, ts) = &made[&k];
            std::hint::black_box(points_asked_settled(s, ts, k, lazy));
        });
    }
}

/// [`three_cases_at`] at r = 1,000·n for n and 8n, eager and lazy: the cases' classes 0 and 1
/// modulo 3 hold 2r + 2 values, joined as one set per class in the product
/// (LIMITS-classed-listing-per-set). Measured at r = 10^6 and 8·10^6, eager: instructions 1.54
/// times and bytes 7.3 times (about 200 instructions and 143 bytes per unit of r over a fixed
/// 2.6·10^9 instructions). By callgrind (DECIDE-perf-cover-site-split) the fixed part was
/// `exact::guarded::two_pins::u_runs` trying each value of a case's strip; read by the strip's
/// equation since PERF-cover-union-of-classes-listed (two_pins part), the same sizes take
/// 227,358,694 and 1,640,999,236 instructions (7.22 times; bytes 148,387,876 and 1,143,523,404,
/// local run, 2026-11-27): about 25·10^6 fixed and the same 200 a unit of r. A probe found the
/// 200 a unit in `row_sums::project`, over the one row `-y + 2x == 0`: the join listed one
/// interval per value (3,000,001 at r = 10^6) until it stopped at its work limit, then the
/// solver answered. Since the row_sums part (module `row_sums::equation`, the equation solved
/// whole) the same sizes take 21,723,425 and 21,791,243 instructions eager, ratio 1.003, and
/// 21,598,017 and 21,662,544 lazy, bytes 5,194,173 and 5,194,181 (local job, 2026-11-28; red
/// on 0eca50cf4 at 7.216 times), so both are held to `scaling::limit(0)`, 1.31 times. Negative
/// control: the same values listed one range a value (`Classed::met` of
/// `Product::classed`, the form the cases had below the old listing limit) are 8 times as many
/// ranges at 8n, over that limit.
#[test]
fn three_cases_of_two_classes_scale() {
    let listed = |r: i64| three_cases_at(r, false).classed().met().len() as u64;
    let (small, large) = (listed(1_000), listed(8_000));
    assert!(
        large as f64 / small as f64 >= zed_tests::scaling::limit(0),
        "control: {small} and {large} ranges listed"
    );
    for lazy in [false, true] {
        let what = format!("three cases of two classes past the old listing limit, lazy: {lazy}");
        zed_tests::scaling::check_order(&what, 1_000, 0, |n| {
            std::hint::black_box(three_cases_at(1_000 * n as i64, lazy));
        });
    }
}

/// The forced test [`forced_sides`] of `k` sides, each but the first split into a dead arm and
/// a live one, narrows a scope in O(k log k), eager and lazy: the arms' liveness comes from
/// the cases the narrowing makes anyway, and one more relation is taken, of the test without
/// the dead arms (the forced arm of `Scope::narrow_linear`, COMPLEXITY.md C42). The value is
/// checked at k = 1, 2 and 5 by
/// `a_forced_test_with_dead_arms_in_many_sides_settles_as_the_eager_scope`.
#[test]
fn a_forced_test_with_dead_arms_scales() {
    let p = Premises::new();
    for lazy in [false, true] {
        let start = || {
            let s = if lazy {
                bounded_hubs().lazy()
            } else {
                bounded_hubs()
            };
            eager_after(&s, &forced_start())
        };
        let built = zed_tests::scaling::inputs(64, |k| (start(), forced_sides(k, &[])));
        let what = format!("a forced test of k sides with a dead arm each, lazy {lazy}");
        zed_tests::scaling::check_order(&what, 64, 1, |k| {
            let (s, t) = &built[&k];
            std::hint::black_box(s.assume(t, false, &p));
        });
    }
}

/// The set-up of [`bound_leaves_scale_with_the_tests`] and [`bound_leaves_scale_with_the_leaves`]:
/// a hub `n` in [-1,000, 1,000] and `b` leaves `x_i`, each bound to the product of its own name
/// `y_i` (a term that reads `y_i`) and then a leaf of the star `x_i >= n + i mod 3`, eager or
/// lazy. Under option 1' of XR-lazy-and-kernel-batch-1 each `x_i` takes the eager steps in a lazy
/// scope too (`Placing::holds`: a leaf a bound term reads or binds).
fn bound_stars(b: usize, lazy: bool) -> (Scope, Vec<Arc<str>>) {
    stars(b, lazy, Bound::ToY)
}

/// How [`stars`] binds each `x_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Bound {
    /// Not bound: a leaf with no term, reader or kept test, lazy in a lazy scope.
    No,
    /// To the product of `y_i`, the term `y_i`.
    ToY,
    /// To the term `n + y_i`, which reads the hub: a projection of `x_i` is read back into
    /// `n` and `y_i` (`Scope::read_back_terms`), the feedback into the hub that `ToY` has
    /// not (XR-lazy-and-kernel-batch-1 round 2, Claude A-5).
    ToHubPlusY,
}

/// [`bound_stars`], with each `x_i` bound as `bound` says.
fn stars(b: usize, lazy: bool, bound: Bound) -> (Scope, Vec<Arc<str>>) {
    let p = Premises::new();
    let xs: Vec<Arc<str>> = (0..b).map(|i| Arc::from(format!("x{i}"))).collect();
    let ys: Vec<Arc<str>> = (0..b).map(|i| Arc::from(format!("y{i}"))).collect();
    let n: Arc<str> = "n".into();
    let all: Vec<Arc<str>> = std::iter::once(n)
        .chain(xs.iter().cloned())
        .chain(ys.iter().cloned())
        .collect();
    let start = ints(&all).assume(
        &and(
            prim(Prim::Ge, var("n"), int(-1_000)),
            prim(Prim::Le, var("n"), int(1_000)),
        ),
        true,
        &p,
    );
    let mut s = if lazy { start.lazy() } else { start };
    for (i, (x, y)) in xs.iter().zip(&ys).enumerate() {
        match bound {
            Bound::No => {}
            Bound::ToY => {
                let e = Shared::new(Term::Var(y.clone()));
                let py = if lazy { s.settled(y) } else { s.get(y) };
                s.bind(x, py, &e);
            }
            Bound::ToHubPlusY => {
                let e = Shared::new(prim(Prim::Add, var("n"), Term::Var(y.clone())));
                let px = if lazy { s.settled(x) } else { s.get(x) };
                s.bind(x, px, &e);
            }
        }
        s = s.assume(&diff_ge(x, "n", (i % 3) as i64), true, &p);
    }
    (s, xs)
}

/// The `k` tests `n >= 1` to `n >= k`, each a move of the hub of every star of [`bound_stars`].
fn hub_moves(s: &Scope, k: usize) -> Scope {
    let p = Premises::new();
    (1..=k as i64).fold(s.clone(), |s, j| {
        s.assume(&prim(Prim::Ge, var("n"), int(j)), true, &p)
    })
}

/// Each leaf as the scope holds it, settled when `lazy`, and checked: `x_i >= k + i mod 3`.
fn read_leaves(s: &Scope, xs: &[Arc<str>], k: usize, lazy: bool) {
    for (i, x) in xs.iter().enumerate() {
        let p = if lazy { s.settled(x) } else { s.get(x) };
        let lo = (k + i % 3) as i64;
        assert!(
            p.ints().contains(lo) && !p.ints().contains(lo - 1),
            "{x} is {:?}, not from {lo}",
            p.ints()
        );
    }
}

/// `what`, the reads of [`read_leaves`] on scopes from `make` at a size and 8 times it. An
/// eager read ([`Scope::get`]) allocates nothing, so its bytes are not compared
/// (`scaling::check_instructions_only_fresh`); a lazy read settles on a copy and is held to
/// its bytes too.
fn reads_scale(
    what: &str,
    n: usize,
    lazy: bool,
    make: impl Fn(usize) -> (Scope, Vec<Arc<str>>, usize) + Sync,
) {
    let run = |_: usize, (s, xs, k): (Scope, Vec<Arc<str>>, usize)| {
        read_leaves(&s, &xs, k, lazy);
        s
    };
    let make = |m: usize, _: usize| make(m);
    if lazy {
        zed_tests::scaling::check_order_fresh(what, n, 1, make, run);
    } else {
        zed_tests::scaling::check_instructions_only_fresh(what, n, 1, make, run);
    }
}

/// Option 1' costs the eager scope's work on the leaves that are not lazy: each hub move
/// projects the star of each bound leaf, Θ(k b) for `k` moves and `b` bound leaves, so Θ(k²)
/// when both grow (COMPLEXITY.md row PERF-lazy-eager-bound-leaves). Here `b` = 8 and `k` from
/// 16 to 128, the moves and the reads each measured alone, eager and lazy.
#[test]
fn bound_leaves_scale_with_the_tests() {
    for lazy in [false, true] {
        zed_tests::scaling::check_inputs(
            &format!("k hub moves over 8 bound stars, lazy: {lazy}"),
            16,
            |k| (bound_stars(8, lazy).0, k),
            |(s, k)| {
                std::hint::black_box(hub_moves(s, *k));
            },
        );
        reads_scale(
            &format!("reads of 8 bound leaves after k hub moves, lazy: {lazy}"),
            16,
            lazy,
            |k| {
                let (s, xs) = bound_stars(8, lazy);
                (hub_moves(&s, k), xs, k)
            },
        );
    }
}

/// As [`bound_leaves_scale_with_the_tests`], `k` = 8 and `b` from 8 to 64: the set-up of the
/// `b` bound stars, the moves and the reads, each measured alone.
#[test]
fn bound_leaves_scale_with_the_leaves() {
    for lazy in [false, true] {
        zed_tests::scaling::check(&format!("b bound stars set up, lazy: {lazy}"), 8, |b| {
            std::hint::black_box(bound_stars(b, lazy));
        });
        zed_tests::scaling::check_inputs(
            &format!("8 hub moves over b bound stars, lazy: {lazy}"),
            8,
            |b| bound_stars(b, lazy).0,
            |s| {
                std::hint::black_box(hub_moves(s, 8));
            },
        );
        reads_scale(
            &format!("reads of b bound leaves after 8 hub moves, lazy: {lazy}"),
            8,
            lazy,
            |b| {
                let (s, xs) = bound_stars(b, lazy);
                (hub_moves(&s, 8), xs, 8)
            },
        );
    }
}

/// The blocks made due by moves (`counts::moved_blocks`) in each phase of [`stars`]: the
/// set-up, the `k` hub moves and the reads of the leaves, for `b` leaves, eager and lazy, bound
/// each way, on a fresh thread so that no other test's moves are counted. Each phase's count is
/// split by the site that found the blocks (`counts::MOVED_AT`).
fn moved_by_phase(b: usize, k: usize, lazy: bool, bound: Bound) -> [[u64; 4]; 3] {
    zed_tests::scaling::on_a_thread(1 << 26, move || {
        let count = zedc::store::preimage::counts::moved_blocks_at;
        let less = |a: [u64; 4], b: [u64; 4]| std::array::from_fn(|i| a[i] - b[i]);
        let at = count();
        let (s, xs) = stars(b, lazy, bound);
        let set_up = count();
        let s = hub_moves(&s, k);
        let moved = count();
        read_leaves(&s, &xs, k, lazy);
        [less(set_up, at), less(moved, set_up), less(count(), moved)]
    })
}

/// The events of option 1' by phase (XR-lazy-and-kernel-batch-1: "count events by phase"),
/// printed for COMPLEXITY.md row PERF-lazy-eager-bound-leaves. A bound leaf costs the lazy
/// scope what it costs the eager one at the hub moves, and those grow with `k` and with `b`;
/// an unbound leaf costs the lazy scope less at the moves, the saving the lazy scope keeps
/// (the negative control). The sizes grow `k` alone, `b` alone and both (`k = b`); the family
/// bound to `n + y_i` adds the read-back into the hub.
#[test]
fn bound_leaves_moved_blocks_by_phase() {
    const SIZES: [(usize, usize); 5] = [(8, 16), (8, 128), (64, 8), (8, 8), (64, 64)];
    let mut seen = std::collections::BTreeMap::new();
    let sum = |c: [u64; 4]| c.iter().sum::<u64>();
    for (b, k) in SIZES {
        for lazy in [false, true] {
            for bound in [Bound::ToY, Bound::ToHubPlusY, Bound::No] {
                let c = moved_by_phase(b, k, lazy, bound);
                println!(
                    "bench blocks moved b={b} k={k} lazy={lazy} bound={bound:?}: {:?} by site {:?} \
                     ({:?}), moves per k*b {:.2}",
                    c.map(sum),
                    c,
                    zedc::store::preimage::counts::MOVED_AT,
                    sum(c[1]) as f64 / (k * b) as f64,
                );
                seen.insert((b, k, lazy, bound), c.map(sum));
            }
        }
    }
    for (b, k) in SIZES {
        for bound in [Bound::ToY, Bound::ToHubPlusY] {
            let (eager, lazy) = (seen[&(b, k, false, bound)], seen[&(b, k, true, bound)]);
            assert_eq!(
                eager[1], lazy[1],
                "{bound:?}, b={b} k={k}: moves eager and lazy"
            );
        }
        let (eager, lazy) = (
            seen[&(b, k, false, Bound::No)],
            seen[&(b, k, true, Bound::No)],
        );
        assert!(
            lazy[1] < eager[1],
            "unbound leaves, b={b} k={k}: the lazy moves {lazy:?} against {eager:?}"
        );
    }
    for bound in [Bound::ToY, Bound::ToHubPlusY] {
        let moves = |b, k| seen[&(b, k, true, bound)][1] as f64;
        assert!(
            moves(8, 128) / moves(8, 16) >= 4.0,
            "{bound:?}: the moves of bound leaves grow with k"
        );
        assert!(
            moves(64, 8) / moves(8, 16) >= 2.0,
            "{bound:?}: the moves of bound leaves grow with b"
        );
        // Θ(k·b) at k = b: 8 times k and b, 64 times the moves; at least 32 holds it above
        // linear in k alone.
        assert!(
            moves(64, 64) / moves(8, 8) >= 32.0,
            "{bound:?}: the moves of bound leaves at k = b grow as k²"
        );
    }
}

/// `k` moves of the satellite of [`satellite_stars`] beside `k` lazy stars of `k` distinct
/// classes (`xi >= n + m + i`), in the lazy scope, at k and 8k: each move reads the one leaf
/// the order holds, so the work is O(k log k) (XR-lazy-and-kernel-batch-1 round 3, Codex A4.2
/// and Gemini A-2). `Scope::due` listed every class at the hubs at each move before, Omega(k)
/// a move and Omega(k²) in all. The scopes are built first and only the moves are timed. At
/// 256 and 2048, since at 64 and 512 the class lists were a small part of the work: 9.49
/// times the instructions on 77dd97d2a, which had them, against 8.08 without. At 256 and 2048:
/// 13.26 on 77dd97d2a (red), 8.09 without (2026-11-27).
#[test]
fn a_moving_satellite_beside_lazy_leaves_of_distinct_classes_scales() {
    let built = zed_tests::scaling::inputs(256, |k| {
        let ([_, lazy], _) = satellite_stars(k, |i| i as i64);
        lazy
    });
    let what = "k moves of a satellite beside k lazy stars of distinct classes";
    zed_tests::scaling::check(what, 256, |k| {
        std::hint::black_box(satellite_moves(&built[&k], k));
    });
}
