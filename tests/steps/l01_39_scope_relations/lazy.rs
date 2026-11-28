//! The lazy scope ([`Scope::lazy`]) against the eager one: under random sequences of tests,
//! joins and bindings on names related to two hubs, the lazy scope settles every name to
//! the product the eager scope holds, and is empty exactly when the eager one is. One run
//! relates each leaf to one hub at a time, within bounded names; the other relates leaves to
//! both hubs at once (`ai - n - m >= c`), with leaves unbounded, so that stars of two hubs
//! come and go, beside tests of a hub against the other and bounds on either side.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Prim, Shared, Term, Value};
use zed_tests::instances::Rng;
use zedc::store::cell::Premises;
use zedc::store::conjuncts::names as mentioned;
use zedc::store::interval::IntervalSet;
use zedc::store::product::{Product, Scope};

use super::ints;
use super::linked::stars_by_definition;
use super::nests::{and, boxed, diff_ge, int, names, or, prim, var};

const LEAVES: [&str; 5] = ["a0", "a1", "a2", "a3", "a4"];
const HUBS: [&str; 2] = ["n", "m"];

/// A random test of nesting `depth` at most: a spoke `ai - n >= c` or `n - ai >= c`, a bound
/// on a hub or on a leaf, or a disjunction or a conjunction of two tests.
fn test(rng: &mut Rng, depth: usize) -> Term {
    let (leaf, hub) = (rng.pick(&LEAVES), rng.pick(&HUBS));
    match rng.below(if depth == 0 { 4 } else { 6 }) {
        0 => diff_ge(leaf, hub, rng.int(-3, 3)),
        1 => diff_ge(hub, leaf, rng.int(-3, 3)),
        2 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(hub),
            int(rng.int(-15, 15)),
        ),
        3 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(leaf),
            int(rng.int(-15, 15)),
        ),
        4 => or(test(rng, depth - 1), test(rng, depth - 1)),
        _ => and(test(rng, depth - 1), test(rng, depth - 1)),
    }
}

/// `a - b - c >= k`, or with `sum` the other way round: `b + c - a >= k`.
fn sum3(a: &str, b: &str, c: &str, k: i64, sum: bool) -> Term {
    let (l, r) = (var(a), prim(Prim::Add, var(b), var(c)));
    let (l, r) = if sum { (r, l) } else { (l, r) };
    prim(Prim::Ge, prim(Prim::Sub, l, r), int(k))
}

/// A random test of nesting `depth` at most, most often of the shape of a star of two hubs:
/// `ai - n - m >= c` or `ai - n >= c`, a lower bound on a leaf or a bound on a hub; now and
/// then one that undoes such a star: `n + m - ai >= c` or an upper bound on a leaf; or a test
/// among the hubs, `n - m >= c` or `n + m >= c`, which a star of the two hubs is projected
/// with.
fn wide(rng: &mut Rng, depth: usize) -> Term {
    let (leaf, hub) = (rng.pick(&LEAVES), rng.pick(&HUBS));
    match rng.below(if depth == 0 { 12 } else { 14 }) {
        0..4 => sum3(leaf, "n", "m", rng.int(-3, 3), false),
        4 => sum3(leaf, "n", "m", rng.int(-3, 3), true),
        5 | 6 => diff_ge(leaf, hub, rng.int(-3, 3)),
        7 if rng.below(2) == 0 => diff_ge(hub, if hub == "n" { "m" } else { "n" }, rng.int(-3, 3)),
        7 => prim(
            Prim::Ge,
            prim(Prim::Add, var("n"), var("m")),
            int(rng.int(-3, 3)),
        ),
        8 => prim(Prim::Ge, var(leaf), int(rng.int(-15, 15))),
        9 => prim(Prim::Le, var(leaf), int(rng.int(-15, 15))),
        10 | 11 => prim(
            rng.pick(&[Prim::Ge, Prim::Le]),
            var(hub),
            int(rng.int(-15, 15)),
        ),
        12 => or(wide(rng, depth - 1), wide(rng, depth - 1)),
        _ => and(wide(rng, depth - 1), wide(rng, depth - 1)),
    }
}

/// Checks that `lazy` settles every name to what `eager` holds, and that the two are empty
/// together. Returns the number of names the lazy scope held unsettled.
fn same(eager: &Scope, lazy: &Scope, all: &[Arc<str>], trace: &[String]) -> usize {
    assert_eq!(eager.bottom, lazy.bottom, "{}", trace.join("\n"));
    if eager.bottom {
        return 0;
    }
    let mut stale = 0;
    for x in all {
        let settled = lazy.settled(x);
        assert_eq!(eager.get(x), settled, "{x} after\n{}", trace.join("\n"));
        stale += usize::from(lazy.held_product(x) != settled);
    }
    stale
}

/// Panics again with `panic`'s message and then `context`, which starts with the seed that
/// failed, unless the message holds `context`'s first line already (a failed comparison names
/// its seed and steps itself). A panic in the scope's own code (a `debug_assert`) names no
/// seed, and the seed [`Rng::fresh`] prints on standard error is not in a merge_check log:
/// b22-scale1's merge_check of wt/b22-scale1-b30d failed at "settling a leaf emptied a
/// scope" in the two-hubs `random_seeds` with no seed to repeat it (FAIL-lazy-hubs-seed
/// family, 2026-11-27).
fn rethrow(panic: Box<dyn std::any::Any + Send>, context: &str) -> ! {
    let text = (panic.downcast_ref::<String>().map(String::as_str))
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("a panic with no message");
    if text.contains(context.lines().next().unwrap_or(context)) {
        std::panic::resume_unwind(panic);
    }
    panic!("{text}\n{context}")
}

/// Runs `f`, the checks of one seed, so that a panic in it names `seed` ([`rethrow`]).
fn naming<T>(seed: u64, f: impl FnOnce() -> T) -> T {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
        .unwrap_or_else(|e| rethrow(e, &format!("seed {seed}")))
}

/// One random step of [`run`], taken on both scopes and written to `trace`: a test, a join of
/// the two outcomes of a test, or a binding. Returns what [`same`] returns after it.
fn step(
    rng: &mut Rng,
    eager: &mut Scope,
    lazy: &mut Scope,
    trace: &mut Vec<String>,
    all: &[Arc<str>],
    test: fn(&mut Rng, usize) -> Term,
    p: &Premises,
) -> usize {
    match rng.below(8) {
        0..6 => {
            let (t, outcome) = (test(rng, 2), rng.below(4) != 0);
            trace.push(format!("assume {t:?} is {outcome}"));
            *eager = eager.assume(&t, outcome, p);
            *lazy = lazy.assume(&t, outcome, p);
        }
        6 => {
            // The two outcomes of a test, each narrowed further, then joined.
            let (t, u, v) = (test(rng, 1), test(rng, 1), test(rng, 1));
            trace.push(format!("join {t:?} and {u:?} with not it and {v:?}"));
            let arms = |s: &Scope| {
                let yes = s.assume(&t, true, p).assume(&u, true, p);
                let no = s.assume(&t, false, p).assume(&v, true, p);
                yes.join(&no)
            };
            (*eager, *lazy) = (arms(eager), arms(lazy));
        }
        _ => {
            // A name bound again, to what another name holds: a hub rebound drops its
            // spokes.
            let (x, y) = (rng.pick(all), rng.pick(all));
            trace.push(format!("bind {x} to the product of {y}"));
            let e = Shared::new(Term::Var(y.clone()));
            let (pe, pl) = (eager.get(&y), lazy.settled(&y));
            eager.bind(&x, pe, &e);
            lazy.bind(&x, pl, &e);
        }
    }
    same(eager, lazy, all, trace)
}

/// Runs, for each seed of `seeds`, a random sequence of tests drawn by `test`, joins and
/// bindings from `start`, eagerly and lazily, and checks them the same after each step.
/// Returns the number of names the lazy scope held unsettled, the number of states with a
/// star of two hubs, and of those the number with a conjunct of the two hubs, and the number
/// with a satellite of the hubs of such a star ([`satellite_kept`]).
fn run(
    start: &Scope,
    seeds: impl IntoIterator<Item = u64>,
    test: fn(&mut Rng, usize) -> Term,
) -> (usize, usize, usize, usize) {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let (mut stale, mut two, mut related, mut kept) = (0, 0, 0, 0);
    for seed in seeds {
        let mut rng = Rng::new(seed);
        let (mut eager, mut lazy) = (start.clone(), start.clone().lazy());
        let mut trace = vec![format!("seed {seed}")];
        for _ in 0..12 {
            // A panic in the scope's own code (a `debug_assert`) names the seed and the steps
            // too, as a failed comparison does: the seed is otherwise printed only on standard
            // error, which a merge_check log does not keep (FAIL-lazy-hubs-seed family,
            // b22-scale1's merge_check of wt/b22-scale1-b30d).
            let step = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                step(&mut rng, &mut eager, &mut lazy, &mut trace, &all, test, &p)
            }));
            stale += step.unwrap_or_else(|e| rethrow(e, &trace.join("\n")));
            let multi = stars_by_definition(&lazy.relation).values().any(|gs| {
                gs.iter()
                    .flat_map(|g| mentioned(g))
                    .collect::<BTreeSet<_>>()
                    .len()
                    > 2
            });
            two += usize::from(multi);
            related += usize::from(
                multi
                    && lazy.relation.set().iter().any(|g| {
                        let ns = mentioned(g);
                        ns.len() == 2 && ns.iter().all(|n| &**n == "n" || &**n == "m")
                    }),
            );
            kept += usize::from(multi && satellite_kept(&lazy));
            if eager.bottom {
                break;
            }
        }
    }
    (stale, two, related, kept)
}

// The seed loops below ran 100 to 1,200 fixed seeds each, 16 to 42 s alone at load 30, split
// into tests of 20 to 100 seeds (TEST-lazy-split). Each is now one test of a few seeds new at
// each run ([`fresh_seeds`]), well under a second, which checks the lazy scope against the
// eager one and leaves out the counts of rare events, and one test of a fixed seed at which
// each event the loop counted occurs, so that the random runs are known to reach it
// (TEST-bench-move-l0139; seeds found 2026-11-14 over the first 30 to 200 seeds of each).

/// `count` seeds in a row from a new one each run, which [`Rng::fresh`] prints and `ZED_TEST_SEED`
/// repeats. Each check names the seed it failed at.
fn fresh_seeds(what: &str, count: u64) -> std::ops::Range<u64> {
    let (_, seed) = Rng::fresh(what);
    let first = seed.min(u64::MAX - count);
    first..first + count
}

/// Random seeds of [`test`]. Seed 19 left names unsettled before option 1' of
/// XR-lazy-and-kernel-batch-1; under 1' none of seeds 0 to 399 does (the drawn disjunctions keep
/// tests on nearly every leaf), so a lazy leaf is tested by hand in
/// [`a_leaf_with_no_term_reader_or_kept_test_stays_lazy_and_a_bound_one_does_not`].
mod a_lazy_scope_settles_each_name_to_the_eager_product {
    use super::*;

    fn start() -> Scope {
        boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20)
    }

    #[test]
    fn random_seeds() {
        run(
            &start(),
            fresh_seeds("lazy scope against the eager product", 10),
            test,
        );
    }

    #[test]
    fn seed_4014432025532948819() {
        // A fresh seed of `random_seeds` (FAIL-lazy-scope-random-seed, merge_check of
        // 2026-11-26): after its eleventh step, `n - a4 >= 2`, the two scopes disagreed on
        // whether the scope is empty. `run` panics on the first step the two differ at. Its
        // six steps that matter: `a_test_of_a_name_reads_its_term_after_a_reduction_narrowed_it`.
        run(&start(), [4014432025532948819], test);
    }

    #[test]
    fn seed_17799186487984213239() {
        // A fresh seed of `random_seeds` (FAIL-lazy-scope-seed-17799186487984213239): `a1` in
        // [0, 20] eager and [-20, 20] lazy. Its steps:
        // `a_name_a_bound_term_reads_is_settled_through_the_binding`.
        run(&start(), [17799186487984213239], test);
    }

    #[test]
    fn seed_17023501841456606916() {
        // A fresh seed of `random_seeds` (FAIL-lazy-scope-seed-17023501841456606908, run seed
        // 17023501841456606908): `a4` bound to `a0`, then `a4 >= n + 3`; eager `a0` in
        // [-16, 19], lazy settled [-15, 19], narrower by one more read-back round
        // (xr-requests/dry-affine2-lazy-seed-17023.md). `a0` and `a4` now take the eager steps
        // (option 1' of XR-lazy-and-kernel-batch-1).
        run(&start(), [17023501841456606916], test);
    }

    #[test]
    fn seeds_from_13729612544510092180() {
        // FAIL-lazy-scope-seed-13729612544510092180 (b30-check, a local suite run): "a1 after"
        // at `assume (a3 - n) >= 3`; whether the number is the run seed or the first of the
        // test's ten is not recorded, so all ten from it.
        run(&start(), 13729612544510092180..13729612544510092190, test);
    }

    #[test]
    fn seeds_from_2048554611750619743() {
        // FAIL-lazy-scope-seed-2048554611750619743 (b30-front2, a PEG merge_check; reproduced on
        // 50b2198dd and 06ed591d0): "settling a leaf emptied a scope", which does not name the
        // seed, so all ten of the run from it. Fixed by option 1' of XR-lazy-and-kernel-batch-1.
        run(&start(), 2048554611750619743..2048554611750619753, test);
    }

    #[test]
    fn seed_1863776162842511285() {
        // A fresh seed of `random_seeds` (run seed 1863776162842511281, merge_check of
        // wt/dry-affine2-eqslack2 on origin/main d420c701d): `m` settled apart, lazy.rs "m after".
        run(&start(), [1863776162842511285], test);
    }

    #[test]
    fn seed_12181213027077511184() {
        // A fresh seed of `random_seeds` (FAIL-lazy-scope-seed-12181213027077511176, run seed
        // 12181213027077511176, filed by b31-kernel): a name settled apart on origin/main
        // 0bf095dab.
        run(&start(), [12181213027077511184], test);
    }

    #[test]
    fn seed_2090299356942025264() {
        // A fresh seed of `random_seeds` (FAIL-lazy-scope-seed-2090299356942025264, the merge
        // check of dry-affine2-hullc on 6ec21561f, 2026-11-27): `a1` differs after the join on
        // `a1 >= -11` of its eleventh step, `a0` bound to `a1`'s product at the first.
        run(&start(), [2090299356942025264], test);
    }

    #[test]
    fn seeds_from_10397413280677257963() {
        // FAIL-lazy-eager-seed-10397413280677257963 (pith-rows' merge_check; failing on
        // 90c9c60c4 too): lazy.rs:93, a name settled apart from the eager product, at run seed
        // 10397413280677257963. Which of the run's ten failed is not recorded, so all ten.
        run(&start(), 10397413280677257963..10397413280677257973, test);
    }

    #[test]
    fn seeds_from_3912401004097402564() {
        // The second run seed of FAIL-lazy-eager-seed-10397413280677257963, the same assert.
        run(&start(), 3912401004097402564..3912401004097402574, test);
    }

    #[test]
    fn seeds_from_1974326044368952918() {
        // A run seed of `random_seeds` (dry-coll; FAIL-lazy-satellites-wider-interval, dry-hash):
        // "n after", eager [-6, 11], lazy [-7, 11], red on origin/main ac8c4cfda and green on
        // part A of XR-lazy-and-kernel-batch-1. Which of the run's ten failed is not recorded,
        // so all ten.
        run(&start(), 1974326044368952918..1974326044368952928, test);
    }

    #[test]
    fn seeds_from_8119798284051346689_and_12120025628507516352() {
        // FAIL-lazy-scope-seed-8119798284051346689 and FAIL-lazy-scope-seed-12120025628507516352:
        // run seeds of `random_seeds` red on origin/main per their filers and green on part A
        // a262708d4 of XR-lazy-and-kernel-batch-1 (local job s811, 2026-11-28). Which of each
        // run's ten failed is not recorded, so all ten of each.
        for first in [8119798284051346689, 12120025628507516352] {
            run(&start(), first..first + 10, test);
        }
    }

    #[test]
    fn seeds_1539050261199919524_and_15005546321011322977() {
        // Case seeds of `random_seeds`: FAIL-lazy-scope-seed-1539050261199919519 (b30-check's
        // merge_check, run seed 1539050261199919519: lazy.rs:93, lazy -11..19 against eager
        // -11..20) and FAIL-lazy-scope-seed-15005546321011322968 (b30-pres4's merge_check, run
        // seed 15005546321011322968: "a1 after", lazy -20..11 against eager -20..8).
        run(&start(), [1539050261199919524, 15005546321011322977], test);
    }

    #[test]
    fn seed_2533336388240946713_and_run_seed_5899313110846177143() {
        // FAIL-lazy-scope-seed-2533336388240946706 (b30-pres28's merge_check, case seed
        // 2533336388240946713: "n after", lazy -20..5 against eager -20..8), and run seed
        // 5899313110846177143 of b31-tools (case seed not recorded, so all ten: "a1 after",
        // eager -20..-13 against lazy -17..-13). Red on origin/main f79759f83 and e2e01f05f
        // (b30-pres29's job lz2, b31-tools' repro), green on part A aa28da140 (local job s1).
        let first = 5899313110846177143;
        run(&start(), [2533336388240946713], test);
        run(&start(), first..first + 10, test);
    }

    #[test]
    fn seeds_13676171914239005553_and_15784569534319398251() {
        // Case seeds of `random_seeds`: FAIL-lazy-scope-seed-13676171914239005552 (b31-kernel's
        // merge_check: "m after", lazy -20..0 against eager -20..-1) and
        // FAIL-lazy-scope-seed-15784569534319398245 (b30-front2's merge_check: "a0 after", lazy
        // -19..-10 against eager -17..-10). Both red on origin/main f79759f83, green on part A
        // (local jobs m2 and l5, 2026-11-28).
        run(&start(), [13676171914239005553, 15784569534319398251], test);
    }
}

/// A satellite `n <= s <= m - 1` of the hubs of `b` stars `xi >= n + m + (i mod 3)`, all lazy
/// but `x0`, bound to the term `y`, so that the lazy scope's order holds it alone; `s` then
/// moves `k` times (`s >= j`), each a move of a satellite that changes every star at the hubs
/// ([`Conjuncts::around`]). The lazy scope reads only the leaf its order holds at each move
/// (`counts::around_reads`, `k` for `k` moves at every `b`), not the `b` leaves of the class
/// (XR round 2, Codex A4: Ω(k·b) before), and every name settles to the eager product, `xi`
/// from `k + 1 + (i mod 3)`. Mutation control: with `Scope::due` reading `around` and dropping
/// the lazy leaves, as before, the reads are `k·b` and the test is red.
///
/// [`Conjuncts::around`]: zedc_presburger::conjuncts::Conjuncts::around
#[test]
fn a_moving_satellite_beside_lazy_leaves_reads_no_lazy_leaf() {
    satellite_reads(|i| (i % 3) as i64);
}

/// [`a_moving_satellite_beside_lazy_leaves_reads_no_lazy_leaf`] with the offsets `i`, so that
/// the `b` stars are `b` classes, one family at the two hubs (XR-lazy-and-kernel-batch-1
/// round 3, Codex A4.2): the leaves read and the settled products are as with three classes.
/// `Scope::due` listed every class at the hubs at each move, Omega(k·b) class visits, which
/// `counts::around_reads` does not count; the benchmark
/// `bench::a_moving_satellite_beside_lazy_leaves_of_distinct_classes_scales` times it.
#[test]
fn a_moving_satellite_beside_lazy_leaves_of_distinct_classes_reads_no_lazy_leaf() {
    satellite_reads(|i| i as i64);
}

/// The scopes, eager and lazy, of `b` stars `xi >= n + m + offset(i)` beside a satellite
/// `n <= s <= m - 1` of their hubs, `n` and `m` in [0, 100000] (room for the benchmark's 2048
/// moves of `s`), with `x0` bound to the term `y` so that the lazy scope's order holds it
/// alone; and their names.
fn satellite_stars(b: usize, offset: fn(usize) -> i64) -> ([Scope; 2], Vec<Arc<str>>) {
    let p = Premises::new();
    let xs: Vec<String> = (0..b).map(|i| format!("x{i}")).collect();
    let mut ns = vec!["n", "m", "s", "y"];
    ns.extend(xs.iter().map(String::as_str));
    let all = names(&ns);
    let start = ints(&all).assume(
        &and(
            and(
                prim(Prim::Ge, var("n"), int(0)),
                prim(Prim::Le, var("n"), int(100_000)),
            ),
            and(
                prim(Prim::Ge, var("m"), int(0)),
                prim(Prim::Le, var("m"), int(100_000)),
            ),
        ),
        true,
        &p,
    );
    let mut scopes = [start.clone(), start.lazy()];
    for (lazy, s) in scopes.iter_mut().enumerate() {
        let (x0, y): (Arc<str>, Arc<str>) = ("x0".into(), "y".into());
        let py = if lazy == 1 { s.settled(&y) } else { s.get(&y) };
        s.bind(&x0, py, &Shared::new(var("y")));
        *s = s.assume(&diff_ge("s", "n", 0), true, &p);
        *s = s.assume(&diff_ge("m", "s", 1), true, &p);
        for (i, x) in xs.iter().enumerate() {
            *s = s.assume(&sum3(x, "n", "m", offset(i), false), true, &p);
        }
    }
    (scopes, all)
}

/// `s` of [`satellite_stars`] moved `k` times, `s >= j` for `j` in 1..=k.
fn satellite_moves(s: &Scope, k: usize) -> Scope {
    let p = Premises::new();
    (1..=k as i64).fold(s.clone(), |s, j| {
        s.assume(&prim(Prim::Ge, var("s"), int(j)), true, &p)
    })
}

/// The checks of [`a_moving_satellite_beside_lazy_leaves_reads_no_lazy_leaf`], at the offsets
/// `offset`.
fn satellite_reads(offset: fn(usize) -> i64) {
    let k = 6;
    let mut read = Vec::new();
    for b in [4usize, 32] {
        let ([eager, lazy], all) = satellite_stars(b, offset);
        let xs = &all[4..];
        assert!(
            lazy.relation.class_of("x1").is_some(),
            "x1 is no leaf of a star of two hubs"
        );
        assert!(
            !lazy.relation.around("s").is_empty(),
            "s is no satellite of the stars' hubs"
        );
        let eager = satellite_moves(&eager, k);
        let before = zedc::store::preimage::counts::around_reads();
        let lazy = satellite_moves(&lazy, k);
        let reads = zedc::store::preimage::counts::around_reads() - before;
        // The satellite and the hubs its moves move, each read once a move at most.
        assert!(
            reads <= 3 * k as u64,
            "b = {b}: {reads} leaves read at {k} moves of the satellite, past the one placed"
        );
        read.push(reads);
        for x in all.iter() {
            assert_eq!(eager.get(x), lazy.settled(x), "{x} at b = {b}");
        }
        for (i, x) in xs.iter().enumerate() {
            let lo = k as i64 + 1 + offset(i);
            let px = eager.get(x);
            let got = px.ints();
            assert!(
                got.contains(lo) && !got.contains(lo - 1),
                "{x} is {got:?}, not from {lo}"
            );
        }
    }
    assert_eq!(
        read[0], read[1],
        "the leaves read grew with the lazy leaves"
    );
}

/// Option 1' by hand (XR-lazy-and-kernel-batch-1, META1 Request 1): a leaf with no binding to a
/// term, no reader (`read_by`), no kept test that names it and no join that reads it stays lazy,
/// its star `a0 >= n` not projected at the hub move `n >= 5`, and settles to the eager [5, inf)
/// when read. Negative control: the same steps after `a0` is bound to `a1`'s product (a term),
/// where `a0` takes the eager steps and the scope holds it settled with no read.
#[test]
fn a_leaf_with_no_term_reader_or_kept_test_stays_lazy_and_a_bound_one_does_not() {
    let p = Premises::new();
    let (a0, a1): (Arc<str>, Arc<str>) = ("a0".into(), "a1".into());
    let star = || diff_ge("a0", "n", 0);
    let hub = || prim(Prim::Ge, var("n"), int(5));
    let moves = |s: Scope| s.assume(&star(), true, &p).assume(&hub(), true, &p);
    let from_5 = |x: &Product| x.ints().contains(5) && !x.ints().contains(4);

    let free = moves(bounded_hubs().lazy());
    assert_ne!(
        free.held_product(&a0),
        free.settled(&a0),
        "the unbound leaf a0 was not lazy"
    );
    assert!(
        from_5(&free.settled(&a0)),
        "a0 settled to {:?}",
        free.settled(&a0).ints()
    );

    let mut bound = bounded_hubs().lazy();
    let pa1 = bound.settled(&a1);
    bound.bind(&a0, pa1, &Shared::new(Term::Var(a1.clone())));
    let bound = moves(bound);
    assert_eq!(
        bound.held_product(&a0),
        bound.settled(&a0),
        "the bound leaf a0 was lazy"
    );
    assert!(
        from_5(&bound.held_product(&a0)),
        "a0 is {:?}",
        bound.held_product(&a0).ints()
    );

    // Both against the eager scope, name by name, at each step.
    let steps = [Step::Assume(star(), true), Step::Assume(hub(), true)];
    assert!(replay(&bounded_hubs(), &steps) > 0, "no name was unsettled");
    let [s1, s2] = steps;
    replay(&bounded_hubs(), &[Step::Bind("a0", "a1"), s1, s2]);
}

/// Every name unbounded but the two hubs, each within [-20, 20].
fn bounded_hubs() -> Scope {
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let hubs = HUBS
        .iter()
        .map(|h| {
            and(
                prim(Prim::Ge, var(h), int(-20)),
                prim(Prim::Le, var(h), int(20)),
            )
        })
        .reduce(and)
        .expect("two hubs");
    ints(&all).assume(&hubs, true, &Premises::new())
}

/// Random seeds of [`wide`]; seed 10 leaves names unsettled and holds a star of two hubs, and
/// one beside a conjunct of the two (all three in 13 of seeds 0 to 119).
mod a_lazy_scope_with_stars_of_two_hubs_settles_each_name_to_the_eager_product {
    use super::*;

    #[test]
    fn random_seeds() {
        let seeds = fresh_seeds("lazy scope with stars of two hubs", 8);
        run(&bounded_hubs(), seeds, wide);
    }

    #[test]
    fn seed_3066150143192435835() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-3066150143192435835): `a0` in
        // [-11, inf) eager and [-18, inf) lazy. Its steps:
        // `a_name_a_bound_term_reads_is_settled_through_the_binding`.
        run(&bounded_hubs(), [3066150143192435835], wide);
    }

    #[test]
    fn seed_8994332253420488859() {
        // A second case of FAIL-lazy-hubs-seed-3066150143192435835 (b30-check, run seed
        // 8994332253420488853): `a3` bound to `a0`'s product; `a0` in [-6, inf) eager and
        // [-9, inf) lazy.
        run(&bounded_hubs(), [8994332253420488859], wide);
    }

    #[test]
    fn seed_5574242637160979656() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-5574242637160979656, run seed
        // 5574242637160979655): `a0` bound to `a3`, then the negated atom `!(a3 - m >= -3)`,
        // a conjunct `m - a3 >= 4` and no kept test, then stars on `a0`; eager `m` in [5, 20],
        // lazy settled [3, 20]. Settling `a0` read it back into `a3`, and that conjunct moved
        // `m`, a path outside `a0`'s star; `a0` now takes the eager steps, as a leaf a bound
        // term reads (option 1' of XR-lazy-and-kernel-batch-1; XR round 2, Codex A3).
        run(&bounded_hubs(), [5574242637160979656], wide);
    }

    #[test]
    fn seed_892430831927573369() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-892430831927573367, run seed
        // 892430831927573367 in merge_check of wt/xr-hole-2 762bc2898). On b74db57be the two
        // scopes settled `a0` apart; with the read-back through bindings they settled the hub
        // `m` apart, [-18, 4] eager and [-18, 9] lazy.
        run(&bounded_hubs(), [892430831927573369], wide);
    }

    #[test]
    fn seed_17568303369781510396() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-17568303369781510396, run seed
        // 17568303369781510395, found by dry-hash). At the last join the eager scope is empty
        // and the lazy one was not: with `n` bound to `m` and `a0` to `a3`, the arm
        // `a0 - m >= -3`, `n + m - a3 >= -2` needs `m >= -5` against `m <= -10`, which the
        // lazy scope found only on settling `a0`.
        run(&bounded_hubs(), [17568303369781510396], wide);
    }

    #[test]
    fn seed_1119513696159792176() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-1119513696159792176, merge_check
        // of wt/dry-affine2-farmdoc on fffd2df52): `n` bound to `a4`, then `n - m >= 2` and
        // `m >= 15`; eager `a4` in [17, inf), lazy [-18, inf).
        run(&bounded_hubs(), [1119513696159792176], wide);
    }

    #[test]
    fn seed_4827059857829881458() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-4827059857829881458, run seed
        // 4827059857829881452, filed by dry-coll): on origin/main 52fe142bd eager `m` in
        // [7, inf), lazy settled [5, inf), the form of seed 5574242637160979656.
        run(&bounded_hubs(), [4827059857829881458], wide);
    }

    #[test]
    fn seed_16087263621314180760() {
        // A fresh seed of `random_seeds` (FAIL-lazy-stars-seed-16087263621314180758, run seed
        // 16087263621314180758, filed by b31-kernel): on origin/main 0bf095dab one scope is
        // empty and the other is not (lazy.rs, the `bottom` check of `same`).
        run(&bounded_hubs(), [16087263621314180760], wide);
    }

    #[test]
    fn seed_6783121585670467195() {
        // A fresh seed of `random_seeds` (FAIL-lazy-hubs-seed-6783121585670467191, run seed
        // 6783121585670467195, merge_check of wt/dry-coll-ma): `a3` bound to `a0`'s product;
        // `a0` in (-inf, 19] eager and (-inf, -8] lazy.
        run(&bounded_hubs(), [6783121585670467195], wide);
    }

    #[test]
    fn seeds_where_settling_a_leaf_emptied_the_scope() {
        // FAIL-lazy-hubs-seed-10000730: on 06ed591d0 each of these run seeds stopped at the
        // `debug_assert` of `Scope::settle_blocks` ("settling a leaf emptied a scope"): a lazy
        // read narrowed the lazy scope to empty where the eager one is not empty (found by a
        // search of about 40,000 seeds; b22-scale1's merge_check of wt/b22-scale1-b30d saw it
        // with no seed printed).
        for seed in [10000730, 13000547, 13001335, 15000329] {
            run(&bounded_hubs(), [seed], wide);
        }
    }

    #[test]
    fn seeds_29000547_and_30000100() {
        // FAIL-lazy-hubs-seed-29000547 and FAIL-lazy-hubs-seed-30000100 (the f07 search on
        // 06ed591d0; still failing on option 1', d2cc775a4): `a4` in (-inf, -3] eager and
        // (-inf, -1] lazy, and `a3` in (-inf, -4] eager and (-inf, 22] lazy. Their steps that
        // matter: `a_forced_conjunction_keeps_what_its_cases_prune_for_a_lazy_star`.
        for seed in [29000547, 30000100] {
            run(&bounded_hubs(), [seed], wide);
        }
    }

    #[test]
    fn seeds_13220432411721724916_and_17() {
        // Two seeds of `random_seeds` at which lazy differs from eager on origin/main
        // 454af9f18 (run seeds 13220432411721724913 and 17, 2026-11-28): `a2` settled lazily
        // is not the eager `a2` at the first, `a3` at the second. Both are equal on round 3's
        // part A of XR-lazy-and-kernel-batch-1, which these tests keep so.
        for seed in [13220432411721724916, 17] {
            run(&bounded_hubs(), [seed], wide);
        }
    }

    /// Seed 2 did this until a projection onto a name of a disjunction's arm kept the arms'
    /// rows (PRECISION-forget-disjunction-arms); its leaves are settled at once since. Seed 10
    /// holds all three before and after that change (with it, 13 of seeds 0 to 119).
    #[test]
    fn seed_10_holds_a_star_of_two_related_hubs() {
        let (stale, two, related, _) = run(&bounded_hubs(), [10], wide);
        assert!(stale > 0, "the lazy scope settled every name at once");
        assert!(two > 0, "no state held a star of two hubs");
        assert!(related > 0, "no state held a star of two related hubs");
    }
}

/// A step of [`replay`]: a test and its outcome, or `x` bound to the product of `y`.
enum Step {
    Assume(Term, bool),
    Bind(&'static str, &'static str),
}

/// Runs `steps` from `start`, eagerly and lazily, and checks after each that the lazy scope
/// settles every name to what the eager one holds ([`same`]). Returns the number of names
/// the lazy scope held unsettled over all steps.
fn replay(start: &Scope, steps: &[Step]) -> usize {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let name = |x: &str| all.iter().find(|n| &***n == x).expect("a name").clone();
    let (mut eager, mut lazy) = (start.clone(), start.clone().lazy());
    let mut trace = Vec::new();
    let mut stale = 0;
    for step in steps {
        match step {
            Step::Assume(t, outcome) => {
                trace.push(format!("assume {t:?} is {outcome}"));
                eager = eager.assume(t, *outcome, &p);
                lazy = lazy.assume(t, *outcome, &p);
            }
            Step::Bind(x, y) => {
                trace.push(format!("bind {x} to the product of {y}"));
                let (x, y) = (name(x), name(y));
                let e = Shared::new(Term::Var(y.clone()));
                let (pe, pl) = (eager.get(&y), lazy.settled(&y));
                eager.bind(&x, pe, &e);
                lazy.bind(&x, pl, &e);
            }
        }
        stale += same(&eager, &lazy, &all, &trace);
    }
    stale
}

#[test]
fn a_name_a_bound_term_reads_is_settled_through_the_binding() {
    // A name `y` that a bound name `x`'s term reads (`x` bound to the product of `y`, its term
    // `y`), where a test then relates `x` to the hubs: the eager scope projects `x`'s star,
    // and the projection narrows `x`, whose term the eager scope reads back into `y`
    // (`Scope::read_back_terms`). The lazy scope leaves `x`'s star stale, and settling `y`
    // settled only `y`'s own stars, so `y` kept the wider bound: `Scope::settled` must settle
    // the stale stars of the bindings whose term reads `y` too, and settling must read back
    // what it narrowed. Leaving out the binding, the disjunction or the last test makes the
    // two scopes agree before the fix. Seed 3066150143192435835 of [`wide`]: `a0` in
    // [-11, inf) eager and [-18, inf) lazy (FAIL-lazy-hubs-seed-3066150143192435835).
    let nm = || prim(Prim::Add, var("n"), var("m"));
    let ge = |x: Term, y: Term, c: i64| prim(Prim::Ge, prim(Prim::Sub, x, y), int(c));
    let steps = [
        Step::Assume(ge(var("a2"), var("m"), 0), true),
        Step::Assume(ge(var("a2"), nm(), 2), true),
        Step::Bind("a1", "a0"),
        Step::Assume(prim(Prim::Ge, var("m"), int(4)), true),
        Step::Assume(
            or(ge(var("a1"), nm(), -2), ge(var("a1"), var("m"), 1)),
            true,
        ),
        Step::Assume(ge(var("a1"), var("n"), -3), true),
        Step::Assume(prim(Prim::Le, var("m"), int(10)), false),
    ];
    let stale = replay(&bounded_hubs(), &steps);
    assert!(stale > 0, "the lazy scope settled every name at once");
    // Seed 17799186487984213239 of [`test`], in boxed names: `a0` bound to the product of
    // `a1`, then `a0 - n >= -1` and `n - a4 >= -2`; `a1` in [0, 20] eager and [-20, 20] lazy
    // (FAIL-lazy-scope-seed-17799186487984213239).
    let steps = [
        Step::Assume(
            and(
                diff_ge("a3", "m", 2),
                and(prim(Prim::Ge, var("m"), int(12)), diff_ge("a0", "n", 1)),
            ),
            true,
        ),
        Step::Assume(prim(Prim::Ge, var("a4"), int(3)), true),
        Step::Assume(
            and(
                diff_ge("a0", "m", 2),
                or(prim(Prim::Le, var("n"), int(11)), diff_ge("n", "a0", 0)),
            ),
            true,
        ),
        Step::Assume(prim(Prim::Ge, var("m"), int(12)), true),
        Step::Assume(
            or(
                diff_ge("n", "a3", 0),
                or(
                    prim(Prim::Le, var("a0"), int(0)),
                    prim(Prim::Ge, var("m"), int(-9)),
                ),
            ),
            true,
        ),
        Step::Bind("a0", "a1"),
        Step::Assume(diff_ge("a0", "n", -1), true),
        Step::Assume(diff_ge("n", "a4", -2), true),
    ];
    replay(
        &boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20),
        &steps,
    );
}

#[test]
fn a_test_between_the_hubs_of_a_star_settles_them_as_the_eager_scope_does() {
    // Seed 1109 of the run above, past its default seeds: a disjunction of tests on `m + n`
    // and a star `ai >= n + m - c` over both hubs, then `n >= m`. The eager scope gave n
    // int[1..=20] and the lazy one int[0..=20]: the disjunction was a part of the star's block
    // and of the hubs' block under one key, so each block found the other's snapshot there and
    // projected it again, with `n >= m` in the eager scope, which projects the star at once.
    // Each block now keys its parts apart (item NARROW-lazy-settle). `run` panics on the first
    // name the two scopes settle apart.
    let (_, two, _, _) = run(&bounded_hubs(), 1109..1110, wide);
    assert!(two > 0, "seed 1109 no longer makes a star of two hubs");
}

#[test]
fn seed_3011_a_new_star_settles_its_leaf_as_the_eager_scope_does() {
    // Seed 3011 of `wide`, past its default seeds: `m + n >= -2` holds (`m <= 8` rules out the
    // other side of a disjunction), then `a0 >= n + m - 2`, then `a0 >= n + m + 1`. The eager
    // scope kept `a0 >= -4` from the first where the lazy scope, settling `a0`, found
    // `a0 >= -1`, on main before item NARROW-lazy-settle too; with the parts of a star's block
    // keyed apart from the hubs' block, the two agree.
    let (_, two, _, _) = run(&bounded_hubs(), 3011..3012, wide);
    assert!(two > 0, "seed 3011 no longer makes a star of two hubs");
}

#[test]
fn wide_seed_13834_settles_a_hub_bounded_through_a_bound_leaf() {
    // Seed 13834 of `wide` (FAIL-lazy-wide-seed-13834): `m >= 3`, then `a1` bound to the product
    // of `m` (so `a1` is in [3, 20] in its own product only), then `a1 - n - m >= 2` and
    // `n >= 0`, so that `m <= 18`. The eager scope gave m in [3, 18], the lazy `settled(m)`
    // [3, 20]: `a1` is a leaf of the star at the hub `m` whose upper bound came by the binding,
    // not by a conjunct. `run` panics on the first name the two scopes settle apart.
    _ = run(&bounded_hubs(), [13834], wide);
}

/// Gemini's finding A.1 of XR-lazy-and-kernel-batch-1 round 2, the steps of seeds 29000547 and
/// 30000100 of [`wide`] that matter: a test the value forces to a conjunction, one of whose
/// sides is a disjunction that the narrowing of its cases prunes to one arm. The eager scope
/// projects the star of an unbound leaf in each case, so it keeps the bound the surviving arm
/// gives; the lazy scope leaves the star stale and settles it later against the relation the
/// narrowing left, which must hold the pruned arm, not the whole disjunction.
#[test]
fn a_forced_conjunction_keeps_what_its_cases_prune_for_a_lazy_star() {
    let nm = || prim(Prim::Add, var("n"), var("m"));
    // Seed 29000547: `n <= -9`, `m` bound to `a2 <= 9`, the star `a4 <= n + m - 3`, then
    // `(n + m >= 3 && n + m >= 1) || a0 <= -3` false, so `n + m <= 0`: the arm `n + m <= 2`
    // of `n + m <= 0 || n + m <= 2` dies against `n + a2 <= 0` within the case. Eager `a4` is
    // (-inf, -3]; lazy, from `n + m <= 2`, (-inf, -1].
    let steps = [
        Step::Assume(prim(Prim::Le, var("n"), int(-9)), true),
        Step::Bind("m", "a2"),
        Step::Assume(prim(Prim::Le, var("a2"), int(9)), true),
        Step::Assume(sum3("a4", "n", "m", 3, true), true),
        Step::Assume(
            or(
                and(prim(Prim::Ge, nm(), int(3)), prim(Prim::Ge, nm(), int(1))),
                prim(Prim::Le, var("a0"), int(-3)),
            ),
            false,
        ),
    ];
    let a4: Arc<str> = "a4".into();
    let eager = {
        let p = Premises::new();
        let mut s = bounded_hubs();
        for step in &steps {
            match step {
                Step::Assume(t, o) => s = s.assume(t, *o, &p),
                Step::Bind(x, y) => {
                    let (x, y): (Arc<str>, Arc<str>) = ((*x).into(), (*y).into());
                    let py = s.get(&y);
                    s.bind(&x, py, &Shared::new(Term::Var(y)));
                }
            }
        }
        s
    };
    let held = eager.get(&a4);
    assert!(
        held.ints().contains(-3) && !held.ints().contains(-2),
        "the eager scope no longer bounds a4 by -3, so the test checks nothing: {:?}",
        held.ints()
    );
    replay(&bounded_hubs(), &steps);
    // Seed 30000100: the star `a3 <= n + m - 2`, `m >= -6`, `a4` bound to `n`, then
    // `(a4 - n >= -3 && n + m >= -1) || a4 - n - m >= 2` false: with `a4 = n` the arm `a4 - n
    // <= -4` of `a4 - n <= -4 || n + m <= -2` dies, so `n + m <= -2` and eager `a3` is
    // (-inf, -4]; lazy, from the boxes `n <= 4` and `m <= 20`, (-inf, 22].
    let steps = [
        Step::Assume(sum3("a3", "n", "m", -1, false), false),
        Step::Assume(prim(Prim::Le, var("m"), int(-7)), false),
        Step::Bind("a4", "n"),
        Step::Assume(
            or(
                and(diff_ge("a4", "n", -3), prim(Prim::Ge, nm(), int(-1))),
                sum3("a4", "n", "m", 2, false),
            ),
            false,
        ),
    ];
    replay(&bounded_hubs(), &steps);
}

/// The steps of seed 29000547 in
/// [`a_forced_conjunction_keeps_what_its_cases_prune_for_a_lazy_star`] before its forced
/// test: `n <= -9`, `m` bound to `a2 <= 9`, the star `a4 <= n + m - 3`.
fn forced_start() -> [Step; 4] {
    [
        Step::Assume(prim(Prim::Le, var("n"), int(-9)), true),
        Step::Bind("m", "a2"),
        Step::Assume(prim(Prim::Le, var("a2"), int(9)), true),
        Step::Assume(sum3("a4", "n", "m", 3, true), true),
    ]
}

/// The forced test of seed 29000547 with `k - 1` more sides and `extra`, to be assumed false:
/// `(n + m >= 3 && n + m >= 1) || (n <= 10 && n + m >= 2) || ... || (n <= 8 + k && n + m >=
/// k) || extra... || a0 <= -3`. False, side i >= 1 splits into the arms `n >= 10 + i`, dead
/// as `n <= -9`, and `n + m <= i`, live and implied by the `n + m <= 0` of side 0; so the eager
/// scope keeps `a4 <= -3` at every k, and the lazy scope does only from the relation of the
/// test with each side's dead arm left out (the forced arm of `Scope::narrow_linear`,
/// COMPLEXITY.md C42).
fn forced_sides(k: usize, extra: &[Term]) -> Term {
    let nm = || prim(Prim::Add, var("n"), var("m"));
    let sides = (1..k as i64).map(|i| {
        and(
            prim(Prim::Le, var("n"), int(9 + i)),
            prim(Prim::Ge, nm(), int(1 + i)),
        )
    });
    let first = and(prim(Prim::Ge, nm(), int(3)), prim(Prim::Ge, nm(), int(1)));
    std::iter::once(first)
        .chain(sides)
        .chain(extra.iter().cloned())
        .chain([prim(Prim::Le, var("a0"), int(-3))])
        .reduce(or)
        .expect("one side at least")
}

/// [`forced_sides`] at k = 1, 2 and 5 settles each name as the eager scope does, `a4` to
/// `(-inf, -3]` (the assert of the benchmark `a_forced_test_with_dead_arms_scales`). Corners:
/// a side both of whose arms are live (`n <= -13 || m <= -13`, kept whole, beside sides that
/// are pruned; eager `a4` stays `(-inf, -3]`), and a side both of whose arms are dead
/// (`n >= 51 || n <= -31`), which makes the scope bottom, eager and lazy.
#[test]
fn a_forced_test_with_dead_arms_in_many_sides_settles_as_the_eager_scope() {
    let a4: Arc<str> = "a4".into();
    let both_live = and(
        prim(Prim::Ge, var("n"), int(-12)),
        prim(Prim::Ge, var("m"), int(-12)),
    );
    // On `n` alone, in [-20, -9]: `m`, bound to the product of `a2`, has no box of its own.
    let both_dead = and(
        prim(Prim::Le, var("n"), int(50)),
        prim(Prim::Ge, var("n"), int(-30)),
    );
    for k in [1, 2, 5] {
        for (extra, bottom) in [(vec![], false), (vec![both_live.clone()], false)] {
            let mut steps = Vec::from(forced_start());
            steps.push(Step::Assume(forced_sides(k, &extra), false));
            let eager = eager_after(&bounded_hubs(), &steps);
            assert_eq!(eager.bottom, bottom, "k {k}");
            // With the side `n <= -13 || m <= -13` too the cases give `n + m <= -4`, but the
            // eager scope still keeps `a4 <= -3` (measured), so -3 is pinned for both.
            let held = eager.get(&a4);
            assert!(
                held.ints().contains(-3) && !held.ints().contains(-2),
                "k {k}, {} extra: the eager scope no longer bounds a4 by -3: {:?}",
                extra.len(),
                held.ints()
            );
            replay(&bounded_hubs(), &steps);
        }
        let mut steps = Vec::from(forced_start());
        steps.push(Step::Assume(
            forced_sides(k, std::slice::from_ref(&both_dead)),
            false,
        ));
        assert!(eager_after(&bounded_hubs(), &steps).bottom, "k {k}");
        replay(&bounded_hubs(), &steps);
    }
}

/// `n` in [0, 20], `m` in [-10, 10], every leaf unbounded.
fn hubs_for_a_product() -> Scope {
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let hubs = [("n", 0, 20), ("m", -10, 10)]
        .into_iter()
        .map(|(h, lo, hi)| {
            and(
                prim(Prim::Ge, var(h), int(lo)),
                prim(Prim::Le, var(h), int(hi)),
            )
        })
        .reduce(and)
        .expect("two hubs");
    ints(&all).assume(&hubs, true, &Premises::new())
}

/// Gemini's case of XR-lazy-and-kernel-batch-1 round 2 (A3): `a1` bound to the leaf `a0` of
/// the star `a0 >= n`, the hub moves to `n >= 1`, then `a1 * m >= 0`, which has no relation.
/// The finding said the eager scope reads `a1 >= 1` and narrows `m` to [0, 10], so that a
/// lazy scope reading `a0` stale would differ. It does not reproduce: the binding holds `a0`'s
/// product at the bind, [0, inf), and the eager steps do not carry `a0`'s later move into
/// `a1`, so the eager scope keeps `m` in [-10, 10] too (on d2cc775a4 and after the fixes of
/// round 3). The test is an equality check of the case, not a red test of option 1'; the
/// first assertion pins the eager result, so that an eager scope that comes to narrow `m`
/// here makes this a red test again and its text is checked.
#[test]
fn a_product_test_on_a_name_bound_to_a_leaf_reads_the_leaf_after_its_hub_moved() {
    let steps = [
        Step::Assume(diff_ge("a0", "n", 0), true),
        Step::Bind("a1", "a0"),
        Step::Assume(prim(Prim::Ge, var("n"), int(1)), true),
        Step::Assume(
            prim(Prim::Ge, prim(Prim::Mul, var("a1"), var("m")), int(0)),
            true,
        ),
    ];
    let eager = eager_after(&hubs_for_a_product(), &steps);
    assert_eq!(
        eager.get("m").ints(),
        &IntervalSet::of(-10, 10),
        "the eager scope now narrows m: the case can tell a stale `a0` apart; update the text"
    );
    replay(&hubs_for_a_product(), &steps);
}

/// Codex's case of XR-lazy-and-kernel-batch-1 round 2 (A3): the leaf `a0` of the star
/// `a0 >= n` read only through two bindings, `a1` bound to `a0` and `a2` to `a1`; the hub moves
/// to `n >= 1`, then `a2 * m >= 0`, a test of `a2` alone. As in
/// [`a_product_test_on_a_name_bound_to_a_leaf_reads_the_leaf_after_its_hub_moved`], the eager
/// scope does not carry `a0`'s move into `a1` or `a2` and keeps `m` in [-10, 10], so the case
/// does not tell a stale `a0` apart: an equality check, with the eager result pinned. The
/// closure itself, that a test of `a2` settles `a0` through the two terms, is checked by the
/// test of the same name in zedc-preimage `product.rs`, which reads [`Scope::test_closure`].
#[test]
fn a_leaf_read_only_through_two_bindings_is_in_the_test_closure() {
    let steps = [
        Step::Assume(diff_ge("a0", "n", 0), true),
        Step::Bind("a1", "a0"),
        Step::Bind("a2", "a1"),
        Step::Assume(prim(Prim::Ge, var("n"), int(1)), true),
        Step::Assume(
            prim(Prim::Ge, prim(Prim::Mul, var("a2"), var("m")), int(0)),
            true,
        ),
    ];
    let eager = eager_after(&hubs_for_a_product(), &steps);
    assert_eq!(
        eager.get("m").ints(),
        &IntervalSet::of(-10, 10),
        "the eager scope now narrows m: the case can tell a stale `a0` apart; update the text"
    );
    replay(&hubs_for_a_product(), &steps);
}

/// Codex's finding A1 of XR-lazy-and-kernel-batch-1 round 2: a join of an eager scope and a lazy
/// one is lazy, and took the eager side's bindings and `read_by`, where a binding made eagerly
/// records no names its term reads. So the leaf `a0` that `a1 = a0` reads was lazy after the
/// join, though both sides bind `a1` to it, and the steps of
/// [`a_product_test_on_a_name_bound_to_a_leaf_reads_the_leaf_after_its_hub_moved`] read it
/// stale. Each order of the two sides is checked against the eager scope; with the lazy side
/// on the left the metadata was right already (the control).
#[test]
fn a_join_of_an_eager_and_a_lazy_scope_keeps_a_leaf_a_binding_reads_eager() {
    let p = Premises::new();
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let (a0, a1): (Arc<str>, Arc<str>) = ("a0".into(), "a1".into());
    let prep = |s: Scope| {
        let mut s = s.assume(&diff_ge("a0", "n", 0), true, &p);
        let pa0 = s.settled(&a0);
        s.bind(&a1, pa0, &Shared::new(Term::Var(a0.clone())));
        s
    };
    let tail = |s: Scope| {
        s.assume(&prim(Prim::Ge, var("n"), int(1)), true, &p)
            .assume(
                &prim(Prim::Ge, prim(Prim::Mul, var("a1"), var("m")), int(0)),
                true,
                &p,
            )
    };
    let eager = tail(prep(hubs_for_a_product()));
    let (e, l) = (
        prep(hubs_for_a_product()),
        prep(hubs_for_a_product().lazy()),
    );
    for (order, joined) in [("eager left", e.join(&l)), ("lazy left", l.join(&e))] {
        let joined = tail(joined);
        assert_eq!(eager.bottom, joined.bottom, "{order}");
        for x in &all {
            assert_eq!(eager.get(x), joined.settled(x), "{order}: {x}");
        }
    }
}

/// Gemini's finding A.2 of XR-lazy-and-kernel-batch-1 round 2: [`Scope::bind_summarized`] meets
/// the bound product with the summary's values over its inputs' products, which a lazy scope
/// held stale. `a0` is the lazy leaf of `a0 >= n` after the move `n >= 5`; `y` bound to the
/// summary of `a0 + 1` lies in [6, inf) in the eager scope, and lay in all the integers in the
/// lazy one, read from `a0`'s stale product.
#[test]
fn a_summarized_binding_reads_its_inputs_settled() {
    use zedc::store::preimage::{Domains, Lets, let_summary};
    let p = Premises::new();
    let (a0, a1, y): (Arc<str>, Arc<str>, Arc<str>) = ("a0".into(), "a1".into(), "y".into());
    let prep = |s: Scope| {
        s.assume(&diff_ge("a0", "n", 0), true, &p).assume(
            &prim(Prim::Ge, var("n"), int(5)),
            true,
            &p,
        )
    };
    let (mut eager, mut lazy) = (prep(bounded_hubs()), prep(bounded_hubs().lazy()));
    assert_ne!(lazy.held_product(&a0), lazy.settled(&a0), "a0 is not lazy");
    let sum = prim(Prim::Add, var("a0"), int(1));
    let doms: Domains = [(a0.clone(), IntervalSet::top())].into_iter().collect();
    let s = let_summary(&sum, &doms, Lets::new()).expect("a summary of a0 + 1");
    let e = Shared::new(sum);
    let top = eager.get(&a1);
    eager.bind_summarized(&y, top.clone(), &e, &s, &doms);
    lazy.bind_summarized(&y, top, &e, &s, &doms);
    let held = eager.get(&y);
    assert!(
        held.ints().contains(6) && !held.ints().contains(5),
        "the eager scope no longer bounds y from 6, so the test checks nothing: {:?}",
        held.ints()
    );
    assert_eq!(held, lazy.settled(&y));
}

/// Codex's finding A3.1 of XR-lazy-and-kernel-batch-1 round 3: [`forward`] reads products as
/// held, and read the stale product of a lazy leaf. `a0` is the lazy leaf of `a0 >= n` after
/// the move `n >= 5`, as in [`a_summarized_binding_reads_its_inputs_settled`]; its forward
/// value is [5, inf) eager, and is so lazy, with the caller's scope still lazy after. The
/// arms of `let y = a0 in if y <= 4 then 1 else 0` ([`arms`]) are reached as in the eager
/// scope: the first is not.
///
/// [`forward`]: zedc::store::product::forward
/// [`arms`]: zedc::store::product::arms
#[test]
fn forwarding_a_variable_of_a_lazy_scope_reads_its_settled_product() {
    use zedc::store::product::{arms, forward};
    let p = Premises::new();
    let a0: Arc<str> = "a0".into();
    let prep = |s: Scope| {
        s.assume(&diff_ge("a0", "n", 0), true, &p).assume(
            &prim(Prim::Ge, var("n"), int(5)),
            true,
            &p,
        )
    };
    let (mut eager, mut lazy) = (prep(bounded_hubs()), prep(bounded_hubs().lazy()));
    assert_ne!(lazy.held_product(&a0), lazy.settled(&a0), "a0 is not lazy");
    let e = var("a0");
    let held = forward(&e, &mut eager);
    assert!(
        held.ints().contains(5) && !held.ints().contains(4),
        "the eager scope no longer bounds a0 from 5, so the test checks nothing: {:?}",
        held.ints()
    );
    assert_eq!(forward(&e, &mut lazy), held, "forward of a0");
    assert_ne!(
        lazy.held_product(&a0),
        lazy.settled(&a0),
        "forward settled the caller's scope"
    );
    let t = Term::Let(
        "y".into(),
        Shared::new(var("a0")),
        Shared::new(Term::If(
            Shared::new(prim(Prim::Le, var("y"), int(4))),
            Shared::new(int(1)),
            Shared::new(int(0)),
        )),
    );
    let reached = |s: &Scope| {
        arms(&t, s)
            .iter()
            .map(|a| a.reachable())
            .collect::<Vec<_>>()
    };
    assert_eq!(reached(&eager), [false, true], "the eager arms");
    assert_eq!(
        reached(&lazy),
        reached(&eager),
        "the arms of the lazy scope"
    );
}

/// [`Scope::statics`] and [`Scope::contains`] read products as held, and read the stale
/// product of a lazy leaf (the author's rule of 2026-11-28: lazy and eager give the same
/// result in every case). `a0` is a leaf of `a0 >= n` with `a0 <= 5`, then the move `n >= 5`
/// makes it `[5, 5]` eagerly, a static value, while the lazy scope holds it stale. Both
/// scopes must give `a0 = 5` as a static, refuse the state `a0 = 4` and hold `a0 = 5`; the
/// caller's lazy scope stays lazy. Corner cases: a state naming `n` too (the relation is
/// checked), and the eager scope, read as held.
#[test]
fn statics_and_contains_of_a_lazy_scope_read_its_settled_products() {
    use std::collections::BTreeMap;
    let p = Premises::new();
    let a0: Arc<str> = "a0".into();
    let prep = |s: Scope| {
        [
            diff_ge("a0", "n", 0),
            prim(Prim::Le, var("a0"), int(5)),
            prim(Prim::Ge, var("n"), int(5)),
        ]
        .iter()
        .fold(s, |s, t| s.assume(t, true, &p))
    };
    let (eager, lazy) = (prep(bounded_hubs()), prep(bounded_hubs().lazy()));
    assert_ne!(lazy.held_product(&a0), lazy.settled(&a0), "a0 is not lazy");
    assert_eq!(eager.get(&a0).ints().to_string(), "[5..=5]", "eager a0");
    let statics = eager.statics();
    assert_eq!(statics.get(&a0), Some(&Value::Int(5)), "eager statics");
    assert_eq!(lazy.statics(), statics, "lazy statics");
    let state = |vs: &[(&str, i64)]| -> BTreeMap<Arc<str>, Value> {
        vs.iter()
            .map(|(n, v)| (Arc::from(*n), Value::Int(*v)))
            .collect()
    };
    for env in [
        state(&[("a0", 4)]),
        state(&[("a0", 5)]),
        state(&[("a0", 4), ("n", 5)]),
        state(&[("a0", 5), ("n", 5)]),
    ] {
        assert_eq!(lazy.contains(&env), eager.contains(&env), "{env:?}");
    }
    assert!(!eager.contains(&state(&[("a0", 4)])), "eager holds a0 = 4");
    assert!(eager.contains(&state(&[("a0", 5)])), "eager refuses a0 = 5");
    assert_ne!(
        lazy.held_product(&a0),
        lazy.settled(&a0),
        "a read settled the caller's scope"
    );
}

/// The scope of [`statics_and_contains_of_a_lazy_scope_read_its_settled_products`], eager
/// and lazy: `a0 >= n`, `a0 <= 5`, then the move `n >= 5`, so that `a0` is `[5, 5]` eagerly
/// and a stale leaf of `n` lazily.
fn stale_a0() -> (Scope, Scope) {
    let p = Premises::new();
    let prep = |s: Scope| {
        [
            diff_ge("a0", "n", 0),
            prim(Prim::Le, var("a0"), int(5)),
            prim(Prim::Ge, var("n"), int(5)),
        ]
        .iter()
        .fold(s, |s, t| s.assume(t, true, &p))
    };
    (prep(bounded_hubs()), prep(bounded_hubs().lazy()))
}

/// The lines [`Scope`]'s `Display` gives under `name`: its product.
fn shown(s: &Scope, name: &str) -> String {
    let (mut out, mut on) = (String::new(), false);
    for line in s.to_string().lines() {
        if !line.starts_with(char::is_whitespace) {
            on = line == format!("{name}:");
        } else if on {
            out.push_str(line);
            out.push('\n');
        }
    }
    out
}

/// The public reads of a product of a lazy scope, [`Scope::get`] and `Display`, give what
/// the eager scope gives, and leave the held product as it was (XR-lazy-and-kernel-batch-1
/// round 4, Codex A4.1 and Claude A4.1; the author's rule of 2026-11-28: lazy and eager give
/// the same result in every case). `a0` of [`stale_a0`] is `[5, 5]` eagerly and held stale
/// lazily. Negative control: the held product (`Scope::held_product`) differs from the eager
/// one before and after the reads.
#[test]
fn a_public_product_read_agrees_with_eager_without_mutating_storage() {
    let (eager, lazy) = stale_a0();
    let a0: Arc<str> = "a0".into();
    let held = lazy.held_product(&a0);
    assert_ne!(
        held,
        eager.get(&a0),
        "a0 is not stale, so the test checks nothing"
    );
    assert_eq!(lazy.get(&a0), eager.get(&a0), "get");
    assert_eq!(shown(&lazy, "a0"), shown(&eager, "a0"), "Display");
    assert_eq!(
        lazy.held_product(&a0),
        held,
        "a read settled the scope it read"
    );
}

/// [`Scope::eager_on`] of a term that reads no stale leaf leaves every read of the scope as
/// the eager scope gives it (XR-lazy-and-kernel-batch-1 round 4, Codex A4.2): it made the
/// scope eager without settling `a0` of [`stale_a0`], so that `statics` and `get` read the
/// stale product as held. Corner cases: a constant (no name read), and the arms of `if n <=
/// 100 then 1 else 0`, which reads the hub `n` but not its leaf `a0` ([`arms`] walks a copy
/// made eager on the term), the live arm's `a0`. Control: the statics agree before.
///
/// [`arms`]: zedc::store::product::arms
#[test]
fn eager_on_of_a_constant_preserves_unrelated_observations() {
    use zedc::store::product::arms;
    let (eager, mut lazy) = stale_a0();
    let a0: Arc<str> = "a0".into();
    assert_ne!(lazy.held_product(&a0), eager.get(&a0), "a0 is not stale");
    assert_eq!(lazy.statics(), eager.statics(), "statics before eager_on");
    let t = Term::If(
        Shared::new(prim(Prim::Le, var("n"), int(100))),
        Shared::new(int(1)),
        Shared::new(int(0)),
    );
    let live_a0 = |s: &Scope| {
        let arms = arms(&t, s);
        assert!(
            arms[0].reachable() && !arms[1].reachable(),
            "the arms of {s}"
        );
        arms[0].scope.get(&a0)
    };
    assert_eq!(live_a0(&lazy), live_a0(&eager), "a0 in the live arm");
    lazy.eager_on(&int(0));
    assert_eq!(lazy.statics(), eager.statics(), "statics after eager_on");
    assert_eq!(lazy.get(&a0), eager.get(&a0), "get after eager_on");
    assert_eq!(lazy.settled(&a0), eager.get(&a0), "settled after eager_on");
}

/// The scope of Gemini's witnesses A3 of XR-lazy-and-kernel-batch-1 round 3: `n`, `m` and `w`
/// in [0, 20], `x` and `t` unbounded, and `y` too when `shadow`, so that the binding of `y`
/// below takes the path of a name the scope has.
fn witness_scope(shadow: bool) -> Scope {
    let mut ns = vec!["n", "m", "w", "x", "t"];
    if shadow {
        ns.push("y");
    }
    let box20 = ["n", "m", "w"]
        .iter()
        .map(|h| {
            and(
                prim(Prim::Ge, var(h), int(0)),
                prim(Prim::Le, var(h), int(20)),
            )
        })
        .reduce(and)
        .expect("three names");
    ints(&names(&ns)).assume(&box20, true, &Premises::new())
}

/// `x >= n`, then `y` bound to `x + w` with no bound of its own (the product of `t`), then
/// `y <= m`: Gemini's witness A3 before the moves of the hubs.
fn witness_bound(s: Scope) -> Scope {
    let p = Premises::new();
    let mut s = s.assume(&diff_ge("x", "n", 0), true, &p);
    let (y, t): (Arc<str>, Arc<str>) = ("y".into(), "t".into());
    let top = s.get(&t);
    s.bind(&y, top, &Shared::new(prim(Prim::Add, var("x"), var("w"))));
    s.assume(&diff_ge("m", "y", 0), true, &p)
}

/// The moves of the hubs of Gemini's witness A3: `n >= 10`, then `m <= 15`.
fn witness_moves(s: Scope) -> Scope {
    let p = Premises::new();
    s.assume(&prim(Prim::Ge, var("n"), int(10)), true, &p)
        .assume(&prim(Prim::Le, var("m"), int(15)), true, &p)
}

/// `w` of a witness scope, settled, and the check that the eager one is [0, 5]: `y = x + w <=
/// m <= 15` with `x >= n >= 10`.
fn witness_w(eager: &Scope, lazy: &Scope, what: &str) {
    let w: Arc<str> = "w".into();
    let held = eager.get(&w);
    assert_eq!(held.ints().to_string(), "[0..=5]", "{what}: the eager w");
    assert_eq!(lazy.settled(&w), held, "{what}: w");
}

/// Gemini's witness A3 (1) and (2) of XR-lazy-and-kernel-batch-1 round 3, against the claim
/// that the `read_by` clause of `Placing::holds` and the two calls of `Scope::promote` in
/// `Scope::bind` are equivalent mutants: the leaf `x` of `x >= n` is read by the term of `y`,
/// bound to `x + w`, and `y <= m`; after `n >= 10` and `m <= 15` the eager scope reads `y`
/// back to `w` in [0, 5]. A lazy `x` would be read back stale, `[0, inf)`, and `w` left in
/// [0, 15]. Once on a fresh `y` (the first call of `promote`) and once on a `y` the scope has
/// (the second).
#[test]
fn a_leaf_a_bound_term_reads_is_read_back_settled() {
    for shadow in [false, true] {
        let what = if shadow {
            "a y the scope has"
        } else {
            "a fresh y"
        };
        let s = witness_scope(shadow);
        let eager = witness_moves(witness_bound(s.clone()));
        let lazy = witness_moves(witness_bound(s.lazy()));
        witness_w(&eager, &lazy, what);
    }
}

/// Gemini's witness A3 (4) of XR-lazy-and-kernel-batch-1 round 3, against the claim that the
/// step of `Scope::join` that makes an eager side lazy is an equivalent mutant: the scope of
/// [`a_leaf_a_bound_term_reads_is_read_back_settled`], eager, joined with the same steps taken
/// lazily, either way round, before the moves of the hubs. The eager side's binding records
/// no names its term reads; without the step the join reads `x` lazily, and `w` is left in
/// [0, 15].
#[test]
fn a_leaf_a_bound_term_reads_on_the_eager_side_of_a_join_is_read_back_settled() {
    let s = witness_scope(false);
    let (e, l) = (witness_bound(s.clone()), witness_bound(s.lazy()));
    let eager = witness_moves(e.join(&e));
    witness_w(&eager, &witness_moves(e.join(&l)), "eager joined with lazy");
    witness_w(&eager, &witness_moves(l.join(&e)), "lazy joined with eager");
}

/// Gemini's witness A3 (3) of XR-lazy-and-kernel-batch-1 round 3, against the claim that the
/// call of `Scope::promote` in `Scope::join_kept` is an equivalent mutant: with `n` and `m`
/// in [0, 20], `x >= n` and `x >= 0`, the test `m * m == 0 || (x <= 5 && m >= 10)` is kept,
/// its cases joined with `x` in [0, inf) as before, and it fires when `x` passes 5: after
/// `n >= 6` the eager `m` is [0, 0]. A lazy `x` would take no eager step at the move, the
/// trigger would not fire, and `m` would be `{0} ∪ [10, 20]`.
#[test]
fn a_leaf_a_kept_test_names_fires_it_at_a_move_of_its_hub() {
    let p = Premises::new();
    let start = ints(&names(&["n", "m", "x"])).assume(
        &and(
            and(
                prim(Prim::Ge, var("n"), int(0)),
                prim(Prim::Le, var("n"), int(20)),
            ),
            and(
                prim(Prim::Ge, var("m"), int(0)),
                prim(Prim::Le, var("m"), int(20)),
            ),
        ),
        true,
        &p,
    );
    let kept = or(
        prim(Prim::Eq, prim(Prim::Mul, var("m"), var("m")), int(0)),
        and(
            prim(Prim::Le, var("x"), int(5)),
            prim(Prim::Ge, var("m"), int(10)),
        ),
    );
    let steps = [
        diff_ge("x", "n", 0),
        prim(Prim::Ge, var("x"), int(0)),
        kept,
        prim(Prim::Ge, var("n"), int(6)),
    ];
    let run = |s: Scope| steps.iter().fold(s, |s, t| s.assume(t, true, &p));
    let (eager, lazy) = (run(start.clone()), run(start.lazy()));
    let m: Arc<str> = "m".into();
    assert_eq!(eager.get(&m).ints().to_string(), "[0..=0]", "the eager m");
    assert_eq!(lazy.settled(&m), eager.get(&m), "m");
}

/// Codex's case A3.2 of XR-lazy-and-kernel-batch-1 round 3, for the call of `Scope::promote`
/// in `Scope::join_kept`: a lazy star `a >= n + m` with `a >= 0`, `n` and `m` in [-20, 20],
/// then the kept test `(a == 0 && y * y == 0) || (a >= 1 && y >= 10)`, whose join of the
/// cases leaves `a` in [0, inf) as before; then `n + m >= 1`, a move of the hubs that takes
/// `a` past 0 without naming it, so the first case is dead and `y` is in [10, inf) eagerly.
#[test]
fn a_kept_test_on_a_lazy_star_fires_at_a_move_of_its_hubs() {
    let p = Premises::new();
    let start = ints(&names(&["n", "m", "a", "y"])).assume(
        &and(
            and(
                prim(Prim::Ge, var("n"), int(-20)),
                prim(Prim::Le, var("n"), int(20)),
            ),
            and(
                prim(Prim::Ge, var("m"), int(-20)),
                prim(Prim::Le, var("m"), int(20)),
            ),
        ),
        true,
        &p,
    );
    let kept = or(
        and(
            prim(Prim::Eq, var("a"), int(0)),
            prim(Prim::Eq, prim(Prim::Mul, var("y"), var("y")), int(0)),
        ),
        and(
            prim(Prim::Ge, var("a"), int(1)),
            prim(Prim::Ge, var("y"), int(10)),
        ),
    );
    let steps = [
        sum3("a", "n", "m", 0, false),
        prim(Prim::Ge, var("a"), int(0)),
        kept,
        prim(Prim::Ge, prim(Prim::Add, var("n"), var("m")), int(1)),
    ];
    let run = |s: Scope| steps.iter().fold(s, |s, t| s.assume(t, true, &p));
    let (eager, lazy) = (run(start.clone()), run(start.lazy()));
    let y: Arc<str> = "y".into();
    assert_eq!(eager.get(&y).ints().to_string(), "[10..]", "the eager y");
    assert_eq!(lazy.settled(&y), eager.get(&y), "y");
}

/// The scope of [`replay`] with `n` and `m` in [0, 20] and every leaf unbounded.
fn hubs_from_zero() -> Scope {
    let all = names(&["n", "m", "a0", "a1", "a2", "a3", "a4"]);
    let hubs = HUBS
        .iter()
        .map(|h| {
            and(
                prim(Prim::Ge, var(h), int(0)),
                prim(Prim::Le, var(h), int(20)),
            )
        })
        .reduce(and)
        .expect("two hubs");
    ints(&all).assume(&hubs, true, &Premises::new())
}

/// The eager scope after `steps` from `start`, as [`replay`] takes them.
fn eager_after(start: &Scope, steps: &[Step]) -> Scope {
    let p = Premises::new();
    steps.iter().fold(start.clone(), |mut s, step| match step {
        Step::Assume(t, outcome) => s.assume(t, *outcome, &p),
        Step::Bind(x, y) => {
            let (x, y): (Arc<str>, Arc<str>) = ((*x).into(), (*y).into());
            let py = s.get(&y);
            s.bind(&x, py, &Shared::new(Term::Var(y)));
            s
        }
    })
}

#[test]
fn a_kept_test_on_an_unbound_leaf_fires_as_the_eager_scope_fires_it() {
    // Gemini's case of XR-lazy-and-kernel-batch-1 round 1 (Q2, path 1): a kept test whose
    // trigger is a leaf no term binds. `m * m == 0` has no relation, so the disjunction is kept
    // with a trigger on `a0` above 5, and `m` is {0} and [10, 20]. Then `a0 >= n` makes `a0` a
    // leaf of the star at `n`, and `n >= 6` moves the hub: the eager scope projects the star,
    // `a0 >= 6` fires the trigger, the first case dies and `m` is [10, 20]. A lazy scope that
    // leaves `a0` stale never fires it, and settles `m` to {0} and [10, 20]. Option 1': a leaf
    // a kept test triggers on takes the eager steps (`Placing::holds`, `kept.by`).
    let sq = prim(Prim::Mul, var("m"), var("m"));
    let steps = [
        Step::Assume(
            or(
                and(
                    prim(Prim::Le, var("a0"), int(5)),
                    prim(Prim::Eq, sq, int(0)),
                ),
                and(
                    prim(Prim::Ge, var("a0"), int(6)),
                    prim(Prim::Ge, var("m"), int(10)),
                ),
            ),
            true,
        ),
        Step::Assume(diff_ge("n", "m", -20), true),
        Step::Assume(
            prim(Prim::Ge, prim(Prim::Add, var("n"), var("m")), int(0)),
            true,
        ),
        Step::Assume(diff_ge("a0", "n", 0), true),
        Step::Assume(prim(Prim::Ge, var("n"), int(6)), true),
    ];
    let eager = eager_after(&hubs_from_zero(), &steps);
    let m: Arc<str> = "m".into();
    assert_eq!(
        eager.get(&m).ints(),
        &IntervalSet::of(10, 20),
        "the eager scope no longer fires the trigger, so the test checks nothing"
    );
    replay(&hubs_from_zero(), &steps);
}

#[test]
fn a_test_on_a_name_bound_to_a_leaf_reads_the_leaf_settled() {
    // Gemini's case of XR-lazy-and-kernel-batch-1 round 1 (Q2, path 2): `a1` bound to the
    // leaf `a0` (`y = x`), the hub `n` moves, then a test of `a1` with two cases. The eager
    // scope projected `a0`'s star at the move, and its test reads `a0 >= 5`; one that settles
    // only the names the test mentions reads `a0`'s stale product. `settle_test` settles the
    // names those names' terms read, to a fixed point (option 1'). An outcome check only: it
    // passes on the base 06ed591d0 too, since the case `a1 <= 4` narrows `a0` through `a1`'s
    // summary and the projection of `a0`'s own star kills that case (XR round 2, Gemini A.3,
    // Codex A3). The two cases those findings gave in its place,
    // `a_product_test_on_a_name_bound_to_a_leaf_reads_the_leaf_after_its_hub_moved` and
    // `a_leaf_read_only_through_two_bindings_is_in_the_test_closure`, are outcome checks too
    // (XR round 3: the eager scope does not carry the move into the binding).
    let steps = [
        Step::Assume(diff_ge("a0", "n", 0), true),
        Step::Bind("a1", "a0"),
        Step::Assume(prim(Prim::Ge, var("n"), int(5)), true),
        Step::Assume(
            or(
                prim(Prim::Le, var("a1"), int(4)),
                prim(Prim::Ge, var("m"), int(10)),
            ),
            true,
        ),
        Step::Assume(prim(Prim::Le, var("a0"), int(4)), false),
    ];
    replay(&bounded_hubs(), &steps);
}

#[test]
fn a_bound_leaf_of_a_star_of_two_hubs_follows_its_class_as_the_eager_scope_does() {
    // A leaf bound to a term (`a0` to `a3`) is the leaf of a star of both hubs, and tests among
    // the hubs change the conjuncts the star's class is keyed by (`due`, `relation.classed`):
    // the eager scope projects the star again at each, reads `a0`'s narrowing back into `a3`,
    // and `!(a3 - m >= -3)` carries it to `m`. A lazy scope that projects only the classes'
    // stars of eager leaves must count `a0` as one (option 1', `Placing::holds`).
    let steps = [
        Step::Bind("a0", "a3"),
        Step::Assume(sum3("a0", "n", "m", 1, false), true),
        Step::Assume(diff_ge("a3", "m", -3), false),
        Step::Assume(diff_ge("n", "m", 3), true),
        Step::Assume(prim(Prim::Ge, var("m"), int(2)), true),
        Step::Assume(sum3("a2", "n", "m", 0, true), true),
        Step::Assume(
            prim(Prim::Ge, prim(Prim::Add, var("n"), var("m")), int(9)),
            true,
        ),
        Step::Assume(prim(Prim::Ge, var("n"), int(8)), true),
    ];
    replay(&bounded_hubs(), &steps);
}

/// As [`wide`], and now and then a kept test whose trigger is a leaf: one case bounds the leaf
/// below `c` beside `h * h == 0` (no relation, so the disjunction is kept), the other bounds it
/// from `c + 1` beside a bound on a hub, as in
/// `a_kept_test_on_an_unbound_leaf_fires_as_the_eager_scope_fires_it` (item F1.3 of
/// XR-lazy-and-kernel-batch-1 round 1). With [`step`]'s bindings of a leaf to another name,
/// which give terms that read leaves, it draws both paths by which a leaf that is not lazy
/// reaches a hub.
fn triggers(rng: &mut Rng, depth: usize) -> Term {
    if rng.below(4) == 0 {
        let (leaf, hub, c) = (rng.pick(&LEAVES), rng.pick(&HUBS), rng.int(-5, 5));
        let sq = prim(Prim::Mul, var(rng.pick(&HUBS)), var(rng.pick(&HUBS)));
        or(
            and(
                prim(Prim::Le, var(leaf), int(c)),
                prim(Prim::Eq, sq, int(0)),
            ),
            and(
                prim(Prim::Ge, var(leaf), int(c + 1)),
                prim(Prim::Ge, var(hub), int(rng.int(-10, 10))),
            ),
        )
    } else {
        wide(rng, depth)
    }
}

/// Random seeds of [`triggers`].
mod a_lazy_scope_with_kept_tests_on_leaves_settles_each_name_to_the_eager_product {
    use super::*;

    #[test]
    fn random_seeds() {
        run(
            &bounded_hubs(),
            fresh_seeds("lazy scope with kept tests on leaves", 10),
            triggers,
        );
    }
}

/// Whether a star of two hubs or more stands beside a satellite of its hubs: a conjunct of a
/// hub of the star and one other name, neither a leaf of a star nor a hub of that one.
fn satellite_kept(s: &Scope) -> bool {
    let stars = stars_by_definition(&s.relation);
    stars.iter().any(|(leaf, gs)| {
        let hubs: BTreeSet<Arc<str>> = gs
            .iter()
            .flat_map(|g| mentioned(g))
            .filter(|n| n != leaf)
            .collect();
        hubs.len() > 1
            && s.relation.set().iter().any(|g| {
                let ns = mentioned(g);
                ns.len() == 2
                    && ns.iter().any(|n| hubs.contains(n))
                    && ns
                        .iter()
                        .any(|n| !hubs.contains(n) && !stars.contains_key(n))
            })
    })
}

/// As [`wide`], and now and then a hub above a leaf, `n - ai >= c`, so that a leaf between the
/// two hubs (`ai >= n`, `m - ai >= c`) is a satellite of them and leaves the stars of the two
/// hubs in place.
fn satellites(rng: &mut Rng, depth: usize) -> Term {
    if rng.below(4) == 0 {
        diff_ge(rng.pick(&HUBS), rng.pick(&LEAVES), rng.int(-3, 3))
    } else {
        wide(rng, depth)
    }
}

/// Random seeds of [`satellites`]. A star of two hubs stood beside a satellite of them at
/// seeds 18, 59, 75 and 99 of 0 to 99 only (2026-11-09; 9 of seeds 0 to 199), so seed 18 is
/// checked on its own.
mod a_lazy_scope_with_satellites_of_two_hubs_settles_each_name_to_the_eager_product {
    use super::*;

    #[test]
    fn random_seeds() {
        let seeds = fresh_seeds("lazy scope with satellites of two hubs", 8);
        run(&bounded_hubs(), seeds, satellites);
    }

    #[test]
    fn seed_18_holds_a_star_beside_a_satellite_of_its_hubs() {
        let (stale, _, _, kept) = run(&bounded_hubs(), [18], satellites);
        assert!(stale > 0, "the lazy scope settled every name at once");
        assert!(
            kept > 0,
            "no star of two hubs stood beside a satellite of them"
        );
    }

    /// Seed 132839571965928555 (FAIL-lazy-satellites-seed-132839571965928555): `a1` bound to
    /// `a4`'s product, then narrowed to (-inf, -5] by `a1 < n + m` and `n + m <= -4`; the
    /// eager scope reads that back to `a4`, and the lazy scope settled `a4` to (-inf, 39].
    #[test]
    fn seed_132839571965928555_reads_a_narrowed_binder_back_to_the_name_it_reads() {
        run(&bounded_hubs(), [132839571965928555], satellites);
    }

    // The next three are dry-hash's (566683ede on wt/dry-hash-sat-3), taken here with the
    // change they test (option 1' of XR-lazy-and-kernel-batch-1).

    /// Seed 4211133997374228451 of [`satellites`] (FAIL-lazy-satellites-wider-interval, a fresh
    /// seed of `random_seeds` on 2026-11-26): the lazy scope settled `a0` to (-inf, -3] where
    /// the eager scope holds (-inf, -5]. A regression of the join, the shadow and the star,
    /// not a test of option 1': its binding `a3 = a0` narrows `a0` through the readers'
    /// read-back, fixed on the base 06ed591d0 (FAIL-lazy-hubs-seed-3066150143192435835; XR round
    /// 2, Gemini A.3, Codex A3).
    #[test]
    fn seed_4211133997374228451_settles_a0_at_most_minus_5() {
        run(&bounded_hubs(), [4211133997374228451], satellites);
    }

    /// Seed 16004534807616651151 of [`satellites`] (FAIL-lazy-satellites-wider-interval): `a1`
    /// is bound to `a3`'s product and narrowed through the hub `m`; the eager scope projects
    /// `a1`'s star, reads it back to `a3` and holds `m` in [15, 18], where the lazy scope held
    /// [13, 18].
    #[test]
    fn seed_16004534807616651151_settles_m_from_15() {
        run(&bounded_hubs(), [16004534807616651151], satellites);
    }

    /// Seed 12944458854883377711 of [`satellites`] (FAIL-lazy-satellites-wider-interval): the
    /// same family through the hub `n`, which the eager scope holds in [-18, 19] and the lazy
    /// scope held in [-19, 19].
    #[test]
    fn seed_12944458854883377711_settles_n_from_minus_18() {
        run(&bounded_hubs(), [12944458854883377711], satellites);
    }

    /// Seed 4415653652323528176 of [`satellites`] (FAIL-lazy-satellites-seed-4415653652323528176,
    /// filed by b31-kernel): `a4` bound to `a0`'s product, then `a0 >= n + m - 3`,
    /// `m - a4 >= -1` and the join's `a3 >= n + m + 2`; at the end the eager scope holds `a0` in
    /// [-14, 16] and the lazy scope settled it to [-14, 11] on origin/main 6ebd79c8d. It passes
    /// on 77dd97d2a, before round 3's part A, so option 1' fixes it, not the settle before
    /// `read_image` (2026-11-27).
    #[test]
    fn seed_4415653652323528176_settles_a0_to_16() {
        run(&bounded_hubs(), [4415653652323528176], satellites);
    }

    /// The 8 seeds `random_seeds` runs from 10735748659401783843 (FAIL-lazy-satellites-seed-
    /// 10735748659401783843, filed by b30-pres4): on origin/main d420c701d settling a leaf
    /// emptied the lazy scope (the debug assertion after the two `reduce_with(false)` of the
    /// settle), and the panic names no seed of the 8; the first alone passes there. They pass on
    /// this branch (2026-11-27).
    #[test]
    fn seeds_from_10735748659401783843_settle_a_leaf_without_emptying_the_scope() {
        run(
            &bounded_hubs(),
            10735748659401783843..10735748659401783851,
            satellites,
        );
    }

    /// Seed 172996873852937618 of [`satellites`] (FAIL-lazy-satellites-seed-172996873852937616,
    /// run seed 172996873852937616, filed by b31-kernel): `m` settled apart on origin/main
    /// 0bf095dab (lazy.rs "m after").
    #[test]
    fn seed_172996873852937618() {
        run(&bounded_hubs(), [172996873852937618], satellites);
    }

    /// Run seeds 18057453501005508156 (FAIL-lazy-satellites-seed-18057453501005508156, b30-pres4:
    /// "n after", eager [-8, 16], lazy [-12, 16]) and 3901955888460722549 (dry-coll: "m after" at
    /// case seed 3901955888460722551, eager [-17, -2], lazy [-17, 0]) of `random_seeds`, red on
    /// origin/main ac8c4cfda and green on part A (dry-hash, 2026-11-28). The case seed of the
    /// first is not recorded, so all eight of each run.
    #[test]
    fn seeds_from_18057453501005508156_and_3901955888460722549() {
        for first in [18057453501005508156, 3901955888460722549] {
            run(&bounded_hubs(), first..first + 8, satellites);
        }
    }

    /// Run seed 13561823126443913154 of `random_seeds`
    /// (FAIL-lazy-satellites-seed-13561823126443913154, filed by b30-pres4: "m after", eager
    /// [-12, 20], lazy [-13, 20]), red on origin/main ce063f500 and green on part A a262708d4
    /// (dry-hash, 2026-11-28). The case seed is not recorded, so all eight run.
    #[test]
    fn seeds_from_13561823126443913154() {
        run(
            &bounded_hubs(),
            13561823126443913154..13561823126443913162,
            satellites,
        );
    }

    /// Run seeds 11284093382845542960 (FAIL-lazy-satellites-seed-11284093382845542960, found by
    /// dry-hash's merge_check of wt/dry-hash-fmt2: "m after", eager [-6, 13], lazy [-13, 13];
    /// red on origin/main f12358c9b, green on part A a262708d4) and 13646106697067029505
    /// (FAIL-lazy-satellites-seed-13646106697067029505, b30-check's merge_check: "settling a
    /// leaf emptied a scope" on origin/main 2790b0cf8, green on 0214af9a9) of `random_seeds`
    /// (dry-hash, 2026-11-28). The case seeds are not recorded, so all eight of each run.
    #[test]
    fn seeds_from_11284093382845542960_and_13646106697067029505() {
        for first in [11284093382845542960, 13646106697067029505] {
            run(&bounded_hubs(), first..first + 8, satellites);
        }
    }

    /// Run seed 7716123424606244342 of `random_seeds` (FAIL-lazy-scope-seed-7716123424606244342,
    /// b30-front2's merge_check of wt/b30-front2-w: "settling a leaf emptied a scope", red on
    /// origin/main f79759f83, green on part A). The case seeds are not recorded, so all eight.
    #[test]
    fn seeds_from_7716123424606244342() {
        let first = 7716123424606244342;
        run(&bounded_hubs(), first..first + 8, satellites);
    }

    /// Case seed 4520948814785025178 of `random_seeds` (run seed 4520948814785025171,
    /// FAIL-lazy-satellites-seed-4520948814785025171, b22-names2's merge_check: "m after",
    /// eager -15..=-2 against lazy -13..=-2). Red on origin/main f79759f83 (local job r2),
    /// green on part A, f6c6c6657 (local job r1, 2026-11-28).
    #[test]
    fn seed_4520948814785025178() {
        run(&bounded_hubs(), [4520948814785025178], satellites);
    }

    /// Seed 14813679539726631198 of [`satellites`]
    /// (FAIL-lazy-satellites-seed-14813679539726631198, run seed 14813679539726631197, filed by
    /// b30-check): `n` settled apart, eager -3..=20 and lazy -3..=2 after the ninth step. Both
    /// are sound, as the concrete set is empty
    /// ([`seed_14813679539726631198_has_no_point_after_its_ninth_step`]); the eager scope was
    /// the looser, as `Conjuncts::forget` of the eighth step's rebound `a3` forgot each
    /// conjunct alone and kept an arm that the other conjuncts rule out. Red on aa28da140
    /// (local job s1, 2026-11-28); PRECISION-forget-disjunction-arms projects each arm under
    /// the bounds on the name.
    #[test]
    fn seed_14813679539726631198() {
        run(&bounded_hubs(), [14813679539726631198], satellites);
    }

    /// Whether some integer point with this `n` meets the first eight steps of seed
    /// 14813679539726631198 (its trace, read by hand), and the ninth too when `ninth`: an
    /// oracle that uses neither scope. A join is the union of its two arms, `t ∧ u` and
    /// `¬t ∧ v`; `a3` is the value the eighth step rebinds, so it is the old `a3`, projected
    /// away after it (the new `a3` is held by no step after, so it is left out).
    ///
    /// `n` and `m` lie in -20..=20 ([`bounded_hubs`]); the other names are searched in
    /// -R..=R. That loses no point: each of them is compared only with thresholds `n + c`,
    /// `m + c` or `n + m + c` for |c| <= 4, all in -44..=44, and moving a value beyond every
    /// threshold to one past the last keeps the truth of each comparison, so a point exists
    /// iff one exists in the box.
    fn seed_14813_has_point(n: i64, ninth: bool) -> bool {
        const R: i64 = 64;
        (-20..=20i64).any(|m| {
            // 4: `m - n >= 2` is false; 5, first conjunct: `m <= 1`.
            m - n <= 1
                && m <= 1
                && (-R..=R).any(|a3| {
                    // 1: `a3 - n >= -1`; 7: `n + m - a3 >= -1`.
                    a3 - n >= -1
                        && n + m - a3 >= -1
                        && (-R..=R).any(|a2| {
                            // 2: join of `a3 - m >= -3`, `n + m - a2 >= 2`, `m - n >= -1`.
                            let two =
                                (a3 - m >= -3 && n + m - a2 >= 2) || (a3 - m < -3 && m - n >= -1);
                            two && (!ninth || a2 - (n + m) >= 0)
                                && (-R..=R).any(|a0| {
                                    // 3: join of `a2 - (n + m) >= 0`, `n - a0 >= 2`,
                                    // `m - a3 >= 0`.
                                    let three = (a2 - (n + m) >= 0 && n - a0 >= 2)
                                        || (a2 - (n + m) < 0 && m - a3 >= 0);
                                    // 6: `a0 <= 2 ∧ n >= -4 ∧ a1 - m >= 3` is false.
                                    three
                                        && (-R..=R).any(|a1| !(a0 <= 2 && n >= -4 && a1 - m >= 3))
                                        // 5, second conjunct: `n + m - a4 >= -2 ∨ a2 - m >= 3`.
                                        && (-R..=R).any(|a4| n + m - a4 >= -2 || a2 - m >= 3)
                                })
                        })
                })
        })
    }

    /// The oracle of seed 14813679539726631198 (FAIL-lazy-satellites-seed-14813679539726631198):
    /// after its eighth step `n` takes exactly -3..=2, which the lazy scope settles; after the
    /// ninth no point is left, so the eager scope's `n` in -3..=20 and the lazy one's -3..=2
    /// are both sound, and the eager one is the looser. By hand: the ninth step's `a2 >= n + m`
    /// leaves the second step's `¬t ∧ v` arm alone, `a3 <= m - 4`, and with the first step's
    /// `a3 >= n - 1` that gives `m - n >= 3`, against the fourth's `m - n <= 1`.
    #[test]
    fn seed_14813679539726631198_has_no_point_after_its_ninth_step() {
        let eighth: Vec<i64> = (-20..=20)
            .filter(|&n| seed_14813_has_point(n, false))
            .collect();
        assert_eq!(eighth, (-3..=2).collect::<Vec<_>>());
        assert!((-20..=20).all(|n| !seed_14813_has_point(n, true)));
    }
}

/// For each name of `all`, the values in `-3..=13` the scope holds of it.
fn held(s: &Scope, all: &[Arc<str>], lazy: bool) -> Vec<Vec<i64>> {
    all.iter()
        .map(|x| {
            let p = if lazy { s.settled(x) } else { s.get(x) };
            (-3..=13).filter(|v| p.contains(&Value::Int(*v))).collect()
        })
        .collect()
}

/// For each name, the values in `-3..=13` it takes at the integer points, with `n` and `m` in
/// `0..=5` and the leaves in `-3..=13`, that meet `a0 >= n + m`, `a0 <= 3`, `n <= a2 <= m - 1`
/// and, with `sandwich`, `n + m <= a1 <= n + m + 1`.
fn points(sandwich: bool) -> Vec<Vec<i64>> {
    let mut out = vec![BTreeSet::new(); 5];
    let w = -3..=13i64;
    for n in 0..=5i64 {
        for m in 0..=5i64 {
            for a0 in w.clone().filter(|a0| *a0 >= n + m && *a0 <= 3) {
                for a2 in w.clone().filter(|a2| *a2 >= n && *a2 < m) {
                    for a1 in w.clone() {
                        if sandwich && !(n + m..=n + m + 1).contains(&a1) {
                            continue;
                        }
                        for (i, v) in [n, m, a0, a1, a2].into_iter().enumerate() {
                            out[i].insert(v);
                        }
                    }
                }
            }
        }
    }
    out.into_iter().map(|s| s.into_iter().collect()).collect()
}

#[test]
fn stars_beside_a_satellite_or_a_sandwich_project_exactly() {
    // A star's core is closed: its conjuncts and the free conjuncts at its hubs, so that
    // projecting the core gives each of its names exactly. With hubs `n` and `m`, the star
    // `a0 >= n + m` and the satellite `n <= a2 <= m - 1`, whose conjuncts each relate it to
    // one hub: the hubs admit `a0` (each relates `a2` to the other hub, which is a hub of
    // `a0`), and the satellite's conjuncts are free at the hubs, so they are in the core;
    // projecting the core with `a0 <= 3` meets `n + m <= 3` with `n <= m - 1` and gives `n`
    // in 0..=1, where the star alone would give 0..=3. Any other conjunct at a name of the
    // core is of the name alone or another leaf's, which only bounds a hub, so nothing outside
    // the core relates its names. The sandwich `n + m <= a1 <= n + m + 1` relates `a1` to the
    // two hubs at once: `a1` is no satellite and no leaf (its sign differs), so the hubs admit
    // no star of `n` and `m`, `a0` is no star, and the whole block is projected together, as
    // before satellites.
    let all = names(&["n", "m", "a0", "a1", "a2"]);
    let p = Premises::new();
    for sandwich in [false, true] {
        let mut t = vec![
            prim(Prim::Ge, var("n"), int(0)),
            prim(Prim::Le, var("n"), int(5)),
            prim(Prim::Ge, var("m"), int(0)),
            prim(Prim::Le, var("m"), int(5)),
            sum3("a0", "n", "m", 0, false),
            diff_ge("a2", "n", 0),
            diff_ge("m", "a2", 1),
        ];
        if sandwich {
            t.push(sum3("a1", "n", "m", 0, false));
            t.push(sum3("a1", "n", "m", -1, true));
        }
        let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
        for t in &t {
            eager = eager.assume(t, true, &p);
            lazy = lazy.assume(t, true, &p);
        }
        let star = stars_by_definition(&lazy.relation).contains_key("a0");
        assert_eq!(star, !sandwich, "a0 a star with sandwich {sandwich}");
        assert_eq!(
            lazy.relation.star("a0").is_some(),
            star,
            "the kept stars and the definition disagree on a0"
        );
        let cap = prim(Prim::Le, var("a0"), int(3));
        let (eager, lazy) = (eager.assume(&cap, true, &p), lazy.assume(&cap, true, &p));
        let want = points(sandwich);
        assert_eq!(want[0], vec![0, 1], "the points give n in 0..=1");
        // Without the sandwich `a1` is unbounded, and so held at each value of the window.
        assert_eq!(
            held(&eager, &all, false),
            want,
            "eager, sandwich {sandwich}"
        );
        assert_eq!(held(&lazy, &all, true), want, "lazy, sandwich {sandwich}");
    }
}

/// `Scope::settle` gives a leaf of a class the projection of an earlier leaf of the class
/// when the other names and the leaf's own interval and class are as the earlier leaf's
/// were. Against settling each leaf alone, which reuses nothing: leaves named before,
/// between and after the hubs, so that the solver orders their names differently; the class
/// one conjunct of the two hubs, of coefficient one or two at the leaf, or two conjuncts of
/// one hub each; each leaf's own lower bound and hole drawn from two of each, so that some
/// leaves share them and some do not; and the hubs with bounds, holes and a class. The last
/// test moves a hub, so that every star is due at once. Each leaf is settled to the product
/// it gets alone, and to the eager scope's. The leaves were in one class in 15 of the 28 runs
/// of seeds 0 to 29 (seeds 12 and 17 give an empty scope; 2026-11-09 and 2026-11-14): random
/// seeds, and seed 1, whose leaves are in one class, with seed 12, whose scope is empty.
mod leaves_of_one_class_settled_together_get_what_each_gets_alone {
    use super::*;

    #[test]
    fn random_seeds() {
        part(fresh_seeds("leaves of one class settled together", 2));
    }

    #[test]
    fn seed_1_has_leaves_of_one_class_and_seed_12_an_empty_scope() {
        assert_eq!(
            part([1, 12]),
            (1, 1),
            "(runs, runs with the leaves in one class)"
        );
    }

    fn part(seeds: impl IntoIterator<Item = u64>) -> (usize, usize) {
        const LEAVES: [&str; 6] = ["a0", "a1", "mm0", "mm1", "z0", "z1"];
        let all = names(&["m", "n", "a0", "a1", "mm0", "mm1", "z0", "z1"]);
        let leaves = names(&LEAVES);
        let p = Premises::new();
        let (mut reused, mut runs) = (0, 0);
        for seed in seeds {
            naming(seed, || {
                let mut rng = Rng::new(seed);
                let form = rng.below(3);
                let c = rng.int(-3, 3);
                let star = |x: &str| -> Vec<Term> {
                    match form {
                        0 => vec![sum3(x, "n", "m", c, false)],
                        1 => vec![prim(
                            Prim::Ge,
                            prim(
                                Prim::Sub,
                                prim(Prim::Add, var(x), var(x)),
                                prim(Prim::Add, var("n"), var("m")),
                            ),
                            int(c),
                        )],
                        _ => vec![diff_ge(x, "n", c), diff_ge(x, "m", -c)],
                    }
                };
                let mut t: Vec<Term> = Vec::new();
                for h in ["n", "m"] {
                    t.push(prim(Prim::Ge, var(h), int(rng.int(-12, -2))));
                    t.push(prim(Prim::Le, var(h), int(rng.int(2, 12))));
                    t.push(prim(Prim::Ne, var(h), int(rng.int(-3, 3))));
                }
                if rng.below(2) == 0 {
                    // `n` even.
                    t.push(prim(Prim::Eq, prim(Prim::Mod, var("n"), int(2)), int(0)));
                }
                let lows = [rng.int(-20, 0), rng.int(-20, 0)];
                let holes = [rng.int(-3, 6), rng.int(-3, 6)];
                for x in LEAVES {
                    t.extend(star(x));
                    t.push(prim(Prim::Ge, var(x), int(rng.pick(&lows))));
                    t.push(prim(Prim::Ne, var(x), int(rng.pick(&holes))));
                }
                let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
                for t in &t {
                    eager = eager.assume(t, true, &p);
                    lazy = lazy.assume(t, true, &p);
                }
                let hub = prim(Prim::Ge, var("n"), int(rng.int(-4, 4)));
                eager = eager.assume(&hub, true, &p);
                lazy = lazy.assume(&hub, true, &p);
                if eager.bottom {
                    assert!(
                        lazy.bottom,
                        "seed {seed}: the eager scope is empty, the lazy one not"
                    );
                    return;
                }
                let classes: BTreeSet<_> = leaves
                    .iter()
                    .filter_map(|x| lazy.relation.class_of(x))
                    .collect();
                let stars = leaves
                    .iter()
                    .filter(|x| lazy.relation.star(x).is_some())
                    .count();
                let mut together = lazy.clone();
                together.settle(&leaves);
                for x in &leaves {
                    let mut alone = lazy.clone();
                    alone.settle([x]);
                    assert_eq!(together.get(x), alone.get(x), "seed {seed}: {x} with {t:?}");
                    assert_eq!(
                        together.get(x),
                        eager.get(x),
                        "seed {seed}: {x} eagerly, with {t:?}"
                    );
                }
                for h in names(&["m", "n"]) {
                    assert_eq!(together.get(&h), eager.get(&h), "seed {seed}: {h}");
                }
                runs += 1;
                reused += usize::from(stars >= 2 && classes.len() == 1);
            })
        }
        println!("{runs} runs, {reused} with two stars or more, all of one class");
        (runs, reused)
    }
}

/// `Scope::join` settles on each side the leaves of the stars whose core may differ
/// between the sides: those at a name the sides hold differently, at a name a written
/// constraint of one side alone mentions, or at a name whose free conjuncts differ
/// ([`zedc::store::conjuncts::Conjuncts::core`]). A leaf of a star whose core and product
/// are one on both sides stays as it is. Against the join of the two sides with every name
/// settled first, and against the eager join: leaves `a0` to `a3` of one class of two hubs
/// (`ai >= n + c` and `ai >= m + c`, or `ai - n + m >= c`), each with its own lower bound
/// and hole, hubs with bounds and holes, then a test that moves a hub, so that the stars
/// are stale, then two joins in a row of the two outcomes of a test, each narrowed
/// further: a test of a hub, of the two hubs (`n - m >= c`, a free conjunct at both, which
/// moves neither), of a leaf, or `b >= n && b >= m` on a further name `b`, whose negation
/// splits in two. Every name is then settled to the product of both. Random seeds, and seed
/// 1, at which a join leaves a leaf stale (7 of seeds 0 to 39; seeds 0 to 199 took 33 s at
/// load 24 to 35, item SPLIT-l01_39-slow).
mod a_join_settles_the_leaves_whose_core_differs_as_settling_every_name_does {
    use super::*;

    const LEAVES: [&str; 4] = ["a0", "a1", "a2", "a3"];

    /// A test on the two hubs, a leaf, or `b`, at nesting `depth` at most.
    fn branch(rng: &mut Rng, depth: usize) -> Term {
        let hub = rng.pick(&HUBS);
        match rng.below(if depth == 0 { 5 } else { 7 }) {
            0 => prim(
                rng.pick(&[Prim::Ge, Prim::Le]),
                var(hub),
                int(rng.int(-12, 12)),
            ),
            1 => diff_ge("n", "m", rng.int(-3, 3)),
            2 => prim(
                rng.pick(&[Prim::Ge, Prim::Le]),
                var(rng.pick(&LEAVES)),
                int(rng.int(-20, 20)),
            ),
            3 | 4 => and(diff_ge("b", "n", 0), diff_ge("b", "m", 0)),
            5 => or(branch(rng, depth - 1), branch(rng, depth - 1)),
            _ => and(branch(rng, depth - 1), branch(rng, depth - 1)),
        }
    }

    fn part(seeds: impl IntoIterator<Item = u64>) -> usize {
        let all = names(&["n", "m", "a0", "a1", "a2", "a3", "b"]);
        let p = Premises::new();
        let (mut runs, mut kept) = (0, 0);
        for seed in seeds {
            naming(seed, || {
                let mut rng = Rng::new(seed);
                let (form, c) = (rng.below(2), rng.int(-3, 3));
                let mut t: Vec<Term> = Vec::new();
                for h in HUBS {
                    t.push(prim(Prim::Ge, var(h), int(rng.int(-20, -2))));
                    t.push(prim(Prim::Le, var(h), int(rng.int(2, 20))));
                    t.push(prim(Prim::Ne, var(h), int(rng.int(-3, 3))));
                }
                let lows = [rng.int(-30, 0), rng.int(-30, 0)];
                for x in LEAVES {
                    if form == 0 {
                        t.push(diff_ge(x, "n", c));
                        t.push(diff_ge(x, "m", c));
                    } else {
                        let d = prim(Prim::Sub, var(x), var("n"));
                        t.push(prim(Prim::Ge, prim(Prim::Add, d, var("m")), int(c)));
                    }
                    t.push(prim(Prim::Ge, var(x), int(rng.pick(&lows))));
                    t.push(prim(Prim::Ne, var(x), int(rng.int(-3, 6))));
                }
                t.push(prim(
                    rng.pick(&[Prim::Ge, Prim::Le]),
                    var(rng.pick(&HUBS)),
                    int(rng.int(-6, 6)),
                ));
                let (mut eager, mut lazy) = (ints(&all), ints(&all).lazy());
                for t in &t {
                    eager = eager.assume(t, true, &p);
                    lazy = lazy.assume(t, true, &p);
                }
                let mut trace = vec![format!("seed {seed}: {t:?}")];
                for _ in 0..2 {
                    if eager.bottom {
                        break;
                    }
                    let (t, u, v) = (
                        branch(&mut rng, 1),
                        branch(&mut rng, 0),
                        branch(&mut rng, 0),
                    );
                    trace.push(format!("join {t:?} and {u:?} with not it and {v:?}"));
                    let arms = |s: &Scope| {
                        let yes = s.assume(&t, true, &p).assume(&u, true, &p);
                        let no = s.assume(&t, false, &p).assume(&v, true, &p);
                        (yes, no)
                    };
                    let (ey, en) = arms(&eager);
                    let (ly, ln) = arms(&lazy);
                    let (mut sy, mut sn) = (ly.clone(), ln.clone());
                    sy.settle(&all);
                    sn.settle(&all);
                    let (every, joined) = (sy.join(&sn), ly.join(&ln));
                    eager = ey.join(&en);
                    assert_eq!(eager.bottom, joined.bottom, "{}", trace.join("\n"));
                    if !eager.bottom {
                        for x in &all {
                            let s = joined.settled(x);
                            assert_eq!(s, every.settled(x), "{x} after\n{}", trace.join("\n"));
                            assert_eq!(s, eager.get(x), "{x} eagerly after\n{}", trace.join("\n"));
                            kept +=
                                usize::from(LEAVES.contains(&&**x) && joined.held_product(x) != s);
                        }
                    }
                    lazy = joined;
                    runs += 1;
                }
            })
        }
        println!("{runs} joins, {kept} leaves left stale by a join");
        kept
    }

    #[test]
    fn random_seeds() {
        part(fresh_seeds(
            "a join settles the leaves whose core differs",
            3,
        ));
    }

    #[test]
    fn seed_1_leaves_a_leaf_stale_after_a_join() {
        assert!(part([1]) > 0, "no join left a leaf stale");
    }

    /// FAIL-lazy-join-random-seed: at seed 317638431778198305 the arms give `m` the points `{1,
    /// 3}`, the eager arm with `1 mod 2` from a projection and the lazy arm, not projected,
    /// with every integer as its class, so the join settled `m` to two products of one set.
    /// The domain reduction now gives a set of points its least class (zedc-lattice
    /// `reduce_congruence`), so the two agree.
    #[test]
    fn seed_317638431778198305_gives_m_one_class_by_either_path() {
        part([317_638_431_778_198_305]);
    }
}

/// A scope of one name narrowed to the points `{1, 3}` by tests on it alone gives it the class
/// `1 mod 2`, eagerly and lazily, as a projection writing those points does
/// (FAIL-lazy-join-random-seed): one set of integers has one product whichever way it was
/// reached. Before the fix both kept every integer as the class.
#[test]
fn tests_on_one_name_leaving_two_points_give_it_their_least_class() {
    let p = Premises::new();
    let m: Arc<str> = "m".into();
    for lazy in [false, true] {
        let mut s = ints(&names(&["m"]));
        if lazy {
            s = s.lazy();
        }
        for t in [
            prim(Prim::Ge, var("m"), int(1)),
            prim(Prim::Le, var("m"), int(3)),
            prim(Prim::Ne, var("m"), int(2)),
        ] {
            s = s.assume(&t, true, &p);
        }
        let got = s.get(&m);
        let points = IntervalSet::single(1).join(&IntervalSet::single(3));
        assert_eq!(*got.ints(), points, "lazy {lazy}");
        assert_eq!(
            got.cell.congruence.element,
            zedc::store::lattice::Congruence::new(2, 1),
            "lazy {lazy}"
        );
    }
}

/// Joins whose two cases keep the values of each hub, so that the stars at the hubs, stale
/// from a move of both hubs, stay stale through the join unless the join settles them. Each
/// leaf `ai` is above `n` and above `m` (or `-m`), and the hubs meet a disjunction of tests
/// on them. Two ways the join's own star can differ from the cases': a case that is a test
/// on another name, `z`, joined with a test on the hubs makes a disjunction that mentions `z`
/// and both hubs, so the hubs no longer admit the star and the join holds none; and two cases
/// that test the hubs alone make a second disjunction among the hubs, which the projection of
/// the star (one disjunction at a time) reads less tightly than each case's one disjunction.
/// In both, the leaf settles to the least value of the leaf over the union of the cases.
mod a_join_settles_a_star_it_drops_or_whose_core_gains_a_disjunction {
    use super::*;

    /// `kn·n + km·m >= k`, each coefficient -1, 0 or 1.
    #[derive(Clone, Copy, Debug)]
    struct HubTest(i64, i64, i64);

    impl HubTest {
        fn holds(self, n: i64, m: i64) -> bool {
            self.0 * n + self.1 * m >= self.2
        }

        /// The test as a program writes it, with sums and differences only: a coefficient
        /// other than one or minus one would make it a written constraint, whose names the
        /// join settles at once.
        fn term(self) -> Term {
            let mut sum: Option<Term> = None;
            for (k, x) in [(self.0, "n"), (self.1, "m")] {
                sum = match (sum, k) {
                    (s, 0) => s,
                    (None, 1) => Some(var(x)),
                    (None, _) => Some(prim(Prim::Sub, int(0), var(x))),
                    (Some(s), 1) => Some(prim(Prim::Add, s, var(x))),
                    (Some(s), _) => Some(prim(Prim::Sub, s, var(x))),
                };
            }
            prim(Prim::Ge, sum.expect("a hub"), int(self.2))
        }
    }

    fn all(ts: &[HubTest], n: i64, m: i64) -> bool {
        ts.iter().all(|t| t.holds(n, m))
    }

    fn conj(ts: &[HubTest]) -> Term {
        ts.iter().map(|t| t.term()).reduce(and).expect("a test")
    }

    /// The hubs' values after the move.
    const LO: i64 = -10;
    const HI: i64 = 10;

    /// A case of the join: leaves `ai >= n` and `ai >= sign·m`, the disjunction `d1`, then
    /// `z >= 0` and `yes`, or `z < 0` and `no`, tested together when `with_z` and one after
    /// the other otherwise.
    struct Case {
        sign: i64,
        d1: Vec<HubTest>,
        yes: Vec<HubTest>,
        no: Vec<HubTest>,
        with_z: bool,
    }

    impl Case {
        /// The random case of `seed`: `d1` of two or three tests, each arm of one or two. A
        /// test of one hub narrows it, and so does a test of two whose bound is above 0 on
        /// this box, so the arms draw tests of two hubs with bounds at or below 0.
        fn of(seed: u64) -> Case {
            let shapes = [
                (1, 0),
                (-1, 0),
                (0, 1),
                (0, -1),
                (1, 1),
                (-1, -1),
                (1, -1),
                (-1, 1),
            ];
            let mut rng = Rng::new(seed);
            let test = |rng: &mut Rng, arm: bool| {
                if arm {
                    let (a, b) = rng.pick(&shapes[4..]);
                    HubTest(a, b, rng.int(-20, 0))
                } else {
                    let (a, b) = rng.pick(&shapes);
                    HubTest(a, b, rng.int(-14, 14))
                }
            };
            let d1: Vec<HubTest> = (0..2 + rng.below(2))
                .map(|_| test(&mut rng, false))
                .collect();
            let yes: Vec<HubTest> = (0..1 + rng.below(2))
                .map(|_| test(&mut rng, true))
                .collect();
            let no: Vec<HubTest> = (0..1 + rng.below(2))
                .map(|_| test(&mut rng, true))
                .collect();
            let (sign, with_z) = (rng.pick(&[1, -1]), rng.below(2) == 0);
            Case {
                sign,
                d1,
                yes,
                no,
                with_z,
            }
        }

        fn trace(&self, seed: u64) -> String {
            let Case {
                sign,
                d1,
                yes,
                no,
                with_z,
            } = self;
            format!("seed {seed}: sign {sign} d1 {d1:?} yes {yes:?} no {no:?} z {with_z}")
        }

        fn d1_holds(&self, n: i64, m: i64) -> bool {
            self.d1.iter().any(|g| g.holds(n, m))
        }

        /// The hubs' values in `LO..=HI` that `d1` and `arm` admit.
        fn points(&self, arm: &[HubTest]) -> Vec<(i64, i64)> {
            (LO..=HI)
                .flat_map(|n| (LO..=HI).map(move |m| (n, m)))
                .filter(|&(n, m)| self.d1_holds(n, m) && all(arm, n, m))
                .collect()
        }

        /// Whether neither arm narrows a hub on the box (otherwise the lazy join settles the
        /// stars at it at once).
        fn keeps(&self) -> bool {
            [&self.yes, &self.no].iter().all(|arm| {
                let points = self.points(arm);
                let ns: BTreeSet<i64> = points.iter().map(|p| p.0).collect();
                let ms: BTreeSet<i64> = points.iter().map(|p| p.1).collect();
                ns.len() == ms.len() && ns.len() == (HI - LO + 1) as usize
            })
        }

        /// The tests before the arms: hubs in `LO - 1..=HI`, the leaves, `d1`, and the move of
        /// both hubs to `LO`.
        fn before(&self) -> Vec<Term> {
            let mut t: Vec<Term> = Vec::new();
            for h in HUBS {
                t.push(prim(Prim::Ge, var(h), int(LO - 1)));
                t.push(prim(Prim::Le, var(h), int(HI)));
            }
            for x in ["a0", "a1", "a2"] {
                t.push(diff_ge(x, "n", 0));
                t.push(if self.sign == 1 {
                    diff_ge(x, "m", 0)
                } else {
                    prim(Prim::Ge, prim(Prim::Add, var(x), var("m")), int(0))
                });
            }
            t.push(self.d1.iter().map(|g| g.term()).reduce(or).expect("a test"));
            for h in HUBS {
                t.push(prim(Prim::Ge, var(h), int(LO)));
            }
            t
        }

        /// The scope after the tests before the arms, lazy or eager.
        fn scope(&self, lazy: bool, p: &Premises) -> Scope {
            let s = ints(&names(&["n", "m", "z", "a0", "a1", "a2"]));
            let s = if lazy { s.lazy() } else { s };
            self.before().iter().fold(s, |s, t| s.assume(t, true, p))
        }

        fn arms(&self, s: &Scope, p: &Premises) -> (Scope, Scope) {
            let z = prim(Prim::Ge, var("z"), int(0));
            if self.with_z {
                let not_z = prim(Prim::Lt, var("z"), int(0));
                (
                    s.assume(&and(z, conj(&self.yes)), true, p),
                    s.assume(&and(not_z, conj(&self.no)), true, p),
                )
            } else {
                (
                    s.assume(&z, true, p).assume(&conj(&self.yes), true, p),
                    s.assume(&z, false, p).assume(&conj(&self.no), true, p),
                )
            }
        }

        /// The least value of a leaf in either arm, by the enumeration of the hubs.
        fn least(&self) -> Option<i64> {
            (self.points(&self.yes).into_iter())
                .chain(self.points(&self.no))
                .map(|(n, m)| n.max(self.sign * m))
                .min()
        }

        /// The join of the eager arms, checked against the enumeration of the hubs and the
        /// lazy join: empty exactly when no point is left; each leaf's least value that of the
        /// enumeration; each hub holding every value a point gives it; and each name the
        /// same as in the lazy join, so a hub is exact wherever the lazy join's is. Each
        /// hub, eager and lazy, has the enumeration's least and greatest values as its ends
        /// (item LAZY-hub-coarse); a hole between them may be lost.
        fn eager_join(&self, trace: &str) -> Scope {
            let p = Premises::new();
            let (ey, en) = self.arms(&self.scope(false, &p), &p);
            let joined = ey.join(&en);
            let least = self.least();
            assert_eq!(joined.bottom, least.is_none(), "eagerly after {trace}");
            let Some(least) = least else {
                return joined;
            };
            let (ly, ln) = self.arms(&self.scope(true, &p), &p);
            let lazy = ly.join(&ln);
            // Equal both ways: the eager join no coarser (`Scope::refresh`), and the lazy one
            // no coarser (row PROOF-product-lazy-not-coarser, `Scope::lazy`), which `Case::run`
            // checks only for a case that keeps the hubs.
            for x in &names(&["n", "m", "z", "a0", "a1", "a2"]) {
                let (e, l) = (joined.get(x), lazy.settled(x));
                assert_eq!(e.ints(), l.ints(), "{x} eagerly, lazily, after {trace}");
            }
            let points: Vec<(i64, i64)> = (self.points(&self.yes).into_iter())
                .chain(self.points(&self.no))
                .collect();
            for (h, at) in [("n", 0), ("m", 1)] {
                let values: BTreeSet<i64> = points
                    .iter()
                    .map(|p| if at == 0 { p.0 } else { p.1 })
                    .collect();
                let (lo, hi) = (values.first(), values.last());
                let ends = IntervalSet::of(*lo.expect("a point"), *hi.expect("a point"));
                let h: Arc<str> = Arc::from(h);
                for (how, ints) in [
                    ("eagerly", joined.get(&h).ints().clone()),
                    ("lazily", lazy.settled(&h).ints().clone()),
                ] {
                    for &v in &values {
                        assert!(
                            ints.contains(v),
                            "{h} is {ints}, holds no {v}, {how} after {trace}"
                        );
                    }
                    assert!(
                        ints.hull() == ends,
                        "{h} is {ints}, the enumeration's ends are {ends}, {how} after {trace}"
                    );
                }
            }
            for x in ["a0", "a1", "a2"] {
                let ints = joined.get(&Arc::from(x)).ints().clone();
                assert!(
                    ints.contains(least) && !ints.contains(least - 1),
                    "{x} is {ints}, least {least}, eagerly after {trace}"
                );
            }
            joined
        }

        /// Checks each name of the lazy join against settling every name first, and against
        /// the eager join, and each leaf's least value against the enumeration of the hubs;
        /// returns how many leaves one arm or the other holds stale before the join.
        fn run(&self, trace: &str) -> usize {
            let all_names = names(&["n", "m", "z", "a0", "a1", "a2"]);
            let p = Premises::new();
            let (ly, ln) = self.arms(&self.scope(true, &p), &p);
            let (mut sy, mut sn) = (ly.clone(), ln.clone());
            sy.settle(&all_names);
            sn.settle(&all_names);
            let (every, joined) = (sy.join(&sn), ly.join(&ln));
            let eager = self.eager_join(trace);
            let least = self.least();
            assert_eq!(joined.bottom, least.is_none(), "{trace}");
            let Some(least) = least else {
                return 0;
            };
            let mut stale = 0;
            for x in &all_names {
                let s = joined.settled(x);
                assert_eq!(s, every.settled(x), "{x} after {trace}");
                assert_eq!(s, eager.get(x), "{x} eagerly after {trace}");
                if x.starts_with('a') {
                    let ints = s.ints();
                    assert!(
                        ints.contains(least) && !ints.contains(least - 1),
                        "{x} is {ints}, least {least}, after {trace}"
                    );
                    stale += usize::from(
                        ly.held_product(x) != ly.settled(x) || ln.held_product(x) != ln.settled(x),
                    );
                }
            }
            stale
        }
    }

    /// The case that tests `z` with a test on the hubs: the join's disjunction
    /// `(z >= 0 && n + m <= -7) || (z < 0 && n - m >= -30)` mentions `z`, which no hub relates
    /// to, so the join holds no star, and the leaves, at `-11` from before the move, read as
    /// they are unless the join settles them first.
    #[test]
    fn a_case_that_tests_another_name_drops_the_star() {
        let case = Case {
            sign: 1,
            d1: vec![HubTest(-1, -1, 10)],
            yes: vec![HubTest(-1, -1, 7)],
            no: vec![HubTest(1, -1, -30)],
            with_z: true,
        };
        assert!(case.run("n + m <= -10; z >= 0 && n + m <= -7, or z < 0 && n - m >= -30") > 0);
    }

    /// Cases that test the hubs alone: the join's core holds `n - m >= -6 || n <= -8` and
    /// `n - m >= -8 || n - m >= -6`, two disjunctions, and is projected one disjunction at a
    /// time, which gives `ai >= -4`; each case's core holds one disjunction and gives the
    /// least value `-3` (at `n = -3`, `m = 3`).
    #[test]
    fn a_join_that_adds_a_second_disjunction_to_the_core() {
        let case = Case {
            sign: -1,
            d1: vec![HubTest(1, -1, -6), HubTest(-1, 0, 8)],
            yes: vec![HubTest(1, -1, -8)],
            no: vec![HubTest(1, -1, -6)],
            with_z: false,
        };
        assert!(case.run("n - m >= -6 || n <= -8; n - m >= -8, or n - m >= -6") > 0);
    }

    /// Seeds at which the eager join was coarser than the lazy one: an arm's test on a term of
    /// the hubs that `d1` does not compare left the projection of `d1` with the leaves as it
    /// was, so each eager arm read a leaf or a hub below the enumeration, and the join took the
    /// union (at seed 22671 `m <= n + 5` under `m + n <= -7 || m + n >= 2` gave `a0 >= -2`,
    /// least `-1`; at seed 272 `m` reached `1`, greatest `0`). The eager join projects those
    /// stars again (`Scope::refresh`). Seeds 116 and 237, reported with them, show no
    /// difference from cc9b8f5b on, and are kept here as checks.
    #[test]
    fn the_eager_join_is_as_tight_as_the_lazy_one_at_these_seeds() {
        part([116, 237, 272, 2_220, 22_490, 22_671]);
    }

    /// Seeds reported with a lazy join's hub coarser than the enumeration (item
    /// LAZY-hub-coarse). At 781, 1515 and 1820 the ends were past the enumeration's: a test
    /// on `n + m` or `m - n` after `d1` made no part of `d1` due, since it is on neither of
    /// `d1`'s terms, so `d1`'s part kept the projection made without it. With that rule the
    /// eager join, checked first, had `n` in `[-10..=3]` at 781 (ends `[-10..=0]`), `m` in
    /// `[-5..=10]` at 1515 (ends `[1..=10]`) and `n` in `[-10..=10]` at 1820 (ends
    /// `[-10..=4]`). A part is now projected again when a group of linked constraints that
    /// holds two of its variables changes ([`Scope::lazy`]). At 397 and 550 the ends were
    /// already exact; a hole between them is lost (`n` is `[-10..=4]` at 397, the enumeration
    /// `[-10..=-9] ∪ [-5..=4]`), which is left open.
    #[test]
    fn the_lazy_join_has_the_enumeration_s_ends_at_these_seeds() {
        part([397, 550, 781, 1_515, 1_820]);
    }

    /// Random cases of both kinds. Each case's eager join is checked against the enumeration;
    /// a case where neither arm narrows a hub (`Case::keeps`) is also checked by
    /// `Case::run`.
    fn part(seeds: impl IntoIterator<Item = u64>) -> (usize, usize) {
        let (mut joins, mut kept) = (0, 0);
        for seed in seeds {
            naming(seed, || {
                let case = Case::of(seed);
                let trace = case.trace(seed);
                if !case.keeps() {
                    case.eager_join(&trace);
                    return;
                }
                kept += case.run(&trace);
                joins += 1;
            })
        }
        println!("{joins} joins, {kept} leaves stale before a join");
        (joins, kept)
    }

    /// Seeds 0 to 1,199 made 100 cases a test; a run now draws a few, of both kinds.
    #[test]
    fn random_seeds() {
        part(fresh_seeds("a join settles a star it drops", 8));
    }

    /// Each step of `seed`'s case, eager and lazy, before any join: the tests before the arms,
    /// then each arm's tests one by one; after each, every name of the eager scope equals the
    /// lazy one settled.
    fn steps_alike(seed: u64) {
        let case = Case::of(seed);
        let trace = case.trace(seed);
        let p = Premises::new();
        let all = names(&["n", "m", "z", "a0", "a1", "a2"]);
        let s = ints(&all);
        let mut tests = case.before();
        let arm = |z: Term, ts: &[HubTest]| -> Vec<Term> {
            [z].into_iter().chain(ts.iter().map(|t| t.term())).collect()
        };
        let arms = [
            arm(prim(Prim::Ge, var("z"), int(0)), &case.yes),
            arm(prim(Prim::Lt, var("z"), int(0)), &case.no),
        ];
        let at = tests.len();
        let (mut e, mut l) = (s.clone(), s.lazy());
        for (arm, more) in arms.into_iter().enumerate() {
            tests.truncate(at);
            tests.extend(more);
            if arm == 1 {
                (e, l) = (ints(&all), ints(&all).lazy());
            }
            for (i, t) in tests.iter().enumerate() {
                (e, l) = (e.assume(t, true, &p), l.assume(t, true, &p));
                for x in &all {
                    assert_eq!(
                        l.settled(x),
                        e.get(x),
                        "{x} at arm {arm} step {i} of {trace}"
                    );
                }
            }
        }
    }

    /// The seeds at which the eager join was coarser than the lazy one
    /// (`the_eager_join_is_as_tight_as_the_lazy_one_at_these_seeds`), step by step, with no
    /// join: an eager part projected before a constraint on another term of its names kept
    /// the coarser product, where the lazy leaf, settled, has the finer one (seed 22671: `m <=
    /// n + 5` under `m + n <= -7 || m + n >= 2` gave `a0 >= -2` eagerly, `-1` lazily).
    #[test]
    fn each_step_of_an_arm_is_alike_eager_and_lazy_at_these_seeds() {
        for seed in [
            116, 237, 272, 397, 550, 781, 1_515, 1_820, 2_220, 22_490, 22_671,
        ] {
            naming(seed, || steps_alike(seed));
        }
    }

    /// Random cases, step by step.
    #[test]
    fn each_step_of_an_arm_is_alike_eager_and_lazy_at_random_seeds() {
        for seed in fresh_seeds("each step of an arm", 16) {
            naming(seed, || steps_alike(seed));
        }
    }

    /// A leaf stale before a join that keeps the hubs (72 of seeds 0 to 199).
    #[test]
    fn seed_1_joins_with_a_leaf_stale() {
        let (joins, kept) = part([1]);
        assert!(joins > 0 && kept > 0, "{joins} joins, {kept} stale");
    }
}

/// The program of seed 1820 made small (item LAZY-hub-coarse): within `-10 <= n, m <= 10`,
/// `m >= 10 || n <= -9` and `n + m <= 14` leave `n` at most `4` (`m == 10` gives `n <= 4`,
/// `n <= -9` gives less). The bound `n + m <= 14` is on neither term of the disjunction, and
/// was assumed after it, so the disjunction's part was not projected again and `n` kept
/// `10`; with the other order, or both tests at once, it was `4`. Each order, eager and lazy,
/// now gives `n` in `[-10..=4]` and `m` in `[-10..=10]`.
#[test]
fn a_bound_on_two_names_of_a_disjunction_assumed_after_it_bounds_its_points() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let sum = || prim(Prim::Add, var("n"), var("m"));
    let dif = || prim(Prim::Sub, var("m"), var("n"));
    let either = || or(ge(var("m"), 10), le(var("n"), -9));
    let orders: [(&str, Vec<Term>); 4] = [
        ("after", vec![either(), le(sum(), 14)]),
        (
            "after another bound",
            vec![either(), ge(dif(), -14), le(sum(), 14)],
        ),
        ("before", vec![le(sum(), 14), either()]),
        ("at once", vec![and(either(), le(sum(), 14))]),
    ];
    let p = Premises::new();
    for (how, tests) in orders {
        for lazy in [false, true] {
            let s = ints(&names(&["n", "m"]));
            let s = if lazy { s.lazy() } else { s };
            let s = ["n", "m"]
                .into_iter()
                .flat_map(|h| [ge(var(h), -10), le(var(h), 10)])
                .chain(tests.iter().cloned())
                .fold(s, |s, t| s.assume(&t, true, &p));
            for (h, lo, hi) in [("n", -10, 4), ("m", -10, 10)] {
                let ints = s.settled(&Arc::from(h)).ints().clone();
                assert_eq!(
                    ints,
                    IntervalSet::of(lo, hi),
                    "{h} with the bound {how}, lazy {lazy}"
                );
            }
        }
    }
}

/// A group of constraints on one name `y` of a disjunction, assumed before it or with it,
/// that leaves holes in `y`'s values: `0 <= y - 3·z <= 1` leaves `y mod 3` in `{0, 1}`, so
/// the arm `x >= 10 && y == 5` has no point (5 mod 3 is 2) and `x` is `0`. The disjunction's
/// cases are tried as it is assumed, each against the constraints then held, and the arm's
/// case finds no point. Assumed after the disjunction, the same constraint left `x` in
/// `{0, 10}`, eager and lazy, until the case's point was asked of the relation
/// (`a_group_on_one_name_of_a_disjunction_assumed_after_it_bounds_its_points`, below).
#[test]
fn a_group_on_one_name_of_a_disjunction_assumed_before_it_bounds_its_points() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let y3z = || prim(Prim::Sub, var("y"), prim(Prim::Mul, int(3), var("z")));
    let either = || {
        or(
            and(ge(var("x"), 10), and(ge(var("y"), 5), le(var("y"), 5))),
            le(var("x"), 0),
        )
    };
    let orders: [(&str, Vec<Term>); 2] = [
        ("before", vec![ge(y3z(), 0), le(y3z(), 1), either()]),
        (
            "at once",
            vec![and(ge(y3z(), 0), and(le(y3z(), 1), either()))],
        ),
    ];
    let p = Premises::new();
    for (how, tests) in orders {
        for lazy in [false, true] {
            let s = ints(&names(&["x", "y", "z"]));
            let s = if lazy { s.lazy() } else { s };
            let s = [ge(var("x"), 0), le(var("x"), 10)]
                .into_iter()
                .chain(tests.iter().cloned())
                .fold(s, |s, t| s.assume(&t, true, &p));
            let x = s.settled(&Arc::from("x")).ints().clone();
            assert_eq!(x, IntervalSet::of(0, 0), "{how}, lazy {lazy}");
        }
    }
}

/// The same group with its second constraint assumed after the disjunction (row
/// FAIL-preimage-group-holes-precision): `0 <= y - 3·z` holds when the disjunction is
/// assumed, so its arm `x >= 10 && y == 5` has the point `y = 5, z = 1` then; `y - 3·z <= 1`
/// comes after, and at `y = 5` the two leave `z` no integer (`4/3 <= z <= 5/3`). The kept
/// disjunction's case fixes `y` to 5 and leaves `z` open, so the later constraint is decided
/// at that point with the other written constraints it reaches through `z`, and the case is
/// found to hold no state: `x` is `0`.
#[test]
fn a_group_on_one_name_of_a_disjunction_assumed_after_it_bounds_its_points() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let y3z = || prim(Prim::Sub, var("y"), prim(Prim::Mul, int(3), var("z")));
    let p = Premises::new();
    for lazy in [false, true] {
        let s = ints(&names(&["x", "y", "z"]));
        let s = if lazy { s.lazy() } else { s };
        let s = [
            ge(var("x"), 0),
            le(var("x"), 10),
            ge(y3z(), 0),
            or(
                and(ge(var("x"), 10), and(ge(var("y"), 5), le(var("y"), 5))),
                le(var("x"), 0),
            ),
            le(y3z(), 1),
        ]
        .into_iter()
        .fold(s, |s, t| s.assume(&t, true, &p));
        let x = s.settled(&Arc::from("x")).ints().clone();
        assert_eq!(x, IntervalSet::of(0, 0), "lazy {lazy}");
    }
}

/// Three cases whose classes join wider than their union (row
/// PROOF-product-join-cases-classes-inexact, sub-case (a)): `x % 3 == 0 && y == 2·x`,
/// `x % 3 == 1 && y == 2·x + 1`, each with `0 <= x <= 9`, and `20 <= x <= 29 && y == 3·x + 1`.
/// The first two give `y` the classes 0 and 3 modulo 6, which join to 0 modulo 3, and `x` the
/// classes 0 and 1 modulo 3, which join to every integer; `x = 2` (and 5, 8) is in no case,
/// and with `y` in 0 modulo 3 neither of the first two cases' relations meets it. The answer
/// is `x` in `{0, 1, 3, 4, 6, 7, 9}` or `20..=29`, eager and lazy, read as the product's
/// integers (`Product::classed`: its interval, its class and the union of the cases' classes
/// its join keeps, row LIMITS-classed-listing-per-set).
#[test]
fn three_cases_whose_classes_join_wide_keep_only_their_values() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let eq = |a: Term, b: Term| prim(Prim::Eq, a, b);
    let modulo = |r: i64| eq(prim(Prim::Mod, var("x"), int(3)), int(r));
    let lin = |a: i64, b: i64| prim(Prim::Add, prim(Prim::Mul, int(a), var("x")), int(b));
    let range = |lo: i64, hi: i64| and(ge(var("x"), lo), le(var("x"), hi));
    let test = or(
        or(
            and(range(0, 9), and(modulo(0), eq(var("y"), lin(2, 0)))),
            and(range(0, 9), and(modulo(1), eq(var("y"), lin(2, 1)))),
        ),
        and(range(20, 29), eq(var("y"), lin(3, 1))),
    );
    let want = [0, 1, 3, 4, 6, 7, 9]
        .into_iter()
        .map(|v| IntervalSet::of(v, v))
        .fold(IntervalSet::of(20, 29), |a, b| a.join(&b));
    let p = Premises::new();
    for lazy in [false, true] {
        let s = ints(&names(&["x", "y"]));
        let s = if lazy { s.lazy() } else { s };
        let s = s.assume(&test, true, &p);
        let x = s.settled(&Arc::from("x")).classed();
        assert_eq!(x, want, "lazy {lazy}");
    }
}

/// `x` after the three cases of [`three_cases_whose_classes_join_wide_past_the_old_listing_limit`]
/// at `r`, eager or lazy, each case assumed in an arm of its own and the arms' scopes joined
/// (`Scope::join`), the join LIMITS-classed-listing-per-set changes. Not one disjunction: the
/// exact cover gives the union of a disjunction's cases of different classes listed
/// (zedc-lattice `Classed::join_all`, O(v) for v values) on origin/main and here alike, a cost
/// of its own (row PERF-cover-union-of-classes-listed).
fn three_cases_at(r: i64, lazy: bool) -> zedc::store::product::Product {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let eq = |a: Term, b: Term| prim(Prim::Eq, a, b);
    let modulo = |r: i64| eq(prim(Prim::Mod, var("x"), int(3)), int(r));
    let lin = |a: i64, b: i64| prim(Prim::Add, prim(Prim::Mul, int(a), var("x")), int(b));
    let range = |lo: i64, hi: i64| and(ge(var("x"), lo), le(var("x"), hi));
    let cases = [
        and(range(0, 3 * r), and(modulo(0), eq(var("y"), lin(2, 0)))),
        and(range(0, 3 * r), and(modulo(1), eq(var("y"), lin(2, 1)))),
        and(range(5 * r, 5 * r + 9), eq(var("y"), lin(3, 1))),
    ];
    let s = ints(&names(&["x", "y"]));
    let s = if lazy { s.lazy() } else { s };
    let p = Premises::new();
    (cases.iter().map(|c| s.assume(c, true, &p)))
        .reduce(|a, b| a.join(&b))
        .expect("three cases")
        .settled(&Arc::from("x"))
}

/// [`three_cases_whose_classes_join_wide_keep_only_their_values`] with the first two cases on
/// `0 <= x <= 3·r` and the third on `5·r <= x <= 5·r + 9`, at `r` = 10^3 and 10^6: the cases'
/// classes 0 and 1 modulo 3 hold 2·r + 2 values, each case in an arm of its own and the arms
/// joined ([`three_cases_at`]). Each value of `x` asked is in the answer exactly where it is in
/// a case (`Product::contains`), eager and lazy. At r = 10^6 each arm's values are past the
/// limit at which a set is listed (`presburger::listed_within_limit`, about 134,800 values), so
/// each arm keeps its ranges and class, and `x`'s interval keeps two ranges (a listed answer
/// has one for each of the 2·r + 2 values). Red before green, run on origin/main at 7351ba062:
/// at r = 10^6, eager, the join of the arms' classes 0 and 1 modulo 3 was every integer, `x`
/// was `[0..=3000000, 5000000..=5000009]` modulo 1, so `x = 2` was held. At r = 10^3 the arms
/// are listed, the answer is exact on both sides, the negative control.
#[test]
fn three_cases_whose_classes_join_wide_past_the_old_listing_limit() {
    for r in [1_000i64, 1_000_000] {
        let held = |v: i64| {
            ((0..=3 * r).contains(&v) && v.rem_euclid(3) != 2) || (5 * r..=5 * r + 9).contains(&v)
        };
        let asked = [
            -1,
            0,
            1,
            2,
            3,
            3 * r - 2,
            3 * r - 1,
            3 * r,
            3 * r + 1,
            4 * r,
            5 * r - 1,
            5 * r,
            5 * r + 4,
            5 * r + 9,
            5 * r + 10,
        ];
        for lazy in [false, true] {
            let x = three_cases_at(r, lazy);
            if r > 1_000 {
                assert!(
                    x.ints().len() <= 2,
                    "r {r}, lazy {lazy}: x's ranges {}",
                    x.ints()
                );
            }
            for v in asked {
                assert_eq!(
                    x.contains(&Value::Int(v)),
                    held(v),
                    "r {r}, lazy {lazy}, x = {v}: {x:?}"
                );
            }
        }
    }
}

/// The tests and constraints of [`points_asked_after_a_disjunction_scale`] at size `k`: for
/// each `i < k`, `0 <= x_i <= 10`, `0 <= y_i - 3·z_i`, the test `(x_i >= 10 && y_i == 5) ||
/// x_i <= 0`, whose first case fixes `y_i`, and after it `y_i - 3·z_i <= 1` for even `i`,
/// which leaves that case no point, or `<= 2` for odd `i`, which leaves it one.
fn points_asked(k: usize) -> Vec<Term> {
    let ge = |a: Term, v: i64| prim(Prim::Ge, a, int(v));
    let le = |a: Term, v: i64| prim(Prim::Le, a, int(v));
    let mut out = Vec::new();
    for i in 0..k {
        let (x, y) = (|| var(&format!("x{i}")), || var(&format!("y{i}")));
        let y3z = || {
            prim(
                Prim::Sub,
                y(),
                prim(Prim::Mul, int(3), var(&format!("z{i}"))),
            )
        };
        out.push(ge(x(), 0));
        out.push(le(x(), 10));
        out.push(ge(y3z(), 0));
        out.push(or(
            and(ge(x(), 10), and(ge(y(), 5), le(y(), 5))),
            le(x(), 0),
        ));
        out.push(le(y3z(), 1 + (i % 2) as i64));
    }
    out
}

/// The scope over the names of [`points_asked`] at size `k`, before its tests.
fn points_asked_scope(k: usize) -> Scope {
    let ns: Vec<String> = (0..k)
        .flat_map(|i| [format!("x{i}"), format!("y{i}"), format!("z{i}")])
        .collect();
    let ns: Vec<&str> = ns.iter().map(|s| s.as_str()).collect();
    ints(&names(&ns))
}

/// `s` with the tests `ts` of [`points_asked`] at size `k` assumed in order, its first two
/// and last two groups' `x_i` checked: 0 for an even `i`, 0 or 10 for an odd one.
fn points_asked_settled(s: &Scope, ts: &[Term], k: usize, lazy: bool) -> Scope {
    let p = Premises::new();
    let s = if lazy { s.clone().lazy() } else { s.clone() };
    let s = ts.iter().fold(s, |s, t| s.assume(t, true, &p));
    for i in [0, 1, k - 2, k - 1] {
        let x = s
            .settled(&Arc::from(format!("x{i}").as_str()))
            .ints()
            .clone();
        let want = if i % 2 == 0 {
            IntervalSet::of(0, 0)
        } else {
            IntervalSet::of(0, 0).join(&IntervalSet::of(10, 10))
        };
        assert_eq!(x, want, "x{i} at {k}, lazy {lazy}");
    }
    s
}

/// A constraint written after a kept test whose case fixes one of its names and leaves
/// another open is asked at the case's point (`Scope::written_dead`, `Scope::no_point_at`):
/// 64 groups of [`points_asked`], eager and lazy. The even groups' `x_i` is 0 and the odd
/// groups' is 0 or 10. The timing at 64 and 512 groups is `bench::points_asked_after_a_
/// disjunction_scale`: in this module's piece it ran 21 s alone on a Colab VM against the
/// limit of 20 s (TEST-vm-pieces-over-20s, 2026-11-22).
#[test]
fn points_asked_after_a_disjunction_are_answered() {
    let (s, ts) = (points_asked_scope(64), points_asked(64));
    for lazy in [false, true] {
        points_asked_settled(&s, &ts, 64, lazy);
    }
}

/// `Σ c·s + k >= 0`.
fn linear(terms: &[(&str, i64)], k: i64) -> Term {
    let sum = terms.iter().fold(int(k), |t, (s, c)| {
        prim(Prim::Add, t, prim(Prim::Mul, int(*c), var(s)))
    });
    prim(Prim::Ge, sum, int(0))
}

/// A refused projection of a lazy leaf's block leaves the leaf as the eager scope has it
/// (the author's rule of 2026-11-28: lazy and eager give the same result in every case; only
/// the cost may differ). `a - n - m >= 0` and `n + 2m >= 0` make `a` a leaf of the two hubs
/// `n` and `m`. At `n >= -10` the eager scope projects the star exactly: the least `a` is
/// the least `n + m` with `m >= -n/2`, which is at least `n/2 >= -5`, so `a >= -5`; the lazy
/// scope leaves `a` stale. At `n <= 10` the eager scope projects again, and `m >= -5` comes
/// from `n + 2m >= 0` alone. Then a system of four constraints among `n`, `m`, `y`, `z`
/// joins the block; the solver refuses its projection, since removing any of the four names
/// would leave more constraints than there are (the warning says "the work could grow
/// without end"). Both scopes project `a`'s block, both are refused and warn, and both keep
/// what single constraints give, `a >= n + m >= -10 + -5 = -15`, met with what each held
/// before. The eager scope held `-5`, met in at `n >= -10`; before the lazy scope settles
/// the stale leaves of a block whose projection a test makes refused (`Scope::assume`), it
/// held `[-15, ∞)` there (XR-lazy-and-kernel-batch-1 round 3, Gemini A-4, Codex A4). The
/// ordering is a construction, not a draw. Corner cases: the leaf read before the refused
/// test (settled then, so nothing is stale at the refusal), the refused test assumed twice,
/// and the four constraints assumed one at a time, the last of them the refused step.
#[test]
fn a_refused_projection_leaves_the_lazy_leaf_as_the_eager_one() {
    let p = Premises::new();
    let ge = |x: &str, v: i64| prim(Prim::Ge, var(x), int(v));
    let refused = |x: &str, w: &str, y: &str, z: &str| {
        and(
            and(
                linear(&[(x, 4), (w, -12), (y, -10), (z, -12)], 11),
                linear(&[(w, 4), (x, 10), (y, -10), (z, -11)], -28),
            ),
            and(
                linear(&[(w, 11), (x, 4), (y, -1), (z, 12)], -28),
                linear(&[(w, -8), (x, -5), (y, 12), (z, -1)], 31),
            ),
        )
    };
    let before = [
        sum3("a", "n", "m", 0, false),
        linear(&[("n", 1), ("m", 2)], 0),
        ge("n", -10),
        prim(Prim::Le, var("n"), int(10)),
        ge("y", -100),
        ge("z", -100),
    ];
    let a = Arc::<str>::from("a");
    let all = names(&["a", "n", "m", "y", "z"]);
    let s = ints(&all);
    let run = |s: Scope, ts: &[Term]| ts.iter().fold(s, |s, t| s.assume(t, true, &p));
    let (e, l) = (run(s.clone(), &before), run(s.clone().lazy(), &before));
    assert_eq!(e.get("a").ints().to_string(), "[-5..]");
    assert_eq!(l.settled(&a), e.get("a"));
    // `a` is stale in `l` here; its public read is the eager one (round 4, Claude A4.1).
    assert_ne!(l.held_product("a"), e.get("a"), "a is not stale here");
    assert_eq!(l.get("a"), e.get("a"), "get of a stale leaf");
    assert!(e.warnings().is_empty() && l.warnings().is_empty());
    let mut read = l.clone();
    read.settle(&all);
    let whole = [refused("n", "m", "y", "z")];
    let one_by_one: Vec<Term> = vec![
        linear(&[("n", 4), ("m", -12), ("y", -10), ("z", -12)], 11),
        linear(&[("m", 4), ("n", 10), ("y", -10), ("z", -11)], -28),
        linear(&[("m", 11), ("n", 4), ("y", -1), ("z", 12)], -28),
        linear(&[("m", -8), ("n", -5), ("y", 12), ("z", -1)], 31),
    ];
    let twice = [whole[0].clone(), whole[0].clone()];
    let cases: [(&str, &Scope, &[Term]); 4] = [
        ("at once", &l, &whole),
        ("read before", &read, &whole),
        ("twice", &l, &twice),
        ("one at a time", &l, &one_by_one),
    ];
    let warned =
        |s: &Scope| -> Vec<String> { s.warnings().iter().map(|w| w.to_string()).collect() };
    for (how, l, ts) in cases {
        let (mut e, mut l) = (e.clone(), l.clone());
        for (i, t) in ts.iter().enumerate() {
            (e, l) = (e.assume(t, true, &p), l.assume(t, true, &p));
            for x in &all {
                assert_eq!(l.settled(x), e.get(x), "{x} {how}, after step {i}");
            }
        }
        let ws = warned(&e);
        assert!(
            ws.iter()
                .any(|w| w.contains("the work could grow without end")),
            "{how}: {ws:?}"
        );
        assert_eq!(warned(&l), ws, "{how}");
        assert_eq!(e.get("a").ints().to_string(), "[-5..]", "{how}");
    }
}

/// Three cases beside a conjunct both sides keep, `x == 3·w + v` (row
/// PROOF-product-join-cases-classes-inexact, the step from sub-case (a) to (b)): `v == 0`
/// and `v == 1`, each with `0 <= x <= 9`, and `v == 2` with `20 <= x <= 29`; and again with
/// `x >= 0`, `x >= 0` and `x <= -10`. The inner join of the first two holds `v` in `{0, 1}`,
/// so the shared conjunct alone could remove `x = 2` at its reduction, which the outer join
/// (`v` in `[0, 2]`) cannot. The joins of `join_cases`, unreduced and then reduced once, give
/// the same `x`, `w` and `v` as the joins reduced at each level and as the test assumed
/// whole, eager and lazy: the cases' finite sets of `x` are exact, so their union is, and an
/// unbounded `x` keeps no hole.
#[test]
fn joins_beside_a_shared_tie_agree_with_and_without_inner_reductions() {
    let ge = |a: Term, k: i64| prim(Prim::Ge, a, int(k));
    let le = |a: Term, k: i64| prim(Prim::Le, a, int(k));
    let eq = |a: Term, b: Term| prim(Prim::Eq, a, b);
    let tie = eq(
        var("x"),
        prim(Prim::Add, prim(Prim::Mul, int(3), var("w")), var("v")),
    );
    let v_is = |v: i64| eq(var("v"), int(v));
    let bounded = [
        and(v_is(0), and(ge(var("x"), 0), le(var("x"), 9))),
        and(v_is(1), and(ge(var("x"), 0), le(var("x"), 9))),
        and(v_is(2), and(ge(var("x"), 20), le(var("x"), 29))),
    ];
    let unbounded = [
        and(v_is(0), ge(var("x"), 0)),
        and(v_is(1), ge(var("x"), 0)),
        and(v_is(2), le(var("x"), -10)),
    ];
    let p = Premises::new();
    let at = |s: &Scope| {
        ["x", "w", "v"]
            .map(|n| s.settled(&Arc::from(n)).ints().to_string())
            .join(" ")
    };
    for (sides, want) in [
        (
            bounded,
            "[0..=1, 3..=4, 6..=7, 9..=9, 20..=20, 23..=23, 26..=26, 29..=29]",
        ),
        (unbounded, ""),
    ] {
        for lazy in [false, true] {
            let s = ints(&names(&["x", "w", "v"]));
            let s = if lazy { s.lazy() } else { s };
            let s = s.assume(&tie, true, &p);
            let cs: Vec<Scope> = sides.iter().map(|t| s.assume(t, true, &p)).collect();
            let mut non = cs[0].join(&cs[1]).join(&cs[2]);
            non.reduce();
            let mut ab = cs[0].join(&cs[1]);
            ab.reduce();
            let mut red = ab.join(&cs[2]);
            red.reduce();
            let test = or(or(sides[0].clone(), sides[1].clone()), sides[2].clone());
            let whole = s.assume(&test, true, &p);
            assert_eq!(at(&non), at(&red), "lazy {lazy}");
            assert_eq!(at(&non), at(&whole), "lazy {lazy}");
            if !want.is_empty() {
                assert_eq!(non.settled(&Arc::from("x")).ints().to_string(), want);
            }
        }
    }
}

/// The six steps left of seed 4014432025532948819 of `random_seeds` when every other is
/// removed (FAIL-lazy-scope-random-seed). `n` is bound to `m`, so `n == m`, and `m - a3 >= 3`
/// with `a3 - n >= 0` leaves no state. `a3 - n >= 0` reads `n <= 17` back through `n`'s term
/// into `m <= 17`, and the reduction after the test then gives `a3 == 14` and `n <= 14`,
/// which no read carried into `m`. In the eager scope a path decides the last test, so it
/// read nothing; the lazy scope, where no path decides a test, read `n <= 14` into `m`
/// there and was empty while the eager one was not. Now the terms of the names a reduction
/// narrows are read once after it (`Scope::read_back_terms`), and both are empty at the
/// fourth step.
#[test]
fn a_test_of_a_name_reads_its_term_after_a_reduction_narrowed_it() {
    let p = Premises::new();
    let start = boxed(&["n", "m", "a0", "a1", "a2", "a3", "a4"], 20);
    let (mut eager, mut lazy) = (start.clone(), start.lazy());
    let assume = |s: &Scope, t: &Term, o: bool| s.assume(t, o, &p);
    for s in [&mut eager, &mut lazy] {
        *s = assume(s, &diff_ge("m", "a3", 3), true);
        let (n, m): (Arc<str>, Arc<str>) = ("n".into(), "m".into());
        let pm = s.settled(&m);
        s.bind(&n, pm, &Shared::new(Term::Var(m.clone())));
        *s = assume(s, &diff_ge("a4", "n", -1), false);
        *s = assume(s, &prim(Prim::Ge, var("a3"), int(14)), true);
        *s = assume(s, &diff_ge("a3", "n", 0), true);
        assert!(s.bottom, "after a3 - n >= 0: {:?}", s.get(&m));
        *s = assume(s, &diff_ge("n", "a4", 2), true);
    }
    assert!(eager.bottom, "eager: {:?}", eager.get(&Arc::from("m")));
    assert!(lazy.bottom, "lazy");
}

mod bench;

/// The four constraints among `n`, `m`, `y`, `z` whose projection the solver refuses
/// ([`a_refused_projection_leaves_the_lazy_leaf_as_the_eager_one`]).
fn refused_four() -> Term {
    and(
        and(
            linear(&[("n", 4), ("m", -12), ("y", -10), ("z", -12)], 11),
            linear(&[("m", 4), ("n", 10), ("y", -10), ("z", -11)], -28),
        ),
        and(
            linear(&[("m", 11), ("n", 4), ("y", -1), ("z", 12)], -28),
            linear(&[("m", -8), ("n", -5), ("y", 12), ("z", -1)], 31),
        ),
    )
}

/// The warnings and the refusals, each with its kept sets, of a lazy scope and the eager one
/// (the author's rule of 2026-11-28; the contract at `Scope::lazy`). XR-lazy-and-kernel-batch-1
/// round 4, Claude A4.2, conjectured a difference: eager projects a leaf's star at every hub
/// move and records a refusal of that projection there, lazy later or in a discarded copy. The
/// witness built here: the leaf `a >= n + m` with `n + 2m >= 0` and bounds on the hubs, the
/// refused four constraints joining its block, then moves of `n`, `m`, `y`, `z` by tests that
/// refuse nothing, and a second leaf `b >= y + z` before or after the refused step. At every
/// step both scopes report the same warnings and hold the same refusal map (kept sets
/// included). Found so on head a262708d4 as well (2026-11-28), so it was never red: the
/// difference is not reached here, and why the eager hub move adds no refusal the lazy scope
/// lacks is not traced. The warnings now read the settled view
/// ([`warnings_of_a_lazy_scope_read_its_settled_view`]).
#[test]
fn a_refusal_only_the_eager_projection_raises_is_warned_alike() {
    let p = Premises::new();
    let ge = |x: &str, v: i64| prim(Prim::Ge, var(x), int(v));
    let le = |x: &str, v: i64| prim(Prim::Le, var(x), int(v));
    let all = names(&["a", "b", "n", "m", "y", "z"]);
    let base = [
        sum3("a", "n", "m", 0, false),
        linear(&[("n", 1), ("m", 2)], 0),
        ge("n", -10),
        le("n", 10),
        ge("y", -100),
        ge("z", -100),
    ];
    let b = || sum3("b", "y", "z", 0, false);
    let tails: Vec<(&str, Vec<Term>)> = vec![
        ("n moved", vec![refused_four(), ge("n", 0)]),
        (
            "n moved twice",
            vec![refused_four(), ge("n", 0), le("n", 5)],
        ),
        ("m moved", vec![refused_four(), ge("m", 0)]),
        ("y moved", vec![refused_four(), ge("y", 0)]),
        ("z moved", vec![refused_four(), le("z", 50)]),
        ("b before", vec![b(), refused_four(), ge("y", 0)]),
        ("b after", vec![refused_four(), b(), ge("y", 0), ge("z", 0)]),
        (
            "every hub",
            vec![
                refused_four(),
                ge("n", 0),
                ge("m", 0),
                ge("y", 0),
                ge("z", 0),
            ],
        ),
    ];
    let s = ints(&all);
    let run = |s: Scope, ts: &[Term]| ts.iter().fold(s, |s, t| s.assume(t, true, &p));
    let warned =
        |s: &Scope| -> Vec<String> { s.warnings().iter().map(|w| w.to_string()).collect() };
    for (what, tail) in &tails {
        let (mut e, mut l) = (run(s.clone(), &base), run(s.clone().lazy(), &base));
        for (i, t) in tail.iter().enumerate() {
            e = e.assume(t, true, &p);
            l = l.assume(t, true, &p);
            assert_eq!(warned(&l), warned(&e), "{what}, step {i}: warnings");
            assert_eq!(l.refusals, e.refusals, "{what}, step {i}: refusals");
            for x in &all {
                assert_eq!(l.get(x), e.get(x), "{what}, step {i}: {x}");
            }
        }
        // Negative control: the refused step warns, so the comparison has a warning to compare.
        assert!(!warned(&e).is_empty(), "{what}: nothing refused");
    }
}

/// Seeded sweep of the warnings (XR-lazy-and-kernel-batch-1 round 4, Claude A4.2): random
/// sequences of up to eight steps among the leaf `a >= n + m`, the refused four constraints,
/// random systems of four constraints among `n`, `m`, `y`, `z` with factors in `-12..=12`
/// (which the solver often refuses), bounds on the hubs, `n + 2m >= 0` and a second leaf
/// `b >= m + y`; after every step the warnings, the refusal maps and every product of the lazy
/// scope equal the eager scope's. Negative control: some steps warn. Not reached: a step
/// that warns while a leaf of the lazy scope is stale (its held product is not the eager
/// one); 624 steps warned and none had a stale leaf (2026-11-28), so this sweep cannot show
/// a refusal the lazy scope skipped, and that count is printed, not asserted. The case is
/// [`warnings_of_a_lazy_scope_read_its_settled_view`]. 150 seeds (300 ran on head a262708d4
/// without a difference, 1278 steps with warnings, 2026-11-28).
#[test]
fn a_lazy_scope_warns_as_the_eager_one_at_every_step_of_random_refusing_systems() {
    let p = Premises::new();
    let vs = ["n", "m", "y", "z"];
    let all = names(&["a", "b", "n", "m", "y", "z"]);
    let s0 = ints(&all);
    let warned =
        |s: &Scope| -> Vec<String> { s.warnings().iter().map(|w| w.to_string()).collect() };
    let (mut warn_steps, mut stale_warn_steps) = (0, 0);
    for seed in 0..150u64 {
        let mut r = Rng::new(seed);
        let c = |lo: i64, hi: i64, r: &mut Rng| lo + r.below((hi - lo + 1) as usize) as i64;
        let mut steps = vec![sum3("a", "n", "m", 0, false)];
        for _ in 0..7 {
            steps.push(match r.below(6) {
                0 => refused_four(),
                1 => {
                    let mut cons = Vec::new();
                    for _ in 0..4 {
                        let ts: Vec<(&str, i64)> =
                            vs.iter().map(|v| (*v, c(-12, 12, &mut r))).collect();
                        cons.push(linear(&ts, c(-30, 30, &mut r)));
                    }
                    and(
                        and(cons[0].clone(), cons[1].clone()),
                        and(cons[2].clone(), cons[3].clone()),
                    )
                }
                2 | 3 => {
                    let (v, k) = (vs[r.below(4)], c(-15, 15, &mut r));
                    match r.below(2) {
                        0 => prim(Prim::Ge, var(v), int(k)),
                        _ => prim(Prim::Le, var(v), int(k)),
                    }
                }
                4 => linear(&[("n", 1), ("m", 2)], 0),
                _ => sum3("b", "m", "y", 0, false),
            });
        }
        let (mut e, mut l) = (s0.clone(), s0.clone().lazy());
        for (i, t) in steps.iter().enumerate() {
            e = e.assume(t, true, &p);
            l = l.assume(t, true, &p);
            let we = warned(&e);
            assert_eq!(warned(&l), we, "seed {seed}, step {i} ({t}): warnings");
            assert_eq!(
                l.refusals, e.refusals,
                "seed {seed}, step {i} ({t}): refusals"
            );
            let mut stale = false;
            for x in &all {
                let want = e.get(x);
                assert_eq!(l.get(x), want, "seed {seed}, step {i} ({t}): {x}");
                stale |= l.held_product(x) != want;
            }
            if !we.is_empty() {
                warn_steps += 1;
                stale_warn_steps += usize::from(stale);
            }
        }
    }
    eprintln!(
        "warnings sweep: {warn_steps} steps with warnings, {stale_warn_steps} of them with a stale leaf"
    );
    assert!(warn_steps > 0, "no step warned");
}

/// The steps before the refused test of
/// [`a_refused_projection_leaves_the_lazy_leaf_as_the_eager_one`], eager and lazy: `a >= n +
/// m`, `n + 2m >= 0`, `n` in [-10, 10], `y` and `z` at least -100. `a` is stale in the lazy
/// scope.
fn refusal_fixture() -> (Scope, Scope) {
    let p = Premises::new();
    let ge = |x: &str, v: i64| prim(Prim::Ge, var(x), int(v));
    let before = [
        sum3("a", "n", "m", 0, false),
        linear(&[("n", 1), ("m", 2)], 0),
        ge("n", -10),
        prim(Prim::Le, var("n"), int(10)),
        ge("y", -100),
        ge("z", -100),
    ];
    let s = ints(&names(&["a", "n", "m", "y", "z"]));
    let run = |s: Scope| before.iter().fold(s, |s, t| s.assume(t, true, &p));
    (run(s.clone()), run(s.lazy()))
}

/// XR-lazy-and-kernel-batch-1 round 4, A4.1: the public product read of a lazy scope is the
/// eager product, at a stale leaf too, and leaves the scope as it was (still stale).
#[test]
fn get_of_a_lazy_scope_is_the_eager_product() {
    let (e, l) = refusal_fixture();
    assert_ne!(l.held_product("a"), e.get("a"), "a is not stale");
    for x in ["a", "n", "m", "y", "z", "q"] {
        assert_eq!(l.get(x), e.get(x), "{x}");
    }
    assert_ne!(
        l.held_product("a"),
        e.get("a"),
        "get settled the scope in place"
    );
}

/// XR-lazy-and-kernel-batch-1 round 4, Gemini A-2: `Scope::reaches` of a test the solver
/// refuses, on a lazy scope with a stale leaf in the refused block, gives the eager answer
/// and refusals, kept sets included: the eager scope kept `a` in `[-5, ∞)` at the refusal,
/// the lazy one, unless asked again with the leaf settled (`Scope::settled_before_refusal`),
/// `[-15, ∞)`. The refused four constraints, and the four with `a <= 100`, each with the
/// outcome true (no split) and false (a split into cases).
#[test]
fn reaches_of_a_lazy_scope_gives_the_eager_refusals() {
    let p = Premises::new();
    let (e, l) = refusal_fixture();
    let mut tests = vec![refused_four()];
    tests.push(and(refused_four(), prim(Prim::Le, var("a"), int(100))));
    let mut refused_once = 0;
    for t in &tests {
        for outcome in [true, false] {
            let (want, got) = (e.reaches(t, outcome, &p), l.reaches(t, outcome, &p));
            assert_eq!(got, want, "{t} {outcome}");
            refused_once += usize::from(!want.1.is_empty());
        }
    }
    // Negative control: the comparison has refusals to compare.
    assert!(refused_once > 0, "nothing refused");
}

/// XR-lazy-and-kernel-batch-1 round 4, A4.2 and Gemini A-3: the warnings, the looped tests
/// and the refusals found by name of a lazy scope are those of the eager scope, read through
/// its settled view: a star `a >= n + m + y + z` over hubs whose four constraints the solver
/// refuses, then moves of each hub by a test that refuses nothing. The eager scope projects
/// `a`'s star at each move and may record a refusal of that projection there; the lazy one
/// leaves `a` stale. Also the two-hub star `a >= n + m` of
/// [`a_refused_projection_leaves_the_lazy_leaf_as_the_eager_one`]. Each step compares
/// `warnings`, `looped`, `refused_on` of every name and of `a` alone, and the products.
#[test]
fn warnings_of_a_lazy_scope_read_its_settled_view() {
    let p = Premises::new();
    let ge = |x: &str, v: i64| prim(Prim::Ge, var(x), int(v));
    let le = |x: &str, v: i64| prim(Prim::Le, var(x), int(v));
    let all = ["a", "n", "m", "y", "z"];
    let stars = [
        (
            "four hubs",
            linear(&[("a", 1), ("n", -1), ("m", -1), ("y", -1), ("z", -1)], 0),
        ),
        ("two hubs", sum3("a", "n", "m", 0, false)),
    ];
    let hubs = [
        ge("n", -10),
        le("n", 10),
        ge("m", -10),
        le("m", 10),
        ge("y", -100),
        ge("z", -100),
    ];
    let moves = [ge("n", 0), ge("m", 0), ge("y", 0), le("z", 50), le("n", 5)];
    let s = ints(&names(&all));
    let warned =
        |s: &Scope| -> Vec<String> { s.warnings().iter().map(|w| w.to_string()).collect() };
    let looped = |s: &Scope| -> Vec<String> { s.looped().iter().map(|w| w.to_string()).collect() };
    let mut stale_warned = 0;
    for (what, star) in &stars {
        for refused_first in [false, true] {
            let mut steps: Vec<Term> = hubs.to_vec();
            if refused_first {
                steps.extend([refused_four(), star.clone()]);
            } else {
                steps.extend([star.clone(), refused_four()]);
            }
            steps.extend(moves.iter().cloned());
            let (mut e, mut l) = (s.clone(), s.clone().lazy());
            for (i, t) in steps.iter().enumerate() {
                (e, l) = (e.assume(t, true, &p), l.assume(t, true, &p));
                let at = format!("{what}, refused first {refused_first}, step {i} ({t})");
                assert_eq!(warned(&l), warned(&e), "{at}: warnings");
                assert_eq!(looped(&l), looped(&e), "{at}: looped");
                assert_eq!(l.refused_on(all), e.refused_on(all), "{at}: refused_on");
                assert_eq!(
                    l.refused_on(["a"]),
                    e.refused_on(["a"]),
                    "{at}: refused_on a"
                );
                let mut stale = false;
                for x in all {
                    let (pl, pe) = (l.get(x), e.get(x));
                    assert!(
                        pl == pe,
                        "{x}: lazy {:?}, eager {:?}; {at}",
                        pl.ints(),
                        pe.ints()
                    );
                    stale |= l.held_product(x) != e.get(x);
                }
                stale_warned += usize::from(stale && !warned(&e).is_empty());
            }
            assert!(!warned(&e).is_empty(), "{what}: nothing refused");
        }
    }
    eprintln!("warnings of the settled view: {stale_warned} steps warned with a stale leaf");
}

/// Gemini's killing test A3 (1) of XR-lazy-and-kernel-batch-1 round 4, for the two calls of
/// `Scope::promote` in `Scope::bind`: `n`, `m`, `k`, `w` in [0, 20], `x >= n + m` (a star the
/// solver projects, not a path, so `x` is recorded unplaced before the binding), `y` bound to
/// `x + w`, `y <= k`, then `n >= 10` and `k <= 15`. The read back of `y` at the last step
/// reads `x`; the eager `w` is [0, 5], and a stale `x` in [0, ∞) leaves it [0, 15]. Once on a
/// fresh `y` (the first call) and once on a `y` the scope has (the second). Round 5: green
/// with either call or both taken out, so both were taken out (META4); the test stays as a
/// check that lazy equals eager here.
#[test]
fn a_leaf_a_bound_term_reads_takes_the_eager_steps_from_the_binding() {
    let p = Premises::new();
    for shadow in [false, true] {
        let mut ns = vec!["n", "m", "k", "w", "x", "t"];
        if shadow {
            ns.push("y");
        }
        let box20 = ["n", "m", "k", "w"]
            .iter()
            .map(|h| {
                and(
                    prim(Prim::Ge, var(h), int(0)),
                    prim(Prim::Le, var(h), int(20)),
                )
            })
            .reduce(and)
            .expect("four names");
        let start = ints(&names(&ns)).assume(&box20, true, &p);
        let run = |s: Scope| {
            let mut s = s.assume(&sum3("x", "n", "m", 0, false), true, &p);
            let (y, t): (Arc<str>, Arc<str>) = ("y".into(), "t".into());
            let top = s.get(&t);
            s.bind(&y, top, &Shared::new(prim(Prim::Add, var("x"), var("w"))));
            s.assume(&diff_ge("k", "y", 0), true, &p)
                .assume(&prim(Prim::Ge, var("n"), int(10)), true, &p)
                .assume(&prim(Prim::Le, var("k"), int(15)), true, &p)
        };
        let what = if shadow {
            "a y the scope has"
        } else {
            "a fresh y"
        };
        witness_w(&run(start.clone()), &run(start.lazy()), what);
    }
}

/// Gemini's killing test A3 (2) of XR-lazy-and-kernel-batch-1 round 4, for the step of
/// `Scope::join` that makes an eager side lazy: `y` bound to `x + w` on an eager copy of
/// [`witness_scope`] (whose binding records no names its term reads) and on a lazy one,
/// joined either way round, then `x >= n + m`, `n >= 10` and `y <= 15`. The eager reference
/// is the eager side joined with itself; its `w` is [0, 5], and the join read with the eager
/// side's empty reads leaves `x` stale and `w` in [0, 15].
#[test]
fn a_leaf_the_eager_side_of_a_join_binds_takes_the_eager_steps() {
    let p = Premises::new();
    let s = witness_scope(false);
    let bound = |mut s: Scope| {
        let (y, t): (Arc<str>, Arc<str>) = ("y".into(), "t".into());
        let top = s.get(&t);
        s.bind(&y, top, &Shared::new(prim(Prim::Add, var("x"), var("w"))));
        s
    };
    let after = |s: Scope| {
        s.assume(&sum3("x", "n", "m", 0, false), true, &p)
            .assume(&prim(Prim::Ge, var("n"), int(10)), true, &p)
            .assume(&prim(Prim::Le, var("y"), int(15)), true, &p)
    };
    let (e, l) = (bound(s.clone()), bound(s.lazy()));
    let eager = after(e.join(&e));
    witness_w(&eager, &after(e.join(&l)), "eager joined with lazy");
    witness_w(&eager, &after(l.join(&e)), "lazy joined with eager");
}

/// Gemini's killing test A3 (3) of XR-lazy-and-kernel-batch-1 round 4, for the call of
/// `Scope::promote` in `Scope::join_kept`: `n`, `m`, `k` in [0, 20], `x >= n + k`, then the
/// kept test `(x <= 5 && m >= 10) || m * m == 0`, arms in that order, so that the case the
/// join starts from leaves `x` as the scope held it, then `n >= 6`, which takes `x` past 5:
/// the eager `m` is [0, 0]; a lazy `x` takes no eager step at the move, the trigger does not
/// fire, and `m` is `{0} ∪ [10, 20]`. Round 5: green with the call taken out, so it was taken
/// out (META4); the test stays as a check that lazy equals eager here.
#[test]
fn a_leaf_a_kept_test_names_takes_the_eager_steps_from_the_join_of_its_cases() {
    let p = Premises::new();
    let box20 = ["n", "m", "k"]
        .iter()
        .map(|h| {
            and(
                prim(Prim::Ge, var(h), int(0)),
                prim(Prim::Le, var(h), int(20)),
            )
        })
        .reduce(and)
        .expect("three names");
    let start = ints(&names(&["n", "m", "k", "x"])).assume(&box20, true, &p);
    let kept = or(
        and(
            prim(Prim::Le, var("x"), int(5)),
            prim(Prim::Ge, var("m"), int(10)),
        ),
        prim(Prim::Eq, prim(Prim::Mul, var("m"), var("m")), int(0)),
    );
    let steps = [
        sum3("x", "n", "k", 0, false),
        kept,
        prim(Prim::Ge, var("n"), int(6)),
    ];
    let run = |s: Scope| steps.iter().fold(s, |s, t| s.assume(t, true, &p));
    let (eager, lazy) = (run(start.clone()), run(start.lazy()));
    let m: Arc<str> = "m".into();
    assert_eq!(eager.get(&m).ints().to_string(), "[0..=0]", "the eager m");
    assert_eq!(lazy.settled(&m), eager.get(&m), "m");
}
