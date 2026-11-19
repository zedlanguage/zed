//! The benchmarks of `disj_groups.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::disj_groups::*;
use zed_tests::scaling;
use zedc::store::presburger::project_each;

#[test]
fn the_middle_of_a_difference_chain_whose_disjuncts_hold_is_projected_in_n_log_n() {
    projects(
        "a difference chain projected, a disjunct holding",
        1100,
        difference_chain,
        Holds::First,
    );
}

#[test]
fn a_difference_chain_whose_disjuncts_do_not_hold_is_decided_in_n_log_n() {
    decides(
        "a difference chain decided, no disjunct holding",
        4500,
        difference_chain,
    );
}

#[test]
fn the_middle_of_a_difference_chain_whose_disjuncts_do_not_hold_is_projected_in_n_log_n() {
    projects(
        "a difference chain projected, no disjunct holding",
        700,
        difference_chain,
        Holds::None,
    );
}

/// At 512 stages, where the limit of 2026-11-10, 11.7 times, was below the 12.13 times of work of order n^1.2;
/// at 64 it was 13.2 (plan item THREE-atom-exponent).
#[test]
fn a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_decided_in_n_log_n() {
    decides(
        "a chain of three-atom rows decided, no disjunct holding",
        1300,
        general_chain,
    );
}

/// At 256 stages, not fewer: the limit for work of order n log n is 12.1 times from 256 to
/// 2048, and work of order n^1.2 gives 8^1.2 = 12.13 times there, but at 32 stages the limit is
/// 14.1 and n log n itself gives 12.8 times, so n^1.2 passed unseen (plan item
/// THREE-atom-exponent; COMPLEXITY.md row THREE-atom-exponent). The same test of the chain whose
/// disjuncts hold is deferred to plan row PRES-scaling-10_5 in
/// wt/scratch/deferred-tests/PRES-scaling-10_5.rs.
#[test]
fn the_middle_of_a_chain_of_three_atom_rows_whose_disjuncts_do_not_hold_is_projected_in_n_log_n() {
    projects(
        "a chain of three-atom rows projected, no disjunct holding",
        190,
        general_chain,
        Holds::None,
    );
}

#[test]
fn the_middle_of_a_chain_whose_disjunctions_jointly_leave_one_step_is_projected_in_n_log_n() {
    joint_chain_scales(Written::AsIs, 180);
}

/// [`joint_chain`] with its equations negated: before item PROJECT-each-canon the greedy
/// search took `x[i + 1] - x[i] == 3` first, failed, and a question per disjunct followed,
/// 122 times the bytes at 8n.
#[test]
fn the_middle_of_a_chain_whose_negated_disjunctions_jointly_leave_one_step_is_projected_in_n_log_n()
{
    joint_chain_scales(Written::Negated, 170);
}

#[test]
fn the_middle_of_a_chain_of_removals_each_needing_the_one_before_is_projected_in_n_log_n() {
    for flipped in [false, true] {
        let inputs = scaling::inputs(110, |m| cascade(m, flipped));
        scaling::check_order(
            &format!("a chain of removals each needing the one before, flipped {flipped}"),
            110,
            1,
            |m| assert_cascade_middle(&inputs[&m], m),
        );
    }
}

#[test]
fn the_middle_of_a_chain_whose_lower_end_only_cases_give_is_projected_in_n_log_n() {
    let inputs = scaling::inputs(820, case_chain);
    scaling::check("a chain whose lower end only cases give", 820, |m| {
        assert_case_chain_middle(&inputs[&m], m);
    });
}

mod row_sums {

    use std::collections::BTreeSet;

    use zed_tests::scaling::{self};
    use zedc::store::presburger::{Atom, ROW_SUMS_OFF, decide, project_each};

    use crate::disj_groups::row_sums::*;

    /// `overlap_rows` at k and 2k: the solver alone refused both after 5,443M and 33,783M
    /// instructions (2026-11-13); the join answers, below the 2^k assignments a plain
    /// enumeration tries, in its run first at both sizes: 0.37M at k = 16 and 0.88M at k = 32,
    /// 2.4 times from k to 2k, against 65,536 times for enumeration (before PRES-overlap-fast,
    /// at the rate of 256, the method ran beside the solver at k = 32: 0.45M and 24.1M).
    #[test]
    fn two_overlapping_sums_of_16_and_32_atoms_are_decided_below_enumeration() {
        let (f16, f32) = (overlap_rows(16).formula(), overlap_rows(32).formula());
        let w16 = work(|| assert_eq!(decide(&f16), Ok(true)));
        let w32 = work(|| assert_eq!(decide(&f32), Ok(true)));
        eprintln!(
            "overlap_rows decided: k = 16 {w16}, k = 32 {w32}, growth {:.1}",
            w32 as f64 / w16 as f64
        );
        assert!(w32 < 1 << 32, "{w32}");
        assert_every_hull_non_empty(&f32, &[v(0), v(31)]);
    }

    /// `overlap_rows` at k = 64 and 512, decided and projected onto its first, middle and last
    /// atoms: the work of order k, not 2^k (2026-11-13: decided 2.02M and 13.93M, 6.9 times;
    /// projected 1.87M and 10.53M, 5.6 times).
    #[test]
    fn two_overlapping_sums_of_64_and_512_atoms_are_decided_and_projected_in_n_log_n() {
        let inputs = scaling::inputs(1000, |k| overlap_rows(k).formula());
        scaling::check_order("two overlapping sums decided", 1000, 1, |k| {
            assert_eq!(decide(&inputs[&k]), Ok(true));
        });
        scaling::check_order("two overlapping sums projected", 1000, 1, |k| {
            assert_every_hull_non_empty(&inputs[&k], &ends_and_middle(k));
        });
    }

    /// `coefficients_one_and_two` at k = 64 and 512, decided and projected onto its first,
    /// middle and last atoms: the two groups the sums share are joined at once (PRES-overlap-
    /// coeffs). 2026-11-13: decided 167.7M and 76.7M, projected 413.1M and 136.1M; before,
    /// decided 3,873M and projected 7,386M at k = 64, the pairs of the two groups' tables.
    #[test]
    fn two_overlapping_sums_with_coefficients_one_and_two_of_64_and_512_atoms_scale() {
        let inputs = scaling::inputs(1800, |k| coefficients_one_and_two(k).formula());
        scaling::check_order(
            "two sums with coefficients one and two decided",
            1800,
            1,
            |k| {
                assert_eq!(decide(&inputs[&k]), Ok(true));
            },
        );
        scaling::check_order(
            "two sums with coefficients one and two projected",
            1800,
            1,
            |k| {
                assert_every_hull_non_empty(&inputs[&k], &ends_and_middle(k));
            },
        );
    }

    /// A chain of m sums, each sharing three atoms with the next: the groups are joined one
    /// after another, in time linear in m.
    #[test]
    fn a_chain_of_overlapping_sums_is_decided_and_projected_in_n_log_n() {
        let inputs = scaling::inputs(1200, |m| chain(m).formula());
        scaling::check_order("a chain of overlapping sums decided", 1200, 1, |m| {
            assert_eq!(decide(&inputs[&m]), Ok(true));
        });
        scaling::check_order("a chain of overlapping sums projected", 1200, 1, |m| {
            assert_every_hull_non_empty(&inputs[&m], &[v(3 * m / 2)]);
        });
    }

    /// Each side of the switch (`row_sums::JOIN_LIMIT`), measured in instructions against the
    /// solver alone: an unreachable sum of 10 and of 16 atoms, which the join answers and the
    /// solver alone refuses; and the solver's cases, a sum of 8 atoms each in 0..=1e5 or
    /// 2e5..=3e5 and the same with ranges of 1e9 (no plan: a key past 2^62), answered alike
    /// both ways. Measured figures are in the module note of `row_sums`.
    #[test]
    fn each_side_of_the_switch_costs_at_most_a_little_more_than_the_solver_alone() {
        for k in [10, 16] {
            let ((both, with), (alone, without)) =
                both_and_alone(&unreachable(k).formula(), decided);
            assert_eq!((with, without), (Some(false), None));
            assert!(both * 20 < alone, "k = {k}: {both} against {alone}");
        }
        for (what, f) in solver_cases() {
            let ((both, with), (alone, without)) = both_and_alone(&f, projected);
            assert_eq!(with, without, "{what}");
            eprintln!("switchover: {what}: {both} against the solver's {alone}");
            assert!(
                both as f64 <= 1.02 * alone as f64,
                "{what}: {both} against {alone}"
            );
        }
    }

    /// `overlap_rows` at k = 8 and 16 projected by the solver alone (ROW_SUMS_OFF), the path
    /// past the join's limit (PRES-solver-projection-uncounted). No polynomial method exists
    /// (one sum is SUBSET-SUM, proof at `project_each_with`), so this checks only that each
    /// atom gets its exact set or a refusal, and prints the time and work: 2026-11-19, load
    /// about 40, k = 16 took 13.7 to 22.3 s and refused each atom (over 60 s before the
    /// hull search skipped the gap between the two values of each atom).
    #[test]
    fn overlap_rows_by_the_solver_alone() {
        for k in [8, 16] {
            let case = overlap_rows(k);
            let (f, sets) = (case.formula(), case.brute());
            let atoms: Vec<Atom> = (0..k).map(v).collect();
            let mut got = None;
            let t = std::time::Instant::now();
            ROW_SUMS_OFF.with(|o| o.set(true));
            let units = work(|| got = Some(project_each(&f, &atoms)));
            ROW_SUMS_OFF.with(|o| o.set(false));
            let (each, _) = got.expect("an answer").expect("a projection");
            let answered = each.iter().filter(|s| s.is_ok()).count();
            eprintln!(
                "overlap_rows({k}) by the solver alone: {:?}, {units} units, {answered} of {k} atoms answered",
                t.elapsed()
            );
            for (i, (s, want)) in each.iter().zip(&sets).enumerate() {
                if let Ok(s) = s {
                    let (lo, hi) = (
                        want.first().map_or(0, |x| x - 50),
                        want.last().map_or(0, |x| x + 50),
                    );
                    let seen: BTreeSet<i64> = (lo..=hi).filter(|x| s.contains(*x)).collect();
                    assert_eq!(&seen, want, "y{i}: {s:?}");
                }
            }
        }
    }

    /// The 3,000 shared-sum formulas of seed 777 (`decide_sat.rs`): every answer is right and
    /// exact, and no answer is coarser than the solver's alone, with which the first 100 are
    /// compared. Many cases, so a benchmark (author P178);
    /// `disj_groups::row_sums::random_shared_sums_are_answered_and_never_coarser_than_the_solver_alone`
    /// draws 300 of a new seed each run.
    #[test]
    fn the_3000_shared_sums_of_seed_777_are_answered_and_never_coarser_than_the_solver_alone() {
        shared_sums_are_answered(777, 3000, 100);
    }
}

/// The classes of `row_sums::classes` answered where the join does not
/// (PRES-overlap-sums-exact-subclasses), each at n and 8n: forced atoms past the join's limit
/// and scaled atoms with no plan.
mod classes {
    use zed_tests::scaling;
    use zedc::store::presburger::{Atom, JOIN_LIMIT_SET, REDUCED, ReducedBy, project_each};

    use crate::disj_groups::row_sums::classes::{Big, overlap_scaled};
    use crate::disj_groups::row_sums::v;

    /// `n + 1` atoms each in `0..=4` or `8..=12`, and the rows `y_i + 40·y_(i+1) == t_i` of
    /// one point: the coefficient 40 is greater than the width 12 of the term `y_i`, so each
    /// row forces `y_(i+1)`, then `y_0` is forced by the first row.
    fn forced_chain(n: usize) -> Big {
        let p = |i: usize| [1, 9, 3, 12][i % 4];
        Big {
            ranges: vec![vec![(0, 4), (8, 12)]; n + 1],
            rows: (0..n)
                .map(|i| {
                    let mut cs = vec![0; n + 1];
                    cs[i] = 1;
                    cs[i + 1] = 40;
                    (cs, p(i) + 40 * p(i + 1), true)
                })
                .collect(),
        }
    }

    /// Each of `atoms` projected, with the join's limit at `limit`: `by` gave the answer and
    /// each set is a point or not empty.
    fn answered(f: &zedc::store::presburger::Formula, atoms: &[Atom], limit: Option<u64>) {
        JOIN_LIMIT_SET.with(|l| l.set(limit));
        let p = project_each(f, atoms);
        JOIN_LIMIT_SET.with(|l| l.set(None));
        let reduced = REDUCED.with(|r| r.take()).expect("answered by the classes");
        assert_ne!(reduced.by, ReducedBy::NoPoint);
        let (each, _) = p.expect("a projection");
        assert!(each.iter().all(|s| s.as_ref().is_ok_and(|s| !s.is_empty())));
    }

    /// A chain of rows each forcing an atom, past the join's limit (set to 0, so the join
    /// stops at its first step): the forcing passes each term a few times, `O(t log t)`.
    #[test]
    fn a_chain_of_forced_rows_past_the_limit_is_projected_in_n_log_n() {
        let inputs = scaling::inputs(1000, |n| forced_chain(n).formula());
        scaling::check_order("a chain of forced rows projected", 1000, 1, |n| {
            answered(&inputs[&n], &[v(0), v(n / 2), v(n)], Some(0));
        });
    }

    /// `overlap_rows(k)` at k = 8, 12, 16 and 24, by the default path (the join answers) and
    /// past the join's limit (set to 0): the atoms answered and the time of each. No class
    /// takes it (no atom is forced, each atom's one value besides 0 scales it but its rows'
    /// coefficients keep gcd 1, so the keys do not shrink), so past the limit it is the solver
    /// with the cover, which answers each atom with the join's set or refuses it.
    #[test]
    fn overlap_rows_by_the_default_path_and_past_the_limit() {
        for k in [8, 12, 16, 24] {
            let f = crate::disj_groups::row_sums::overlap_rows(k).formula();
            let atoms: Vec<Atom> = (0..k).map(v).collect();
            let t = std::time::Instant::now();
            let (exact, _) = project_each(&f, &atoms).expect("a projection");
            let joined = t.elapsed();
            assert!(exact.iter().all(Result::is_ok), "k = {k}");
            REDUCED.with(|r| r.set(None));
            JOIN_LIMIT_SET.with(|l| l.set(Some(0)));
            let t = std::time::Instant::now();
            let past = project_each(&f, &atoms);
            let past_time = t.elapsed();
            JOIN_LIMIT_SET.with(|l| l.set(None));
            assert_eq!(REDUCED.with(|r| r.take()), None, "k = {k}");
            let answered = match &past {
                Ok((each, _)) => {
                    for (got, want) in each.iter().zip(&exact) {
                        assert!(got.is_err() || got == want, "k = {k}");
                    }
                    each.iter().filter(|s| s.is_ok()).count()
                }
                Err(_) => 0,
            };
            eprintln!(
                "overlap_rows({k}): the join {joined:?}, {k} of {k} atoms; past the limit \
                 {past_time:?}, {answered} of {k} atoms ({:?})",
                past.as_ref().err()
            );
        }
    }

    /// `overlap_rows(k)` with its values times `10^15`, with no plan: scaled, then joined.
    #[test]
    fn overlapping_sums_of_scaled_values_are_projected_in_n_log_n() {
        let inputs = scaling::inputs(128, |k| overlap_scaled(k, 1_000_000_000_000_000).formula());
        scaling::check_order("overlapping sums of scaled values projected", 128, 1, |k| {
            answered(&inputs[&k], &[v(0), v(k / 2), v(k - 1)], None);
        });
    }
}

/// The measurements behind the switch of `row_sums` between the join of row sums, the solver
/// and refusal (PRES-switchover-not-race, author P196/P197, A96): the join's time per unit of
/// its work, which sets `JOIN_LIMIT`, and both sides of the switch on a family where the
/// solver is the faster of the two and one where the join is.
mod switchover {
    use std::time::Instant;

    use zedc::store::presburger::{
        Formula, JOIN_LIMIT, JOINED, ROW_SUMS_JOIN, ROW_SUMS_OFF, decide, project_each, satisfiable,
    };

    use crate::disj_groups::row_sums::*;

    /// k atoms each in `0..=1e9` or `2e9..=3e9`, summing to 1e9 + 7.
    fn wide(k: usize) -> Case {
        Case {
            ranges: vec![vec![(0, 1_000_000_000), (2_000_000_000, 3_000_000_000)]; k],
            rows: vec![(vec![1; k], 1_000_000_007, true)],
        }
    }

    /// k atoms each in `0..=m` or `2m..=3m`, with coefficients the powers of `10m`: every
    /// choice of values gives its own sum, so the join's tables hold `(2m)^(k-1)` intervals,
    /// while the solver splits the target by the coefficients at once.
    fn sparse(k: usize, m: i64) -> Case {
        let g = 10 * m;
        Case {
            ranges: vec![vec![(0, m), (2 * m, 3 * m)]; k],
            rows: vec![((0..k).map(|i| g.pow(i as u32)).collect(), 3 + g * m, true)],
        }
    }

    /// The least time of three runs of `f`, the last answer, and the join's units, with the
    /// join (`join`) or the solver alone; the formula is built before the timer starts.
    fn timed<T>(join: bool, f: impl Fn() -> T) -> (u128, T, Option<(u64, bool)>) {
        ROW_SUMS_OFF.with(|o| o.set(!join));
        ROW_SUMS_JOIN.with(|o| o.set(join));
        let (mut best, mut out) = (u128::MAX, None);
        for _ in 0..3 {
            let t = Instant::now();
            out = Some(std::hint::black_box(f()));
            best = best.min(t.elapsed().as_nanos());
        }
        let joined = JOINED.with(|j| j.take());
        ROW_SUMS_OFF.with(|o| o.set(false));
        ROW_SUMS_JOIN.with(|o| o.set(false));
        (best, out.expect("an answer"), joined)
    }

    /// The join's time per unit on the families of `disj_groups.rs` and the sparse family,
    /// each at a size where the join does at least a million units, so that the reading of
    /// the formula and the other fixed costs do not count (at 10^4 units they are most of the
    /// time: `wide` at k = 32 took 40 ns per unit, a chain of 128 sums 126), each asked for a
    /// point. The worst, times `JOIN_LIMIT`, is the most time a join stopped at the limit
    /// takes; it is checked against twice A99's 250 ms, the factor for the load of the test
    /// machine. Measured 2026-11-14 (Ryzen 9 5950X, load 52): see `JOIN_LIMIT`.
    #[test]
    fn the_join_takes_a_few_nanoseconds_per_unit_of_work() {
        let cases: [(&str, Formula); 4] = [
            ("overlap_rows k=1024", overlap_rows(1024).formula()),
            (
                "coefficients 1, 2 k=512",
                coefficients_one_and_two(512).formula(),
            ),
            ("sparse k=2 m=1e6", sparse(2, 1_000_000).formula()),
            ("sparse k=3 m=300", sparse(3, 300).formula()),
        ];
        let mut worst = 0f64;
        for (name, f) in &cases {
            let (ns, p, joined) = timed(true, || satisfiable(f).map(|m| m.is_some()));
            let (units, answered) = joined.expect("a plan");
            assert!(
                answered && p.is_ok() && units >= 1_000_000,
                "{name}: {units}"
            );
            let per = ns as f64 / units as f64;
            worst = worst.max(per);
            eprintln!("switchover: {name}: {units} units in {ns} ns, {per:.2} ns per unit");
        }
        let most = worst * JOIN_LIMIT as f64 / 1e6;
        eprintln!("switchover: worst {worst:.2} ns per unit; the limit takes at most {most:.0} ms");
        assert!(most <= 500.0, "{most:.0} ms at the limit");
    }

    /// Each question on `f` by the join alone, by the solver alone and by the default path,
    /// with the time of each and whether the default path's join answered (else the solver
    /// answered `decide` and `satisfiable`, and `project_each` with the exact cover).
    fn three_ways<T: PartialEq + std::fmt::Debug>(name: &str, ask: &str, f: impl Fn() -> T) -> T {
        let (join_ns, by_join, _) = timed(true, &f);
        let (solver_ns, by_solver, _) = timed(false, &f);
        let t = Instant::now();
        let by_default = f();
        let default_ns = t.elapsed().as_nanos();
        let (units, joined) = JOINED.with(|j| j.take()).expect("a plan");
        eprintln!(
            "switchover: {name} {ask}: join {join_ns} ns, solver {solver_ns} ns, default \
             {default_ns} ns ({}, {units} units)",
            if joined {
                "the join answered"
            } else {
                "the join stopped"
            }
        );
        if joined {
            assert_eq!(by_default, by_join, "{name} {ask}");
        } else {
            assert_eq!(by_default, by_solver, "{name} {ask}");
        }
        by_join
    }

    /// Both sides of the switch on the sparse family, where the solver is the faster (the join
    /// answers below the limit and stops past it), and the wide family, where the join is
    /// (and the solver's projection is coarser): the join's and the solver's answers to
    /// `decide` and `satisfiable` are equal, and the default path gives the answer of the side
    /// it takes; its projection is the join's exact sets on both sides, past the limit by the
    /// solver with the exact cover (PRES-project-exact-solver; before, `Refusal::Work`), and
    /// the time of each side's projection is printed (A96).
    #[test]
    fn each_side_of_the_switch_gives_the_same_answer_and_the_faster_side_is_measured() {
        for (name, case, k) in [
            ("sparse k=2 m=1e4", sparse(2, 10_000), 2),
            ("sparse k=2 m=1e5", sparse(2, 100_000), 2),
            ("sparse k=2 m=1e6", sparse(2, 1_000_000), 2),
            ("sparse k=3 m=300", sparse(3, 300), 3),
            ("wide k=16", wide(16), 16),
            ("wide k=32", wide(32), 32),
        ] {
            let f = case.formula();
            let atoms: Vec<_> = (0..k).map(v).collect();
            let d = three_ways(name, "decide", || decide(&f));
            let (_, d_alone, _) = timed(false, || decide(&f));
            assert_eq!(d, d_alone, "{name}");
            let p = three_ways(name, "point", || satisfiable(&f).map(|m| m.is_some()));
            let (_, p_alone, _) = timed(false, || satisfiable(&f).map(|m| m.is_some()));
            assert_eq!(p, p_alone, "{name}");
            let ask = || project_each(&f, &atoms).map(|e| e.0);
            ROW_SUMS_JOIN.with(|o| o.set(true));
            let exact = ask();
            ROW_SUMS_JOIN.with(|o| o.set(false));
            let t = Instant::now();
            let by_default = ask();
            let default_ns = t.elapsed().as_nanos();
            let (units, joined) = JOINED.with(|j| j.take()).expect("a plan");
            assert_eq!(by_default, exact, "{name} project, joined {joined}");
            let (solver_ns, by_solver, _) = timed(false, ask);
            assert_eq!(
                by_solver, exact,
                "{name} project by the solver and the cover"
            );
            eprintln!(
                "switchover: {name} project: default {default_ns} ns, solver and cover \
                 {solver_ns} ns, joined {joined}, {units} units"
            );
        }
    }
}

/// One question of [`two_wide_atoms`] for each of its rows, at boxes of half-width 64 and 512:
/// the work of the projection is held to the scaling limit as the ranges widen with no new
/// atom or row (FAIL-scope-chain-scales-bytes, FAIL-join-pair-table). The join of row sums
/// builds a table of every pair of values of `x` and `y`, of order m^2, and stops at its
/// limit at m = 512; the `chain` family of l01_39 asks such a question once per test, so its
/// work grew as k^3.
#[test]
fn two_wide_atoms_are_projected_in_work_that_does_not_grow_with_their_ranges() {
    let m = 64;
    for row in TWO_WIDE_ROWS {
        let (small, ns) = two_wide_atoms(m, row);
        let (large, nl) = two_wide_atoms(scaling::FACTOR as i128 * m, row);
        for (f, n) in [(&small, &ns), (&large, &nl)] {
            let (each, skipped) = project_each(f, n).expect("a projection");
            assert!(
                skipped.is_empty() && each.iter().all(Result::is_ok),
                "{row:?}"
            );
        }
        scaling::check_order(
            &format!("two wide atoms {row:?} projected"),
            m as usize,
            1,
            |k| {
                drop(if k == m as usize {
                    project_each(&small, &ns)
                } else {
                    project_each(&large, &nl)
                });
            },
        );
    }
}
