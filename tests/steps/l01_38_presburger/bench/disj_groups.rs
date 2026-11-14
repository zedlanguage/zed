//! The benchmarks of `disj_groups.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::disj_groups::*;
use zed_tests::scaling;

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

/// At 512 stages, where the limit, 11.7 times, is below the 12.13 times of work of order n^1.2;
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

    use zed_tests::scaling::{self};
    use zedc::store::presburger::decide;

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

    /// Each way the race goes, measured in instructions against the solver alone
    /// (2026-11-13, figures at the rate of 2048):
    /// - the method answers in its run first, before the solver starts: an unreachable sum of 10
    ///   atoms, 0.22M against the solver's refusal at 57.0M, and of 16 atoms, 0.36M against
    ///   91.2M (of 32 atoms, 0.63M against 178.6M);
    /// - the solver answers: a sum of 8 atoms, each in 0..=1e5 or 2e5..=3e5, at most 200,003,
    ///   projected, 13.57M against 13.55M;
    /// - ranges of 1e9 values, where the method does not answer: 128.0M against 128.2M.
    ///
    /// The branches of the race itself are tested with a stand-in method and solver in
    /// `row_sums::tests::each_branch_of_the_race`.
    #[test]
    fn each_way_the_race_goes_costs_at_most_a_little_more_than_the_solver_alone() {
        let ((both, with), (alone, without)) = both_and_alone(&unreachable(10).formula(), decided);
        assert_eq!((with, without), (Some(false), None));
        assert!(both * 20 < alone, "first run: {both} against {alone}");
        let ((both, with), (alone, without)) = both_and_alone(&unreachable(16).formula(), decided);
        assert_eq!((with, without), (Some(false), None));
        assert!(both * 20 < alone, "first run: {both} against {alone}");
        for (what, f) in solver_cases() {
            let ((both, with), (alone, without)) = both_and_alone(&f, projected);
            assert_eq!(with, without, "{what}");
            assert!(
                both as f64 <= 1.02 * alone as f64,
                "{what}: {both} against {alone}"
            );
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
