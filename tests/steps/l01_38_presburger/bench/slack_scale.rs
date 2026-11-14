//! The benchmarks of `slack_scale.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::slack_scale::*;
use zed_tests::scaling;
use zedc::store::interval::IntervalSet;
use zedc::store::presburger::{ROW_SUMS_OFF, Refusal, decide, project_each, satisfiable};

#[test]
fn ss_decide_scales() {
    // Regression check for the round-1 I3 point-loss counterexample: y0 in {0, 101} with
    // w = [101, 104, 107, 110, 113] and t = 214 (= 104 + 110 = 101 + 113) keeps both {0, 101}.
    let i3 = choice_sum(&[101, 104, 107, 110, 113], 214);
    assert_eq!(decide(&i3), Ok(true));
    let (i3_proj, _) = project_each(&i3, &[sym("y0")]).expect("projected");
    assert_eq!(i3_proj[0], Ok(pt_set(&[0, 101])));

    // Immune subset-sum regime (unreachable target near half, zero single-arm refutations).
    // 128, so that the 8 × 128 = 1024 weights of `weights_untied` are distinct: it takes 1027
    // values (the squares mod 2053), and from 1028 weights on equal weights tie the names, which
    // the solver refuses (`Unordered(Tie)`) where this test asks for `Disjuncts`.
    let k_imm = 128;
    let (imm_s, imm_l) = (
        subset_sum_dp(&weights_untied(k_imm)),
        subset_sum_dp(&weights_untied(scaling::FACTOR * k_imm)),
    );
    // The solver alone refuses both sizes. The join of row sums (module `row_sums`) answers both
    // exactly: the target is unreachable by construction. Its cost relative to the solver's
    // depends on which side of the race wins at each size, so the order is checked on the
    // solver alone, and the method is held to the solver's cost at each size.
    assert_eq!(decide(&imm_s), Ok(false));
    assert_eq!(decide(&imm_l), Ok(false));
    assert_eq!(decided_alone(&imm_s), Err(Refusal::Disjuncts));
    assert_eq!(decided_alone(&imm_l), Err(Refusal::Disjuncts));
    scaling::check_order(
        "decide: ss_untied immune, the solver alone",
        k_imm,
        1,
        |m| {
            drop(decided_alone(if m == k_imm { &imm_s } else { &imm_l }));
        },
    );
    let mut meter = scaling::Meter::new();
    for f in [&imm_s, &imm_l] {
        let with = meter.work(|| drop(decide(f))).units;
        let without = meter.work(|| drop(decided_alone(f))).units;
        assert!(
            with as f64 <= 1.02 * without as f64,
            "{with} with the method against {without} alone"
        );
    }

    // Forced-cascade subset-sum regime (unreachable target sum - gap with gap in 4500..5052
    // outside w, refuting ~27% of y_i == 0 arms in round 1 while leaving ~73% unforced,
    // exercising learn + settle + WidePointRepairer + unit-equation search).
    let k = 64;
    let (cas_s, cas_l) = (cascade(k), cascade(scaling::FACTOR * k));
    assert_eq!(decide(&cas_s), Ok(false));
    assert_eq!(decide(&cas_l), Ok(false));
    scaling::check_order("decide: ss_untied cascade", k, 1, |m| {
        drop(decide(if m == k { &cas_s } else { &cas_l }));
    });

    // Original ss weights (tied at 8k = 512).
    let (ss_s, ss_l) = (
        subset_sum_dp(&weights(k)),
        subset_sum_dp(&weights(scaling::FACTOR * k)),
    );
    // Unreachable by construction; the solver alone refuses both sizes.
    assert_eq!(decide(&ss_s), Ok(false));
    assert_eq!(decide(&ss_l), Ok(false));
    scaling::check_order("decide: ss", k, 1, |m| {
        drop(decide(if m == k { &ss_s } else { &ss_l }));
    });
}

#[test]
fn ss_project_scales() {
    let k = 910;
    let y0 = [sym("y0")];
    let (ss_s, ss_l) = (
        subset_sum_dp(&weights(k)),
        subset_sum_dp(&weights(scaling::FACTOR * k)),
    );
    let (p_s, _) = project_each(&ss_s, &y0).expect("ss project, small");
    let (p_l, _) = project_each(&ss_l, &y0).expect("ss project, large");
    // The target is unreachable by construction, so the exact projection is empty; the solver
    // alone gives {0, 1000} and {1000}.
    assert_eq!(p_s[0], Ok(IntervalSet::empty()));
    assert_eq!(p_l[0], Ok(IntervalSet::empty()));
    // The large size has ties (from k = 497), so it is answered by the tied path, which is
    // cheaper than the untied one at k = 64: this compares two paths, not one at n and 8n.
    // Untied subset sums are not near linear here: `ss_untied` project_each costs 5.4G
    // instructions at k = 64, 11.1G at 128 and over 60 s at 256 (round 5, Claude).
    scaling::check_order("project_each: ss", k, 1, |m| {
        drop(project_each(if m == k { &ss_s } else { &ss_l }, &y0));
    });
}

#[test]
fn sat_half_decide_scales() {
    let k = 720;
    let build_tied = |n: usize| half_sum(&weights(n));
    let (t_s, t_l) = (build_tied(k), build_tied(scaling::FACTOR * k));
    for f in [&t_s, &t_l] {
        assert_eq!(decide(f), Ok(true));
        let m = satisfiable(f).expect("decided").expect("satisfiable");
        assert!(f.holds(&m));
    }
    scaling::check_order("decide: sat_half", k, 1, |m| {
        drop(decide(if m == k { &t_s } else { &t_l }));
    });

    let build_u = |n: usize| half_sum(&weights_untied(n));
    let (small, large) = (build_u(k), build_u(scaling::FACTOR * k));
    // The target is a sum of weights by construction; the solver alone refuses both sizes, and
    // the join of row sums (module `row_sums`) answers them.
    assert_eq!(decide(&small), Ok(true));
    assert_eq!(decide(&large), Ok(true));
    scaling::check_order("decide: sat_half_untied", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
}

#[test]
fn sat_half_tied_512_is_deterministic_and_scales() {
    let k = 670;
    let y0 = [sym("y0")];
    let build = |n: usize| half_sum(&weights(n));
    let (small, large) = (build(k), build(scaling::FACTOR * k));
    assert_eq!(decide(&small), Ok(true));
    assert_eq!(decide(&large), Ok(true));
    let (p_s, _) = project_each(&small, &y0).expect("sat_half project, small");
    let (p_l, _) = project_each(&large, &y0).expect("sat_half project, large");
    assert_eq!(p_s[0], Ok(pt_set(&[0, 1000])));
    assert_eq!(p_l[0], Ok(pt_set(&[0, 1000])));

    let (rev_l, rev_y0) = reverse_renamed(&large, &y0[0]);
    assert_eq!(decide(&rev_l), Ok(true));
    let (rev_p, _) = project_each(&rev_l, &[rev_y0]).expect("renamed sat_half project, large");
    assert_eq!(p_l[0], rev_p[0]);

    scaling::check_order("project_each: sat_half", k, 1, |m| {
        drop(project_each(if m == k { &small } else { &large }, &y0));
    });

    let build_u = |n: usize| half_sum(&weights_untied(n));
    let (u_s, u_l) = (build_u(k), build_u(scaling::FACTOR * k));
    let (pu_l, _) = project_each(&u_l, &y0).expect("sat_half_untied project, large");
    assert_eq!(pu_l[0], Ok(pt_set(&[0, 3000])));
    scaling::check_order("project_each: sat_half_untied", k, 1, |m| {
        drop(project_each(if m == k { &u_s } else { &u_l }, &y0));
    });
}

#[test]
fn two_rows_scales() {
    let k = 690;
    let y0 = [sym("y0")];
    let u_8 = build_two_rows(&weights_untied(8));
    assert_eq!(decide(&u_8), Ok(true));
    let (u_s, u_l) = (
        build_two_rows(&weights_untied(k)),
        build_two_rows(&weights_untied(scaling::FACTOR * k)),
    );
    // Satisfiable by construction; the solver alone refuses k = 64.
    assert_eq!(decide(&u_s), Ok(true));
    assert_eq!(decide(&u_l), Ok(true));
    let m_l = satisfiable(&u_l).expect("decided").expect("satisfiable");
    assert!(u_l.holds(&m_l));
    let (pu_l, _) = project_each(&u_l, &y0).expect("two_rows_untied project, large");
    assert!(pu_l[0].as_ref().expect("interval").contains(3000));
    scaling::check_order("decide: two_rows_untied", k, 1, |m| {
        drop(decide(if m == k { &u_s } else { &u_l }));
    });
    scaling::check_order("project_each: two_rows_untied", k, 1, |m| {
        drop(project_each(if m == k { &u_s } else { &u_l }, &y0));
    });

    let t_8 = build_two_rows(&weights(8));
    assert_eq!(decide(&t_8), Ok(true));
    let (t_s, t_l) = (
        build_two_rows(&weights(k)),
        build_two_rows(&weights(scaling::FACTOR * k)),
    );
    assert_eq!(decide(&t_s), Ok(true));
    assert_eq!(decide(&t_l), Ok(true));
    scaling::check_order("decide: two_rows", k, 1, |m| {
        drop(decide(if m == k { &t_s } else { &t_l }));
    });
    let (pt_l, _) = project_each(&t_l, &y0).expect("two_rows project, large");
    assert!(pt_l[0].as_ref().expect("interval").contains(1000));
    scaling::check_order("project_each: two_rows", k, 1, |m| {
        drop(project_each(if m == k { &t_s } else { &t_l }, &y0));
    });
}

#[test]
fn paired_chain_project_scales() {
    let k = 19000;
    let y0 = [sym("y0")];
    let (small, large) = (
        build_paired_chain(k),
        build_paired_chain(scaling::FACTOR * k),
    );
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(false));
        let (p, _) = project_each(f, &y0).expect("paired_chain project");
        assert_eq!(p[0], Ok(IntervalSet::empty()));
    }
    scaling::check_order("decide: paired_chain", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
    scaling::check_order("project_each: paired_chain", k, 1, |m| {
        drop(project_each(if m == k { &small } else { &large }, &y0));
    });
}

#[test]
fn alternating_weights_greedy_scales() {
    let k = 980;
    let y0 = [sym("y0")];
    let (small, large) = (build_alternating(k), build_alternating(scaling::FACTOR * k));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true));
        let (p, _) = project_each(f, &y0).expect("alternating project");
        assert!(p[0].as_ref().expect("interval").contains(1));
    }
    scaling::check_order("decide: alternating_weights", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
    scaling::check_order("project_each: alternating_weights", k, 1, |m| {
        drop(project_each(if m == k { &small } else { &large }, &y0));
    });
}

#[test]
fn dense_scales() {
    let k = 840;
    let y0 = [sym("y0")];
    let (small, large) = (build_dense(k), build_dense(scaling::FACTOR * k));
    for f in [&small, &large] {
        assert_eq!(decide(f), Ok(true));
    }
    scaling::check_order("decide: dense", k, 1, |m| {
        drop(decide(if m == k { &small } else { &large }));
    });
    scaling::check_order("project_each: dense", k, 1, |m| {
        drop(project_each(if m == k { &small } else { &large }, &y0));
    });
}

/// I22: neither size has repeated weights. The old survivor's endpoint query was followed
/// by logarithmically many whole-formula questions even though its probe was immune.
#[test]
fn untied_projection_uses_the_endpoint_report() {
    let k = 512;
    let small = subset_sum_dp(&weights_untied(k));
    let large = subset_sum_dp(&weights_untied(8 * k));
    let y0 = [sym("y0")];
    let red = std::env::var_os("PDCX_RED").is_some();
    // The solver alone: the join of row sums (module `row_sums`) answers both sizes exactly with
    // the empty set, since the target is unreachable, and the endpoint report is not reached.
    scaling::check_order("I22 untied endpoint reports", k, 1, |m| {
        ROW_SUMS_OFF.with(|o| o.set(true));
        zedc::store::presburger::HULL_BISECT.with(|c| c.set(red));
        let got = project_each(if m == k { &small } else { &large }, &y0).expect("projection");
        assert!(got.0[0].as_ref().expect("set").contains(3000));
        zedc::store::presburger::HULL_BISECT.with(|c| c.set(false));
        ROW_SUMS_OFF.with(|o| o.set(false));
    });
    scaling::check_order("I22 untied, with the method", k, 1, |m| {
        let got = project_each(if m == k { &small } else { &large }, &y0).expect("projection");
        assert_eq!(got.0[0], Ok(IntervalSet::empty()));
    });
}

/// I22's large tied path is checked independently of the first collision at k=497.
#[test]
fn tied_projection_endpoint_reports_scale_past_512() {
    let k = 512;
    let small = subset_sum_dp(&weights(k));
    let large = subset_sum_dp(&weights(8 * k));
    let y0 = [sym("y0")];
    // The solver alone, as in the untied test above.
    scaling::check_order("I22 tied endpoint reports", k, 1, |m| {
        ROW_SUMS_OFF.with(|o| o.set(true));
        let got = project_each(if m == k { &small } else { &large }, &y0).expect("projection");
        assert_eq!(got.0[0], Ok(pt_set(&[1000])));
        ROW_SUMS_OFF.with(|o| o.set(false));
    });
    scaling::check_order("I22 tied, with the method", k, 1, |m| {
        let got = project_each(if m == k { &small } else { &large }, &y0).expect("projection");
        assert_eq!(got.0[0], Ok(IntervalSet::empty()));
    });
}

/// `project_each` of `y0` on `ss` at `k = 64` costs at most 4 times `decide` on the same formula.
/// The hull of `y0` is the two points {0, 1000}, and the question at each end is refused at full
/// cost, so `Hull::tighten` must not halve the integers between them: halving asked about 11
/// refused questions per end and cost 4,616M instructions against 440M with the returned endpoint
/// report (round 6), with `decide` at about 348M. Negative control: `presburger::HULL_BISECT` set
/// on this thread brings the halving back, and the same limit then fails. Counts of processor
/// time vary too much with load for a limit of 4, so on a machine that cannot count instructions
/// this measures nothing. (Claude round 6, carried onto the round-6 tree.)
#[test]
fn ss_project_each_costs_at_most_four_decides() {
    use zed_tests::scaling::Meter;
    use zedc::store::presburger::HULL_BISECT;
    let mut meter = Meter::new();
    if meter.unit() != "instructions" {
        return;
    }
    // The solver alone: with the join of row sums (module `row_sums`) the questions the
    // halving asks are narrow enough for it, and q is the exact empty set.
    ROW_SUMS_OFF.with(|o| o.set(true));
    let f = subset_sum_dp(&weights(64));
    let y0 = [sym("y0")];
    let least = |meter: &mut Meter, run: &dyn Fn()| {
        (0..2)
            .map(|_| meter.work(run).units)
            .min()
            .expect("two runs")
    };
    let d = least(&mut meter, &|| drop(std::hint::black_box(decide(&f))));
    let reported = least(&mut meter, &|| {
        drop(std::hint::black_box(project_each(&f, &y0)))
    });
    let (p, _) = project_each(&f, &y0).expect("ss 64 project");
    HULL_BISECT.with(|c| c.set(true));
    let halved = least(&mut meter, &|| {
        drop(std::hint::black_box(project_each(&f, &y0)))
    });
    let (q, _) = project_each(&f, &y0).expect("ss 64 project, halving");
    HULL_BISECT.with(|c| c.set(false));
    // The endpoint report is never coarser than the halving on this formula.
    assert!(
        p[0].as_ref()
            .ok()
            .zip(q[0].as_ref().ok())
            .is_some_and(|(p, q)| p.is_subset(q))
    );
    ROW_SUMS_OFF.with(|o| o.set(false));
    let (with, _) = project_each(&f, &y0).expect("ss 64 project, with the method");
    assert!(
        with[0]
            .as_ref()
            .ok()
            .zip(p[0].as_ref().ok())
            .is_some_and(|(w, p)| w.is_subset(p)),
        "{with:?} against {p:?}"
    );
    assert!(
        reported <= 4 * d,
        "project_each {reported} > 4 x decide {d} instructions"
    );
    assert!(
        halved > 4 * d,
        "negative control: halving cost {halved} <= 4 x decide {d} instructions"
    );
}

/// `check_order` of `project_each` of `y0` on `sat_half` at 512 and 4,096: 1,249M and 10,796M
/// instructions on the round-6 tree. (Claude round 6.)
#[test]
fn sat_half_project_each_scales_past_512() {
    let k = 2260;
    let y0 = [sym("y0")];
    let build = |n: usize| half_sum(&weights(n));
    let (s, l) = (build(k), build(scaling::FACTOR * k));
    scaling::check_order("project_each: sat_half past 512", k, 1, |m| {
        drop(project_each(if m == k { &s } else { &l }, &y0));
    });
}

/// Negative control for the scaling checks above: `build_many_linked`, whose `project_each` by
/// the solver alone is not near linear (175M and 4,963M instructions at 64 and 512 in round 6,
/// over 60 s at 4,096), fails the same limit on instructions (its bytes grow 13.9 times, too
/// near the limit of 13.2 to test). If this test stops panicking, the solver has become near
/// linear on this family, or the check has stopped measuring. (Claude round 6.)
#[test]
#[should_panic(expected = "times the work")]
fn many_linked_rows_project_each_fails_the_order_check() {
    let k = 64;
    let y0 = [sym("y0")];
    let (s, l) = (build_many_linked(k), build_many_linked(scaling::FACTOR * k));
    // The solver alone, set on the thread each run is measured on: the join of row sums (module
    // `row_sums`) makes this family near linear, as
    // `many_linked_rows_project_each_scales_with_the_method` checks.
    scaling::check_instructions_only("project_each: many linked rows", k, 1, |m| {
        ROW_SUMS_OFF.with(|o| o.set(true));
        drop(project_each(if m == k { &s } else { &l }, &y0));
        ROW_SUMS_OFF.with(|o| o.set(false));
    });
}

/// The same family with the join of row sums (module `row_sums`): the first row forces
/// `y0 = w_0 = 1000` and `y1 = 0`, since `w_1 = 1037`, and the inequality holds whenever a value
/// is 0, so `y0` is exactly {1000}; `project_each` is near linear.
#[test]
fn many_linked_rows_project_each_scales_with_the_method() {
    let k = 1000;
    let y0 = [sym("y0")];
    let (s, l) = (build_many_linked(k), build_many_linked(scaling::FACTOR * k));
    scaling::check_order(
        "project_each: many linked rows, with the method",
        k,
        1,
        |m| {
            let got = project_each(if m == k { &s } else { &l }, &y0).expect("projection");
            assert_eq!(got.0[0], Ok(pt_set(&[1000])));
        },
    );
}
