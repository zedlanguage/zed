//! The benchmarks of `factored::tests`, run by `tools/run_tests.sh --bench` and left out of its
//! default run. Each checks the measured work at n and 8n against the limit 10.5
//! (`crate::scaling`). Their negative control is the count of every pair (what `products`
//! listed before the factored solver), which grows 64 times on the same family
//! (`no_pair_of_the_star_is_listed_and_the_work_scales`), and the red run of
//! `entails::bench_entails_on_the_star`: the same file run on the code before the solver.
//! On `wlgrow` the exact peel grows 47 times at 8 times the input (exception 3 of the design,
//! COMPLEXITY.md, the A225 entry), all of it output: `bench_factored_peel_on_wlgrow` holds the
//! solver there to the limit in the measure of input and output.

use super::*;

mod entails;

/// `products`' pair search end to end on [`star`]: k rows on each factor, no pair kept.
#[test]
fn bench_factored_star() {
    crate::scaling::check_inputs(
        "factored kept_pairs on the star",
        2000,
        star,
        |(rows, on, wanted, partners)| {
            let rows: Vec<&Lin> = rows.iter().collect();
            assert!(super::super::kept_pairs(&rows, on, wanted, partners).is_empty());
        },
    );
}

/// PERF-factored-peel-wlisted, by instructions: the whole solver (count rules, worklist and
/// exact peel) on wlgrow at l = 10 and l = 17, where the input and output k + W_R grows about 8
/// times, is held to the limit 10.5 of work of order n in that measure, in instructions (each
/// size in a new process, `scaling::compare_fresh`). At l = 10, 17 and 28 the peel drops no
/// pair (the pairs left equal those left without the peel), so the incidences it lists,
/// W_listed, are W_R, the terms `products` writes. Control: at l = 28, where the input grows
/// about 8 times over l = 10 but the output 52 times, the same work grows past 10.5, measured
/// by this thread's meter (processor time where the machine has no counter of instructions:
/// 32.82 times on l43, 2026-11-24).
#[test]
fn bench_factored_peel_on_wlgrow() {
    let mut meter = crate::scaling::Meter::new();
    let mut runs = Vec::new();
    for l in [10, 17, 28] {
        let p = build_wlgrow(l, l, false);
        let mut out = None;
        let work = meter.work(|| out = Some(solve(&p, Opts::default())));
        let out = out.expect("the run");
        let ctrl = solve(
            &p,
            Opts {
                no_peel: true,
                ..Opts::default()
            },
        );
        assert_eq!(
            out.left, ctrl.left,
            "l = {l}: the peel drops no pair on wlgrow"
        );
        let (k, w_r) = (size(&p), incidences(&p, &out.left));
        eprintln!(
            "wlgrow l={l}: size {k}, W_R {w_r}, single {}, {} {}",
            out.single, work.units, meter.unit
        );
        runs.push((k, k + w_r, work.units));
    }
    let grew = runs[1].1 as f64 / runs[0].1 as f64;
    assert!(
        (6.5..9.5).contains(&grew),
        "k + W_R grows {grew:.2} times from l = 10 to 17, not about 8"
    );
    let input = runs[2].0 as f64 / runs[0].0 as f64;
    let control = runs[2].2 as f64 / runs[0].2 as f64;
    eprintln!(
        "control: l 10 to 28, input {input:.2} times, {control:.2} times the {}",
        meter.unit
    );
    assert!(
        control > crate::scaling::LIMIT,
        "the control (l = 28 against 10, input {input:.2} times) grew only {control:.2} times"
    );
    crate::scaling::compare_fresh(
        "the factored solver on wlgrow, l 10 and 17 (k + W_R about 8 times)",
        1,
        (10, 17),
        |l, _| build_wlgrow(l, l, false),
        |_, p| solve(&p, Opts::default()),
    );
}
