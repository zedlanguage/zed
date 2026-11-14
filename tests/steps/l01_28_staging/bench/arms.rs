//! The work counts and the scaling check of `arms.rs`. Each input is built before the timing.

use zed_tests::scaling::{self, Meter};
use zedc::run::load;

use crate::arms::{cut_reads_loaded, mixed_from, staging_work, stopped_each, stopped_read_by};

/// DESIGN step L1.28: an evaluation that stops leaves the term to run whole, and the name it
/// binds becomes run-stage, so nothing evaluates it twice. The evaluations are counted by
/// their work: the stop of `huge` costs about 6.8 million instructions, and 8 readers of it
/// cost about 0.5 million more than one (measured 2026-11-11); were each reader to evaluate
/// `huge` again, 7 more readers would cost 7 stops more.
#[test]
fn a_stopped_binding_read_twice_is_evaluated_once() {
    let mut meter = Meter::new();
    let [one, eight] = [1, 8].map(|k| load(stopped_read_by(k).as_bytes()).unwrap());
    let [each_one, each_two] = [1, 2].map(|k| load(stopped_each(k).as_bytes()).unwrap());
    let (one, eight) = (
        staging_work(&mut meter, &one),
        staging_work(&mut meter, &eight),
    );
    let stop = staging_work(&mut meter, &each_two) - staging_work(&mut meter, &each_one);
    assert!(
        eight - one < stop / 2,
        "8 readers of one stopped binding cost {} {unit} more than 1 reader; one more stop costs \
         {stop}",
        eight - one,
        unit = meter.unit()
    );
}

/// Keeping cut reads stays O(N log N) in the unit's size with many roots and many definitions
/// left to run: every `g{i}` and `main` a root, `n` definitions left, each kept by one read
/// (COMPLEXITY.md row of `keep_cut_reads`). Units are elaborated before timing; `arms.rs`
/// checks what is kept at small sizes.
#[test]
fn cut_reads_are_kept_in_time_that_scales() {
    let n = 600;
    let units = scaling::inputs(n, cut_reads_loaded);
    let (_, report) = mixed_from(&units[&n]);
    assert_eq!(report.left.len(), n, "{:?}", report.left);
    scaling::check("keeping the cut reads of n left definitions", n, |k| {
        std::hint::black_box(mixed_from(&units[&k]));
    });
}
