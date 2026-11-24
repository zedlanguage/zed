use zed_tests::scaling;
use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::super::lit_branches::{nest, summed_ifs, wide_branch};

#[test]
fn scaling() {
    // Complexity tradeoff (DESIGN.md Part G): the branches are read once, each adopts once,
    // and their singletons are joined in pairs, O(n log n); joined one at a time, each union
    // copies the type so far, O(n^2). The small instance is
    // `an_if_of_many_literal_branches_takes_f64_at_a_parameter`.
    scaling::on_a_thread(1 << 29, || {
        let n = 880;
        let units = scaling::inputs(n, |m| Resolved::new(&nest(m)));
        scaling::check("checking an `if` of n literal branches at `f64`", n, |m| {
            units[&m].check();
        });
    });
}

/// A sum of `n` `if`s, each `if c { 1 / 2 } else { 1.5 }`: each `if` notes its first branch
/// as rejected alone (`Ck::note_alone`), and the `n` notes move with the classes as they join,
/// the smaller list into the larger (`Ck::merge`), O(n log n); the one rejection then takes
/// the earliest note and the first literal in it, one pass over the notes and the literals
/// (`Ck::lits_take`); its fixes then sort the notes once and look each literal up by one
/// binary search, to drop the `rat` fix a sum of `if`s refuses (`Ck::resolve`, row
/// MSG-branch-sum-fix-unchecked), O((n + l) log n). At `x: f64` the same notes are kept and
/// never read. Measured at
/// n = 500 and 4,000: 8.01 times at both. Negative control (run once, not committed): the
/// merge copying the whole list once per note it holds, O(n²), ran past the piece's limit.
///
/// Besides its ratio: one rejection without `x`, none at `x: f64`. Small instance:
/// `lit_branches::many_divisions_beside_decimals_are_rejected_once`.
#[test]
fn a_sum_of_many_divisions_beside_decimals_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        for x in [None, Some("f64")] {
            // Each program is resolved only in the process that checks it, and the count of
            // rejections is asserted on what each run finds (`scaling::check_inputs`;
            // FAIL-bench-first-phase-past-20s-l0126-l0129).
            let unit = |m: usize| Resolved::new(&summed_ifs(m, x));
            let what = format!("checking a sum of n `if`s of a division and a decimal at {x:?}");
            scaling::check_inputs(&what, n, unit, |u| {
                let errors = u.type_errors();
                assert_eq!(errors.len(), usize::from(x.is_none()));
                std::hint::black_box(errors);
            });
        }
    });
}

/// One `if` whose first branch is a sum of `n` divisions `1 / 2`, beside a decimal: one note,
/// whose literals are walked once for the first (`Ck::lits_take`).
///
/// Besides its ratio: one rejection. Small instance:
/// `lit_branches::many_divisions_beside_decimals_are_rejected_once`.
#[test]
fn a_wide_branch_of_divisions_beside_a_decimal_scales() {
    scaling::on_a_thread(1 << 29, || {
        let n = 500;
        let units = scaling::inputs(n, |m| Resolved::new(&wide_branch(m)));
        for u in units.values() {
            assert_eq!(u.type_errors().len(), 1);
        }
        scaling::check(
            "rejecting an `if` of n divisions beside a decimal",
            n,
            |m| {
                std::hint::black_box(units[&m].type_errors());
            },
        );
    });
}
