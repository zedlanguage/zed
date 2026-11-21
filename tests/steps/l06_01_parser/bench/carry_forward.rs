//! The checks of recurrences and `with carryForward` in time of order `n log n`: the benchmarks
//! of `carry_forward.rs`, whose tests make each check of each input at small sizes. Each input
//! is lexed and parsed before timing.

use zed_tests::scaling;

use crate::carry_forward::{
    carry_word, carry_word_refused, dot_call_notes, dot_calls, for_each_key_cases,
    for_each_key_verdict, must_assign_cases, must_assign_verdict,
};
use crate::initial::parsed;

/// The message for a word after `with` scans the statement and parses the repair once, so a
/// loop of `n` statements whose `initial` value has `n` terms is refused in time of order `n`.
#[test]
fn the_carry_word_message_scales() {
    let units = scaling::inputs(500, carry_word);
    scaling::check("a word after `with`", 500, |n| {
        carry_word_refused(&units[&n])
    });
}

/// The must-assign check is one walk of the body with sets merged smaller into larger, so `n`
/// variables updated each on its own paths, `n` variables updated on both branches of one `if`,
/// directly or in nested blocks, an update `n` constructs or blocks deep, `n` keyed writes in the
/// value of one indexed definition, with or without `n` domains of one key, a write `n` indexed
/// definitions deep, and a write whose key holds a `*.` call at each of `n` levels are each
/// checked in time of order `n log n`, accepted or refused. `n` calls on paths of fields and
/// entries, and `n` calls on the names of `n` imported units, which one pass over the tokens
/// lists, are too.
///
/// One test for each case of [`must_assign_cases`] (TEST-split-chkbub1-long). Until then the
/// 18 cases were one test, which took 51 s at load 23 and 34 s at load 13 in main-watch's runs
/// of 2026-11-21: on a count of instructions the run at 8n of each check runs in a new process
/// of the test binary, which runs the test from its start, building each earlier case's input
/// and replaying its check at both sizes (`scaling::compare_by`), so 18 checks in one test ran
/// 18 · 19 / 2 = 171 checks' runs and input builds where 18 do. The cases, sizes and verdicts
/// are as before.
mod the_must_assign_check_scales {
    use super::*;

    /// The case at place `k` of [`must_assign_cases`], which must be the one named `what` (so a
    /// test runs the case its name says), at n 500 and 8n. The length 18 is the number of tests
    /// below: a case added to the list changes it, and this fails to compile until the case has
    /// a test of its own.
    fn case(k: usize, what: &str) {
        let cases: [_; 18] = must_assign_cases();
        let (name, make, row) = cases[k];
        assert_eq!(name, what, "must_assign_cases()[{k}]");
        let units = scaling::inputs(500, |n| parsed(make(n)));
        scaling::check(what, 500, |n| must_assign_verdict(what, &units[&n], row));
    }

    #[test]
    fn fields_accepted() {
        case(0, "fields, accepted");
    }

    #[test]
    fn fields_refused_at_the_end() {
        case(1, "fields, refused at the end");
    }

    #[test]
    fn qualified_names_accepted() {
        case(2, "qualified names, accepted");
    }

    #[test]
    fn wide_accepted() {
        case(3, "wide, accepted");
    }

    #[test]
    fn wide_refused_at_the_end() {
        case(4, "wide, refused at the end");
    }

    #[test]
    fn branches_accepted() {
        case(5, "branches, accepted");
    }

    #[test]
    fn deep_refused() {
        case(6, "deep, refused");
    }

    #[test]
    fn deep_carried() {
        case(7, "deep, carried");
    }

    #[test]
    fn nested_branches_accepted() {
        case(8, "nested branches, accepted");
    }

    #[test]
    fn nested_branches_refused_at_the_end() {
        case(9, "nested branches, refused at the end");
    }

    #[test]
    fn nested_blocks_accepted() {
        case(10, "nested blocks, accepted");
    }

    #[test]
    fn nested_blocks_refused() {
        case(11, "nested blocks, refused");
    }

    #[test]
    fn keyed_writes_accepted() {
        case(12, "keyed writes, accepted");
    }

    #[test]
    fn keyed_writes_refused_at_the_end() {
        case(13, "keyed writes, refused at the end");
    }

    #[test]
    fn nested_keys_accepted() {
        case(14, "nested keys, accepted");
    }

    #[test]
    fn nested_keys_refused() {
        case(15, "nested keys, refused");
    }

    #[test]
    fn keyed_writes_after_one_key_domains_accepted() {
        case(16, "keyed writes after one-key domains, accepted");
    }

    #[test]
    fn calls_in_keys_at_each_level_refused() {
        case(17, "calls in keys at each level, refused");
    }
}

/// The `.` call notes cost one walk of the method declarations, one lookup per call and one
/// more walk of the step for the repair: `n` methods and `n` calls of them are refused in time
/// of order `n log n`.
#[test]
fn the_dot_call_notes_scale() {
    let units = scaling::inputs(500, |n| parsed(dot_calls(n)));
    scaling::check("dot calls, refused", 500, |n| dot_call_notes(&units[&n], n));
}

/// The checks of writes in code run for each key cost one walk of the step: `n` `for` bodies
/// with keyed writes, accepted or refused at the end; a write under `n` binders that hide its
/// key, whose repair renames each; and `n` `.` calls each made once before its definition, each
/// with a new name, are each checked in time of order `n log n`.
#[test]
fn writes_run_for_each_key_scale() {
    for (what, make, row, fixed) in for_each_key_cases() {
        let units = scaling::inputs(500, |n| parsed(make(n)));
        scaling::check(what, 500, |n| {
            for_each_key_verdict(what, &units[&n], row, fixed, n)
        });
    }
}
