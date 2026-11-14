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
#[test]
fn the_must_assign_check_scales() {
    for (what, make, row) in must_assign_cases() {
        let units = scaling::inputs(500, |n| parsed(make(n)));
        scaling::check(what, 500, |n| must_assign_verdict(what, &units[&n], row));
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
