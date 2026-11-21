//! Cycles and calls of `n` overloads, at `n` and `8n` (`overload_cycles.rs`).

use zed_tests::scaling;

use crate::overload_cycles::*;

/// One cycle of n overloads (each overload has a type of its own, `int | #t0`, `int | #t1`,
/// …, since a scope declares a function once for each list of parameter types), ordered and
/// reported. Each call is matched to its overload through an index by argument place and
/// carrier, `O(n log n)` in all; testing each call against each overload would be `O(n^2)`.
#[test]
fn a_cycle_through_n_overloads_scales() {
    let n = 11_000;
    let units = scaling::inputs(n, a_cycle_of_overloads);
    scaling::check_order("a cycle through n overloads", n, 1, |k| {
        the_cycle_of_overloads_reported(&units[&k], k);
    });
}

/// n rejections, each copying a string of the program that holds `$0` (row
/// FAIL-msg-named-reads-program-text): one lexing of the program and, for each text of a
/// message, one lookup per distinct length of a piece at each `"` or `/` (`ProgramTexts` in
/// zedc-check mod.rs), `O(N)` in all here, where the pieces have one length.
#[test]
fn quoting_n_strings_that_hold_a_dollar_scales() {
    let n = 200;
    let units = scaling::inputs(n, dollar_strings);
    scaling::check("quoting n strings that hold `$0`", n, |k| {
        the_dollar_strings_quoted(&units[&k], k);
    });
}

/// n overloads and n definitions each calling one of them: a chain with no cycle, and n calls
/// that two or more overloads admit, which refer to none.
#[test]
fn n_calls_of_n_overloads_scale() {
    let n = 4800;
    let units = scaling::inputs(n, calls_of_overloads);
    scaling::check_order("n calls of n overloads", n, 1, |k| {
        the_calls_of_overloads_ordered(&units[&k], k);
    });
}
