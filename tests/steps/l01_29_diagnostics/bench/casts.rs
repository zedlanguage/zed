//! The cast menus of `casts.rs` at `n` and `8n`, and their cost beside a program `8` times as
//! large (CAST-menu, MSG-cast-repair-parens, K41). The texts at small sizes are held by the
//! tests of `casts.rs`.

use zed_tests::scaling::{self, Meter};

use crate::casts::*;

#[test]
fn the_cast_menus_of_many_rejections_scale() {
    let n = 300;
    let srcs = scaling::inputs(n, mixed);
    scaling::check("the cast menus of n rejected sums", n, |k| {
        the_cast_menus_of_rejections(&srcs[&k], k);
    });
}

/// The work of the check of `make(m, R)` less that of `make(m, 0)`, with `per * R` rejections
/// with a menu.
fn rejections(
    meter: &mut Meter,
    m: usize,
    r: usize,
    per: usize,
    make: fn(usize, usize) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution),
) -> u64 {
    let mut work = |r: usize| {
        let (stmts, res) = make(m, r);
        let mut errors = 0;
        let units = meter
            .work(|| errors = rejections_with_a_menu(&stmts, &res))
            .units;
        assert_eq!(errors, per * r, "rejections with a menu among {r}");
        units
    };
    let without = work(0);
    work(r)
        .checked_sub(without)
        .expect("the rejections add work")
}

#[test]
fn a_cast_menu_costs_the_same_in_a_larger_program() {
    // The test above holds the work of n rejections to n, but not the cost of one rejection
    // to a constant: the checker spends about 33,000 instructions on each expression and a
    // scan of its record of expressions about 16 per entry, so a menu that scanned the whole
    // record once per offered cast, O(n) per rejection and O(n²) in all, did 8.8 times the
    // work at 1,000 and 8,000 rejections and passed it. Here the work of the rejections
    // alone, the check of the program with them less the check without, is held to the
    // limit of work of order n^0 as the program around them grows from m to 8m expressions.
    // That scan did 4.1 times the work at m = 60,000 against 480,000; this code 1.00 times.
    // The difference of two counts needs the count of instructions; a meter of processor time
    // does not repeat closely enough. With malloc's cache per thread, one check at 8m now and
    // then took 0.26 billion instructions more in malloc, from what earlier threads left in
    // its arena, and the difference came out 1.38 to 1.44 times (4 of 18 runs of this step on
    // 2026-11-09). `tools/run_tests.sh` turns that cache off: the difference then repeats to
    // within 0.04% when the checks run alone, and beside this step's other tests, which
    // allocate at the same time, it was 0.97 to 1.02 times in 30 runs. At m = 60,000 this test
    // took 36 s alone at load 46, so m is now 30,000: a scan of that record once per offered
    // repair still did 1.88 times the work there, against a limit of 1.32 (TESTS-l01_29-split).
    const R: usize = 100;
    let meter = &mut Meter::new();
    let unit = meter.unit();
    let m = 30_000;
    scaling::hold(
        &format!(
            "{R} rejections beside {m} and {} expressions",
            scaling::FACTOR * m
        ),
        unit,
        rejections(meter, m, R, 1, padded),
        rejections(meter, scaling::FACTOR * m, R, 1, padded),
        0,
    );
}

#[test]
fn the_menus_of_calls_literals_and_comparisons_scale() {
    let n = 200;
    let srcs = scaling::inputs(n, called);
    scaling::check(
        "the menus of 3n rejected calls, literals and comparisons",
        n,
        |k| the_menus_of_calls_literals_and_comparisons(&srcs[&k], k),
    );
}

#[test]
fn the_menus_of_calls_literals_and_comparisons_cost_the_same_in_a_larger_program() {
    // As `a_cast_menu_costs_the_same_in_a_larger_program`, for the menus of a call of `max`, a
    // `rat` literal and a comparison with a literal: the work of R functions of three
    // rejections each, held to order n^0 as the program around them grows from m to 8m. The
    // same scan per offered repair did 1.91 times the work at m = 30,000.
    const R: usize = 100;
    let meter = &mut Meter::new();
    let unit = meter.unit();
    let m = 30_000;
    let make = |m: usize, r: usize| padded_with(m, &called(r));
    scaling::hold(
        &format!(
            "{R} functions beside {m} and {} expressions",
            scaling::FACTOR * m
        ),
        unit,
        rejections(meter, m, R, 3, make),
        rejections(meter, scaling::FACTOR * m, R, 3, make),
        0,
    );
}

#[test]
fn a_cast_in_place_of_many_parentheses_scales() {
    let n = 19_000;
    let srcs = scaling::inputs(n, nested);
    scaling::check(
        "the cast repair of an operand in n pairs of parentheses",
        n,
        |d| a_cast_in_place_of_parentheses(&srcs[&d]),
    );
}

#[test]
fn the_message_of_a_long_literal_with_a_suffix_scales() {
    // At 8,000 and 64,000 digits the work grew 13.3 times, and at 64,000 and 512,000 14.5 times,
    // past the limit and past the 12.1 of n log² n (COMPLEXITY.md K41), so the size stays
    // (TEST-bench-move-l0125; plan row PERF-long-literal-digits).
    let n = 1000;
    let srcs = scaling::inputs(n, long_suffixed_literals);
    scaling::check(
        "the messages of two literals of n digits with a suffix",
        n,
        |k| the_messages_of_long_literals_with_a_suffix(&srcs[&k]),
    );
}

#[test]
fn a_literal_of_many_digits_ordered_with_a_text_is_offered_as_text_and_scales() {
    let n = 260_000;
    let srcs = scaling::inputs(n, a_literal_of_digits_ordered_with_a_text);
    scaling::check(
        "the text repair of a literal of d digits ordered with a text",
        n,
        |d| a_literal_ordered_with_a_text_is_offered_as_text(&srcs[&d], d),
    );
}
