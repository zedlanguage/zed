//! The texts of `print.rs` at `d` and `8d` levels: their lengths grow at most about 8 times
//! (a logarithm included), and the time to the order check. Each term is built before the
//! timing; `print.rs` holds the texts at small sizes.

use std::collections::HashMap;

use zed_kernel::Term;
use zed_tests::scaling::{self, FACTOR};

use crate::print::{arms, chains, lets, shown, spine, wide};

/// The text's length at `d` and at `FACTOR * d` is held to a constant over the factor (a
/// logarithm included), and the time to the order check.
fn scales(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Term,
    print: impl Fn(&Term) -> String + Sync,
) {
    let terms: HashMap<usize, Term> = scaling::inputs(n, make);
    let lens: HashMap<usize, usize> = terms.iter().map(|(&d, t)| (d, print(t).len())).collect();
    assert!(
        lens[&(FACTOR * n)] <= 3 * FACTOR * lens[&n],
        "{what}: the text is {} long at {n}, {} at {}",
        lens[&n],
        lens[&(FACTOR * n)],
        FACTOR * n
    );
    scaling::check(what, n, |d| {
        assert_eq!(print(&terms[&d]).len(), lens[&d]);
    });
}

#[test]
fn writing_nested_ifs_over_one_part_scales() {
    scales(
        "pretty_in on d nested ifs over one part",
        400,
        |d| arms(d, true),
        shown,
    );
    scales(
        "Display on d nested ifs over one part",
        400,
        |d| arms(d, true),
        |t| t.to_string(),
    );
}

#[test]
fn writing_nested_lets_whose_part_reads_a_name_bound_twice_scales() {
    scales(
        "pretty_in on d nested ifs binding a name over one part",
        400,
        lets,
        shown,
    );
    scales(
        "Display on d nested ifs binding a name over one part",
        400,
        lets,
        |t| t.to_string(),
    );
}

/// Plan row STAGE-scaling-10_5, back from the deferred tests (TESTS-defer-failing, 2026-11-13:
/// 11.5 times the instructions from 50 to 400 on main cdf07ac4f, as each read of `Q` wrote its
/// path in the env and each binder rebuilt one). The text is now linear in the term (the
/// comments on `Builder::read` and `Builder::update` in `crates/zed-kernel/src/print/dag.rs`):
/// 8.08 times the instructions from 800 to 6400. Sized as its siblings, 400, not the deferred
/// 50.
#[test]
fn writing_a_part_reading_many_names_bound_twice_scales() {
    scales("pretty_in on wide(n, n)", 400, |n| wide(n, n), shown);
    scales(
        "Display on wide(n, n)",
        400,
        |n| wide(n, n),
        |t| t.to_string(),
    );
}

/// Round 2 of XR-lazy-and-kernel-batch-1 (Claude C-1, Gemini C.1): an update walked up the
/// chain of envs past each env with one env set from it, and the next binder's update, built
/// after the first had passed its env, walked the same chain again, Θ(k²) in time and text for
/// k names. `chains` binds each name in two places beside one part, `spine` binds each once
/// over a nested `if` whose `else` holds the part.
#[test]
fn writing_chains_of_envs_passed_and_named_later_scales() {
    scales("pretty_in on chains(k)", 400, chains, shown);
    scales("pretty_in on spine(k)", 400, spine, shown);
}
