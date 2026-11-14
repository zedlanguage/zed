//! The benchmarks of the definedness and lattice `fix` (DESIGN.md Part G), run by
//! `tools/run_tests.sh --bench` and left out of its default run (TEST-bench-move-rest). They
//! hold linear in the keys: a `fix` whose entries read entry 0 or the one before, under every
//! schedule; one entry reading every other and entries reading the ones after them, under
//! demand; a chain ending in a cycle, which stalls; a lattice ascent adding a key a round; and
//! a string joined by a `foldl` of `++`. What each asserts besides its ratio is checked at
//! small sizes by a test of `scaling.rs`.

use zed_kernel::Schedule;
use zed_tests::scaling;

use crate::scaling::{
    ascent_has_its_keys, chain_to_a_cycle, counts, fan_in_sums, joins_its_pieces, letters,
    reverse_chain_sums, run, stalls_on_every_entry,
};

#[test]
fn the_definedness_fix_scales() {
    // Two rounds: every entry but 0 is postponed once.
    scaling::check("rounds, entries reading entry 0, by keys", 1000, |d| {
        run(&counts(d, false), Schedule::Rounds);
    });
    scaling::check("chaotic, entries reading entry 0, by keys", 1000, |d| {
        run(&counts(d, false), Schedule::Chaotic(7));
    });
    // Each entry waits on, or demands, the one before it.
    for schedule in [Schedule::Rounds, Schedule::Chaotic(7), Schedule::Pull] {
        scaling::check(&format!("{schedule:?}, a chain, by keys"), 1000, |d| {
            run(&counts(d, true), schedule);
        });
    }
}

#[test]
fn an_entry_reading_many_undefined_entries_scales_under_demand() {
    // Each read of an undefined entry stopped the attempt, and the entry was tried again from
    // the start once the entry read was defined: entry 0 of `fan_in(d)` was tried `d` times
    // and read `d²/2` entries. Now the entry read is evaluated where it is read.
    scaling::check(
        "pull, one entry reading every other, by keys",
        1000,
        fan_in_sums,
    );
    scaling::check(
        "pull, entries reading the ones after them, by keys",
        1000,
        reverse_chain_sums,
    );
}

#[test]
fn a_chain_ending_in_a_cycle_stalls_in_linear_time_under_demand() {
    // When the cycle stops the nested demands, every entry on the chain has stalled. Trying
    // each from the start again would walk the rest of the chain each time, `D²/2` reads.
    let (small, large) = (chain_to_a_cycle(1000), chain_to_a_cycle(8000));
    scaling::check("pull, a chain ending in a cycle, by keys", 1000, |d| {
        let chain = if d == 1000 { &small } else { &large };
        stalls_on_every_entry(chain, d);
    });
}

#[test]
fn a_lattice_ascent_by_one_key_a_round_scales() {
    // The test for the fixpoint compared the iterate with the one before in the total order
    // of values, reading both in full each round: `n` rounds took `O(n²)` steps (ratio 40 to
    // 44). Families are now equal by their maps, which differ at once in size.
    scaling::check(
        "a lattice ascent adding a key a round, by keys",
        1000,
        ascent_has_its_keys,
    );
}

#[test]
fn a_string_joined_by_a_fold_scales() {
    // `++` copied both strings, and a `foldl` keeps every accumulator, so joining `n` pieces
    // took `O(n²)` time and memory (8,000 against 64,000 pieces: ratio 26.5). A join is now
    // the node of its two parts, written out once when it is read as text.
    let want = letters(scaling::FACTOR * 8000);
    scaling::check("a foldl of ++, by pieces", 8000, |n| {
        joins_its_pieces(n, &want)
    });
}
