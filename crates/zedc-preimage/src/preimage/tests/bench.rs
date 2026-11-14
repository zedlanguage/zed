//! The benchmarks of `preimage::tests`, run by `tools/run_tests.sh --bench` and left out of
//! its default run (TEST-bench-move-crates). The correctness tests that keep a small instance
//! of what each checks besides the ratio are `two_large_classes_stay_apart`,
//! `chains_are_read_exactly_at_small_lengths` and `a_staged_chain_is_read_exactly`.
//! Sizes are set (2026-11-14) so the 1x case takes about 0.4 to 0.7 s and a piece stays under
//! 20 s, except the two chains held below the sizes where reading them stops being near
//! linear (see each).

use super::*;

/// The n of [`refused_joins_between_two_large_classes_scale`].
const REFUSED_N: usize = 350_000;

/// Eight pairs of classes of n/8 functions each, each pair sharing one function `s(x, y)`
/// (`x` in the first class, `y` in the second), and n/8 functions
/// `t{j}(x) = ra(x: x) && rb(y: x)` a pair, each joining its parameter to the first class
/// and then refused against the second for `s`, which is neither its caller nor its callee.
/// Looking through the smaller class at each refusal is O(n²) (eight pairs, so the place of
/// `s` in each class's order varies less between runs); remembered, a repeated refusal is
/// O(1).
#[test]
fn refused_joins_between_two_large_classes_scale() {
    let (small, large) = (
        two_large_classes(REFUSED_N),
        two_large_classes(8 * REFUSED_N),
    );
    crate::scaling::compare(
        "refused joins between two classes of n/8 functions, eight pairs, n and 8n",
        1,
        || {
            std::hint::black_box(unite(&small.first, &small.joins));
        },
        || {
            std::hint::black_box(unite(&large.first, &large.joins));
        },
    );
}

/// [`Gen::chain`] makes a chain of `n` `if`s in work of order `n`: each level reads the
/// one term below it, shared, so neither the work nor the term doubles at a level.
#[test]
fn a_chain_is_made_in_work_of_order_its_length() {
    crate::scaling::check_order("a chain of n ifs over one input made", 200_000, 1, |n| {
        let mut g = Gen::new(0x5851_f42d_4c95_7f2d, true);
        g.chains = true;
        std::hint::black_box(g.chain(n, true));
    });
}

/// A chain of guards on `x mod 3` whose arms move, reflect, negate, scale and clamp the
/// term below, with `min` and `max` across their constant and `0 * u` (COMPLEXITY.md row
/// S22-order-chain: 6.7 ms, 209 ms, 3.37 s and 30.2 s at k = 20, 40, 80 and 160). Each
/// level is one summary over the classes ([`ByClass`]), so the shared term is read once.
/// Held at k = 40 (1x about 1 ms): this seed's chain is read in 5 to 15 ms up to k = 320,
/// then 54 ms at 340, 122 ms at 360, 0.93 s at 380, 3.5 s at 400 and over 60 s at 500
/// (measured 2026-11-14, load 20 to 30), so 8k must stay under about 340 (item
/// PREIMAGE-chain-cliff).
#[test]
fn a_chain_is_read_in_time_near_its_length() {
    crate::scaling::check_order("the preimage of a chain of k ifs", 40, 1, |k| {
        chain_preimage(0x5851_f42d_4c95_7f2d, k)
    });
}

/// A chain on `y` whose guards compare `y` with constants or take `y mod 2`, with `min`
/// arms across their constant, and `if`s on a comparison whose arms read the remainder in
/// different ways ([`Walk::by_class_if`], [`ByClass::clamp`]). Held at k = 250 (1x about
/// 25 ms): this seed's chain is read in 51 ms at k = 2000, then 0.34 s at 2150, 1.1 s at
/// 2200, 4.4 s at 2250 and 17.5 s at 2300, and at 4000 the recursion of `Terms::form`
/// overflows the default 2 MiB test thread stack (measured 2026-11-14; item
/// PREIMAGE-chain-cliff).
#[test]
fn a_chain_with_clamps_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage of a chain of k ifs, mixed guards",
        250,
        1,
        |k| chain_preimage(0xa, k),
    );
}

/// A chain whose guards compare `x` with constants, with `min` and `max` arms across their
/// constant: one summary of each level ([`Pa::clamp`]).
#[test]
fn a_chain_of_comparisons_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage of a chain of k ifs, comparisons",
        6000,
        1,
        |k| chain_preimage(1, k),
    );
}

/// The preimage of [`staged_chain`] under `false`, whose hulls are tightened by questions
/// to the solver over the whole formula (`presburger::project_each`). Before item
/// PREIMAGE-slow-rounds each question probed every disjunct again; now the points found
/// are kept across the questions and a disjunct is searched from both ends of the chain.
/// What is left is the probe of the formula itself, whose `learn` settles a bound at
/// stage `i` in about `i` rounds of the whole formula (COMPLEXITY.md
/// PREIMAGE-slow-rounds).
#[test]
fn a_staged_chain_under_false_is_read_in_time_near_its_length() {
    crate::scaling::check_order(
        "the preimage under false of a chain of k stages",
        3000,
        1,
        |k| {
            let p = preimage(&staged_chain(k), &domains(), &Demand::Bool(false));
            assert!(p.exact, "k = {k}: {p:?}");
        },
    );
}
