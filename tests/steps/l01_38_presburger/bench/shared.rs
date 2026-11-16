//! The benchmarks of `shared.rs` (TEST-bench-move-l0138), run by `tools/run_tests.sh --bench`.

use crate::shared::*;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use zed_tests::scaling;
use zedc::store::presburger::Formula;

#[test]
fn comparing_a_named_chain_with_one_built_apart_takes_time_near_linear_in_its_length() {
    // Two chains built apart share no part, so each pair of their parts is compared.
    let built: BTreeMap<usize, Vec<[Formula; 3]>> = [10000, 80000]
        .map(|d| {
            let three = |and| {
                [
                    named_chain(d, and),
                    named_chain(d, and),
                    extended_chain(d, and),
                ]
            };
            (d, vec![three(true), three(false)])
        })
        .into();
    scaling::check(
        "a chain of d names compared with an equal and an extended one built apart",
        10000,
        |d| {
            for three @ [a, b, c] in &built[&d] {
                assert_chain_equal_and_before_extended(three);
                std::hint::black_box((a.cmp(b), c.cmp(a)));
            }
        },
    );
}

#[test]
fn chains_whose_inner_parts_end_apart_compare_in_time_near_linear_in_their_length() {
    let built: BTreeMap<usize, Vec<(Formula, Formula)>> = [12000, 96000]
        .map(|d| (d, vec![split_chains(d, and), split_chains(d, or)]))
        .into();
    scaling::check(
        "two chains of d levels whose inner parts end at other places on each side",
        12000,
        |d| {
            for (a, b) in &built[&d] {
                assert!(a == b);
                std::hint::black_box(b.cmp(a));
            }
        },
    );
    let (a, b) = split_chains(6, and);
    assert_eq!(flat(&a), flat(&b));
    assert_eq!(hash(&a), hash(&b));
}

#[test]
fn one_sequence_grouped_at_other_places_on_each_side_compares_in_time_near_quadratic_in_the_depth()
{
    // Each side has n = 2d + 2 distinct parts and 2^(d+1) - 1 constraints written out. The
    // parse of a sequence of N parts has O(log N) = O(d) levels and each part joins its parts'
    // parses at O(d) levels, so compare costs O(n log N) = O(d^2), of power 2: no exact method
    // known compares two such sequences in time near n alone (the tradeoff at
    // [`Formula::cmp`], COMPLEXITY.md S31b). Read through, it costs 2^d.
    let built: BTreeMap<usize, Vec<(Formula, Formula, Ordering)>> =
        [22, 176].map(|d| (d, shifted_pairs(d))).into();
    scaling::check_order(
        "one sequence of 2^(d+1) - 1 constraints in d levels, grouped at other places on each side",
        22,
        2,
        |d| {
            for (a, b, o) in &built[&d] {
                assert_eq!(a.cmp(b), *o);
                assert_eq!(b.cmp(a), o.reverse());
            }
        },
    );
}

#[test]
fn tops_sharing_parts_compare_in_time_near_quadratic_in_the_depth() {
    // Each side has n = O(d) distinct parts and up to 2^d constraints written out, so compare
    // costs O(n log N) = O(d^2), as for [`shifted_chains`] (COMPLEXITY.md S31b). Equal pairs
    // and pairs that differ at the last top are both read to the end.
    let built: BTreeMap<usize, Vec<(Formula, Formula, bool)>> =
        [24, 192].map(|d| (d, tops_pairs(d))).into();
    scaling::check_order(
        "staircases and random DAGs of d tops, equal or differing at the last top",
        24,
        2,
        |d| {
            for (a, b, equal) in &built[&d] {
                assert_eq!(a == b, *equal);
                assert_eq!(b.cmp(a), a.cmp(b).reverse());
            }
        },
    );
}

#[test]
fn pairs_of_shared_sets_compare_in_time_near_linear_in_the_parts() {
    // k sets of k constraints and k^2 / 2 tops: n = O(k^2) distinct parts, so k to 8k is n to
    // 64n, and power 2 in k is time near linear in n.
    let built: BTreeMap<usize, [(Formula, Formula, bool); 2]> = [49, 392]
        .map(|k| {
            (
                k,
                [
                    (pairs(k, 9, 0), pairs(k, 9, 0), true),
                    (pairs(k, 9, 0), pairs(k, 9, 1), false),
                ],
            )
        })
        .into();
    scaling::check_order(
        "k^2 / 2 tops, each two of k sets of k constraints, equal or differing at the last top",
        49,
        2,
        |k| {
            for (a, b, equal) in &built[&k] {
                assert_eq!(a == b, *equal);
                assert_eq!(b.cmp(a), a.cmp(b).reverse());
            }
        },
    );
}

#[test]
fn unequal_formulas_grouped_at_other_places_compare_in_time_near_linear_in_the_depth() {
    // The unequal pairs of [`shifted_pairs`]: `==` finds each side's hash once, O(n) for its
    // n = 2d + 2 distinct parts, and then answers in O(1); `cmp` alone parses both sides,
    // O(n log N) = O(d^2) (the tradeoff at `Formula`'s `eq`, COMPLEXITY.md S31b).
    let unequal = |d: usize| -> Vec<(Formula, Formula)> {
        shifted_pairs(d)
            .into_iter()
            .filter(|(_, _, o)| *o != Ordering::Equal)
            .map(|(a, b, _)| (a, b))
            .collect()
    };
    let built: BTreeMap<usize, Vec<(Formula, Formula)>> =
        [13000, 104000].map(|d| (d, unequal(d))).into();
    scaling::check(
        "== on one sequence of 2^(d+1) - 1 constraints in d levels, grouped at other places on \
         each side and differing at the last",
        13000,
        |d| {
            for (a, b) in &built[&d] {
                assert!(a != b);
                assert!(b != a);
            }
        },
    );
}

/// `shared::one_sequence_grouped_at_other_places_on_each_side_compares_as_written_out` as
/// first written, 1.5 s (2026-11-14, load 25): depths 0 to 12.
#[test]
fn one_sequence_grouped_at_other_places_on_each_side_compares_as_written_out_to_depth_12() {
    for d in 0..=12 {
        grouped_sequences_compare_as_written_out(d);
    }
}

/// `shared::taking_a_shared_part_out_of_a_disjunction_loses_no_precision` as first written,
/// 1.06 s (2026-11-14, load 25): 600 formulas of seed 0x5f5b.
#[test]
fn taking_a_shared_part_out_of_the_600_disjunctions_of_seed_0x5f5b_loses_no_precision() {
    let mut rng = zed_tests::instances::Rng::new(0x5F5B);
    let c = factoring_loses_no_precision((0..600).map(|i| (i, random_tiers(&mut rng))));
    // On 2026-11-14 one projection, of formula 9, is narrower than as written, and no refusal
    // as written is answered.
    assert_eq!((c.same, c.narrower, c.answered), (599, 1, 0), "{c:?}");
}
