//! The benchmarks of step L1.27: the checker on long chains of loose atoms, at the rule of low
//! complexity (DESIGN.md Part G), run by `tools/run_tests.sh --bench` (TEST-bench-split, author
//! P169). The programs and the check each makes besides its ratio are in `scaling.rs`, whose
//! correctness tests make that check at small sizes (author P170); each benchmark names its own.

use std::collections::BTreeMap;

use zed_tests::scaling::{self, FACTOR};

use super::scaling::*;

/// Runs `f` on a thread with a large stack: the parser and checker recurse once per operator
/// or `else if`.
fn on_large_stack(f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

/// Coverage: `scaling::a_chain_of_failure_atoms_is_accepted_on_each_check`.
#[test]
fn a_chain_of_many_failure_atoms_scales() {
    on_large_stack(|| {
        scaling::check(
            "a chain of n failure atoms, checked twice",
            1000,
            checks_the_chain_twice,
        )
    })
}

/// Coverage: `scaling::each_discard_gets_its_own_error_or_none`.
#[test]
fn checking_many_discards_scales() {
    for (what, tail, per) in DISCARDS {
        let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
            .into_iter()
            .map(|n| (n, ready(&discards(n, tail))))
            .collect();
        scaling::check_order(what, 500, 1, |n| {
            assert_eq!(errors(&units[&n]).len(), per * n);
        });
    }
}

/// The walk to where the failure enters follows each name once, on its own stack. Coverage:
/// `scaling::a_dropped_failure_behind_names_is_found_where_it_enters`.
#[test]
fn a_dropped_failure_found_through_a_long_chain_of_names_scales() {
    let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
        .into_iter()
        .map(|n| (n, ready(&deep_discard(n))))
        .collect();
    scaling::check_order("a dropped failure behind n names", 500, 1, |n| {
        found_through_the_names(&units[&n])
    })
}

/// Each branch is checked on its own: the defaults of the others name nothing in it. Coverage:
/// `scaling::each_defaulted_branch_is_checked_alone`.
#[test]
fn a_chain_of_many_defaulted_branches_scales() {
    on_large_stack(|| {
        for (what, last, errors) in LAST_BRANCHES {
            let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
                .into_iter()
                .map(|n| (n, ready(&defaulted_branches(n, last))))
                .collect();
            scaling::check_order(what, 500, 1, |n| the_branches_check(&units[&n], errors));
        }
    })
}

/// A check that walks each `if`'s branches again costs O(n²) here: a walk that only counts the
/// nodes under each `if` took 28.6 times the work from 2000 to 16000 branches. Coverage:
/// `scaling::branches_that_each_default_one_name_are_accepted`.
#[test]
fn a_long_chain_of_defaulted_names_scales() {
    on_large_stack(|| {
        let units: BTreeMap<usize, Ready> = [2000, FACTOR * 2000]
            .into_iter()
            .map(|n| (n, ready(&defaulted_names(n))))
            .collect();
        scaling::check_order(
            "an `if` of n branches, each naming the miss of one name",
            2000,
            1,
            |n| {
                let found = errors(&units[&n]);
                assert!(found.is_empty(), "{found:?}");
            },
        );
    })
}

/// Coverage: `scaling::dropped_generic_calls_with_defaults_are_accepted`.
#[test]
fn many_dropped_generic_calls_scale() {
    let units: BTreeMap<usize, Ready> = [500, FACTOR * 500]
        .into_iter()
        .map(|n| (n, ready(&generic_calls(n))))
        .collect();
    scaling::check_order("n dropped generic calls", 500, 1, |n| {
        let found = errors(&units[&n]);
        assert!(found.is_empty(), "{found:?}");
    });
}

/// Each `+` compares its operands' failures with the first one's (`ty::merges`), and the left
/// operand already holds the failures of the chain before it; the result keeps one flat
/// `#errs`, and none when every operand carries the same failure. Coverage:
/// `scaling::the_failures_of_a_chain_of_sums_merge_into_one_flat_errs`.
#[test]
fn merging_the_failures_of_a_long_chain_scales() {
    on_large_stack(|| {
        for (kinds, errs) in KINDS {
            let what = format!("a chain of n sums of {kinds:?} kinds of failure");
            scaling::check(&what, 1000, |n| merges(n, kinds, errs))
        }
    })
}

/// The repairs hold one `else` pattern and one `match` arm for each atom of the family, so the
/// error's text is linear in the number of atoms. Coverage:
/// `scaling::the_repairs_for_a_family_name_its_atoms`.
#[test]
fn the_repairs_for_a_family_of_many_atoms_scale() {
    let u = ready(FAMILY_TEXT);
    let families: BTreeMap<usize, zedc::check::ty::Ty> = [1000, FACTOR * 1000]
        .into_iter()
        .map(|n| (n, family(n)))
        .collect();
    scaling::check_order("the repairs for a family of n atoms", 1000, 1, |n| {
        repairs_name_each_atom(&u, n, families[&n].clone())
    });
}
