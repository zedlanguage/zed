//! The benchmarks of step L1.27: the checker on long chains of loose atoms, at the rule of low
//! complexity (DESIGN.md Part G), run by `tools/run_tests.sh --bench` (TEST-bench-split, author
//! P169). The programs and the check each makes besides its ratio are in `scaling.rs`, whose
//! correctness tests make that check at small sizes (author P170); each benchmark names its own.

use std::collections::BTreeMap;

use zed_tests::scaling::{self, FACTOR};

use zed_tests::step_helpers::l01_26_type_resolution::Resolved;

use super::scaling::*;

/// Runs `f` on a thread with a large stack: the parser and checker recurse once per operator
/// or `else if`.
fn on_large_stack(f: impl FnOnce() + Send) {
    scaling::on_a_stack(1 << 29, f)
}

/// Coverage: `scaling::a_chain_of_failure_atoms_is_accepted_on_each_check`.
#[test]
fn a_chain_of_many_failure_atoms_scales() {
    on_large_stack(|| {
        scaling::check(
            "a chain of n failure atoms, checked twice",
            1250,
            checks_the_chain_twice,
        )
    })
}

/// Coverage: `scaling::each_discard_gets_its_own_error_or_none`.
#[test]
fn checking_many_discards_scales() {
    for (what, tail, per) in DISCARDS {
        let units: BTreeMap<usize, Ready> = [1600, FACTOR * 1600]
            .into_iter()
            .map(|n| (n, ready(&discards(n, tail))))
            .collect();
        scaling::check_order(what, 1600, 1, |n| {
            assert_eq!(errors(&units[&n]).len(), per * n);
        });
    }
}

/// The walk to where the failure enters follows each name once, on its own stack. Coverage:
/// `scaling::a_dropped_failure_behind_names_is_found_where_it_enters`.
#[test]
fn a_dropped_failure_found_through_a_long_chain_of_names_scales() {
    let units: BTreeMap<usize, Ready> = [2000, FACTOR * 2000]
        .into_iter()
        .map(|n| (n, ready(&deep_discard(n))))
        .collect();
    scaling::check_order("a dropped failure behind n names", 2000, 1, |n| {
        found_through_the_names(&units[&n])
    })
}

/// Each branch is checked on its own: the defaults of the others name nothing in it. Coverage:
/// `scaling::each_defaulted_branch_is_checked_alone`.
#[test]
fn a_chain_of_many_defaulted_branches_scales() {
    on_large_stack(|| {
        for (what, last, errors) in LAST_BRANCHES {
            let units: BTreeMap<usize, Ready> = [820, FACTOR * 820]
                .into_iter()
                .map(|n| (n, ready(&defaulted_branches(n, last))))
                .collect();
            scaling::check_order(what, 820, 1, |n| the_branches_check(&units[&n], errors));
        }
    })
}

/// A check that walks each `if`'s branches again costs O(n²) here: a walk that only counts the
/// nodes under each `if` took 28.6 times the work from 2000 to 16000 branches. Coverage:
/// `scaling::branches_that_each_default_one_name_are_accepted`.
#[test]
fn a_long_chain_of_defaulted_names_scales() {
    on_large_stack(|| {
        let units: BTreeMap<usize, Ready> = [3600, FACTOR * 3600]
            .into_iter()
            .map(|n| (n, ready(&defaulted_names(n))))
            .collect();
        scaling::check_order(
            "an `if` of n branches, each naming the miss of one name",
            3600,
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
    let units: BTreeMap<usize, Ready> = [1500, FACTOR * 1500]
        .into_iter()
        .map(|n| (n, ready(&generic_calls(n))))
        .collect();
    scaling::check_order("n dropped generic calls", 1500, 1, |n| {
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
            scaling::check(&what, 700, |n| merges(n, kinds, errs))
        }
    })
}

/// The repairs hold one `else` pattern and one `match` arm for each atom of the family, so the
/// error's text is linear in the number of atoms. Coverage:
/// `scaling::the_repairs_for_a_family_name_its_atoms`.
#[test]
fn the_repairs_for_a_family_of_many_atoms_scale() {
    let u = ready(FAMILY_TEXT);
    let families: BTreeMap<usize, zedc::check::ty::Ty> = [15000, FACTOR * 15000]
        .into_iter()
        .map(|n| (n, family(n)))
        .collect();
    scaling::check_order("the repairs for a family of n atoms", 15000, 1, |n| {
        repairs_name_each_atom(&u, n, families[&n].clone())
    });
}

/// Each bare `else` is refused once, its repair built from its operand's loose atoms alone, so
/// the check is linear in the program (plan row ELSE-explicit-atoms). Coverage:
/// `bare_else::each_bare_else_is_refused_once`.
#[test]
fn refusing_many_bare_elses_scales() {
    let units: BTreeMap<usize, Resolved> = [1600, FACTOR * 1600]
        .into_iter()
        .map(|n| (n, Resolved::new(&super::bare_else::bare_else_units(n))))
        .collect();
    scaling::check_order("n bare `else`s, each refused", 1600, 1, |n| {
        super::bare_else::each_bare_else_refused_once(&units[&n], n)
    });
}

/// The repair of one bare `else` whose operand holds n loose atoms lists each once, a chain of
/// n tails: O(n log n) to sort the names and O(n) bytes of text for a one-byte default.
/// Coverage: `bare_else::the_repair_lists_each_of_many_atoms_once`.
#[test]
fn the_repair_of_an_else_over_many_atoms_scales() {
    let units: BTreeMap<usize, Resolved> = [3000, FACTOR * 3000]
        .into_iter()
        .map(|n| (n, Resolved::new(&super::bare_else::many_atoms(n))))
        .collect();
    scaling::check_order("one bare `else` over n loose atoms", 3000, 1, |n| {
        super::bare_else::lists_each_atom_once(&units[&n], n)
    });
}

/// A lambda checked at each of n arrows, each adding one loose atom to its bare `else`'s
/// operand: the `else` is joined at each arrow in O(1) and refused once, its repair naming the
/// n atoms, so the check stays linear in the program. Coverage:
/// `bare_else::a_bare_else_at_many_arrows_is_refused_once_naming_each_atom`.
#[test]
fn a_bare_else_checked_at_many_arrows_scales() {
    let units: BTreeMap<usize, Resolved> = [400, FACTOR * 400]
        .into_iter()
        .map(|n| (n, Resolved::new(&super::bare_else::many_arrows(n))))
        .collect();
    scaling::check_order("one bare `else` at n arrows of n atoms", 400, 1, |n| {
        super::bare_else::refused_once_naming_each_arrow_s_atom(&units[&n], n)
    });
}
