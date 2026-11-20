//! The canonicalizer at the rule of low complexity (DESIGN.md Part G): a chain of n binders,
//! n facets in reverse order, and the address of each deep term, each linear. The benchmarks of
//! this step, run by `tools/run_tests.sh --bench`; what each asserts besides its ratio is
//! checked by `scaling::chains_facets_and_deep_terms_are_canonicalized_at_small_sizes`, and
//! on a 2 MiB stack by `terms_12500_deep_are_addressed_on_a_2_mib_stack` here (author P178).

use zed_tests::scaling;

use super::misplaced_level::{steps_once, under_and_over};
use super::scaling::{addresses_ignore_names, canonicalizes_chain, deep_terms, sorts_facets};
use super::{addr, def};

/// `f` on a thread whose stack holds the recursion of a term `O(n)` deep.
fn deep(f: impl FnOnce() + Send + 'static) {
    scaling::on_a_stack(1 << 29, f);
}

#[test]
fn canonicalizing_many_binders_scales() {
    deep(|| {
        scaling::check(
            "canonicalizing a chain of n binders",
            250,
            canonicalizes_chain,
        )
    });
}

#[test]
fn sorting_many_facets_scales() {
    scaling::check(
        "canonicalizing n facets in reverse order",
        250,
        sorts_facets,
    );
}

#[test]
fn terms_100000_deep_are_addressed_on_a_2_mib_stack() {
    // Renaming the binders and writing the canonical form recursed once per level of the
    // term, and dropping a term did too; each overflowed this stack near 10,000 levels.
    let n = 12_500;
    let deep = scaling::FACTOR * n;
    zed_tests::deep::on_small_stack(|| {
        let small = deep_terms(n, "x");
        let large = deep_terms(deep, "x");
        for ((what, s), (_, l)) in small.into_iter().zip(large) {
            let (s, l) = (def("f", s), def("f", l));
            scaling::check_order(&format!("addressing {what}"), n, 1, |k| {
                addr(if k == n { &s } else { &l });
            });
            // The address names no binder: the same term with other names has it too.
            let renamed = deep_terms(deep, "y").into_iter().find(|(w, _)| *w == what);
            assert_eq!(addr(&l), addr(&def("f", renamed.unwrap().1)), "{what}");
        }
    });
}

/// Renaming the binders and writing the canonical form recursed once per level of the term,
/// and dropping a term did too; each overflowed a 2 MiB stack near 10,000 levels. At 12,500
/// levels each deep term is addressed on that stack, by the address of its renamed copy.
#[test]
fn terms_12500_deep_are_addressed_on_a_2_mib_stack() {
    zed_tests::deep::on_small_stack(|| addresses_ignore_names(12_500));
}

#[test]
fn stepping_past_a_deep_binder_scales() {
    // One step of the rule finds the binder to rename under n calls and `match` arms and walks
    // its scope of n lambdas: O(n log n). The inputs are built before timing.
    deep(|| {
        let terms = scaling::inputs(2000, under_and_over);
        scaling::check(
            "one step of the binder rule, under n calls and match arms, over n lambdas",
            2000,
            |n| steps_once(&terms[&n]),
        )
    });
}
