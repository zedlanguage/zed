//! The canonicalizer at the rule of low complexity (DESIGN.md Part G): a chain of n binders,
//! n facets in reverse order, and the address of each deep term, each linear. The benchmarks of
//! this step, run by `tools/run_tests.sh --bench`; what each asserts besides its ratio is
//! checked by `scaling::chains_facets_and_deep_terms_are_canonicalized_at_small_sizes` and,
//! on a 2 MiB stack, by `scaling::terms_12500_deep_are_addressed_on_a_2_mib_stack`.

use zed_tests::scaling;

use super::scaling::{canonicalizes_chain, deep_terms, sorts_facets};
use super::{addr, def};

/// `f` on a thread whose stack holds the recursion of a term `O(n)` deep.
fn deep(f: impl FnOnce() + Send + 'static) {
    let t = std::thread::Builder::new().stack_size(1 << 29).spawn(f);
    t.unwrap().join().unwrap();
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
    let deep = 8 * n;
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
