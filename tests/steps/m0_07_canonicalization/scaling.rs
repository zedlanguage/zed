//! The inputs of the canonicalizer's benchmarks in `bench.rs` (DESIGN.md Part G: the rules
//! renamed one binder per step, each step walking the whole term, so a term of `n` binders
//! took `O(n²)` steps at least; the facet rule swapped one pair of facets per step, `O(F²)`
//! steps of `O(F)` each), and what each benchmark asserts besides its ratio, checked here at
//! small sizes and, for the deep terms, at one depth past where the old recursion overflowed a
//! 2 MiB stack (TEST-bench-move-rest, P170).

use std::sync::Arc;

use zed_kernel::term::Prim;
use zed_kernel::term::Term;
use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zedc::canon::{Facet, canonicalize};

use super::{addr, def};

/// `let x0 = 0 in let x1 = x0 + 1 in … x{n-1}`.
pub(super) fn chain(n: usize) -> Term {
    let mut body = var(&format!("x{}", n - 1));
    for i in (0..n).rev() {
        let e = match i {
            0 => lit(0),
            _ => prim(Prim::Add, vec![var(&format!("x{}", i - 1)), lit(1)]),
        };
        body = let_(&format!("x{i}"), e, body);
    }
    body
}

/// The canonical form of [`chain`]`(n)` is a `let`.
pub(super) fn canonicalizes_chain(n: usize) {
    let c = canonicalize(&def("f", chain(n)));
    assert!(matches!(c.body, Term::Let(..)));
}

/// `n` facets in reverse order, a third of them hints, are sorted and none stays a hint.
pub(super) fn sorts_facets(n: usize) {
    let mut d = def("f", lit(0));
    d.facets = (0..n)
        .rev()
        .map(|i| Facet {
            hint: i % 3 == 0,
            kind: Arc::from("units"),
            value: Value::Int(i as i64 / 2),
        })
        .collect();
    let c = canonicalize(&d);
    assert!(c.facets.windows(2).all(|w| w[0] < w[1]));
    assert!(c.facets.iter().all(|f| !f.hint));
}

/// Each shape of deep term, `n` deep, with its binders named `{x}0`, `{x}1`, …: a `let` chain,
/// nested lambdas, a left-nested sum, nested `if`s, and a literal tuple nested `n` deep.
pub(super) fn deep_terms(n: usize, x: &str) -> Vec<(&'static str, Term)> {
    let name = |i: usize| format!("{x}{i}");
    let lams = (0..n)
        .rev()
        .fold(var(&name(0)), |body, i| lam(&[&name(i)], body));
    let sum = (0..n).fold(lit(0), |a, _| prim(Prim::Add, vec![a, lit(1)]));
    let ifs = (0..n).fold(lit(0), |b, i| if_(var(&name(i)), lit(1), b));
    let ifs = (0..n).rev().fold(ifs, |body, i| lam(&[&name(i)], body));
    let tuple = lit(zed_tests::deep::int_list(n, Value::Int(0)));
    let chain = (0..n).rev().fold(var(&name(n - 1)), |body, i| {
        let e = match i {
            0 => lit(0),
            _ => prim(Prim::Add, vec![var(&name(i - 1)), lit(1)]),
        };
        let_(&name(i), e, body)
    });
    vec![
        ("a `let` chain", chain),
        ("nested lambdas", lams),
        ("a left-nested sum", sum),
        ("`if`s nested under lambdas", ifs),
        ("a literal tuple", tuple),
    ]
}

/// The address names no binder: each term of [`deep_terms`]`(n, "x")` has the address of the same
/// term with other names.
pub(super) fn addresses_ignore_names(n: usize) {
    for ((what, x), (_, y)) in deep_terms(n, "x").into_iter().zip(deep_terms(n, "y")) {
        assert_eq!(addr(&def("f", x)), addr(&def("f", y)), "{what}");
    }
}

/// The chain and the facets the benchmarks time, and the address of each deep term, at small
/// sizes; the times are held in `bench.rs`.
#[test]
fn chains_facets_and_deep_terms_are_canonicalized_at_small_sizes() {
    for n in [1, 2, 9] {
        canonicalizes_chain(n);
        sorts_facets(n);
        addresses_ignore_names(n);
    }
    sorts_facets(0);
}

/// Renaming the binders and writing the canonical form recursed once per level of the term,
/// and dropping a term did too; each overflowed a 2 MiB stack near 10,000 levels. At 12,500
/// levels each deep term is addressed on that stack, by the address of its renamed copy.
#[test]
fn terms_12500_deep_are_addressed_on_a_2_mib_stack() {
    zed_tests::deep::on_small_stack(|| addresses_ignore_names(12_500));
}
