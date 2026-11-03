//! The canonicalizer at the rule of low complexity (DESIGN.md Part G). The rules rename one
//! binder per step, and each step walked the whole term to find the binder and its scope, so
//! a term of `n` binders took `O(n²)` steps at least; the facet rule swapped one pair of
//! facets per step, `O(F²)` steps of `O(F)` each.

use std::sync::Arc;

use zed_kernel::term::Prim;
use zed_kernel::term::Term;
use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_tests::scaling;
use zedc::canon::{Facet, canonicalize};

use super::{addr, def};

/// `let x0 = 0 in let x1 = x0 + 1 in … x{n-1}`.
fn chain(n: usize) -> Term {
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

/// `f` on a thread whose stack holds the recursion of a term `O(n)` deep.
fn deep(f: impl FnOnce() + Send + 'static) {
    let t = std::thread::Builder::new().stack_size(1 << 29).spawn(f);
    t.unwrap().join().unwrap();
}

#[test]
fn canonicalizing_many_binders_scales() {
    deep(|| {
        scaling::check("canonicalizing a chain of n binders", 250, |n| {
            let c = canonicalize(&def("f", chain(n)));
            assert!(matches!(c.body, Term::Let(..)));
        })
    });
}

#[test]
fn sorting_many_facets_scales() {
    scaling::check("canonicalizing n facets in reverse order", 250, |n| {
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
    });
}

/// Each shape of deep term, `n` deep, with its binders named `{x}0`, `{x}1`, …: a `let` chain,
/// nested lambdas, a left-nested sum, nested `if`s, and a literal tuple nested `n` deep.
fn deep_terms(n: usize, x: &str) -> Vec<(&'static str, Term)> {
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
