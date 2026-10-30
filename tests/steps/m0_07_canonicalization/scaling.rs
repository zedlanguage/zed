//! The canonicalizer at the rule of low complexity (DESIGN.md Part G). The rules rename one
//! binder per step, and each step walked the whole term to find the binder and its scope, so
//! a term of `n` binders took `O(n²)` steps at least; the facet rule swapped one pair of
//! facets per step, `O(F²)` steps of `O(F)` each.

use std::sync::Arc;

use zed_kernel::term::Prim;
use zed_kernel::term::Term;
use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::value::Value;
use zed_tests::scaling;
use zedc::canon::{Facet, canonicalize};

use super::def;

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
