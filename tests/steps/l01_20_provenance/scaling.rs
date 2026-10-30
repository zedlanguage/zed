//! Provenance at the rule of low complexity (DESIGN.md Part G). A fact's address holds the
//! call sites and the keypath the run is inside, which a recursion of depth `n` makes `n`
//! long; the addresses share them, so recording the `O(n)` facts of the recursion costs
//! `O(n)`, not `O(n²)`.

use zed_kernel::term::build::{app, if_, lam, lit, var};
use zed_kernel::{Term, Value};
use zed_tests::kernel::*;
use zed_tests::scaling;

use super::trace;

/// `let f = (f, n) -> if n == 0 then 0 else f(f, n - 1) + 1 in f(f, depth)`: a recursion of
/// `depth` nested calls.
fn countdown(depth: usize) -> Term {
    let body = if_(
        eq(var("n"), lit(Value::Int(0))),
        lit(Value::Int(0)),
        add(
            app(var("f"), vec![var("f"), sub(var("n"), lit(Value::Int(1)))]),
            lit(Value::Int(1)),
        ),
    );
    let f = lam(&["f", "n"], body);
    app(f.clone(), vec![f, lit(Value::Int(depth as i64))])
}

#[test]
fn recording_a_deep_recursion_scales() {
    // Each fact copied the call sites it was inside: the facts of a recursion of depth `n`
    // held `n²/2` of them.
    scaling::check("the provenance of a recursion, by depth", 1000, |n| {
        let (v, p) = trace(&countdown(n));
        assert_eq!(v, Value::Int(n as i64));
        assert!(p.facts().len() > 5 * n);
    });
}

#[test]
fn the_facts_of_a_recursion_are_at_their_call_sites() {
    // The fact of `n == 0` at depth `d` is `d + 1` call sites deep: the outer call, then the
    // recursive call site `d` times; no two facts share an address.
    let (_, p) = trace(&countdown(30));
    super::unique(&p);
    let mut depths: Vec<usize> = super::at(&p, "(n == 0)")
        .iter()
        .map(|f| f.address.node.0.len())
        .collect();
    depths.sort();
    depths.dedup();
    assert_eq!(depths.len(), 31, "{depths:?}");
    assert_eq!(depths[30] - depths[0], 30, "{depths:?}");
}

/// The balanced tree of `op` over the leaves `leaf(lo..hi)`.
fn tree(lo: usize, hi: usize, op: fn(Term, Term) -> Term, leaf: &dyn Fn(usize) -> Term) -> Term {
    match hi - lo {
        1 => leaf(lo),
        _ => {
            let mid = (lo + hi) / 2;
            op(tree(lo, mid, op, leaf), tree(mid, hi, op, leaf))
        }
    }
}

#[test]
fn the_term_of_every_fact_scales() {
    // The term at a node is found by walking the term in preorder to its position, so
    // reading the term of each of the `O(n)` facts of an `n`-node term one at a time took
    // `O(n²)` steps (ratio 61). `terms()` reads them all in one walk.
    scaling::check("the term at each fact, by term size", 1000, |n| {
        let (v, p) = trace(&tree(0, n, add, &|_| lit(Value::Int(1))));
        assert_eq!(v, Value::Int(n as i64));
        let terms = p.terms();
        let adds = p
            .facts()
            .iter()
            .filter(|f| matches!(terms[f.address.node.position() as usize], Term::Prim(..)))
            .count();
        assert_eq!(adds, n - 1);
    });
}

#[test]
fn the_origins_of_a_failure_with_many_members_scale() {
    // The product of `n` distinct loose atoms: its `#errs` has `n` members, each first
    // appearing at its literal. Each member's search tested every input fact by walking its
    // value, an `#errs` of up to `n` members: `O(n² log n)` steps.
    scaling::check("the origins of an n-member failure, by n", 64, |n| {
        let leaf = |i: usize| lit(Value::atom(&format!("e{i}")));
        let (v, p) = trace(&tree(0, n, mul, &leaf));
        assert_eq!(v.errs().map(|e| e.len()), Some(n), "{v}");
        let o = p.origins(p.result());
        assert_eq!(o.len(), n);
        let at = |j: usize| p.term(&p.facts()[j].address.node);
        assert!(o.iter().all(|&j| matches!(at(j), Term::Lit(_))));
    });
}
