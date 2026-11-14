//! Provenance at the rule of low complexity (DESIGN.md Part G). A fact's address holds the
//! call sites and the keypath the run is inside, which a recursion of depth `n` makes `n`
//! long; the addresses share them, so recording the `O(n)` facts of the recursion costs
//! `O(n)`, not `O(n²)`. The benchmarks of `bench.rs` hold that order; here each of their checks
//! is made at small sizes.

use zed_kernel::term::build::{app, if_, lam, lit, var};
use zed_kernel::{Term, Value};
use zed_tests::kernel::*;

use super::trace;

/// `let f = (f, n) -> if n == 0 then 0 else f(f, n - 1) + 1 in f(f, depth)`: a recursion of
/// `depth` nested calls.
pub(super) fn countdown(depth: usize) -> Term {
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

/// The recursion `countdown(n)` gives `n` and records more than `5n` facts.
pub(super) fn records_the_recursion(term: &Term, n: usize) {
    let (v, p) = trace(term);
    assert_eq!(v, Value::Int(n as i64));
    assert!(p.facts().len() > 5 * n);
}

#[test]
fn a_recursion_gives_its_depth_and_records_its_facts() {
    for n in [0, 1, 2, 9] {
        records_the_recursion(&countdown(n), n);
    }
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

/// A balanced sum of `n` ones.
pub(super) fn sum_of_ones(n: usize) -> Term {
    tree(0, n, add, &|_| lit(Value::Int(1)))
}

/// The sum of `n` ones gives `n`, and the terms of its facts hold its `n - 1` additions.
pub(super) fn finds_the_term_of_every_fact(term: &Term, n: usize) {
    let (v, p) = trace(term);
    assert_eq!(v, Value::Int(n as i64));
    let adds = p
        .fact_terms()
        .iter()
        .filter(|t| matches!(t, Term::Prim(..)))
        .count();
    assert_eq!(adds, n - 1);
}

#[test]
fn the_term_of_every_fact_of_a_sum_is_found() {
    for n in [1, 2, 9] {
        finds_the_term_of_every_fact(&sum_of_ones(n), n);
    }
}
