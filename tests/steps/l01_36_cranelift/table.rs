//! The heap's table of uncounted values and its cells against the number of runs of a match
//! or a read (COMPLEXITY.md R12): a match adds no entry, and a value made again and dropped
//! uses the entry or cell it had, so both stay the same size at `n` and `8n`.

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Pattern, Prim, Term, Value, World};

use super::planned;
use super::scaling::{check_run, strings, unused};

/// `f = (y) -> y; g = (z) -> match f { p -> body }; (g(0), g(1), …, g(n-1))`: `n` matches of
/// a function.
fn fun_match(n: usize, p: Pattern, body: Term) -> Term {
    let m = Term::Match(Arc::new(var("f")), vec![(p, body)]);
    let g = lam(&["z"], m);
    let calls = (0..n).map(|i| app(var("g"), vec![lit(i as i64)])).collect();
    let_(
        "f",
        lam(&["y"], var("y")),
        let_("g", g, prim(Prim::Tuple, calls)),
    )
}

fn fun_is(n: usize) -> Term {
    fun_match(n, Pattern::Is(Type::top()), var("z"))
}

fn fun_wild(n: usize) -> Term {
    fun_match(n, Pattern::Wild, var("z"))
}

/// `f = (y) -> match (read x, #none(), y) { (a, b, c) -> c }; (f(0), …, f(n-1))`: each call
/// reads the bare values of `x`, makes a bare atom, and drops both.
fn bare(n: usize) -> Term {
    let none = prim(Prim::Atom, vec![lit("none"), lit(Value::tuple(Vec::new()))]);
    let s = prim(Prim::Tuple, vec![Term::Read("x".into()), none, var("y")]);
    let p = Pattern::Tuple(["a", "b", "c"].map(|x| Pattern::Bind(x.into())).to_vec());
    let f = lam(&["y"], Term::Match(Arc::new(s), vec![(p, var("c"))]));
    let calls = (0..n).map(|i| app(var("f"), vec![lit(i as i64)])).collect();
    let_("f", f, prim(Prim::Tuple, calls))
}

/// A world whose input port `x` holds `((), #nil, #some(()))`.
fn bare_world(_: usize) -> World {
    let mut w = World::new();
    let some = Value::atom_with("some", vec![Value::tuple(Vec::new())]);
    let xs = vec![Value::tuple(Vec::new()), Value::atom("nil"), some];
    w.inputs.insert("x".into(), Value::tuple(xs));
    w
}

/// The table's entries and the heap's cells after the native run of `make(m)` in `world(m)`.
fn sizes(make: fn(usize) -> Term, world: fn(usize) -> World, m: usize) -> (usize, usize) {
    let (g, p) = planned(&make(m));
    let o = zed_native::run(&g, &p, &mut Evaluator::new(world(m))).unwrap();
    (o.table, o.cells)
}

/// The table and the cells are the same size at `n` and `8n`.
fn fixed(what: &str, n: usize, make: fn(usize) -> Term, world: fn(usize) -> World) {
    let (small, large) = (sizes(make, world, n), sizes(make, world, 8 * n));
    assert_eq!(
        small,
        large,
        "{what}: (table entries, cells) at sizes {n} and {}",
        8 * n
    );
}

/// A binder the arm does not use takes no entry of the table (COMPLEXITY.md R7, R12).
#[test]
fn matches_with_an_unused_binder_add_no_entry() {
    fixed("n matches with an unused binder", 50, unused, |_| {
        strings(4)
    });
}

/// A function matched by `is` or `_` is tested in place and takes no entry.
#[test]
fn matches_of_a_function_add_no_entry() {
    fixed("n matches of a function by is", 50, fun_is, |_| {
        World::new()
    });
    fixed("n matches of a function by _", 50, fun_wild, |_| {
        World::new()
    });
}

#[test]
fn matches_of_a_function_scale() {
    check_run("n matches of a function by is", 500, fun_is, |_| {
        World::new()
    });
    check_run("n matches of a function by _", 500, fun_wild, |_| {
        World::new()
    });
}

/// The empty tuple and a bare atom read or made again are the entry they had, and the cells
/// of a dropped tuple are used again, so `n` reads and drops need no free list of entries.
#[test]
fn bare_values_made_and_dropped_use_their_entry_again() {
    fixed("n reads and drops of bare values", 50, bare, bare_world);
}

#[test]
fn bare_values_made_and_dropped_scale() {
    check_run("n reads and drops of bare values", 500, bare, bare_world);
}
