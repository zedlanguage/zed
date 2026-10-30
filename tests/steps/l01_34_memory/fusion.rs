//! Dup/drop fusion: a `match` that owns its scrutinee releases it at the arm's entry, keeping
//! the binders the arm uses; a unique scrutinee's cell is freed and its kept parts move out
//! without a count write.

use std::sync::Arc;

use zed_kernel::term::build::{let_, lit, prim, var};
use zed_kernel::{Pattern, Prim, Term, Value};
use zedc::zir::memory::Mode;

use super::{cat, planned, run};

fn first(scrutinee: Term) -> Term {
    let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
    Term::Match(Arc::new(scrutinee), vec![(p, var("x"))])
}

/// The count writes of `t` with fusion and without, after the same value.
fn writes(t: &Term) -> (u64, u64, String) {
    let (g, p) = planned(t, true);
    let (v, fused) = run(&g, &p).unwrap();
    let (g, p) = planned(t, false);
    let (w, unfused) = run(&g, &p).unwrap();
    assert_eq!(v, w);
    assert_eq!(
        (fused.frees, fused.allocations),
        (unfused.frees, unfused.allocations)
    );
    (fused.writes(), unfused.writes(), v)
}

#[test]
fn a_fresh_pair_destructured_costs_one_write_fused_and_four_unfused() {
    // Fused: the pair's cell is freed and `x` moves out of it; only "cd" is decremented.
    // Unfused: a dup of `x`, then the pair's drop and its two parts'. The result's own drop
    // after the run adds one write to each.
    let t = first(prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")]));
    let (g, p) = planned(&t, true);
    assert_eq!(p.regions["r"].nodes[3].modes, [Mode::Owned]);
    assert_eq!(p.regions["r.3/0"].args, [Mode::Owned]);
    drop(g);
    assert_eq!(writes(&t), (1 + 1, 4 + 1, r#""ab""#.into()));
}

#[test]
fn a_shared_scrutinee_dups_what_it_keeps() {
    // `t = (p, p)` holds the pair twice, so the match's pair is shared: the arm's entry dups
    // `x` and decrements the pair, fused or not, and nothing is freed early.
    let pair = prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")]);
    let get = prim(Prim::TupleGet, vec![var("t"), lit(0)]);
    let t = let_(
        "p",
        pair,
        let_(
            "t",
            prim(Prim::Tuple, vec![var("p"), var("p")]),
            prim(Prim::Tuple, vec![first(get), var("t")]),
        ),
    );
    let (f, u, v) = writes(&t);
    assert_eq!(v, r#"("ab", (("ab", "cd"), ("ab", "cd")))"#);
    assert_eq!(f, u);
}

#[test]
fn a_struct_binder_is_found_by_field_name() {
    // `#point(x: "a" ++ "b", y: "c" ++ "d")` matched by `#point(y: v)`: the payload is
    // sorted by field name, and the arm keeps the cell of `y`.
    let names = Value::Tuple(vec![Value::str("y"), Value::str("x")]);
    let atom = prim(
        Prim::Atom,
        vec![lit("point"), lit(names), cat("c", "d"), cat("a", "b")],
    );
    let p = Pattern::Fields(
        "point".into(),
        vec![("y".into(), Pattern::Bind("v".into()))],
    );
    let t = Term::Match(Arc::new(atom), vec![(p, var("v"))]);
    assert_eq!(writes(&t), (1 + 1, 4 + 1, r#""cd""#.into()));
}
