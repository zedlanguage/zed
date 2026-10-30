//! Static last-use drops and precise counts: which values are cells, a value used once is
//! never counted, a borrowed value is dropped at its last use, and each owned use but the
//! last gets a dup.

use zed_kernel::Prim;
use zed_kernel::term::build::{let_, lit, prim, var};
use zedc::zir::Src;
use zedc::zir::memory::Mode;

use super::{cat, machine};

#[test]
fn a_value_used_once_is_never_counted() {
    // Two fresh strings moved into a fresh pair: three cells, no dup and no drop in the
    // program; the three decrements are the result's, dropped after the run.
    let t = prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")]);
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#"("ab", "cd")"#);
    let r = &p.regions["r"];
    assert!(
        r.nodes
            .iter()
            .all(|n| n.dups.is_empty() && n.drops.is_empty())
    );
    assert_eq!(r.nodes[2].modes, [Mode::Owned, Mode::Owned]);
    assert_eq!(
        (s.increments, s.decrements, s.allocations, s.frees),
        (0, 3, 3, 3)
    );
}

#[test]
fn a_borrowed_value_is_dropped_at_its_last_use() {
    // `s = "ab" ++ "c"; (len(s), upper(s))`: both reads borrow `s`, and the second drops it,
    // so `s` is freed before the pair is made: at most two cells are ever live.
    let t = let_(
        "s",
        cat("ab", "c"),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#"(3, "ABC")"#);
    let r = &p.regions["r"];
    assert_eq!(r.nodes[1].drops, []);
    assert_eq!(r.nodes[2].drops, [Src::Out(0, 0)]);
    assert_eq!((s.increments, s.peak), (0, 2));
}

#[test]
fn each_owned_use_but_the_last_gets_a_dup() {
    // `(s, s)`: the pair holds `s` twice, so `s` gets one dup and its cell is shared.
    let t = let_(
        "s",
        cat("ab", "c"),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#"("abc", "abc")"#);
    assert_eq!(p.regions["r"].nodes[1].dups, [0]);
    assert_eq!((s.increments, s.shared, s.allocations), (1, 1, 2));
}

#[test]
fn strings_tuples_and_big_integers_are_cells_and_scalars_are_not() {
    // A tuple, a big integer and a string are cells; an integer, a float and a boolean are
    // unboxed; a constant string is static. So the tuple below allocates three cells.
    let big = prim(Prim::Pow, vec![lit(2), lit(70)]);
    let t = prim(
        Prim::Tuple,
        vec![
            big,
            lit(1),
            prim(Prim::CastF64, vec![lit(2)]),
            lit(true),
            cat("s", "t"),
            lit("static"),
        ],
    );
    let (v, s, _) = machine(&t);
    assert_eq!(
        v,
        r#"(1180591620717411303424, 1, 2.0, true, "st", "static")"#
    );
    assert_eq!((s.allocations, s.frees), (3, 3));
}

#[test]
fn an_arm_that_ignores_an_owned_capture_drops_it_on_entry() {
    // `if len(s) > 5 { (s, 1) } else { 0 }`: the first arm consumes `s`, so the `if` passes it
    // owned; the second arm, which runs, does not use it and drops it on entry.
    let c = prim(Prim::Gt, vec![prim(Prim::Len, vec![var("s")]), lit(5)]);
    let t = let_(
        "s",
        cat("ab", "c"),
        zed_kernel::term::build::if_(c, prim(Prim::Tuple, vec![var("s"), lit(1)]), lit(0)),
    );
    let (v, s, p) = machine(&t);
    assert_eq!(v, "0");
    assert_eq!(p.regions["r.3/1"].entry_drops, [0]);
    assert_eq!((s.allocations, s.frees, s.increments), (1, 1, 0));
}

#[test]
fn a_borrowed_value_returned_gets_a_dup() {
    // `f = x -> s` returns its capture, which the closure holds: the result is a dup of it.
    let f = zed_kernel::term::build::lam(&["x"], var("s"));
    let call = zed_kernel::term::build::app(var("f"), vec![lit(0)]);
    let t = let_("s", cat("ab", "c"), let_("f", f, call));
    let (v, s, p) = machine(&t);
    assert_eq!(v, r#""abc""#);
    assert_eq!(p.regions["r.1/0"].result_dups, [0]);
    assert_eq!(s.increments, 1);
}
