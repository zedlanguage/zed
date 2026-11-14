//! The four families the cross-review found slow (X13), at the rule of low complexity (DESIGN.md
//! Part G). Each size below is that of the input the check reads, and `power` is its power in
//! the family's parameter: `nth_from_end(n)` has Θ(n) definitions, and the choice chain of depth
//! `d` joins tuples of width `2d + 1` `d` times, Θ(d²) in all. The union of `nth_from_end(1..=n)`
//! has Θ(n²) definitions, so its two sizes are chosen to have 8 times the definitions, counted.
//! Each run clears the kept emptiness results first, and a group is kept with its decisions by
//! its definitions (`Group::instance`), so a run of the lists builds its groups under names no
//! other run used: no run reads another's. Before the fixes E4b took 33.9 s at `n = 3`, the
//! chain did not build in 60 s at `d = 23`, and the union of `nth_from_end(1..=4)` was not
//! decided in 60 s.

use std::hint::black_box;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use zed_kernel::Value;
use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_tests::scaling;

fn def(name: &str, body: Expr) -> Def {
    Def {
        name: name.into(),
        params: vec![],
        body,
    }
}

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn cons(head: Type, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![Expr::Type(head), tail])
}

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).unwrap()
}

/// The lists of integers whose `n`th element from the end is 1: `R{k}` is the lists of exactly
/// `k` integers, and `G` the lists that end in `1` followed by `n - 1` integers.
fn nth_from_end(n: usize) -> Type {
    nth_from_end_named(n, "")
}

/// `nth_from_end(n)` with `tag` after each definition's name. A group is kept by its
/// definitions (`Group::instance`), and its members' decisions with it, so a scaling run that
/// must decide afresh builds its groups under a tag no earlier run used.
fn nth_from_end_named(n: usize, tag: &str) -> Type {
    let mut defs = vec![def(&format!("R0{tag}"), Expr::Type(Type::atom("nil")))];
    for k in 1..n {
        defs.push(def(&format!("R{k}{tag}"), cons(Type::int(), r(k - 1))));
    }
    defs.push(def(
        &format!("G{tag}"),
        Expr::Union(vec![cons(Type::int(), r(n)), cons(lit(1), r(n - 1))]),
    ));
    Group::new(defs).unwrap().instance(vec![]).pop().unwrap()
}

fn nth_union(n: usize) -> Type {
    nth_union_named(n, "")
}

fn nth_union_named(n: usize, tag: &str) -> Type {
    (1..=n).fold(Type::empty(), |t, i| &t | &nth_from_end_named(i, tag))
}

/// The union of `nth_from_end(1..=n)` and that union with `nth_from_end(n + 1)`, under `tag`.
fn nth_pair(n: usize, tag: &str) -> (Type, Type) {
    let t = nth_union_named(n, tag);
    let v = &t | &nth_from_end_named(n + 1, tag);
    (t, v)
}

/// The definitions `nth_pair(n, _)` reads: `nth_from_end(i)` has `i + 1`.
fn nth_pair_size(n: usize) -> usize {
    (1..=n + 1).map(|i| i + 1).sum()
}

/// A tuple type of width `w` that fixes column `k` to 1 and no other.
fn row(k: usize, w: usize) -> Type {
    row_at(k, w, 1)
}

/// A tuple type of width `w` that fixes column `k` to `v` and no other.
fn row_at(k: usize, w: usize, v: i64) -> Type {
    let mut c = vec![Type::top(); w];
    c[k] = lit(v);
    Type::tuple(c)
}

/// The choice chain `t = t & u | !t & v`, `d` times, on independent rows.
fn mux(d: usize) -> Type {
    mux_at(d, 1)
}

/// `mux(d)` on rows that fix their column to `v`.
fn mux_at(d: usize, v: i64) -> Type {
    let (w, row) = (2 * d + 1, |k, w| row_at(k, w, v));
    (0..d).fold(row(0, w), |t, i| {
        &(&t & &row(2 * i + 1, w)) | &(&!&t & &row(2 * i + 2, w))
    })
}

/// The same chain written `(!t | u) & (t | v)`.
fn mux2(d: usize) -> Type {
    mux2_at(d, 1)
}

/// `mux2(d)` on rows that fix their column to `v`.
fn mux2_at(d: usize, v: i64) -> Type {
    let (w, row) = (2 * d + 1, |k, w| row_at(k, w, v));
    (0..d).fold(row(0, w), |t, i| {
        &(&!&t | &row(2 * i + 1, w)) & &(&t | &row(2 * i + 2, w))
    })
}

/// `mux2(d)` with its last choice swapped: not equal to `mux(d)`.
fn swapped(d: usize) -> Type {
    swapped_at(d, 1)
}

/// `swapped(d)` on rows that fix their column to `v`.
fn swapped_at(d: usize, v: i64) -> Type {
    let (y, w, row) = (mux2_at(d, v), 2 * d + 1, |k, w| row_at(k, w, v));
    &(&y & &row(0, w)) | &(&!&y & &row(1, w))
}

#[test]
fn the_families_are_decided_exactly_at_small_sizes() {
    for n in 1..=4 {
        let (a, b) = (nth_from_end(n), nth_from_end(n + 1));
        assert!(a.subtype(&nth_from_end(n)), "n = {n}");
        assert!(!a.subtype(&b) && !b.subtype(&a), "n = {n}");
        let t = nth_union(n);
        assert!(t.subtype(&(&t | &b)) && !(&t | &b).subtype(&t), "n = {n}");
        let u = (1..=n)
            .rev()
            .fold(Type::empty(), |t, i| &t | &nth_from_end(i));
        assert!(t.equiv(&u), "n = {n}");
    }
    for d in 1..=4 {
        assert!(mux(d).equiv(&mux2(d)), "d = {d}");
        assert!(!mux(d).equiv(&swapped(d)), "d = {d}");
    }
}

#[test]
fn the_choice_forms_keep_their_meaning() {
    // Each choice form, nested twice, against the Boolean formula it stands for, on every tuple
    // of 0s and 1s of width 6. Column `k` is in `row(k, 6)` when it is 1. `f` and `g` are the
    // two forms of `if c then x else y`, and `h` and `i` the two forms of `if f then z else u`.
    let w = 6;
    let (c, x, y, z, u) = (row(0, w), row(1, w), row(2, w), row(3, w), row(4, w));
    let f = &(&c & &x) | &(&!&c & &y);
    let g = &(&!&c | &x) & &(&c | &y);
    let h = &(&f & &z) | &(&!&f & &u);
    let i = &(&!&f | &z) & &(&f | &u);
    for bits in 0..1usize << w {
        let b = |k: usize| bits >> k & 1 == 1;
        let v = Value::tuple((0..w).map(|k| Value::Int(i64::from(b(k)))).collect());
        let f1 = if b(0) { b(1) } else { b(2) };
        let h1 = if f1 { b(3) } else { b(4) };
        assert_eq!(f.contains(&v), f1, "f at {bits:06b}");
        assert_eq!(g.contains(&v), f1, "g at {bits:06b}");
        assert_eq!(h.contains(&v), h1, "h at {bits:06b}");
        assert_eq!(i.contains(&v), h1, "i at {bits:06b}");
    }
    // A tuple of another width, and a value that is not a tuple, are in none of them.
    for t in [&f, &g, &h, &i] {
        assert!(!t.contains(&Value::tuple(vec![Value::Int(1); w - 1])));
        assert!(!t.contains(&Value::Int(1)));
    }
}

/// Small instance of `bench::the_choice_chain_with_a_choice_swapped_scales`
/// (TEST-bench-move-l0123, author P170): on rows that fix their column to each of eight values,
/// giving the shared nodes eight shapes, the choice chain equals its other form and differs from
/// the form with a choice swapped. `the_families_are_decided_exactly_at_small_sizes` reads the
/// value 1 only.
#[test]
fn the_choice_chain_keeps_its_answers_on_every_shape() {
    for d in 1..=4 {
        for v in 1..=8 {
            Type::forget_emptiness();
            assert!(mux_at(d, v).equiv(&mux2_at(d, v)), "d = {d}, v = {v}");
            assert!(!mux_at(d, v).equiv(&swapped_at(d, v)), "d = {d}, v = {v}");
        }
    }
}

mod bench;
