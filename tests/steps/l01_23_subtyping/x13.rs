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

/// The sizes of the union compared: 64, and 186, whose input has 8.04 times the definitions
/// (2,210 and 17,765).
const NTH_SIZES: (usize, usize) = (64, 186);

/// A tuple type of width `w` that fixes column `k` to 1 and no other.
fn row(k: usize, w: usize) -> Type {
    let mut c = vec![Type::top(); w];
    c[k] = lit(1);
    Type::tuple(c)
}

/// The choice chain `t = t & u | !t & v`, `d` times, on independent rows.
fn mux(d: usize) -> Type {
    let w = 2 * d + 1;
    (0..d).fold(row(0, w), |t, i| {
        &(&t & &row(2 * i + 1, w)) | &(&!&t & &row(2 * i + 2, w))
    })
}

/// The same chain written `(!t | u) & (t | v)`.
fn mux2(d: usize) -> Type {
    let w = 2 * d + 1;
    (0..d).fold(row(0, w), |t, i| {
        &(&!&t | &row(2 * i + 1, w)) & &(&t | &row(2 * i + 2, w))
    })
}

/// `mux2(d)` with its last choice swapped: not equal to `mux(d)`.
fn swapped(d: usize) -> Type {
    let (y, w) = (mux2(d), 2 * d + 1);
    &(&y & &row(0, w)) | &(&!&y & &row(1, w))
}

fn big(f: impl FnOnce() + Send) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, f)
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn the_families_are_decided_exactly_at_small_sizes() {
    big(|| {
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
    });
}

#[test]
fn e4b_scales() {
    // Input Θ(n). Neither of `nth_from_end(n)` and `nth_from_end(n + 1)` contains the other.
    // A chain of plain lists was walked once from each of its definitions, Θ(n²) in all.
    big(|| {
        let tag = AtomicUsize::new(0);
        scaling::check_order("E4b, by n", 64, 1, |n| {
            Type::forget_emptiness();
            let tag = format!("_{}", tag.fetch_add(1, Relaxed) + 1);
            let (a, b) = (nth_from_end_named(n, &tag), nth_from_end_named(n + 1, &tag));
            assert!(!a.subtype(&b) && !b.subtype(&a));
        })
    });
}

/// Why the union's two sizes may differ 24 times in work.
const NTH_WHY: &str = "the input has 8.04 times the definitions; for work of order n log n in \
                       them the rule of low complexity allows at most 24 times (DESIGN.md Part G)";

#[test]
fn the_union_of_nth_from_end_is_built_in_its_size() {
    // The input is Θ(n²) definitions; the build reads each once.
    big(|| {
        let ((n, m), tag) = (NTH_SIZES, AtomicUsize::new(0));
        let build = |k: usize| {
            black_box(nth_pair(k, &format!("_b{}", tag.fetch_add(1, Relaxed) + 1)));
        };
        let (small, large) = (nth_pair_size(n), nth_pair_size(m));
        assert!((8.0..8.1).contains(&(large as f64 / small as f64)));
        scaling::compare(
            &format!("the nth union built: n {n} and {m}, {small} and {large} definitions"),
            NTH_WHY,
            24.0,
            || build(n),
            || build(m),
        );
    });
}

#[test]
fn the_union_of_nth_from_end_is_decided_in_its_size() {
    // `t <: t | nth_from_end(n + 1)` holds, and the converse does not: a list of `n + 1`
    // integers that starts with 1 is in `nth_from_end(n + 1)` alone. Each run decides a pair
    // built before any run is timed, under its own tag.
    big(|| {
        let (n, m) = NTH_SIZES;
        let (runs_small, runs_large) = scaling::Meter::new().runs();
        let pool = |k: usize, runs: usize| {
            let pairs = (0..runs).map(|i| nth_pair(k, &format!("_{k}_{i}")));
            Mutex::new(pairs.collect::<Vec<_>>())
        };
        let (small_pairs, large_pairs) = (pool(n, runs_small), pool(m, runs_large));
        let decide = |pairs: &Mutex<Vec<(Type, Type)>>| {
            let (t, v) = pairs
                .lock()
                .expect("the pool of pairs")
                .pop()
                .expect("one pair per run");
            Type::forget_emptiness();
            assert!(t.subtype(&v));
            assert!(!v.subtype(&t));
        };
        let (small, large) = (nth_pair_size(n), nth_pair_size(m));
        scaling::compare(
            &format!("the nth union decided: n {n} and {m}, {small} and {large} definitions"),
            NTH_WHY,
            24.0,
            || decide(&small_pairs),
            || decide(&large_pairs),
        );
    });
}

#[test]
fn the_choice_chain_scales() {
    // Input Θ(d²): power 2 in d. The build alone at d = 23 took more than 60 s.
    big(|| {
        scaling::check_order("the choice chain, built and compared, by d", 23, 2, |d| {
            Type::forget_emptiness();
            assert!(mux(d).equiv(&mux2(d)));
        })
    });
}

#[test]
fn the_choice_chain_with_a_choice_swapped_scales() {
    big(|| {
        scaling::check_order("the choice chain against a swapped one, by d", 4, 2, |d| {
            Type::forget_emptiness();
            assert!(!mux(d).equiv(&swapped(d)));
        })
    });
}
