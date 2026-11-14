//! The cost of the verdicts that end in a refusal (item T6-refusal-cost): `verdict` and
//! `subtype_verdict` on two families whose verdict is `Refused` at every size, each refused for
//! the same cause at n and 8n. The x_tail family (the lists of integers against the lists with a
//! 1 at place i from the end, for each i up to n, and one with a 1 at place n + 1 or further) is
//! refused at a fork; random 3-CNF over n bits at 4.26 clauses a variable is refused at shared
//! cells (COMPLEXITY.md K71). Both are written in Θ(n²): the x_tail family as n + O(1) groups,
//! the one for place i of i + 1 definitions, and a CNF as 4.26n clauses of three tuple types of
//! n components. So each is held to power 2 in n, the order of the size written. The inputs are
//! built before any run is timed, one for each run, each named apart, so that no run reads a
//! group another run judged.

use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use zed_kernel::Value;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;
use zed_tests::scaling;

fn r(i: usize) -> Expr {
    Expr::Ref(i, vec![])
}

fn cons(head: Type, tail: Expr) -> Expr {
    Expr::Atom("cons".into(), vec![Expr::Type(head), tail])
}

fn nil() -> Expr {
    Expr::Type(Type::atom("nil"))
}

fn lit(i: i64) -> Type {
    Type::lit(&Value::Int(i)).expect("an integer literal")
}

fn def(name: &str, body: Expr) -> Def {
    Def {
        name: name.into(),
        params: vec![],
        body,
    }
}

/// Member `at` of the group `defs`.
fn member(defs: Vec<Def>, at: usize) -> Type {
    Group::new(defs)
        .expect("a group")
        .instance(vec![])
        .remove(at)
}

/// The lists of `head`.
fn list_of(head: Type, tag: &str) -> Type {
    member(
        vec![def(
            &format!("L{tag}"),
            Expr::Union(vec![nil(), cons(head, r(0))]),
        )],
        0,
    )
}

/// The lists of integers with a 1 at place `n` from the end (place 1 the last item): `G` holds
/// any integer before a `G`, or a 1 before one of the lists `R(n - 1)` of `n - 1` items.
fn nth(n: usize, tag: &str) -> Type {
    let mut defs = vec![def(&format!("R0{tag}"), nil())];
    defs.extend((1..n).map(|k| def(&format!("R{k}{tag}"), cons(Type::int(), r(k - 1)))));
    defs.push(def(
        &format!("G{tag}"),
        Expr::Union(vec![cons(Type::int(), r(n)), cons(lit(1), r(n - 1))]),
    ));
    member(defs, n)
}

/// The lists of integers with a 1 at place `n + 1` from the end or further.
fn far(n: usize, tag: &str) -> Type {
    let mut defs = vec![def(
        &format!("FL{tag}"),
        Expr::Union(vec![nil(), cons(Type::int(), r(0))]),
    )];
    defs.extend((1..=n).map(|k| def(&format!("F{k}{tag}"), cons(Type::int(), r(k - 1)))));
    defs.push(def(
        &format!("FH{tag}"),
        Expr::Union(vec![cons(Type::int(), r(n + 1)), cons(lit(1), r(n))]),
    ));
    member(defs, n + 1)
}

/// The x_tail family at `n` (cross-review Q1Q7, `x_tail.rs`, case `nfa`): the lists of integers
/// and the union of the lists with no 1, those with a 1 at place i from the end for each i up to
/// n, and those with one further on. Every list is in the union, but the decision of the
/// difference follows the places at once, a fork.
fn x_tail(n: usize, tag: &str) -> (Type, Type) {
    let list = list_of(Type::int(), &format!("{tag}l"));
    let b = (1..=n).fold(
        list_of(&Type::int() - &lit(1), &format!("{tag}n")),
        |b, i| &b | &nth(i, &format!("{tag}_{i}")),
    );
    (list, &b | &far(n, tag))
}

/// The tuples of `vars` bits, and the complement of those in which every clause of random 3-CNF
/// at 4.26 clauses a variable holds, by `seed` (the generator of `two_sat.rs`); each literal is
/// the tuple type with that bit fixed and `top` elsewhere.
fn r3(vars: usize, seed: u64) -> (Type, Type) {
    let mut g = Rng::new(seed * 2 + 1);
    let cylinder = |v: usize, b: bool| {
        let mut c = vec![Type::top(); vars];
        c[v] = lit(i64::from(b));
        Type::tuple(c)
    };
    let t = (0..vars * 426 / 100).fold(Type::top(), |t, _| {
        let c = (0..3).fold(Type::empty(), |u, _| {
            let (v, b) = (g.below(vars), g.below(2) == 0);
            &u | &cylinder(v, b)
        });
        &t & &c
    });
    (Type::tuple(vec![&lit(0) | &lit(1); vars]), !&t)
}

/// Holds the verdict of `a - b`, or `a.subtype_verdict(b)` when `subtype`, for `make(n, tag)` to
/// power 2 in n: refused for `cause` at n and 8n, in every run.
fn refusal_scales(
    what: &str,
    n: usize,
    cause: Refusal,
    subtype: bool,
    make: impl Fn(usize, &str) -> (Type, Type) + Send + Sync,
) {
    scaling::on_a_thread(1 << 28, || {
        let (small_runs, large_runs) = scaling::Meter::new().runs();
        let inputs = |m: usize, runs: usize| -> Vec<(Type, Type, Type)> {
            (0..runs)
                .map(|i| {
                    let (a, b) = make(m, &format!("_rc{m}_{i}"));
                    let d = &a - &b;
                    (a, b, d)
                })
                .collect()
        };
        let small = inputs(n, small_runs);
        let large = inputs(scaling::FACTOR * n, large_runs);
        let (si, li) = (AtomicUsize::new(0), AtomicUsize::new(0));
        scaling::check_order(what, n, 2, |m| {
            Type::forget_emptiness();
            let (a, b, d) = if m == n {
                &small[si.fetch_add(1, Relaxed)]
            } else {
                &large[li.fetch_add(1, Relaxed)]
            };
            let v = if subtype {
                a.subtype_verdict(b)
            } else {
                d.verdict()
            };
            assert_eq!(v, Verdict::Refused(cause), "{what} at {m}");
        });
    });
}

// Measured at 8d0bfe954 with the classes of values (COMPLEXITY.md K111; instructions of
// `subtype_verdict`, `verdict` about 7% less): 131M at n = 16 and 4.01G at n = 128, 30.6 times,
// under a limit of 123. Before, a value read in from each group that built it was tested
// against each type under a number of its own (Θ(n³) tests): 145M and 20.3G, 140 times.

// Seed 2 is refused at shared cells at both sizes; other seeds are decided at one of them,
// Empty or Inhabited by the instance, not by its size. Measured at 8d0bfe954: 61.0M
// instructions at n = 8 and 3.82G at n = 64, 62.6 times, under a limit of 141.

mod bench;
