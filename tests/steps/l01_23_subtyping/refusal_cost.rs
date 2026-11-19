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
pub(super) fn r3(vars: usize, seed: u64) -> (Type, Type) {
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

/// Small instance of `bench::the_verdict_of_the_x_tail_family_is_refused_in_its_size` and
/// `bench::the_subtype_verdict_of_the_x_tail_family_is_refused_in_its_size`
/// (TEST-bench-move-l0123, author P170): the x_tail family is refused at a fork by `verdict` and
/// by `subtype_verdict` at small sizes, the benchmark's small size 16 among them.
#[test]
fn the_x_tail_family_is_refused_at_a_fork() {
    for n in [1, 2, 4, 16] {
        let (a, b) = x_tail(n, &format!("_small{n}"));
        Type::forget_emptiness();
        assert_eq!((&a - &b).verdict(), Verdict::Refused(Refusal::Fork), "{n}");
        Type::forget_emptiness();
        assert_eq!(
            a.subtype_verdict(&b),
            Verdict::Refused(Refusal::Fork),
            "{n}"
        );
    }
}

/// The number of tuples of `vars` bits in which every clause of `r3(vars, seed)` holds, by trying
/// each of the 2^vars tuples (with the same draws as `r3`).
fn models(vars: usize, seed: u64) -> usize {
    let mut g = Rng::new(seed * 2 + 1);
    let clauses: Vec<Vec<(usize, bool)>> = (0..vars * 426 / 100)
        .map(|_| (0..3).map(|_| (g.below(vars), g.below(2) == 0)).collect())
        .collect();
    (0u64..1 << vars)
        .filter(|x| {
            clauses
                .iter()
                .all(|c| c.iter().any(|&(v, b)| ((x >> v) & 1 == 1) == b))
        })
        .count()
}

/// Both verdicts of `a - b` for `r3(vars, seed)`: `verdict` and `subtype_verdict`.
fn r3_verdicts(vars: usize, seed: u64) -> (Verdict, Verdict) {
    let (a, b) = r3(vars, seed);
    Type::forget_emptiness();
    let v = (&a - &b).verdict();
    Type::forget_emptiness();
    (v, a.subtype_verdict(&b))
}

/// Small instance of `bench::the_verdict_of_random_3_cnf_is_refused_in_its_size` and
/// `bench::the_subtype_verdict_of_random_3_cnf_is_refused_in_its_size`
/// (TEST-bench-move-l0123, author P170): random 3-CNF over 16 bits, seed 7, the benchmarks'
/// small instance, is refused at shared cells of component 0 by `verdict` and by
/// `subtype_verdict`.
#[test]
fn random_3_cnf_is_refused_at_shared_cells() {
    let refused = Verdict::Refused(Refusal::SharedCells(0));
    assert_eq!(r3_verdicts(16, 7), (refused, refused));
}

/// Asserts that both verdicts of `r3(vars, seed)`, which has a model, are `Inhabited`, each
/// resting on a value of the difference. The short-addresses build orders the pairs of
/// `Searching::refine` by other digests, so its blind cuts differ; there it asserts only what
/// holds in both builds: no verdict is `Empty`, and an `Inhabited` one rests on such a value.
fn assert_found(vars: usize, seed: u64) {
    let (a, b) = r3(vars, seed);
    for v in <[Verdict; 2]>::from(r3_verdicts(vars, seed)) {
        match v {
            Verdict::Empty => panic!("r3({vars}, {seed}) has a model, and a verdict is Empty"),
            Verdict::Inhabited => {
                Type::forget_emptiness();
                let x = (&a - &b)
                    .witness()
                    .expect("an Inhabited verdict has a value");
                assert!(
                    a.contains(&x) && !b.contains(&x),
                    "{x} is not in {a} \\ {b}"
                );
            }
            Verdict::Refused(r) => {
                if !cfg!(feature = "short-addresses") {
                    panic!("r3({vars}, {seed}) has a model, and a verdict is refused: {r:?}");
                }
            }
        }
    }
}

/// Seed 2, the benchmarks' instance until GROUP-order-cpoly-merge: over 8 bits no tuple meets
/// every clause (counted by trying all 256) and the verdict is a refusal at shared cells; over
/// 16 bits 5 tuples meet every clause (all 65,536 tried), and both verdicts find one. There
/// `refine` cuts two pairs blindly, at components 0 and 1; the 5 values lie inside the first
/// and outside the second, so the inside pass and the outside pass each end in a box proved
/// empty, and the inside pass finds a value once it undoes its second blind cut and keeps the
/// other side (the tradeoff at `Searching::refine`, COMPLEXITY.md K133; plan row
/// REFUSAL-r3-seed2-16-inhabited).
#[test]
fn random_3_cnf_seed_2_is_refused_at_8_bits_and_found_at_16() {
    let refused = Verdict::Refused(Refusal::SharedCells(0));
    assert_eq!(models(8, 2), 0);
    assert_eq!(r3_verdicts(8, 2), (refused, refused));
    assert_eq!(models(16, 2), 5);
    assert_found(16, 2);
}

/// The passes of `Searching::refine` (COMPLEXITY.md K133). Seed 7 over 8 bits has 2 models;
/// the first pass, cutting each pair it proves neither way to `inside`, finds none, and the
/// second, cutting to `outside`, finds one. Seed 89 over 12 bits has 1 model, which both passes
/// missed until a pass undid its latest blind cut once the box was proved empty. Seed 19 over
/// 16 bits has a model that both passes still miss with that undo: it is refused, a documented
/// miss (in the full build; the short-addresses build cuts in another order). No rule of
/// polynomial work finds a model of every satisfiable 3-CNF unless P = NP.
#[test]
fn random_3_cnf_found_by_a_second_pass_or_an_undone_cut_or_refused() {
    assert_eq!(models(8, 7), 2);
    assert_found(8, 7);
    assert_eq!(models(12, 89), 1);
    assert_found(12, 89);
    assert_eq!(models(16, 19), 5);
    if !cfg!(feature = "short-addresses") {
        let (v, s) = r3_verdicts(16, 19);
        assert!(
            matches!(v, Verdict::Refused(_)) && matches!(s, Verdict::Refused(_)),
            "r3(16, 19): {v:?} and {s:?}"
        );
    }
}

// Measured at 8d0bfe954 with the classes of values (COMPLEXITY.md K111; instructions of
// `subtype_verdict`, `verdict` about 7% less): 131M at n = 16 and 4.01G at n = 128, 30.6 times,
// under a limit of 123. Before, a value read in from each group that built it was tested
// against each type under a number of its own (Θ(n³) tests): 145M and 20.3G, 140 times.

// The benchmarks use seed 7, refused at shared cells at 16 and 128 bits by both verdicts (the
// assert of `refusal_scales`): 39.2 times the time per 8 times the bits, limit 84 (branch
// wt/order2, 2026-11-18, load 41 to 55). With the second, outside pass of `refine` (order3,
// 2026-11-18): 42.8 times the work per 8 times the bits against 39.0 for one pass, measured
// together, load5 63.2 at the start and 62.9 at the end. With the undo of a pass's latest blind
// cut once the box is proved empty (order3b, 2026-11-19): 40.6 times the instructions for both
// verdicts (466M at 16 bits, 18.9G at 128), against 43.7 (412M, 18.0G) without it, load5 21 to
// 27. Seed 2 was used until GROUP-order-cpoly-merge. Measured at 8d0bfe954 for seed 2: 61.0M
// instructions at n = 8 and 3.82G at n = 64, 62.6 times, under a limit of 141.

mod bench;
