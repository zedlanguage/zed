//! Each kind of stop is reported, with the term it stopped at, and the preimage at a stop
//! keeps the whole domain, so it stays necessary.

use zed_kernel::Shared;

use zed_kernel::term::build::{lam, lit, prim, var};
use zed_kernel::{Family, GuardPos, Prim, Term, Value};
use zed_tests::kernel::{add, eq, fam, fix_lattice, fold, lt, rc, sub};
use zedc::store::preimage::{Demand, StopKind, preimage};

use super::{check, doms, function, listed, pre, pre_listed, shown};

/// The preimage of `true` under `src` over `ds`, printed, after checking it on the window
/// `-150..=150`.
fn holds(src: &str, ds: &[(&str, Option<i64>, Option<i64>)]) -> String {
    let p = pre(src, ds, &Demand::Bool(true));
    let (_, body) = function(src);
    check(&body, &doms(ds), &Demand::Bool(true), &p, (-150, 150));
    shown(&p)
}

#[test]
fn a_string_operation_stops_the_transfer() {
    assert_eq!(
        holds("ok(x) = String(x) == \"12\";\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation `String` stops the transfer at String(x)"
    );
    // Below `len` the string stops it; a listed domain is then enumerated, and the stop is
    // still reported.
    let src = "ok(x) = len(String(x)) <= 2;\n";
    let ds = listed(&[("x", &[-100, -10, -9, 0, 9, 10, 99, 100])]);
    let p = pre_listed(&function(src).1, &ds, &Demand::Bool(true));
    check(&function(src).1, &ds, &Demand::Bool(true), &p, (-100, 100));
    assert_eq!(
        shown(&p),
        "x [-9..=-9, 0..=0, 9..=10, 99..=99]; exact; enumerated; stop: string operation `String` \
         stops the transfer at String(x)"
    );
    assert_eq!(
        holds("ok(x) = len(trim(String(x))) <= 2;\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation `trim` stops the transfer at trim(String(x))"
    );
}

#[test]
fn a_string_operation_on_constants_only_is_run() {
    assert_eq!(
        holds("ok(x) = x < len(String(1000));\n", &[("x", None, None)]),
        "x [..=3]; exact"
    );
}

#[test]
fn a_foreign_call_stops_the_transfer() {
    // `hash` is a foreign function: a name the term does not bind.
    let call = Term::App(
        Shared::new(Term::Var("hash".into())),
        vec![Term::Var("x".into())],
    );
    let t = Term::Prim(Prim::Lt, vec![call, Term::Lit(Value::Int(10))]);
    let p = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)"
    );
    assert_eq!(p.stops[0].kind, StopKind::Foreign("hash".into()));
}

#[test]
fn a_term_outside_the_scalar_catalog_is_reported() {
    // `sum` of a tuple belongs to the catalog's tuple entries, not its scalar ones.
    let x = Term::Var("x".into());
    let tuple = Term::Prim(Prim::Tuple, vec![x, Term::Lit(Value::Int(1))]);
    let t = Term::Prim(
        Prim::Lt,
        vec![Term::Prim(Prim::Sum, vec![tuple]), Term::Lit(Value::Int(5))],
    );
    let wide = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert_eq!(
        shown(&wide),
        "x [..]; necessary; stop: no scalar catalog entry for sum((x, 1))"
    );
    assert_eq!(wide.stops[0].kind, StopKind::Outside);
    // On a listed domain the enumeration decides it, and the stop is still reported.
    let ds = listed(&[("x", &[-10, 2, 3, 5, 10])]);
    let p = pre_listed(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-10, 10));
    assert_eq!(
        shown(&p),
        "x [-10..=-10, 2..=3]; exact; enumerated; stop: no scalar catalog entry for sum((x, 1))"
    );
}

#[test]
fn a_length_under_arithmetic_is_read_through_to_its_stop() {
    assert_eq!(
        holds("ok(x) = len(String(x)) + 1 <= 3;\n", &[("x", None, None)]),
        "x [..]; necessary; stop: string operation `String` stops the transfer at String(x)"
    );
}

#[test]
fn a_call_that_never_returns_stops_where_it_calls_itself() {
    // `w(w) >= x` with `w = \g. g(g)`: each call makes another, so the transfer stops at the
    // first call of `w` made while `w` is being read.
    let g = || Term::Var("g".into());
    let w = Term::Lam(
        vec!["g".into()],
        Shared::new(Term::App(Shared::new(g()), vec![g()])),
    );
    let t = Term::Prim(
        Prim::Ge,
        vec![
            Term::App(Shared::new(w.clone()), vec![w]),
            Term::Var("x".into()),
        ],
    );
    let p = preimage(&t, &doms(&[("x", None, None)]), &Demand::Bool(true));
    assert!(!p.exact, "{}", shown(&p));
    assert!(
        p.stops.iter().any(|s| s.kind == StopKind::Recursion),
        "{}",
        shown(&p)
    );
}

/// The family `0 -> 0, 1 -> 1, …, n - 1 -> n - 1`.
fn upto(n: i64) -> Term {
    let leaves = (0..n).map(|i| (vec![Value::Int(i)], Value::Int(i)));
    Term::Lit(Value::Family(Family::from_leaves(leaves).unwrap()))
}

#[test]
fn a_fold_between_the_demand_and_an_input_stops_the_transfer() {
    // Three monthly payments of `x`, `x + 1` and `x + 2` cents total under 20: reading the
    // demand back through the `fold` would unfold it once per entry, so the transfer stops at
    // the `fold` and keeps the whole box.
    let payments = fam(upto(3), "i", add(var("x"), var("i")));
    let total = fold(payments, Term::PrimFn(Prim::Add), Some(lit(0)));
    let t = lt(total, lit(20));
    let ds = doms(&[("x", None, None)]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: no scalar catalog entry for fold(fam({0, 1, 2}, \
         i -> (x + i)), (+), identity: 0, depth: 1, ev: {})"
    );
    assert_eq!(p.stops.len(), 1);
    assert_eq!(p.stops[0].kind, StopKind::Outside);
    // On a listed domain the enumeration decides it, and the stop is still reported.
    let ds = listed(&[("x", &[0, 5, 6, 100])]);
    let p = pre_listed(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [0..=0, 5..=5]; exact; enumerated; stop: no scalar catalog entry for \
         fold(fam({0, 1, 2}, i -> (x + i)), (+), identity: 0, depth: 1, ev: {})"
    );
}

#[test]
fn a_gen_between_the_demand_and_an_input_stops_the_transfer() {
    // A countdown from `x` shows 3, 2, 1, 0: the frames of a `gen` compared with a family.
    // The comparison is not of integers, so its operands are scanned for stops, and the scan
    // stops at the `gen`.
    let countdown = Term::Gen {
        init: rc(var("x")),
        step: rc(lam(&["n"], sub(var("n"), lit(1)))),
        guard: rc(lam(&["n"], prim(Prim::Gt, vec![var("n"), lit(0)]))),
        pos: GuardPos::Before,
    };
    let shows =
        Family::from_leaves((0..4).map(|i| (vec![Value::Int(i)], Value::Int(3 - i)))).unwrap();
    let t = eq(countdown, Term::Lit(Value::Family(shows)));
    let ds = doms(&[("x", None, None)]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: no scalar catalog entry for gen(x, n -> (n - 1), \
         n -> (n > 0), guard: before)"
    );
    assert_eq!(p.stops.len(), 1);
    assert_eq!(p.stops[0].kind, StopKind::Outside);
    // A `gen` is not shown to end, so a listed domain is not enumerated either: the box is
    // the whole listed domain.
    let ds = listed(&[("x", &[-1, 2, 3, 4])]);
    let p = pre_listed(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [-1..=-1, 2..=4]; necessary; stop: no scalar catalog entry for gen(x, n -> (n - 1), \
         n -> (n > 0), guard: before)"
    );
}

#[test]
fn a_fix_between_the_demand_and_an_input_stops_the_transfer() {
    // A level starts at `x` and climbs one step at a time to a ceiling of 10, so it settles
    // at the larger of `x` and 10; it must stay under 12. The transfer stops at the `fix`.
    let climb = lam(
        &["n"],
        prim(Prim::Min, vec![add(var("n"), lit(1)), lit(10)]),
    );
    let level = fix_lattice(var("x"), climb, Term::PrimFn(Prim::Max));
    let t = lt(level, lit(12));
    let ds = doms(&[("x", None, None)]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: no scalar catalog entry for fix(x, n -> min((n + 1), 10), \
         join: max, ev: {})"
    );
    assert_eq!(p.stops.len(), 1);
    assert_eq!(p.stops[0].kind, StopKind::Outside);
    // Nor is a `fix` shown to end: on a listed domain the box is the whole domain.
    let ds = listed(&[("x", &[-5, 10, 11, 12, 40])]);
    let p = pre_listed(&t, &ds, &Demand::Bool(true));
    check(&t, &ds, &Demand::Bool(true), &p, (-150, 150));
    assert_eq!(
        shown(&p),
        "x [-5..=-5, 10..=12, 40..=40]; necessary; stop: no scalar catalog entry for fix(x, \
         n -> min((n + 1), 10), join: max, ev: {})"
    );
}

/// `hash(a)`, a call of the foreign name `hash`.
fn hash(a: Term) -> Term {
    Term::App(Shared::new(var("hash")), vec![a])
}

#[test]
fn copies_of_a_stop_are_two_stops_shown_once() {
    // `hash(x) < 10 && hash(x) > 0`, each `hash(x)` its own copy: two stops, which print alike
    // and are shown once.
    let call = || hash(var("x"));
    let t = prim(
        Prim::And,
        vec![lt(call(), lit(10)), prim(Prim::Gt, vec![call(), lit(0)])],
    );
    let ds = doms(&[("x", None, None)]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    assert_eq!(p.stops.len(), 2);
    assert_eq!(p.stop_texts().len(), 1);
    assert_eq!(
        shown(&p),
        "x [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x)"
    );
    // One call held in a `let` and read twice is one term, so one stop.
    let t = Term::Let(
        "h".into(),
        Shared::new(call()),
        Shared::new(prim(
            Prim::And,
            vec![
                lt(var("h"), lit(10)),
                prim(Prim::Gt, vec![var("h"), lit(0)]),
            ],
        )),
    );
    let p = preimage(&t, &ds, &Demand::Bool(true));
    assert_eq!(p.stops.len(), 1);
    assert_eq!(p.stops[0].kind, StopKind::Foreign("hash".into()));
    // Two calls that print apart are two stops, each shown.
    let t = prim(
        Prim::And,
        vec![lt(call(), lit(10)), lt(hash(var("y")), lit(10))],
    );
    let ds = doms(&[("x", None, None), ("y", None, None)]);
    let p = preimage(&t, &ds, &Demand::Bool(true));
    assert_eq!(
        shown(&p),
        "x [..]; y [..]; necessary; stop: foreign name `hash` stops the transfer at hash(x); \
         stop: foreign name `hash` stops the transfer at hash(y)"
    );
}

/// `s = x + 1 + … + 1` with `n` ones, one shared term, and `hash(let u = s in u) < 0 && … &&
/// hash(let u = s in u) < n - 1`: `n` stops, each at a term that prints at the size of `s`.
fn stops_over_one_term(n: usize) -> Term {
    let s = Shared::new((0..n).fold(var("x"), |a, _| add(a, lit(1))));
    let call = || hash(Term::Let("u".into(), s.clone(), Shared::new(var("u"))));
    (1..n as i64).fold(lt(call(), lit(0)), |a, j| {
        prim(Prim::And, vec![a, lt(call(), lit(j))])
    })
}

/// A stop holds its term and makes its text only when read, so `n` stops over one shared term
/// of size `n` take time of order `n`; printing each stop's term during the transfer took
/// `n^2`.
#[test]
fn many_stops_over_one_shared_term_make_no_text() {
    let ds = doms(&[("x", None, None)]);
    let ds = &ds;
    let terms = zed_tests::scaling::inputs(64, stops_over_one_term);
    zed_tests::scaling::on_a_thread(2 << 20, || {
        zed_tests::scaling::check("stops over one shared term", 64, |n| {
            let p = preimage(&terms[&n], ds, &Demand::Bool(true));
            assert_eq!(p.stops.len(), n);
        })
    });
}
