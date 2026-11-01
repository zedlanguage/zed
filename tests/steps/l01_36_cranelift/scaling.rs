//! The counting machine and the native code against the size of the program (the rule of low
//! complexity, DESIGN.md Part G): an atom of many named fields, many lookup ports,
//! many constants, many lambdas and one value used many times each run in time near linear in
//! their number (COMPLEXITY.md Z14).

use std::sync::Arc;

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Value, World};
use zed_tests::scaling;
use zedc::zir::memory;

use super::planned;

/// A lookup port whose every key holds the same value.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// Lookup ports `p0`, `p1`, … `p{n-1}`.
fn world(n: usize) -> World {
    let mut w = World::new();
    for i in 0..n {
        let p: Arc<dyn Lookup> = Arc::new(Same(Value::Int(i as i64)));
        w.sources.insert(format!("p{i}"), p);
    }
    w
}

/// `t` run by the counting machine and natively in `w`: both values, printed, which agree.
fn both(t: &Term, w: &World) -> String {
    let (g, p) = planned(t);
    let (v, _) =
        memory::run(&g, &p, &mut Evaluator::new(w.clone())).unwrap_or_else(|e| panic!("{t}: {e}"));
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w.clone()))
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(o.value, v);
    v.to_string()
}

/// `#a(f{n-1}: "x{n-1}" ++ "", …, f0: "x0" ++ "")`, the names given last first, matched by a
/// pattern that binds every field, and the binders made a tuple.
fn fields(n: usize) -> Term {
    let name = |i: usize| format!("f{i:05}");
    let names = Value::Tuple((0..n).rev().map(|i| Value::str(&name(i))).collect());
    let mut ins = vec![lit("a"), lit(names)];
    ins.extend(
        (0..n)
            .rev()
            .map(|i| super::super::l01_34_memory::cat(&format!("x{i}"), "")),
    );
    let p = Pattern::Fields(
        "a".into(),
        (0..n)
            .map(|i| (name(i).into(), Pattern::Bind(format!("v{i}").into())))
            .collect(),
    );
    let body = prim(Prim::Tuple, (0..n).map(|i| var(&format!("v{i}"))).collect());
    Term::Match(Arc::new(prim(Prim::Atom, ins)), vec![(p, body)])
}

/// `(p0(0), p1(0), …)`: `n` lookup ports, each read once.
fn ports(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n)
            .map(|i| app(Term::Read(format!("p{i}").into()), vec![lit(0i64)]))
            .collect(),
    )
}

/// `("s0", "s1", …)`: a tuple of `n` constant strings.
fn consts(n: usize) -> Term {
    prim(
        Prim::Tuple,
        (0..n).map(|i| lit(format!("s{i}").as_str())).collect(),
    )
}

/// `f0 = (x) -> x ++ "0"; …; (f0("a"), f1("a"), …)`: `n` lambdas, each called once.
fn lambdas(n: usize) -> Term {
    let calls = prim(
        Prim::Tuple,
        (0..n)
            .map(|i| app(var(&format!("f{i}")), vec![lit("a")]))
            .collect(),
    );
    (0..n).rev().fold(calls, |b, i| {
        let f = lam(
            &["x"],
            prim(Prim::Concat, vec![var("x"), lit(format!("{i}").as_str())]),
        );
        let_(&format!("f{i}"), f, b)
    })
}

/// `x = "a" ++ "b"; (x, x, …)`: one cell used `n` times by one node.
fn dups(n: usize) -> Term {
    let_(
        "x",
        super::super::l01_34_memory::cat("a", "b"),
        prim(Prim::Tuple, (0..n).map(|_| var("x")).collect()),
    )
}

#[test]
fn small_programs_agree() {
    let w = world(3);
    assert_eq!(both(&fields(3), &w), r#"("x0", "x1", "x2")"#);
    assert_eq!(both(&consts(3), &w), r#"("s0", "s1", "s2")"#);
    assert_eq!(both(&lambdas(3), &w), r#"("a0", "a1", "a2")"#);
    assert_eq!(both(&dups(3), &w), r#"("ab", "ab", "ab")"#);
    assert_eq!(both(&ports(3), &w), "(0, 1, 2)");
}

fn check(what: &str, n: usize, w: &World, make: fn(usize) -> Term) {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 29)
            .spawn_scoped(s, || {
                scaling::check(what, n, |n| {
                    both(&make(n), w);
                })
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn an_atom_of_many_named_fields_scales() {
    check(
        "an atom of n named fields, matched",
        1000,
        &World::new(),
        fields,
    );
}

#[test]
fn a_tuple_of_many_lookup_ports_scales() {
    check("a tuple of n lookup ports", 1000, &world(8000), ports);
}

#[test]
fn many_constants_scale() {
    check("a tuple of n constants", 1000, &World::new(), consts);
}

#[test]
fn many_lambdas_scale() {
    check("n lambdas, each called", 1000, &World::new(), lambdas);
}

#[test]
fn one_value_used_many_times_scales() {
    check(
        "one cell used n times by one node",
        1000,
        &World::new(),
        dups,
    );
}
