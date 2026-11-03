//! The hooks of the native runtime against the counting machine and the kernel: atoms made
//! from their words with no call to the kernel, a binder its arm does not use, and a lookup
//! port as the condition of an `if`.

use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Term, Value, World};
use zedc::zir::memory;

use super::super::l01_34_memory::cat;
use super::planned;
use super::scaling::{counted_in, strings, unused};

/// `#a(n0: a0, n1: a1, …)`, with the field names in the order given; no names makes a tuple
/// payload.
fn named(names: &[&str], args: Vec<Term>) -> Term {
    let ns = Value::tuple(names.iter().map(|n| Value::str(n)).collect());
    let mut ins = vec![lit("a"), lit(ns)];
    ins.extend(args);
    prim(Prim::Atom, ins)
}

/// `t` run natively agrees with the counting machine, in value and counts, and with the
/// kernel; returns the value printed and the native run's kernel calls.
fn agreed(t: &Term, w: World) -> (String, u64) {
    let v = counted_in(t, w.clone());
    let k = Evaluator::new(w.clone())
        .run(t)
        .unwrap_or_else(|e| panic!("{t}: {e}"));
    assert_eq!(v, k.to_string(), "{t}");
    let (g, p) = planned(t);
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w)).unwrap();
    (v, o.kernel_calls)
}

/// The kernel's refusal of `t`, which the native run and the counting machine give too.
fn refused(t: &Term, w: World) -> String {
    let k = match Evaluator::new(w.clone()).run(t) {
        Ok(v) => panic!("{t}: the kernel gives {v}"),
        Err(e) => e.to_string(),
    };
    let (g, p) = planned(t);
    let n = zed_native::run(&g, &p, &mut Evaluator::new(w.clone())).map(|o| o.value);
    assert_eq!(n, Err(k.clone()), "{t}: native");
    let m = memory::run(&g, &p, &mut Evaluator::new(w)).map(|(v, _)| v);
    assert_eq!(m, Err(k.clone()), "{t}: machine");
    k
}

#[test]
fn a_named_atom_holds_its_fields_in_name_order() {
    let t = named(
        &["b", "c", "a"],
        vec![cat("x", "1"), lit(3i64), cat("y", "")],
    );
    assert_eq!(
        agreed(&t, World::new()),
        (r#"#a(a: "y", b: "x1", c: 3)"#.into(), 0)
    );
}

#[test]
fn a_named_atom_gives_each_field_to_its_binder() {
    let atom = named(&["b", "a"], vec![cat("x", "1"), cat("y", "")]);
    let p = Pattern::Fields(
        "a".into(),
        vec![
            ("a".into(), Pattern::Bind("u".into())),
            ("b".into(), Pattern::Bind("v".into())),
        ],
    );
    let t = Term::Match(
        Arc::new(atom),
        vec![(p, prim(Prim::Tuple, vec![var("v"), var("u")]))],
    );
    assert_eq!(agreed(&t, World::new()).0, r#"("x1", "y")"#);
}

#[test]
fn a_positional_atom_keeps_its_order() {
    let t = named(&[], vec![cat("b", ""), lit(1i64), cat("a", "")]);
    assert_eq!(agreed(&t, World::new()), (r#"#a("b", 1, "a")"#.into(), 0));
}

#[test]
fn a_bare_atom_is_made_without_the_kernel() {
    assert_eq!(
        agreed(&named(&[], Vec::new()), World::new()),
        ("#a".into(), 0)
    );
}

/// One atom node run with other payloads, from the shape kept after its first run.
#[test]
fn an_atom_made_many_times_holds_each_payload() {
    let f = lam(&["y"], named(&["b", "a"], vec![var("y"), cat("z", "")]));
    let calls = (0..3).map(|i| app(var("f"), vec![lit(i as i64)])).collect();
    let t = let_("f", f, prim(Prim::Tuple, calls));
    let (v, calls) = agreed(&t, World::new());
    assert_eq!(
        v,
        r#"(#a(a: "z", b: 0), #a(a: "z", b: 1), #a(a: "z", b: 2))"#
    );
    assert_eq!(calls, 0);
}

#[test]
fn a_repeated_field_name_is_the_kernels_refusal() {
    refused(
        &named(&["a", "a"], vec![lit(1i64), lit(2i64)]),
        World::new(),
    );
}

#[test]
fn a_field_name_that_is_not_a_string_is_the_kernels_refusal() {
    let ins = vec![lit("a"), lit(Value::tuple(vec![Value::Int(1)])), lit(2i64)];
    refused(&prim(Prim::Atom, ins), World::new());
}

#[test]
fn field_names_unlike_the_payload_in_number_are_the_kernels_refusal() {
    refused(&named(&["a", "b"], vec![lit(1i64)]), World::new());
    refused(&named(&["a"], Vec::new()), World::new());
}

#[test]
fn an_atom_name_that_is_not_a_string_is_the_kernels_refusal() {
    let ins = vec![lit(1i64), lit(Value::tuple(Vec::new())), lit(2i64)];
    refused(&prim(Prim::Atom, ins), World::new());
}

/// The arm reads `b` and not `a`, which is the whole tuple `x`: the run gives `a` no copy and
/// still agrees with the machine in every count.
#[test]
fn a_binder_the_arm_does_not_use_changes_no_count() {
    assert_eq!(agreed(&unused(3), strings(5)).0, "(0, 1, 2)");
}

/// A lookup port whose every key holds the same value.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// A lookup port as the condition of an `if` is read as every kernel term reads one, so the
/// native run and the counting machine give the kernel's own answer, not an unbound variable.
#[test]
fn a_lookup_port_as_a_condition_is_read() {
    let mut w = World::new();
    let p: Arc<dyn Lookup> = Arc::new(Same(Value::Bool(true)));
    w.sources.insert("p".into(), p);
    let t = if_(Term::Read("p".into()), lit(1i64), lit(2i64));
    assert_eq!(
        refused(&t, w),
        "type error: expected data, found a function"
    );
}
