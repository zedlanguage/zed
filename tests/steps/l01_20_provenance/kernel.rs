//! Fact addresses in kernel terms: calls, higher-order calls, and every region form.

use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, GuardPos, Pattern, Prim, Term, Value, World};
use zed_tests::kernel::*;

use super::{at, origins, trace, unique};

#[test]
fn two_calls_of_one_function_are_two_facts() {
    // let shipping = w -> w * 3 + 5 in shipping(2) + shipping(10)
    let body = add(mul(var("w"), lit(3)), lit(5));
    let t = let_(
        "shipping",
        lam(&["w"], body.clone()),
        add(
            app(var("shipping"), vec![lit(2)]),
            app(var("shipping"), vec![lit(10)]),
        ),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(46));
    unique(&p);
    let calls = at(&p, &body.to_string());
    assert_eq!(calls.len(), 2);
    // Same node, same keypath: only the call site tells them apart.
    assert_eq!(calls[0].address.keypath, calls[1].address.keypath);
    assert_eq!(
        calls[0].address.node.position(),
        calls[1].address.node.position()
    );
    assert_ne!(calls[0].address.node, calls[1].address.node);
    assert_eq!(
        calls
            .iter()
            .map(|f| f.value.clone().unwrap())
            .collect::<Vec<_>>(),
        [Value::Int(11), Value::Int(35)]
    );
}

#[test]
fn a_function_called_through_another_is_named_by_both_call_sites() {
    // let twice = (f, x) -> f(f(x)) in twice(y -> y * 2, 3) + twice(y -> y * 2, 4)
    let twice = lam(
        &["f", "x"],
        app(var("f"), vec![app(var("f"), vec![var("x")])]),
    );
    let double = lam(&["y"], mul(var("y"), lit(2)));
    let t = let_(
        "twice",
        twice,
        add(
            app(var("twice"), vec![double.clone(), lit(3)]),
            app(var("twice"), vec![double, lit(4)]),
        ),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(28));
    unique(&p);
    let doubled = at(&p, "(y * 2)");
    assert_eq!(doubled.len(), 4);
    // Each instance is two calls deep: the call of `twice`, then a call of `f` inside it.
    assert!(doubled.iter().all(|f| f.address.node.0.len() == 3));
}

#[test]
fn an_atom_passed_through_functions_keeps_its_literal_as_origin() {
    // let pass = x -> x; let wrap = x -> pass(x) in wrap(#late)
    let t = let_(
        "pass",
        lam(&["x"], var("x")),
        let_(
            "wrap",
            lam(&["x"], app(var("pass"), vec![var("x")])),
            app(var("wrap"), vec![atom("late")]),
        ),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("late"));
    unique(&p);
    assert_eq!(origins(&p, p.result()), [("#late".into(), "#late".into())]);
}

#[test]
fn a_failure_bound_by_a_match_arm_keeps_its_origin() {
    // match int("7.5x") { #inexact -> 0; n -> n + 1 }: the sum read the cast through `n`.
    let t = Term::Match(
        rc(prim(Prim::CastInt, vec![lit(s("7.5x"))])),
        vec![
            (Pattern::Lit(Value::atom("inexact")), lit(0)),
            (Pattern::Bind("n".into()), add(var("n"), lit(1))),
        ],
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("invalid"));
    unique(&p);
    assert_eq!(
        origins(&p, p.result()),
        [("int(\"7.5x\")".into(), "#invalid".into())]
    );
}

#[test]
fn a_merged_failure_names_the_origin_of_each_member() {
    // let price = int("12x"); let qty = 3 div 0 in price * qty
    let t = let_(
        "price",
        prim(Prim::CastInt, vec![lit(s("12x"))]),
        let_("qty", idiv(lit(3), lit(0)), mul(var("price"), var("qty"))),
    );
    let (v, p) = trace(&t);
    assert_eq!(v.errs().map(|e| e.len()), Some(2), "{v}");
    unique(&p);
    let o = origins(&p, p.result());
    assert_eq!(o.len(), 2, "{o:?}");
    assert!(o[0].0.contains("div") || o[1].0.contains("div"), "{o:?}");
    assert!(o.iter().any(|(t, _)| t.contains("12x")), "{o:?}");
}

#[test]
fn word_count_has_a_fact_per_word_and_per_group() {
    let doc = lines_of(&[&["to", "be", "or"], &["not", "to", "be"]]);
    // Each word to `word -> line -> 1`, then summed over the lines.
    let kf = lam(&["p", "w"], path(vec![var("w"), key(var("p"), 0)]));
    let ones = reindex(lit(doc), kf, lam(&["p", "w"], lit(1)));
    let counts = fold_at(ones, 2, Term::PrimFn(Prim::Add), None);
    let (v, p) = trace(&counts);
    assert_eq!(
        v.to_string(),
        r#"{"be" -> 2, "not" -> 1, "or" -> 1, "to" -> 2}"#
    );
    unique(&p);
    // The value function runs once per word, keyed by the word's line and position.
    let ones: Vec<_> = at(&p, "1")
        .into_iter()
        .map(|f| f.address.keypath.clone())
        .collect();
    assert_eq!(ones.len(), 6);
    assert!(ones.contains(&vec![Value::Int(0), Value::Int(1), Value::Int(2)]));
}

#[test]
fn a_combine_step_is_named_by_its_group_and_index() {
    // Per customer, the order totals summed by a written function.
    let orders = Value::Family(
        Family::from_leaves(vec![
            (vec![s("ann"), Value::Int(1)], Value::Int(5)),
            (vec![s("ann"), Value::Int(2)], Value::Int(7)),
            (vec![s("ann"), Value::Int(3)], Value::Int(9)),
            (vec![s("bob"), Value::Int(4)], Value::Int(2)),
            (vec![s("bob"), Value::Int(5)], Value::Int(4)),
        ])
        .unwrap(),
    );
    let plus = lam(&["a", "b"], add(var("a"), var("b")));
    let (v, p) = trace(&fold_at(lit(orders), 2, plus, None));
    assert_eq!(v.to_string(), r#"{"ann" -> 21, "bob" -> 6}"#);
    unique(&p);
    let mut steps: Vec<_> = at(&p, "(a + b)")
        .into_iter()
        .map(|f| f.address.keypath.clone())
        .collect();
    steps.sort();
    assert_eq!(
        steps,
        [
            vec![Value::Int(0), s("ann"), Value::Int(0)],
            vec![Value::Int(0), s("ann"), Value::Int(1)],
            vec![Value::Int(0), s("bob"), Value::Int(0)],
        ]
    );
}

#[test]
fn a_selector_runs_once_per_key_at_every_level() {
    // Keep the teams and players whose score is above 3; teams always pass.
    let scores = Value::Family(
        Family::from_leaves(vec![
            (vec![s("red"), s("ada")], Value::Int(5)),
            (vec![s("red"), s("bo")], Value::Int(2)),
            (vec![s("blue"), s("cy")], Value::Int(4)),
        ])
        .unwrap(),
    );
    let sel = lam(
        &["p", "v"],
        if_(
            eq(prim(Prim::PathLen, vec![var("p")]), lit(1)),
            lit(true),
            lt(lit(3), var("v")),
        ),
    );
    let (v, p) = trace(&discard(lit(scores), sel));
    assert_eq!(
        v.to_string(),
        r#"{"blue" -> {"cy" -> 4}, "red" -> {"ada" -> 5}}"#
    );
    unique(&p);
    assert_eq!(at(&p, "(3 < v)").len(), 3);
}

#[test]
fn a_family_body_runs_once_per_key() {
    let t = fam(
        lit(Family::set([1, 2, 3].map(Value::Int))),
        "n",
        mul(var("n"), var("n")),
    );
    let (v, p) = trace(&t);
    assert_eq!(v.to_string(), "{1 -> 1, 2 -> 4, 3 -> 9}");
    unique(&p);
    let keys: Vec<_> = at(&p, "(n * n)")
        .into_iter()
        .map(|f| f.address.keypath.clone())
        .collect();
    assert_eq!(keys, [1, 2, 3].map(|n| vec![Value::Int(0), Value::Int(n)]));
}

#[test]
fn a_lattice_fixpoint_names_each_iterate() {
    // Airports reachable from cdg: the `to` of each route whose `from` is reached.
    let routes = Value::Family(Family::set(
        [
            ("cdg", "lhr"),
            ("lhr", "jfk"),
            ("jfk", "sfo"),
            ("syd", "akl"),
        ]
        .map(|(a, b)| Value::Tuple(vec![s(a), s(b)])),
    ));
    let from_reached = discard(
        lit(routes),
        lam(&["p", "e"], found(get(var("r"), nth(var("e"), 0)))),
    );
    let step = lam(
        &["r"],
        fam(group_by(from_reached, |e| nth(e, 1)), "k", var("k")),
    );
    let t = fix_lattice(
        lit(Family::set([s("cdg")])),
        step,
        Term::PrimFn(Prim::Union),
    );
    let (v, p) = trace(&t);
    assert_eq!(v.to_string(), r#"{"cdg", "jfk", "lhr", "sfo"}"#);
    unique(&p);
    // The step ran four times, the last finding nothing new.
    let mut iterates: Vec<_> = p
        .facts()
        .iter()
        .filter(|f| matches!(p.term(&f.address.node), Term::Fam { .. }))
        .map(|f| f.address.keypath.clone())
        .collect();
    iterates.dedup();
    assert_eq!(
        iterates,
        (0..4)
            .map(|i| vec![Value::Int(0), Value::Int(i)])
            .collect::<Vec<_>>()
    );
}

#[test]
fn a_definedness_entry_is_one_fact_however_many_attempts_it_took() {
    let domain = lit(Family::set((0..=12).map(Value::Int)));
    let fib = fix_defined(domain, |this, i| {
        let at = |d: i64| get(this.clone(), sub(i.clone(), lit(d)));
        if_(lt(i.clone(), lit(2)), i.clone(), add(at(1), at(2)))
    });
    let (v, p) = trace(&fib);
    assert_eq!(
        v.as_family().unwrap().get(&Value::Int(12)),
        Some(&Value::Int(144))
    );
    unique(&p);
    // One `if` per entry: the attempts that read an undefined entry were dropped.
    let ifs: Vec<_> = p
        .facts()
        .iter()
        .filter(|f| matches!(p.term(&f.address.node), Term::If(..)))
        .collect();
    assert_eq!(ifs.len(), 13);
}

#[test]
fn a_generation_names_its_step_and_guard_by_t() {
    // Halve 40 while it is even: 40, 20, 10, 5.
    let t = Term::Gen {
        init: Arc::new(lit(40)),
        step: Arc::new(lam(&["x"], idiv(var("x"), lit(2)))),
        guard: Arc::new(lam(&["x"], eq(modulo(var("x"), lit(2)), lit(0)))),
        pos: GuardPos::Before,
    };
    let (v, p) = trace(&t);
    assert_eq!(v.to_string(), "{0 -> 40, 1 -> 20, 2 -> 10, 3 -> 5}");
    unique(&p);
    let steps: Vec<_> = at(&p, "(x div 2)")
        .into_iter()
        .map(|f| f.address.keypath.clone())
        .collect();
    assert_eq!(steps, [1, 2, 3].map(|t| vec![Value::Int(0), Value::Int(t)]));
    let guards = at(&p, "((x mod 2) == 0)");
    assert_eq!(guards.len(), 4);
    // The step making generation 2 read generation 1's fact.
    let made: Vec<_> = at(&p, "(x div 2)")
        .iter()
        .map(|f| f.value.clone().unwrap())
        .collect();
    assert_eq!(made, [20, 10, 5].map(Value::Int));
}

#[test]
fn every_keypath_starts_with_the_wave_stamp() {
    let t = fam(
        lit(Family::set([1, 2].map(Value::Int))),
        "n",
        add(var("n"), lit(1)),
    );
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(7)]);
    ev.run(&t).unwrap();
    let p = ev.provenance().unwrap();
    assert!(
        p.facts()
            .iter()
            .all(|f| f.address.keypath.first() == Some(&Value::Int(7)))
    );
}

#[test]
fn without_the_request_nothing_is_recorded_and_the_value_is_the_same() {
    let t = let_(
        "f",
        lam(&["x"], add(var("x"), lit(1))),
        app(var("f"), vec![lit(1)]),
    );
    let mut ev = Evaluator::new(World::new());
    assert_eq!(ev.run(&t).unwrap(), trace(&t).0);
    assert!(ev.provenance().is_none());
}
