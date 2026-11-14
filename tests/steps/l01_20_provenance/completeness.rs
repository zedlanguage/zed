//! The completeness pass over provenance (row TEST-complete-diagnostics): the cases
//! COMPLETENESS.md lists that the other files leave out. Expected results are from DESIGN.md,
//! step L1.20.

use std::collections::HashSet;

use zed_kernel::provenance::Position;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, Pattern, Prim, Term, Value, World};
use zed_tests::kernel::*;

use super::{at, origins, trace, unique};

/// `(a, b)`.
fn pair(a: Term, b: Term) -> Term {
    prim(Prim::Tuple, vec![a, b])
}

/// `int(text)`.
fn cast(text: &str) -> Term {
    prim(Prim::CastInt, vec![lit(s(text))])
}

/// The keypath of `f`, as a plain list.
fn keys(f: &zed_kernel::Fact) -> Vec<Value> {
    f.address.keypath.iter().cloned().collect()
}

#[test]
fn positions_print_as_their_child_indices() {
    let root = Position::root();
    assert_eq!(root.to_string(), ".");
    assert_eq!(root.depth(), 0);
    assert!(root.path().is_empty());
    let p = root.child(1).child(0);
    assert_eq!(p.to_string(), ".1.0");
    assert_eq!(p.depth(), 2);
    assert_eq!(p.path(), [1, 0]);
}

#[test]
fn two_positions_built_apart_are_equal_when_their_paths_are() {
    let a = Position::root().child(2).child(5).child(0);
    let b = Position::root().child(2).child(5).child(0);
    assert_eq!(a, b);
    let set: HashSet<Position> = [a.clone(), b].into_iter().collect();
    assert_eq!(set.len(), 1);
    // A shared prefix with one index changed, at the top, the middle or the bottom.
    for other in [
        Position::root().child(3).child(5).child(0),
        Position::root().child(2).child(4).child(0),
        Position::root().child(2).child(5).child(1),
        Position::root().child(2).child(5),
        Position::root(),
    ] {
        assert_ne!(a, other, "{a} against {other}");
    }
}

#[test]
fn positions_are_ordered_as_the_term_preorder() {
    let r = Position::root();
    let p = |path: &[u32]| path.iter().fold(Position::root(), |p, &i| p.child(i));
    // A node comes before every node below it, and siblings in index order; the index
    // nearest the root decides, whatever lies below it.
    let ordered = [
        r.clone(),
        p(&[0]),
        p(&[0, 9]),
        p(&[0, 9, 9]),
        p(&[1]),
        p(&[1, 0]),
        p(&[2, 0, 0]),
        p(&[10]),
    ];
    for (i, a) in ordered.iter().enumerate() {
        for (j, b) in ordered.iter().enumerate() {
            assert_eq!(a.cmp(b), i.cmp(&j), "{a} against {b}");
        }
    }
    // Two positions sharing their links compare as equal.
    let q = p(&[4, 2]);
    assert_eq!(q.cmp(&q.clone()), std::cmp::Ordering::Equal);
}

#[test]
fn a_fact_address_prints_its_call_sites_then_its_keypath() {
    let t = fam(
        lit(Family::set([5].map(Value::Int))),
        "n",
        add(var("n"), lit(1)),
    );
    let (_, p) = trace(&t);
    let body = at(&p, "(n + 1)");
    assert_eq!(body.len(), 1);
    assert_eq!(body[0].address.to_string(), ".1@(0, 5)");
    let result = &p.facts()[p.result()];
    assert_eq!(result.address.to_string(), ".@(0)");
}

#[test]
fn a_variable_is_no_fact() {
    // let x = 5 in x: the facts are the literal and the `let`, never the read of `x`.
    let t = let_("x", lit(5), var("x"));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(5));
    assert!(at(&p, "x").is_empty());
    assert_eq!(p.facts().len(), 2);
    // The `let` read the facts its two subterms produced: the bound literal, and the body,
    // which passes the literal on through `x`.
    assert_eq!(p.facts()[p.result()].inputs, [0, 0]);
}

#[test]
fn an_application_reads_its_function_its_arguments_and_its_body() {
    // (w -> w + 1)(41)
    let t = app(lam(&["w"], add(var("w"), lit(1))), vec![lit(41)]);
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(42));
    unique(&p);
    let terms = p.fact_terms();
    let r = p.result();
    let read: Vec<String> = p.facts()[r]
        .inputs
        .iter()
        .map(|&i| terms[i].to_string())
        .collect();
    assert_eq!(read.len(), 3, "{read:?}");
    assert!(read[0].contains("->"), "the function first: {read:?}");
    assert_eq!(read[1], "41");
    assert_eq!(read[2], "(w + 1)");
}

#[test]
fn a_function_fact_has_no_value_and_holds_no_failure() {
    let t = app(lam(&["w"], var("w")), vec![lit(1)]);
    let (_, p) = trace(&t);
    let terms = p.fact_terms();
    let funs: Vec<_> = p
        .facts()
        .iter()
        .zip(&terms)
        .filter(|(_, t)| matches!(t, Term::Lam(..)))
        .map(|(f, _)| f)
        .collect();
    assert_eq!(funs.len(), 1);
    assert!(funs[0].value.is_none());
    assert!(!funs[0].holds_failure);
}

#[test]
fn every_fact_comes_after_the_facts_it_read() {
    let t = let_(
        "f",
        lam(&["x"], mul(var("x"), lit(2))),
        fam(
            lit(Family::set([1, 2, 3].map(Value::Int))),
            "k",
            app(var("f"), vec![var("k")]),
        ),
    );
    let (_, p) = trace(&t);
    unique(&p);
    for (j, f) in p.facts().iter().enumerate() {
        assert!(
            f.inputs.iter().all(|&k| k < j),
            "fact {j} reads {:?}",
            f.inputs
        );
    }
}

#[test]
fn the_result_fact_is_the_last_and_holds_the_value() {
    let t = add(lit(2), mul(lit(3), lit(4)));
    let (v, p) = trace(&t);
    assert_eq!(p.result(), p.facts().len() - 1);
    assert_eq!(p.facts()[p.result()].value, Some(v));
}

#[test]
fn each_fact_term_is_the_term_at_its_node() {
    let t = let_(
        "f",
        lam(&["x"], if_(lt(var("x"), lit(2)), var("x"), lit(0))),
        add(app(var("f"), vec![lit(1)]), app(var("f"), vec![lit(5)])),
    );
    let (_, p) = trace(&t);
    let terms = p.fact_terms();
    for (f, t) in p.facts().iter().zip(terms) {
        assert_eq!(p.term(&f.address.node).to_string(), t.to_string());
    }
}

#[test]
fn a_fact_holding_no_failure_has_no_origins() {
    let (_, p) = trace(&add(lit(1), lit(2)));
    assert!(p.origins(p.result()).is_empty());
    assert!(p.facts().iter().all(|f| !f.holds_failure));
}

#[test]
fn a_failure_taken_from_a_tuple_has_its_origin_where_it_was_made() {
    // (int("x1"), 7).0: the tuple holds the failure, so it is not where the failure appears.
    let t = nth(pair(cast("x1"), lit(7)), 0);
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("invalid"));
    unique(&p);
    assert_eq!(
        origins(&p, p.result()),
        [("int(\"x1\")".into(), "#invalid".into())]
    );
    let tuples: Vec<_> = p
        .facts()
        .iter()
        .filter(|f| matches!(&f.value, Some(Value::Tuple(_))))
        .collect();
    assert_eq!(tuples.len(), 1);
    assert!(tuples[0].holds_failure);
}

#[test]
fn a_failure_taken_from_a_family_has_its_origin_in_the_entry() {
    // fam({1, 2}, n -> if n == 2 then int("y") else n)[2]
    let t = get(
        fam(
            lit(Family::set([1, 2].map(Value::Int))),
            "n",
            if_(eq(var("n"), lit(2)), cast("y"), var("n")),
        ),
        lit(2),
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("invalid"));
    unique(&p);
    let o: Vec<_> = p.origins(p.result()).into_iter().collect();
    assert_eq!(o.len(), 1);
    let f = &p.facts()[o[0]];
    assert_eq!(p.term(&f.address.node).to_string(), "int(\"y\")");
    assert_eq!(keys(f), [Value::Int(0), Value::Int(2)]);
    // The family holds the failure in an entry's value.
    let fams: Vec<_> = p
        .facts()
        .iter()
        .filter(|f| matches!(&f.value, Some(Value::Family(_))) && f.inputs.len() > 1)
        .collect();
    assert!(fams.iter().any(|f| f.holds_failure));
}

#[test]
fn a_failure_in_a_payload_has_its_origin_where_it_was_made() {
    // match #wrap(int("z")) { #wrap(e) -> e; _ -> 0 }
    let t = Term::Match(
        rc(prim(
            Prim::Atom,
            vec![lit(s("wrap")), lit(Value::tuple(vec![])), cast("z")],
        )),
        vec![
            (
                Pattern::Atom("wrap".into(), vec![Pattern::Bind("e".into())]),
                var("e"),
            ),
            (Pattern::Wild, lit(0)),
        ],
    );
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("invalid"));
    unique(&p);
    assert_eq!(
        origins(&p, p.result()),
        [("int(\"z\")".into(), "#invalid".into())]
    );
}

#[test]
fn one_atom_made_at_two_facts_has_both_as_origins() {
    // int("a") + int("b"): the sum passes on its left `#invalid`, and both casts made one.
    let t = add(cast("a"), cast("b"));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("invalid"));
    unique(&p);
    assert_eq!(
        origins(&p, p.result()),
        [
            ("int(\"a\")".into(), "#invalid".into()),
            ("int(\"b\")".into(), "#invalid".into())
        ]
    );
}

#[test]
fn a_failed_condition_is_the_origin_of_the_if() {
    // if int("q") == 1 then 1 else 2: the comparison has an arrow at an atom, so the
    // condition is false, and the `if` holds no failure.
    let t = if_(eq(cast("q"), lit(1)), lit(1), lit(2));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(2));
    assert!(p.origins(p.result()).is_empty());
    // A condition that is the failure itself: the `if` passes it on.
    let t = if_(cast("maybe"), lit(1), lit(2));
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(0)]);
    let v = ev.run(&t).unwrap();
    let p = ev.provenance().unwrap();
    assert!(matches!(v, Value::Atom(_)), "{v}");
    let o = origins(&p, p.result());
    assert_eq!(o.len(), 1, "{o:?}");
    assert!(o[0].0.contains("maybe"), "{o:?}");
}

#[test]
fn nested_families_give_a_key_per_level() {
    // fam({1, 2}, i -> fam({10, 20}, j -> i + j))
    let t = fam(
        lit(Family::set([1, 2].map(Value::Int))),
        "i",
        fam(
            lit(Family::set([10, 20].map(Value::Int))),
            "j",
            add(var("i"), var("j")),
        ),
    );
    let (_, p) = trace(&t);
    unique(&p);
    let mut paths: Vec<_> = at(&p, "(i + j)").into_iter().map(keys).collect();
    paths.sort();
    let want: Vec<Vec<Value>> = [(1, 10), (1, 20), (2, 10), (2, 20)]
        .map(|(i, j)| vec![Value::Int(0), Value::Int(i), Value::Int(j)])
        .into();
    assert_eq!(paths, want);
}

#[test]
fn a_primitive_a_fold_calls_is_no_fact() {
    // fold({0 -> 1, 1 -> 2, 2 -> 3}, +): no fact inside the fold's tree.
    let f = Family::from_leaves((0..3).map(|i| (vec![Value::Int(i)], Value::Int(i + 1)))).unwrap();
    let t = fold(lit(Value::Family(f)), Term::PrimFn(Prim::Add), None);
    let (v, p) = trace(&t);
    assert_eq!(v, Value::Int(6));
    assert!(
        p.facts().iter().all(|f| f.address.keypath.len() == 1),
        "{:?}",
        p.facts()
            .iter()
            .map(|f| f.address.to_string())
            .collect::<Vec<_>>()
    );
}

#[test]
fn a_run_that_stops_with_an_error_records_nothing() {
    let t = add(lit(1), lit(s("x")));
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(0)]);
    assert!(ev.run(&t).is_err());
    assert!(ev.provenance().is_none());
}

#[test]
fn a_second_run_records_only_its_own_facts() {
    let mut ev = Evaluator::new(World::new()).with_provenance(vec![Value::Int(0)]);
    ev.run(&add(lit(1), lit(2))).unwrap();
    let first = ev.provenance().unwrap();
    ev.run(&lit(9)).unwrap();
    let second = ev.provenance().unwrap();
    assert_eq!(first.facts().len(), 3);
    assert_eq!(second.facts().len(), 1);
    assert_eq!(second.facts()[0].value, Some(Value::Int(9)));
    // Asked again, nothing is left.
    assert!(ev.provenance().is_none());
}

#[test]
fn an_empty_keypath_root_is_allowed() {
    let mut ev = Evaluator::new(World::new()).with_provenance(Vec::new());
    ev.run(&add(lit(1), lit(2))).unwrap();
    let p = ev.provenance().unwrap();
    assert!(p.facts().iter().all(|f| f.address.keypath.is_empty()));
}

/// `{"k" -> {<leaves>}}`, each leaf a key and the atom it maps to.
fn nested(leaves: &[(&str, &str)]) -> Family {
    Family::of([(
        "k",
        Value::Family(Family::of(leaves.iter().map(|&(k, a)| (k, Value::atom(a))))),
    )])
}

#[test]
fn a_failure_read_from_a_union_of_nested_families_has_its_origin_in_its_operand() {
    // ({"k" -> {"a" -> #x}} ∪ {"k" -> {"b" -> #y}})["k"]["a"]: the union holds both atoms,
    // made from its operands, which hold one each and read nothing: each operand is where its
    // atom first appears.
    let a = nested(&[("a", "x")]);
    let b = nested(&[("b", "y")]);
    let u = prim(Prim::Union, vec![lit(a.clone()), lit(b.clone())]);
    let t = get(get(u.clone(), lit(s("k"))), lit(s("a")));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("x"));
    unique(&p);
    let o = origins(&p, p.result());
    assert_eq!(o.len(), 1, "{o:?}");
    assert_eq!(o[0].1, Value::Family(a).to_string());
    // The other atom, read through the same union.
    let t = get(get(u, lit(s("k"))), lit(s("b")));
    let (v, p) = trace(&t);
    assert_eq!(v, Value::atom("y"));
    let o = origins(&p, p.result());
    assert_eq!(o.len(), 1, "{o:?}");
    assert_eq!(o[0].1, Value::Family(b).to_string());
}

#[test]
fn a_merge_of_failures_read_from_a_union_names_each_operand() {
    // u["k"]["a"] + u["k"]["b"], u = {"k" -> {"a" -> #x}} ∪ {"k" -> {"b" -> #y, "c" -> #z}}:
    // the inner level of the union is made from the larger operand's, the outer level from
    // the other's; the sum merges one atom from each operand.
    let a = nested(&[("a", "x")]);
    let b = nested(&[("b", "y"), ("c", "z")]);
    let u = prim(Prim::Union, vec![lit(a.clone()), lit(b.clone())]);
    let read = |k: &str| get(get(u.clone(), lit(s("k"))), lit(s(k)));
    let t = add(read("a"), read("b"));
    let (v, p) = trace(&t);
    assert_eq!(v.errs().map(|e| e.len()), Some(2), "{v}");
    unique(&p);
    let mut o: Vec<String> = origins(&p, p.result())
        .into_iter()
        .map(|(_, v)| v)
        .collect();
    o.sort();
    let mut want = vec![Value::Family(a).to_string(), Value::Family(b).to_string()];
    want.sort();
    assert_eq!(o, want);
}
