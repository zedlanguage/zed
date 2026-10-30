//! Each kernel form the L1 surface does not yet write, lowered and raised back: families,
//! reindexing, discards, folds, both fixpoints, generation loops and nested patterns, on the
//! small programs of step M0.9.

use zed_kernel::term::build::{if_, lam, let_, lit, prim, var};
use zed_kernel::{Evidence, Family, FixKind, GuardPos, Pattern, Prim, Term, Value};
use zed_tests::kernel::*;
use zedc::zir::lower::lower;

use super::{count, eval, round_trip};

/// Checks that `t` keeps its value through ZIR and that its graph has `n` nodes of `op`.
fn keeps(t: &Term, op: &str, n: usize) {
    let want = eval(t).expect("the term evaluates");
    assert_eq!(round_trip(t), Ok(want));
    let g = lower(t).unwrap();
    assert_eq!(count(&g, op), n, "{op} nodes");
}

#[test]
fn word_count_reindexes_then_folds() {
    let doc = lines_of(&[&["the", "cat", "sat"], &["the", "end"]]);
    let kf = lam(
        &["p", "w"],
        path(vec![var("w"), key(var("p"), 0), key(var("p"), 1)]),
    );
    let ones = reindex(lit(doc), kf, lam(&["p", "w"], lit(1)));
    let per_line = fold_at(ones, 3, Term::PrimFn(Prim::Add), None);
    let t = fold_at(per_line, 2, Term::PrimFn(Prim::Add), None);
    keeps(&t, "reindex", 1);
    keeps(&t, "fold", 2);
}

#[test]
fn a_float_fold_keeps_its_identity_and_its_tree() {
    let xs = Value::Family(Family::of(
        [(0, 0.1), (1, 0.2), (2, 0.3)].map(|(k, x)| (Value::Int(k), Value::float(x))),
    ));
    let plus = lam(&["a", "b"], add(var("a"), var("b")));
    keeps(&fold(lit(xs.clone()), plus, None), "fold", 1);
    let exact = fold(
        lit(xs),
        Term::PrimFn(Prim::Add),
        Some(lit(Value::float(0.0))),
    );
    assert_eq!(round_trip(&exact), Ok("0.6".into()));
    // An empty family folds to the identity, which the graph keeps as the fold's third input.
    let empty = fold(lit(Family::new()), Term::PrimFn(Prim::Add), Some(lit(7)));
    assert_eq!(round_trip(&empty), Ok("7".into()));
}

#[test]
fn a_family_reads_a_computed_rate_as_a_capture() {
    let bands = lit(Family::set([100, 250, 1000].map(Value::Int)));
    let t = let_(
        "rate",
        add(lit(2), lit(3)),
        fam(
            bands,
            "b",
            prim(
                Prim::Sub,
                vec![prim(Prim::IntDiv, vec![var("b"), var("rate")]), var("rate")],
            ),
        ),
    );
    keeps(&t, "fam", 1);
    let g = lower(&t).unwrap();
    let fam = g.nodes.iter().find(|n| zedc::zir::op_name(&n.op) == "fam");
    // The domain, then the rate, read twice but captured once; the region takes the key, then
    // the rate.
    assert_eq!(fam.unwrap().inputs.len(), 2);
    assert_eq!(fam.unwrap().regions[0].args.len(), 2);
}

#[test]
fn discard_keeps_categories_and_stocked_items() {
    let leaves = [
        ("fruit", "apple", 3),
        ("fruit", "fig", 0),
        ("veg", "kale", 0),
    ];
    let stock = Family::from_leaves(leaves.map(|(c, i, n)| (vec![s(c), s(i)], Value::Int(n))));
    let sel = lam(
        &["p", "v"],
        if_(
            prim(Prim::Eq, vec![prim(Prim::PathLen, vec![var("p")]), lit(1)]),
            lit(true),
            prim(Prim::Gt, vec![var("v"), lit(0)]),
        ),
    );
    keeps(
        &discard(lit(Value::Family(stock.unwrap())), sel),
        "discard",
        1,
    );
}

#[test]
fn reachability_is_a_lattice_fixpoint() {
    let edges = Family::set(
        [
            ("lhr", "jfk"),
            ("jfk", "sfo"),
            ("cdg", "lhr"),
            ("syd", "akl"),
        ]
        .map(|(a, b)| Value::Tuple(vec![s(a), s(b)])),
    );
    let from_reached = discard(
        lit(edges),
        lam(&["p", "e"], found(get(var("r"), nth(var("e"), 0)))),
    );
    let targets = group_by(from_reached, |e| nth(e, 1));
    let t = Term::Fix {
        init: rc(lit(Family::set([s("cdg")]))),
        step: rc(lam(&["r"], fam(targets, "k", var("k")))),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: rc(Term::PrimFn(Prim::Union)),
        },
        ev: Evidence::new(),
    };
    keeps(&t, "fix", 1);
}

fn definedness(domain: Term, body: Term) -> Term {
    Term::Fix {
        init: rc(domain),
        step: rc(body),
        this: "this".into(),
        key: "i".into(),
        kind: FixKind::Definedness,
        ev: Evidence::new(),
    }
}

#[test]
fn fibonacci_is_a_definedness_fixpoint() {
    let domain = lit(Family::set((0..=20).map(Value::Int)));
    let at = |d: i64| get(var("this"), prim(Prim::Sub, vec![var("i"), lit(d)]));
    let body = if_(
        prim(Prim::Lt, vec![var("i"), lit(2)]),
        var("i"),
        add(at(1), at(2)),
    );
    keeps(&definedness(domain, body), "fix", 1);
}

#[test]
fn an_org_chart_matches_inside_a_fixpoint() {
    let managers = lit(Family::of(
        [("bo", "ann"), ("cy", "bo")].map(|(e, m)| (s(e), s(m))),
    ));
    let domain = lit(Family::set(["ann", "bo", "cy"].map(s)));
    let up = add(get(var("this"), get(managers, var("i"))), lit(1));
    let body = Term::Match(
        rc(up),
        vec![
            (Pattern::Atom("notFound".into(), vec![]), lit(0)),
            (Pattern::Bind("d".into()), var("d")),
        ],
    );
    keeps(&definedness(domain, body), "match", 1);
}

#[test]
fn a_running_balance_is_a_generation_loop() {
    let ledger =
        Family::of([(0, 500), (1, -200), (2, -450)].map(|(t, x)| (Value::Int(t), Value::Int(x))));
    let step = lam(
        &["f"],
        prim(
            Prim::Tuple,
            vec![
                add(nth(var("f"), 0), lit(1)),
                add(nth(var("f"), 1), get(lit(ledger), nth(var("f"), 0))),
            ],
        ),
    );
    for pos in [GuardPos::Before, GuardPos::After] {
        let guard = lam(
            &["f"],
            if_(
                prim(Prim::Lt, vec![nth(var("f"), 1), lit(0)]),
                lit(Value::atom("overdrawn")),
                prim(Prim::Lt, vec![nth(var("f"), 0), lit(3)]),
            ),
        );
        let t = Term::Gen {
            init: rc(prim(Prim::Tuple, vec![lit(0), lit(0)])),
            step: rc(step.clone()),
            guard: rc(guard),
            pos,
        };
        keeps(&t, "gen", 1);
    }
}

#[test]
fn nested_patterns_bind_in_preorder() {
    let arms = vec![
        (
            Pattern::Tuple(vec![Pattern::Bind("n".into()), Pattern::Lit(Value::Int(0))]),
            prim(Prim::Concat, vec![var("n"), lit(": out of stock")]),
        ),
        (
            Pattern::Atom(
                "parseError".into(),
                vec![Pattern::Bind("pos".into()), Pattern::Bind("msg".into())],
            ),
            prim(
                Prim::Concat,
                vec![var("msg"), prim(Prim::Show, vec![var("pos")])],
            ),
        ),
        (Pattern::Wild, lit("ok")),
    ];
    for r in [
        Value::Tuple(vec![s("fig"), Value::Int(0)]),
        Value::atom_with("parseError", vec![Value::Int(17), s("expected , at ")]),
        Value::Int(3),
    ] {
        keeps(&Term::Match(rc(lit(r)), arms.clone()), "match", 1);
    }
}

#[test]
fn a_primitive_passed_as_a_value_stays_the_primitive() {
    // A fold of `+` itself sums exactly, and of a lambda that adds rounds at each step; the
    // graph keeps the two apart, as a `prim` node with no inputs and as a `lambda`.
    let xs = Value::Family(Family::of(
        [(0, 0.1), (1, 0.2), (2, 0.3)].map(|(k, x)| (Value::Int(k), Value::float(x))),
    ));
    let exact = let_(
        "plus",
        Term::PrimFn(Prim::Add),
        fold(lit(xs.clone()), var("plus"), None),
    );
    let tree = fold(lit(xs), lam(&["a", "b"], add(var("a"), var("b"))), None);
    assert_eq!(round_trip(&exact), Ok("0.6".into()));
    assert_eq!(round_trip(&tree), Ok("0.6000000000000001".into()));
    keeps(&exact, "lambda", 0);
    keeps(&tree, "lambda", 1);
    let g = lower(&exact).unwrap();
    assert!(
        g.nodes
            .iter()
            .any(|n| n.inputs.is_empty() && zedc::zir::op_name(&n.op) == "prim")
    );
}
