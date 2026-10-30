//! Step M0.9: the kernel reference evaluator.
//!
//! Each test builds the kernel term that a small real program elaborates to and checks what
//! it computes: one or more tests per generator, the failure rules, ports, and the limits.

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{
    Evaluator, Evidence, Family, FixKind, GuardPos, KernelError, Pattern, Prim, Term, Value, World,
    eval,
};
use zed_tests::kernel::*;

mod scaling;

#[test]
fn word_count_groups_then_folds() {
    let doc = lines_of(&[
        &["the", "cat", "sat"],
        &["on", "the", "mat"],
        &["the", "end"],
    ]);
    // reindex each word to `word -> line -> position`, count 1 per occurrence, sum per word.
    let kf = lam(
        &["p", "w"],
        path(vec![var("w"), key(var("p"), 0), key(var("p"), 1)]),
    );
    let ones = reindex(lit(doc), kf, lam(&["p", "w"], lit(1)));
    let per_line = fold_at(ones, 3, Term::PrimFn(Prim::Add), None);
    let counts = fold_at(per_line, 2, Term::PrimFn(Prim::Add), None);
    let out = eval(&counts).unwrap();
    assert_eq!(
        out.to_string(),
        r#"{"cat" -> 1, "end" -> 1, "mat" -> 1, "on" -> 1, "sat" -> 1, "the" -> 3}"#
    );
}

fn orders() -> Value {
    // order id -> (customer, region, amount)
    let rows = [
        (101, "ann", "north", 0.1),
        (102, "bob", "south", 2.5),
        (103, "ann", "north", 0.2),
        (104, "cy", "north", 0.3),
    ];
    Value::Family(Family::of(rows.map(|(id, c, r, a)| {
        (
            Value::Int(id),
            Value::Tuple(vec![s(c), s(r), Value::float(a)]),
        )
    })))
}

#[test]
fn revenue_by_region_is_the_exact_sum() {
    let amounts = reindex(
        lit(orders()),
        lam(&["p", "o"], path(vec![nth(var("o"), 1), key(var("p"), 0)])),
        lam(&["p", "o"], nth(var("o"), 2)),
    );
    let revenue = fold_at(
        amounts,
        2,
        Term::PrimFn(Prim::Add),
        Some(lit(Value::float(0.0))),
    );
    let out = eval(&revenue).unwrap();
    // 0.1 + 0.2 + 0.3 is exactly 0.6 rounded once; left to right it would be 0.6000000000000001.
    assert_eq!(out.to_string(), r#"{"north" -> 0.6, "south" -> 2.5}"#);
}

#[test]
fn a_float_fold_of_another_operator_uses_the_canonical_tree() {
    let xs = Value::Family(Family::of(
        [(0, 0.1), (1, 0.2), (2, 0.3)].map(|(k, x)| (Value::Int(k), Value::float(x))),
    ));
    // A function whose body is `a + b` is not the primitive `+`, so it folds on the tree
    // ((x0 + x1) + x2), rounding at each node.
    let plus = lam(&["a", "b"], add(var("a"), var("b")));
    assert_eq!(
        eval(&fold(lit(xs.clone()), plus, None)).unwrap(),
        Value::float(0.1 + 0.2 + 0.3)
    );
    assert_eq!(
        eval(&fold(lit(xs), Term::PrimFn(Prim::Add), None)).unwrap(),
        Value::float(0.6)
    );
}

#[test]
fn rekeying_orders_by_customer_collides_on_a_repeat_customer() {
    let by_customer = reindex(
        lit(orders()),
        lam(&["p", "o"], nth(var("o"), 0)),
        lam(&["p", "o"], var("o")),
    );
    let err = eval(&by_customer).unwrap_err();
    assert_eq!(
        err,
        KernelError::Collision {
            keypath: vec![s("ann")]
        }
    );
    // Grouping keeps the order id beneath the customer, so the keypaths stay distinct.
    let grouped = eval(&group_by(lit(orders()), |o| nth(o, 0))).unwrap();
    let ann = grouped
        .as_family()
        .unwrap()
        .get(&s("ann"))
        .unwrap()
        .as_family()
        .unwrap();
    assert_eq!(
        ann.keys().cloned().collect::<Vec<_>>(),
        vec![Value::Int(101), Value::Int(103)]
    );
}

#[test]
fn map_is_a_reindex_that_keeps_keys() {
    // map(f) = reindex((k, v) -> k, f): a 10% price rise in cents.
    let prices = Value::Family(Family::of(
        [("tea", 250), ("cake", 400)].map(|(k, v)| (s(k), Value::Int(v))),
    ));
    let kf = lam(&["p", "v"], var("p"));
    let vf = lam(
        &["p", "v"],
        prim(
            Prim::IntDiv,
            vec![prim(Prim::Mul, vec![var("v"), lit(11)]), lit(10)],
        ),
    );
    assert_eq!(
        eval(&reindex(lit(prices), kf, vf)).unwrap().to_string(),
        r#"{"cake" -> 440, "tea" -> 275}"#
    );
}

fn stock() -> Value {
    let leaves = [
        ("fruit", "apple", 3),
        ("fruit", "fig", 0),
        ("veg", "kale", 0),
        ("dairy", "milk", 12),
    ];
    Value::Family(
        Family::from_leaves(leaves.map(|(c, i, n)| (vec![s(c), s(i)], Value::Int(n)))).unwrap(),
    )
}

#[test]
fn discard_drops_out_of_stock_items_and_their_emptied_category() {
    // Keep every category entry; keep an item when its count is above zero.
    let sel = lam(
        &["p", "v"],
        if_(
            prim(Prim::Eq, vec![prim(Prim::PathLen, vec![var("p")]), lit(1)]),
            lit(true),
            prim(Prim::Gt, vec![var("v"), lit(0)]),
        ),
    );
    let out = eval(&discard(lit(stock()), sel)).unwrap();
    // `veg` held only kale, so its level emptied and its key is gone.
    assert_eq!(
        out.to_string(),
        r#"{"dairy" -> {"milk" -> 12}, "fruit" -> {"apple" -> 3}}"#
    );
}

#[test]
fn a_boundary_verdict_keeps_the_key_as_a_set_leaf() {
    // The set of categories: stop at depth 1, keeping each key as itself.
    let sel = lam(&["p", "v"], lit(Value::atom("boundary")));
    let out = eval(&discard(lit(stock()), sel)).unwrap();
    assert_eq!(
        out,
        Value::Family(Family::set([s("dairy"), s("fruit"), s("veg")]))
    );
    let bad = lam(&["p", "v"], lit(3));
    assert_eq!(
        eval(&discard(lit(stock()), bad)).unwrap_err(),
        KernelError::Type("a discard selector returned 3".into())
    );
}

#[test]
fn fold_collapses_the_innermost_level() {
    // store -> day -> takings: the fold gives each store's total, a second fold the chain's.
    let leaves = [
        ("east", 1, 120),
        ("east", 2, 80),
        ("west", 1, 95),
        ("west", 2, 0),
        ("west", 3, 40),
    ];
    let takings = Value::Family(
        Family::from_leaves(leaves.map(|(st, d, n)| (vec![s(st), Value::Int(d)], Value::Int(n))))
            .unwrap(),
    );
    let per_store = fold_at(lit(takings), 2, Term::PrimFn(Prim::Add), None);
    assert_eq!(
        eval(&per_store).unwrap().to_string(),
        r#"{"east" -> 200, "west" -> 135}"#
    );
    assert_eq!(
        eval(&fold(per_store, Term::PrimFn(Prim::Add), None)).unwrap(),
        Value::Int(335)
    );
    let best_day = fold(
        lit(eval(&fold_at(lit(stock()), 2, Term::PrimFn(Prim::Max), None)).unwrap()),
        Term::PrimFn(Prim::Max),
        None,
    );
    assert_eq!(eval(&best_day).unwrap(), Value::Int(12));
}

#[test]
fn folding_leaves_at_mixed_depths_is_an_error() {
    let ragged = Value::Family(
        Family::from_leaves(vec![
            (vec![s("a")], Value::Int(1)),
            (vec![s("b"), s("c")], Value::Int(2)),
        ])
        .unwrap(),
    );
    assert_eq!(
        eval(&fold_at(lit(ragged), 2, Term::PrimFn(Prim::Add), None)).unwrap_err(),
        KernelError::MixedDepth
    );
}

#[test]
fn an_empty_level_folds_to_the_identity_or_empty() {
    let none = lit(Family::new());
    assert_eq!(
        eval(&fold(none.clone(), Term::PrimFn(Prim::Add), Some(lit(0)))).unwrap(),
        Value::Int(0)
    );
    assert_eq!(
        eval(&fold(none, Term::PrimFn(Prim::Max), None)).unwrap(),
        Value::atom("empty")
    );
}

#[test]
fn an_empty_family_folds_by_the_depth_its_type_gives() {
    // Sales by store and day with no sales yet: the per-store totals are an empty table, not
    // `#empty`, which is what folding one empty level gives.
    let none = lit(Family::new());
    assert_eq!(
        eval(&fold_at(none, 2, Term::PrimFn(Prim::Add), None)).unwrap(),
        Value::Family(Family::new())
    );
    // A one-level table folded as two levels has a leaf at the wrong depth.
    let flat = lit(Family::of([("east", 3i64)]));
    assert_eq!(
        eval(&fold_at(flat, 2, Term::PrimFn(Prim::Add), None)).unwrap_err(),
        KernelError::MixedDepth
    );
}

#[test]
fn fam_builds_a_table_over_a_domain() {
    // VAT at 20% for each price band, and a band with no entries drops its key.
    let bands = lit(Family::set([100, 250, 1000].map(Value::Int)));
    let vat = fam(
        bands.clone(),
        "b",
        prim(Prim::IntDiv, vec![var("b"), lit(5)]),
    );
    assert_eq!(
        eval(&vat).unwrap().to_string(),
        "{100 -> 20, 250 -> 50, 1000 -> 200}"
    );
    let nothing = fam(bands, "b", lit(Family::new()));
    assert_eq!(eval(&nothing).unwrap(), Value::Family(Family::new()));
}

fn edges() -> Value {
    // A flight network as a set of (from, to) pairs.
    let pairs = [
        ("lhr", "jfk"),
        ("jfk", "sfo"),
        ("sfo", "nrt"),
        ("cdg", "lhr"),
        ("syd", "akl"),
    ];
    Value::Family(Family::set(
        pairs.map(|(a, b)| Value::Tuple(vec![s(a), s(b)])),
    ))
}

#[test]
fn reachability_is_a_lattice_fixpoint() {
    // step(r) = the set of `to` over edges whose `from` is in r; the join is set union.
    let from_reached = discard(
        lit(edges()),
        lam(&["p", "e"], found(get(var("r"), nth(var("e"), 0)))),
    );
    let targets = group_by(from_reached, |e| nth(e, 1));
    let step = lam(&["r"], fam(targets, "k", var("k")));
    let reach = Term::Fix {
        init: rc(lit(Family::set([s("cdg")]))),
        step: rc(step),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: rc(Term::PrimFn(Prim::Union)),
        },
        ev: Evidence::new(),
    };
    let out = eval(&reach).unwrap();
    assert_eq!(
        out,
        Value::Family(Family::set(["cdg", "jfk", "lhr", "nrt", "sfo"].map(s)))
    );
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
fn fibonacci_by_general_recursion() {
    let domain = lit(Family::set((0..=40).map(Value::Int)));
    let at = |d: i64| get(var("this"), prim(Prim::Sub, vec![var("i"), lit(d)]));
    let body = if_(
        prim(Prim::Lt, vec![var("i"), lit(2)]),
        var("i"),
        add(at(1), at(2)),
    );
    let fib = eval(&definedness(domain, body)).unwrap();
    let fib = fib.as_family().unwrap();
    assert_eq!(fib.get(&Value::Int(10)), Some(&Value::Int(55)));
    assert_eq!(fib.get(&Value::Int(40)), Some(&Value::Int(102_334_155)));
}

fn sheet(cells: &[(&str, Term)]) -> Term {
    let domain = lit(Family::set(cells.iter().map(|(c, _)| s(c))));
    let arms = cells
        .iter()
        .map(|(c, t)| (Pattern::Lit(s(c)), t.clone()))
        .collect();
    definedness(domain, Term::Match(rc(var("i")), arms))
}

fn cell(name: &str) -> Term {
    get(var("this"), lit(s(name)))
}

#[test]
fn a_spreadsheet_evaluates_in_dependency_order() {
    let book = sheet(&[
        ("total", add(cell("net"), cell("tax"))),
        ("tax", prim(Prim::IntDiv, vec![cell("net"), lit(5)])),
        ("net", prim(Prim::Mul, vec![cell("units"), cell("price")])),
        ("units", lit(12)),
        ("price", lit(250)),
        ("rate", get(var("this"), lit(s("missing")))),
    ]);
    let out = eval(&book).unwrap();
    // A read outside the domain is `#notFound`, an ordinary value.
    assert_eq!(
        out.to_string(),
        r##"{"net" -> 3000, "price" -> 250, "rate" -> #notFound, "tax" -> 600, "total" -> 3600, "units" -> 12}"##
    );
}

#[test]
fn a_circular_reference_stalls_and_names_its_cells() {
    let book = sheet(&[
        ("a", add(cell("b"), lit(1))),
        ("b", add(cell("c"), lit(1))),
        ("c", add(cell("a"), lit(1))),
        ("d", lit(7)),
    ]);
    assert_eq!(
        eval(&book).unwrap_err(),
        KernelError::Stalled {
            keys: vec![s("a"), s("b"), s("c")]
        }
    );
}

fn ledger() -> Value {
    Value::Family(Family::of(
        [(0, 500), (1, -200), (2, -450), (3, 100)].map(|(t, x)| (Value::Int(t), Value::Int(x))),
    ))
}

/// A running balance: frame `(t, balance)`, one transaction per generation.
fn balance_loop(guard: Term, pos: GuardPos) -> Term {
    let step = lam(
        &["f"],
        prim(
            Prim::Tuple,
            vec![
                add(nth(var("f"), 0), lit(1)),
                add(nth(var("f"), 1), get(lit(ledger()), nth(var("f"), 0))),
            ],
        ),
    );
    Term::Gen {
        init: rc(prim(Prim::Tuple, vec![lit(0), lit(0)])),
        step: rc(step),
        guard: rc(guard),
        pos,
    }
}

#[test]
fn a_running_balance_is_a_generation_loop() {
    let more = lam(
        &["f"],
        prim(
            Prim::Lt,
            vec![nth(var("f"), 0), prim(Prim::Count, vec![lit(ledger())])],
        ),
    );
    let out = eval(&balance_loop(more, GuardPos::Before)).unwrap();
    assert_eq!(
        out.to_string(),
        "{0 -> (0, 0), 1 -> (1, 500), 2 -> (2, 300), 3 -> (3, -150), 4 -> (4, -50)}"
    );
}

#[test]
fn a_guard_atom_ends_the_loop_with_that_value() {
    // Stop at an overdraft: the end-position guard reads the frame it just committed.
    let guard = lam(
        &["f"],
        if_(
            prim(Prim::Lt, vec![nth(var("f"), 1), lit(0)]),
            lit(Value::atom("overdrawn")),
            lit(true),
        ),
    );
    let out = eval(&balance_loop(guard.clone(), GuardPos::After)).unwrap();
    assert_eq!(
        out.to_string(),
        "{0 -> (0, 0), 1 -> (1, 500), 2 -> (2, 300), 3 -> (3, -150), 4 -> #overdrawn}"
    );
    // Tested before each step, a guard that ends the loop commits nothing more.
    let at_start = eval(&balance_loop(lam(&["f"], lit(false)), GuardPos::Before)).unwrap();
    assert_eq!(at_start.to_string(), "{0 -> (0, 0)}");
}

#[test]
fn a_loop_that_never_stops_runs_out_of_fuel() {
    let forever = balance_loop(lam(&["f"], lit(true)), GuardPos::Before);
    let mut ev = Evaluator::new(World::new()).with_fuel(1000);
    // The ledger runs out at t = 4, after which a lookup is `#notFound` and propagates, so the
    // loop goes on with an atom balance until the fuel is spent.
    assert_eq!(ev.run(&forever).unwrap_err(), KernelError::OutOfFuel);
}

#[test]
fn self_application_is_cut_off() {
    let w = lam(&["x"], app(var("x"), vec![var("x")]));
    assert_eq!(
        eval(&app(w.clone(), vec![w])).unwrap_err(),
        KernelError::TooDeep
    );
}

#[test]
fn failure_atoms_propagate_through_primitives() {
    // A missing price makes the line total `#notFound`, never a crash.
    let prices = lit(Family::of(
        [("tea", 250)].map(|(k, v)| (s(k), Value::Int(v))),
    ));
    let line = |item: &str| prim(Prim::Mul, vec![get(prices.clone(), lit(s(item))), lit(3)]);
    assert_eq!(eval(&line("tea")).unwrap(), Value::Int(750));
    assert_eq!(eval(&line("scone")).unwrap(), Value::atom("notFound"));
    // Two failures merge into the set of them, whichever side each is on (step L1.18).
    let both = add(lit(Value::atom("a")), lit(Value::atom("b")));
    assert_eq!(eval(&both).unwrap().to_string(), "#errs({#a, #b})");
    let swapped = add(lit(Value::atom("b")), lit(Value::atom("a")));
    assert_eq!(eval(&swapped).unwrap(), eval(&both).unwrap());
    // `match` sees the atom and can supply a default.
    let priced = Term::Match(
        rc(line("scone")),
        vec![
            (Pattern::Atom("notFound".into(), vec![]), lit(0)),
            (Pattern::Bind("x".into()), var("x")),
        ],
    );
    assert_eq!(eval(&priced).unwrap(), Value::Int(0));
}

#[test]
fn integer_division_is_euclidean() {
    let div = |a, b| eval(&prim(Prim::IntDiv, vec![lit(a), lit(b)])).unwrap();
    let rem = |a, b| eval(&prim(Prim::Mod, vec![lit(a), lit(b)])).unwrap();
    assert_eq!((div(7, 2), rem(7, 2)), (Value::Int(3), Value::Int(1)));
    assert_eq!((div(-7, 2), rem(-7, 2)), (Value::Int(-4), Value::Int(1)));
    assert_eq!((div(7, -2), rem(7, -2)), (Value::Int(-3), Value::Int(1)));
    assert_eq!(div(1, 0), Value::atom("divByZero"));
    assert_eq!(rem(1, 0), Value::atom("divByZero"));
    // `int` is unbounded (step L1.17): past 64 bits an integer widens.
    assert_eq!(
        eval(&add(lit(i64::MAX), lit(1))).unwrap().to_string(),
        "9223372036854775808"
    );
}

#[test]
fn floats_compare_as_ieee() {
    // The language's `==` follows IEEE 754 (step L1.17); the values stay distinct keys.
    let eq = prim(
        Prim::Eq,
        vec![lit(Value::float(0.0)), lit(Value::float(-0.0))],
    );
    assert_eq!(eval(&eq).unwrap(), Value::Bool(true));
    assert_ne!(Value::float(0.0), Value::float(-0.0));
    let nan = prim(
        Prim::Div,
        vec![lit(Value::float(0.0)), lit(Value::float(0.0))],
    );
    assert_eq!(
        eval(&prim(Prim::Eq, vec![nan.clone(), nan])).unwrap(),
        Value::Bool(false)
    );
    let mixed = prim(Prim::Lt, vec![lit(1), lit(Value::float(2.0))]);
    assert!(matches!(eval(&mixed).unwrap_err(), KernelError::Type(_)));
}

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), rc(v))
}

#[test]
fn pushes_to_an_output_port_return_acknowledgments() {
    let greeting = Term::Read("stdin".into());
    let prog = let_(
        "a",
        push("stdout", prim(Prim::Concat, vec![lit("hello, "), greeting])),
        let_(
            "b",
            push("stdout", lit("bye")),
            prim(Prim::Tuple, vec![var("a"), var("b")]),
        ),
    );
    let mut ev = Evaluator::new(
        World::new()
            .input("stdin", "ada")
            .bounded_output("stdout", 1),
    );
    let acks = ev.run(&prog).unwrap();
    // The second push finds the port full.
    assert_eq!(acks.to_string(), "(#ok, #full)");
    assert_eq!(ev.world.log("stdout"), &[s("hello, ada")]);
}

#[test]
fn a_port_inside_a_pure_region_is_rejected() {
    let leak = fold(
        lit(ledger()),
        lam(&["a", "b"], push("stdout", var("a"))),
        None,
    );
    let mut ev = Evaluator::new(World::new().output("stdout"));
    assert_eq!(
        ev.run(&leak).unwrap_err(),
        KernelError::Type("port `stdout` used inside a pure region".into())
    );
    assert!(ev.world.log("stdout").is_empty());
    assert_eq!(
        eval(&Term::Read("nope".into())).unwrap_err(),
        KernelError::UnknownPort("nope".into())
    );
    assert_eq!(
        eval(&push("nope", lit(1))).unwrap_err(),
        KernelError::UnknownPort("nope".into())
    );
}

#[test]
fn ill_typed_terms_are_reported() {
    for (t, msg) in [
        (var("x"), "unbound variable `x`"),
        (app(lit(3), vec![]), "3 is not a function"),
        (
            app(lam(&["x"], var("x")), vec![]),
            "a function of 1 parameters called with 0 arguments",
        ),
        (if_(lit(1), lit(2), lit(3)), "`if` on 1"),
        (lam(&["x"], var("x")), "the program's result is a function"),
        (
            Term::Match(rc(lit(5)), vec![(Pattern::Lit(Value::Int(4)), lit(0))]),
            "no arm matches 5",
        ),
        (
            prim(Prim::Neg, vec![lit(1), lit(2)]),
            "Neg takes 1 arguments, given 2",
        ),
        (prim(Prim::Not, vec![lit(1)]), "Not applied to 1"),
    ] {
        assert_eq!(eval(&t).unwrap_err(), KernelError::Type(msg.into()));
    }
}

#[test]
fn a_signup_rule_uses_every_comparison() {
    // Accept an applicant aged 18 to 65 with a name, or any applicant on the invite list.
    let rule = |name: &str, age: i64, invited: bool| {
        let in_range = prim(
            Prim::And,
            vec![
                prim(Prim::Ge, vec![lit(age), lit(18)]),
                prim(Prim::Le, vec![lit(age), lit(65)]),
            ],
        );
        let named = prim(Prim::Ne, vec![lit(name), lit("")]);
        let ok = prim(
            Prim::Or,
            vec![prim(Prim::And, vec![in_range, named]), lit(invited)],
        );
        eval(&ok).unwrap()
    };
    assert_eq!(rule("ada", 36, false), Value::Bool(true));
    assert_eq!(rule("", 36, false), Value::Bool(false));
    assert_eq!(rule("tim", 70, false), Value::Bool(false));
    assert_eq!(rule("tim", 70, true), Value::Bool(true));
    assert_eq!(rule("kid", 17, false), Value::Bool(false));
}

#[test]
fn temperature_conversion_and_negation() {
    // Fahrenheit to Celsius, (f - 32) * 5 / 9, and a freezer's offset below zero.
    let c = |f: f64| {
        prim(
            Prim::Div,
            vec![
                prim(
                    Prim::Mul,
                    vec![
                        prim(
                            Prim::Sub,
                            vec![lit(Value::float(f)), lit(Value::float(32.0))],
                        ),
                        lit(Value::float(5.0)),
                    ],
                ),
                lit(Value::float(9.0)),
            ],
        )
    };
    assert_eq!(eval(&c(212.0)).unwrap(), Value::float(100.0));
    assert_eq!(
        eval(&prim(Prim::Neg, vec![c(-4.0)])).unwrap(),
        Value::float(20.0)
    );
    assert_eq!(
        eval(&prim(Prim::Neg, vec![lit(18)])).unwrap(),
        Value::Int(-18)
    );
    assert_eq!(
        eval(&prim(Prim::Neg, vec![lit(i64::MIN)]))
            .unwrap()
            .to_string(),
        "9223372036854775808"
    );
}

#[test]
fn a_missing_price_flows_through_if_and_sum() {
    let prices = lit(Family::of(
        [("tea", 250), ("cake", 400)].map(|(k, v)| (s(k), Value::Int(v))),
    ));
    // `if price > 300 { "dear" } else { "cheap" }` on a missing item is the atom itself.
    let label = |item: &str| {
        if_(
            prim(Prim::Gt, vec![get(prices.clone(), lit(s(item))), lit(300)]),
            lit("dear"),
            lit("cheap"),
        )
    };
    assert_eq!(eval(&label("cake")).unwrap(), s("dear"));
    assert_eq!(eval(&label("scone")).unwrap(), Value::atom("notFound"));
    // A basket total with one unknown item is `#notFound`, not a partial sum.
    let basket = Family::set([s("tea"), s("scone"), s("cake")]);
    let total = fold(
        fam(lit(basket), "i", get(prices, var("i"))),
        Term::PrimFn(Prim::Add),
        Some(lit(0)),
    );
    assert_eq!(eval(&total).unwrap(), Value::atom("notFound"));
}

#[test]
fn org_chart_depth_by_recursion() {
    // depth(e) = depth(manager(e)) + 1; the head has no manager, so the read is `#notFound`.
    let managers = lit(Family::of(
        [("bo", "ann"), ("cy", "bo"), ("di", "bo")].map(|(e, m)| (s(e), s(m))),
    ));
    let domain = lit(Family::set(["ann", "bo", "cy", "di"].map(s)));
    let up = add(get(var("this"), get(managers, var("i"))), lit(1));
    let body = Term::Match(
        rc(up),
        vec![
            (Pattern::Atom("notFound".into(), vec![]), lit(0)),
            (Pattern::Bind("d".into()), var("d")),
        ],
    );
    let out = eval(&definedness(domain, body)).unwrap();
    assert_eq!(
        out.to_string(),
        r#"{"ann" -> 0, "bo" -> 1, "cy" -> 2, "di" -> 2}"#
    );
}

#[test]
fn match_destructures_tuples_and_atom_payloads() {
    // A parser's result: a record `(name, qty)` or `#parseError(pos, msg)`.
    let report = |r: Value| {
        let arms = vec![
            (
                Pattern::Tuple(vec![Pattern::Bind("n".into()), Pattern::Lit(Value::Int(0))]),
                prim(Prim::Concat, vec![var("n"), lit(": out of stock")]),
            ),
            (
                Pattern::Tuple(vec![Pattern::Bind("n".into()), Pattern::Wild]),
                prim(Prim::Concat, vec![var("n"), lit(": ok")]),
            ),
            (
                Pattern::Atom(
                    "parseError".into(),
                    vec![Pattern::Bind("pos".into()), Pattern::Wild],
                ),
                var("pos"),
            ),
        ];
        eval(&Term::Match(rc(lit(r)), arms)).unwrap()
    };
    assert_eq!(
        report(Value::Tuple(vec![s("fig"), Value::Int(0)])),
        s("fig: out of stock")
    );
    assert_eq!(
        report(Value::Tuple(vec![s("fig"), Value::Int(4)])),
        s("fig: ok")
    );
    assert_eq!(
        report(Value::atom_with(
            "parseError",
            vec![Value::Int(17), s("expected ,")]
        )),
        Value::Int(17)
    );
}

#[test]
fn a_step_or_guard_of_the_wrong_kind_is_reported() {
    let id = lam(&["x"], var("x"));
    let cases = [
        (
            Term::Fix {
                init: rc(lit(Family::new())),
                step: rc(lam(&["r"], id.clone())),
                this: "this".into(),
                key: "k".into(),
                kind: FixKind::Lattice {
                    join: rc(Term::PrimFn(Prim::Union)),
                },
                ev: Evidence::new(),
            },
            "a fix step returned a function",
        ),
        (
            definedness(lit(Family::set([Value::Int(0)])), id.clone()),
            "a fix entry is a function",
        ),
        (
            definedness(
                lit(Family::set([Value::Int(0)])),
                app(var("this"), vec![lit(0)]),
            ),
            "a family is read with `[]`, not called",
        ),
        (
            Term::Gen {
                init: rc(lit(0)),
                step: rc(lam(&["f"], id.clone())),
                guard: rc(lam(&["f"], lit(true))),
                pos: GuardPos::Before,
            },
            "a gen step returned a function",
        ),
        (
            Term::Gen {
                init: rc(lit(0)),
                step: rc(id.clone()),
                guard: rc(lam(&["f"], lit(3))),
                pos: GuardPos::Before,
            },
            "a gen guard returned 3",
        ),
        (
            fold(lit(3), Term::PrimFn(Prim::Add), None),
            "expected a family, found 3",
        ),
        (
            if_(id.clone(), lit(1), lit(2)),
            "expected data, found a function",
        ),
        (add(id, lit(1)), "Add applied to a function"),
    ];
    for (t, msg) in cases {
        assert_eq!(eval(&t).unwrap_err(), KernelError::Type(msg.into()));
    }
}
