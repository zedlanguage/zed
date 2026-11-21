//! Step M0.9: the kernel reference evaluator.
//!
//! Each test builds the kernel term that a small real program elaborates to and checks what
//! it computes: one or more tests per generator, the failure rules, ports, and the limits.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{
    Commutes, Evaluator, Evidence, Family, FixKind, GuardPos, KernelError, Lookup, Pattern, Prim,
    Schedule, Term, Value, World, eval,
};
use zed_tests::kernel::*;

// binary.rs is not a module of this target: crates/zed-native/Cargo.toml builds it as the test
// `zedc_binary`, since only a test of that package can name the zedc executable.
mod bench;
mod complete;
mod deep;
mod empty_levels;
mod hash_keys;
mod provenance;
mod scaling;
mod shared;

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
            Value::tuple(vec![s(c), s(r), Value::float(a)]),
        )
    })))
}

#[test]
fn revenue_by_region_sums_on_the_canonical_tree() {
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
    // DESIGN.md sec:reduction items 1 and 2: a float `+` fold rounds at each node of the
    // canonical tree, `(0.1 + 0.2) + 0.3`, and no float policy claims exactness (an exact sum
    // is written through `rat`).
    assert_eq!(
        out.to_string(),
        r#"{"north" -> 0.6000000000000001, "south" -> 2.5}"#
    );
}

#[test]
fn a_float_fold_of_any_operator_uses_the_canonical_tree() {
    let xs = Value::Family(Family::of(
        [(0, 0.1), (1, 0.2), (2, 0.3)].map(|(k, x)| (Value::Int(k), Value::float(x))),
    ));
    // A function whose body is `a + b` and the primitive `+` both fold on the tree
    // ((x0 + x1) + x2), rounding at each node.
    let plus = lam(&["a", "b"], add(var("a"), var("b")));
    assert_eq!(
        eval(&fold(lit(xs.clone()), plus, None)).unwrap(),
        Value::float(0.1 + 0.2 + 0.3)
    );
    assert_eq!(
        eval(&fold(lit(xs), Term::PrimFn(Prim::Add), None)).unwrap(),
        Value::float(0.1 + 0.2 + 0.3)
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
fn discard_drops_out_of_stock_items_and_keeps_their_emptied_category() {
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
    // `veg` held only kale, so its level emptied; the key stays above an empty level.
    assert_eq!(
        out.to_string(),
        r#"{"dairy" -> {"milk" -> 12}, "fruit" -> {"apple" -> 3}, "veg" -> {}}"#
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
        KernelError::Type("a discard selector returned a value of type `int`".into())
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
    // VAT at 20% for each price band, and a band with no entries keeps its key.
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
    assert_eq!(
        eval(&nothing).unwrap().to_string(),
        "{100 -> {}, 250 -> {}, 1000 -> {}}"
    );
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
        pairs.map(|(a, b)| Value::tuple(vec![s(a), s(b)])),
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

/// A frame may hold a function (DESIGN.md step L1.17), as the frame `(entry, acc)` of
/// `foldl` does when its accumulator is one: frame `(n, g)` steps to `(n + 1, y -> g(y) + 1)`
/// while `n < 2`, and the last frame's function is called. Before (row
/// FAIL-fold-rotating-tuple-rounds), the run stopped at the first frame with "expected data,
/// found a function".
#[test]
fn a_frame_may_hold_a_function() {
    let step = lam(
        &["f"],
        prim(
            Prim::Tuple,
            vec![
                add(nth(var("f"), 0), lit(1)),
                lam(&["y"], add(app(nth(var("f"), 1), vec![var("y")]), lit(1))),
            ],
        ),
    );
    let more = lam(&["f"], prim(Prim::Lt, vec![nth(var("f"), 0), lit(2)]));
    let frames = Term::Gen {
        init: rc(prim(Prim::Tuple, vec![lit(0), lam(&["x"], var("x"))])),
        step: rc(step),
        guard: rc(more),
        pos: GuardPos::Before,
    };
    let last = nth(get(frames, lit(2)), 1);
    assert_eq!(eval(&app(last, vec![lit(5)])).unwrap(), Value::Int(7));
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
fn self_application_runs_until_the_fuel_ends() {
    // `x(x)` is a loop in tail position, which holds no frames, so only fuel stops it.
    let w = lam(&["x"], app(var("x"), vec![var("x")]));
    let mut ev = Evaluator::new(World::new()).with_fuel(100_000);
    assert_eq!(
        ev.run(&app(w.clone(), vec![w])).unwrap_err(),
        KernelError::OutOfFuel
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
    // The language's `==` follows IEEE 754 (step L1.17); the values stay distinct keys. IEEE
    // Std 754-2019, doi:10.1109/IEEESTD.2019.8766229, section 5.11; the full comment is in
    // zed-kernel `value.rs`, `Value::surface_cmp`.
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
        (
            app(lit(3), vec![]),
            "a value of type `int` is not a function",
        ),
        (
            app(lam(&["x"], var("x")), vec![]),
            "a function of 1 parameters called with 0 arguments",
        ),
        (if_(lit(1), lit(2), lit(3)), "`if` on a value of type `int`"),
        (lam(&["x"], var("x")), "the program's result is a function"),
        (
            Term::Match(rc(lit(5)), vec![(Pattern::Lit(Value::Int(4)), lit(0))]),
            "no arm matches a value of type `int`",
        ),
        (
            prim(Prim::Neg, vec![lit(1), lit(2)]),
            "`-` takes 1 argument, given 2",
        ),
        (prim(Prim::Not, vec![lit(1)]), "`!` applied to `int`"),
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
        report(Value::tuple(vec![s("fig"), Value::Int(0)])),
        s("fig: out of stock")
    );
    assert_eq!(
        report(Value::tuple(vec![s("fig"), Value::Int(4)])),
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
                step: rc(id.clone()),
                guard: rc(lam(&["f"], lit(3))),
                pos: GuardPos::Before,
            },
            "a gen guard returned a value of type `int`",
        ),
        (
            fold(lit(3), Term::PrimFn(Prim::Add), None),
            "expected a family, found a value of type `int`",
        ),
        (
            if_(id.clone(), lit(1), lit(2)),
            "expected data, found a function",
        ),
        (add(id, lit(1)), "`+` applied to a function"),
    ];
    for (t, msg) in cases {
        assert_eq!(eval(&t).unwrap_err(), KernelError::Type(msg.into()));
    }
}

fn every_schedule() -> Vec<Schedule> {
    vec![Schedule::Rounds, Schedule::Pull, Schedule::Chaotic(7)]
}

/// A family's key is the value with each `-0.0` made `0.0`, so a `fix` over floats reads an
/// entry by either zero, whichever order the schedule takes the entries in.
#[test]
fn a_fix_reads_its_entries_by_key() {
    // A price table where the entry at 1.0 reads the entry at a zero computed as -0.0.
    let domain = || lit(Family::set([Value::float(0.0), Value::float(1.0)]));
    let read_at = |key: Value| {
        definedness(
            domain(),
            if_(
                eq(var("i"), lit(Value::float(1.0))),
                get(var("this"), lit(key)),
                lit(5),
            ),
        )
    };
    let pair = |x: f64| Value::tuple(vec![Value::float(x), s("a")]);
    let in_a_tuple = definedness(
        lit(Family::set([pair(0.0), pair(1.0)])),
        if_(
            eq(var("i"), lit(pair(1.0))),
            get(var("this"), lit(pair(-0.0))),
            lit(5),
        ),
    );
    let on_itself = definedness(domain(), get(var("this"), lit(Value::float(-0.0))));
    for schedule in every_schedule() {
        let run = |t: &Term| Evaluator::new(World::new()).with_schedule(schedule).run(t);
        let by_negative = run(&read_at(Value::float(-0.0))).unwrap();
        assert_eq!(by_negative, run(&read_at(Value::float(0.0))).unwrap());
        assert_eq!(
            by_negative.to_string(),
            "{0.0 -> 5, 1.0 -> 5}",
            "{schedule:?}"
        );
        assert_eq!(
            run(&in_a_tuple).unwrap().to_string(),
            r#"{(0.0, "a") -> 5, (1.0, "a") -> 5}"#,
            "{schedule:?}"
        );
        // Outside the domain is still `#notFound`.
        assert_eq!(
            run(&read_at(Value::float(2.0))).unwrap().to_string(),
            "{0.0 -> 5, 1.0 -> #notFound}",
            "{schedule:?}"
        );
        // Both entries read the entry at zero, which reads itself: a cycle, not `#notFound`.
        assert_eq!(
            run(&on_itself).unwrap_err(),
            KernelError::Stalled {
                keys: vec![Value::float(0.0), Value::float(1.0)],
            },
            "{schedule:?}"
        );
    }
}

/// A chain of `n` entries, each reading the one before by a key that holds `-0.0`.
fn neg_zero_chain(n: usize) -> Term {
    let key = |i: Term, x: f64| prim(Prim::Tuple, vec![lit(Value::float(x)), i]);
    definedness(
        lit(Family::set((0..n as i64).map(|i| {
            Value::tuple(vec![Value::float(0.0), Value::Int(i)])
        }))),
        if_(
            eq(nth(var("i"), 1), lit(0)),
            lit(0),
            add(
                get(var("this"), key(sub(nth(var("i"), 1), lit(1)), -0.0)),
                lit(1),
            ),
        ),
    )
}

/// `t`, a [`neg_zero_chain`] of `n` entries, is defined under `schedule` and has `n` entries.
fn neg_zero_chain_is_defined(t: &Term, schedule: Schedule, n: usize) {
    let out = Evaluator::new(World::new()).with_schedule(schedule).run(t);
    let Ok(Value::Family(f)) = out else {
        panic!("a chain is defined")
    };
    assert_eq!(f.len(), n);
}

/// A chain read by `-0.0` keys is defined under both schedules at small sizes; its time is held
/// in `bench/mod.rs`.
#[test]
fn a_chain_read_by_negative_zero_keys_is_defined_at_small_sizes() {
    for schedule in [Schedule::Rounds, Schedule::Pull] {
        for n in [1, 2, 9] {
            neg_zero_chain_is_defined(&neg_zero_chain(n), schedule, n);
        }
    }
}

/// Answers with the text of the key it is asked for, and counts the times it is asked.
#[derive(Debug, Default)]
struct Rates(AtomicUsize);

impl Lookup for Rates {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Ok(Value::str(&format!("rate at {key}")))
    }
}

/// A wave sees one value at each key, and `0.0` and `-0.0` are one key.
#[test]
fn a_lookup_port_is_read_by_key() {
    let read = |x: f64| {
        let k = Value::tuple(vec![Value::float(x), s("usd")]);
        get(Term::Read("rates".into()), lit(k))
    };
    let port = Arc::new(Rates::default());
    let mut run = Evaluator::new(World::new().source("rates", port.clone()));
    let out = run
        .run(&prim(Prim::Tuple, vec![read(-0.0), read(0.0), read(-0.0)]))
        .unwrap();
    let rate = Value::str(r#"rate at (0.0, "usd")"#);
    assert_eq!(out, Value::tuple(vec![rate.clone(); 3]));
    assert_eq!(port.0.load(Ordering::SeqCst), 1);
    let keys: Vec<&Value> = run.world.reads["rates"].keys().collect();
    assert_eq!(keys, [&Value::tuple(vec![Value::float(0.0), s("usd")])]);
}

/// A read of a port inside a pure region gives the value the wave holds, as outside one
/// (FAIL-port-read-in-mapped-function): a `fam` reading a lookup port at a key each entry
/// computes, the same key from every entry, asked once in all; a `fold` reading an input port;
/// and a definedness `fix` whose entries read the lookup port. A push inside a `fam` is still
/// a type error and writes nothing.
#[test]
fn a_read_inside_a_pure_region_gives_the_waves_value() {
    let rate = |k: Term| get(Term::Read("rates".into()), k);
    let keys = lit(Family::set((0..3).map(Value::Int)));
    let port = Arc::new(Rates::default());
    let mut run = Evaluator::new(World::new().source("rates", port.clone()));
    let by_key = fam(keys.clone(), "k", rate(var("k")));
    assert_eq!(
        run.run(&by_key).unwrap().to_string(),
        r#"{0 -> "rate at 0", 1 -> "rate at 1", 2 -> "rate at 2"}"#
    );
    assert_eq!(port.0.load(Ordering::SeqCst), 3);
    let same = fam(keys.clone(), "k", rate(lit(7)));
    assert_eq!(
        run.run(&same).unwrap().to_string(),
        r#"{0 -> "rate at 7", 1 -> "rate at 7", 2 -> "rate at 7"}"#
    );
    assert_eq!(port.0.load(Ordering::SeqCst), 4);
    let joined = fold(
        fam(keys.clone(), "k", lit("")),
        lam(
            &["a", "b"],
            prim(
                Prim::Concat,
                vec![
                    var("a"),
                    prim(Prim::Concat, vec![var("b"), Term::Read("stdin".into())]),
                ],
            ),
        ),
        None,
    );
    let mut ev = Evaluator::new(World::new().input("stdin", "ab"));
    assert_eq!(ev.run(&joined).unwrap(), s("abab"));
    for schedule in [Schedule::Rounds, Schedule::Pull] {
        let port = Arc::new(Rates::default());
        let out = Evaluator::new(World::new().source("rates", port.clone()))
            .with_schedule(schedule)
            .run(&definedness(keys.clone(), rate(lit(1))))
            .unwrap();
        assert_eq!(
            out.to_string(),
            r#"{0 -> "rate at 1", 1 -> "rate at 1", 2 -> "rate at 1"}"#,
            "{schedule:?}"
        );
        assert_eq!(port.0.load(Ordering::SeqCst), 1, "{schedule:?}");
    }
    let leak = fam(keys, "k", push("stdout", var("k")));
    let mut ev = Evaluator::new(World::new().output("stdout"));
    assert_eq!(
        ev.run(&leak).unwrap_err(),
        KernelError::Type("port `stdout` used inside a pure region".into())
    );
    assert!(ev.world.log("stdout").is_empty());
}

/// A push inside a pure region whose port's `commutes` makes it order-independent there is
/// accepted (DESIGN.md sec:kernel, reference semantics, (h); QUESTIONS A108; step L7.2b): a
/// `#keypath` port inside `fam`, nested `fam`, `discard` and `reindex`, its log in the
/// keypaths' order whatever order the domain was written in; a `#all` port inside `fold` and a
/// definedness `fix`. Negative controls: a `#keypath` push inside `fold`, inside a `fam` that
/// a `fold`'s operator runs, and inside a definedness `fix` is a type error that writes
/// nothing; the `#none` port is `a_port_inside_a_pure_region_is_rejected` and the end of
/// `a_read_inside_a_pure_region_gives_the_waves_value`.
#[test]
fn a_commuting_push_inside_a_pure_region_is_accepted() {
    let keyed = || World::new().commuting_output("out", Commutes::Keypath);
    let ints = |xs: &[i64]| xs.iter().map(|&x| Value::Int(x)).collect::<Vec<_>>();
    // `fam` over a set written out of order: the pushes come in key order.
    let keys = lit(Family::set([2, 0, 1].map(Value::Int)));
    let mut ev = Evaluator::new(keyed());
    let out = ev
        .run(&fam(keys.clone(), "k", push("out", var("k"))))
        .unwrap();
    assert_eq!(out.to_string(), "{0 -> #ok, 1 -> #ok, 2 -> #ok}");
    assert_eq!(ev.world.log("out"), ints(&[0, 1, 2]));
    // Nested `fam`: the log is in the lexicographic order of the keypaths `(i, j)`.
    let two = lit(Family::set([1, 0].map(Value::Int)));
    let pair = prim(Prim::Tuple, vec![var("i"), var("j")]);
    let nested = fam(two.clone(), "i", fam(two.clone(), "j", push("out", pair)));
    let mut ev = Evaluator::new(keyed());
    ev.run(&nested).unwrap();
    let pairs: Vec<String> = ev.world.log("out").iter().map(|v| v.to_string()).collect();
    assert_eq!(pairs, ["(0, 0)", "(0, 1)", "(1, 0)", "(1, 1)"]);
    // `discard`: the selector pushes each keypath it tests, a level before the levels below.
    let tree = Value::Family(
        Family::from_leaves(vec![
            (vec![Value::Int(1), Value::Int(0)], s("b")),
            (vec![Value::Int(0), Value::Int(0)], s("a")),
        ])
        .unwrap(),
    );
    let sel = lam(&["p", "v"], let_("_", push("out", var("p")), lit(true)));
    let mut ev = Evaluator::new(keyed());
    assert_eq!(ev.run(&discard(lit(tree.clone()), sel)).unwrap(), tree);
    let at = |ks: &[i64]| Value::path(ints(ks));
    assert_eq!(
        ev.world.log("out"),
        [at(&[0]), at(&[0, 0]), at(&[1]), at(&[1, 0])]
    );
    // `reindex`: the value map pushes each leaf, in the input's keypath order.
    let vf = lam(&["p", "v"], let_("_", push("out", var("v")), var("v")));
    let mut ev = Evaluator::new(keyed());
    ev.run(&reindex(lit(tree), lam(&["p", "v"], var("p")), vf))
        .unwrap();
    assert_eq!(ev.world.log("out"), [s("a"), s("b")]);
    // A `#all` port inside `fold` and inside a definedness `fix`.
    let all = || World::new().commuting_output("out", Commutes::All);
    let summed = fold(
        lit(ledger()),
        lam(
            &["a", "b"],
            let_("_", push("out", var("b")), add(var("a"), var("b"))),
        ),
        None,
    );
    let mut ev = Evaluator::new(all());
    assert_eq!(ev.run(&summed).unwrap(), Value::Int(-50));
    assert_eq!(ev.world.log("out").len(), 3);
    let mut ev = Evaluator::new(all());
    let out = ev
        .run(&definedness(keys.clone(), push("out", var("i"))))
        .unwrap();
    assert_eq!(out.to_string(), "{0 -> #ok, 1 -> #ok, 2 -> #ok}");
    let mut seen = ev.world.log("out").to_vec();
    seen.sort();
    assert_eq!(seen, ints(&[0, 1, 2]));
    // Negative controls: a `#keypath` push where no keypath orders it.
    let refused = |port: &str| {
        KernelError::Type(format!(
            "port `{port}`, whose pushes take their order from a keypath, pushed in a `fold` \
             or `fix` step, which has none: port `{port}` used inside a pure region"
        ))
    };
    let leak = fold(
        lit(ledger()),
        lam(
            &["a", "b"],
            let_("_", push("out", var("b")), add(var("a"), var("b"))),
        ),
        None,
    );
    let in_fam_in_fold = fold(
        lit(ledger()),
        lam(
            &["a", "b"],
            let_(
                "_",
                fam(keys.clone(), "k", push("out", var("k"))),
                add(var("a"), var("b")),
            ),
        ),
        None,
    );
    let in_fix = definedness(keys, push("out", var("i")));
    for term in [leak, in_fam_in_fold, in_fix] {
        let mut ev = Evaluator::new(keyed());
        assert_eq!(ev.run(&term).unwrap_err(), refused("out"));
        assert!(ev.world.log("out").is_empty());
    }
}

/// A called port: answers with the text of its key, counts the times it is asked, and takes
/// a function argument only when its body is the variable `z`, at the atom `#z`.
#[derive(Debug, Default)]
struct Calls(AtomicUsize);

impl Lookup for Calls {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Ok(Value::str(&format!("answer at {key}")))
    }

    fn calls(&self) -> bool {
        true
    }

    fn function(&self, body: &Term) -> Option<Value> {
        matches!(body, Term::Var(z) if &**z == "z").then(|| Value::atom("z"))
    }
}

/// A called port is asked at the tuple of its arguments as they are: `-0.0` and `0.0` are two
/// keys, a repeated call is answered from what the wave read, and a function argument is keyed
/// by the value the port gives it, or stops the wave when the port gives none.
#[test]
fn a_called_port_keeps_minus_zero_apart_and_keys_functions() {
    let call = |args: Vec<Term>| app(Term::Read("p".into()), args);
    let port = Arc::new(Calls::default());
    let mut run = Evaluator::new(World::new().source("p", port.clone()));
    let at = |x: f64| call(vec![lit(Value::float(x)), lit(1)]);
    let out = run
        .run(&prim(
            Prim::Tuple,
            vec![
                at(-0.0),
                at(0.0),
                at(-0.0),
                call(vec![lam(&["z"], var("z"))]),
            ],
        ))
        .unwrap();
    let answer = |k: &str| Value::str(&format!("answer at {k}"));
    let want = vec![
        answer("(-0.0, 1)"),
        answer("(0.0, 1)"),
        answer("(-0.0, 1)"),
        answer("(#z,)"),
    ];
    assert_eq!(out, Value::tuple(want));
    assert_eq!(port.0.load(Ordering::SeqCst), 3);
    let mut run = Evaluator::new(World::new().source("p", port.clone()));
    let e = run.run(&call(vec![lam(&["y"], var("y"))])).unwrap_err();
    assert!(
        e.to_string()
            .contains("an argument holding a function the port does not take"),
        "{e}"
    );
}

/// A lookup port that holds no answer, as a replay's record that lacks a read does, and
/// counts the times it is asked.
#[derive(Debug, Default)]
struct NoAnswer(AtomicUsize);

impl Lookup for NoAnswer {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Err(format!("no answer at {key}"))
    }
}

/// A read a lookup port cannot answer stops the run with that port's error, and `zedc replay`
/// tells a record that lacks a read by this stop (plan row PROOF-replay-missing-read-status).
/// The one place the evaluator catches a stop is an entry of a definedness fix that reads an
/// entry not yet defined; a fix is a pure region, where a read is allowed
/// (FAIL-port-read-in-mapped-function), and that catch takes only a read of an undefined
/// entry, so the port's error passes through it and stops the run. Here entries 0 to 2 each
/// read the next and wait on it, and entry 3 reads the port, under each schedule; then the
/// read alone, outside any fix.
#[test]
fn a_read_the_port_cannot_answer_stops_the_run() {
    let read = || get(Term::Read("p".into()), lit(Value::str("gone.txt")));
    let domain = lit(Family::set((0..=3).map(Value::Int)));
    let next = get(var("this"), prim(Prim::Add, vec![var("i"), lit(1)]));
    let body = if_(prim(Prim::Lt, vec![var("i"), lit(3)]), next, read());
    let fix = definedness(domain, body);
    for schedule in [Schedule::Rounds, Schedule::Pull] {
        let port = Arc::new(NoAnswer::default());
        let out = Evaluator::new(World::new().source("p", port.clone()))
            .with_schedule(schedule)
            .run(&fix);
        match out {
            Err(KernelError::Port(p, why)) => {
                assert_eq!(
                    (&*p, &*why),
                    ("p", "no answer at \"gone.txt\""),
                    "{schedule:?}"
                );
            }
            other => panic!("{schedule:?}: the run went on past the read: {other:?}"),
        }
        assert_eq!(port.0.load(Ordering::SeqCst), 1, "{schedule:?}");
    }
    let port = Arc::new(NoAnswer::default());
    let out = Evaluator::new(World::new().source("p", port.clone())).run(&read());
    match out {
        Err(KernelError::Port(p, why)) => {
            assert_eq!((&*p, &*why), ("p", "no answer at \"gone.txt\""));
        }
        other => panic!("the run went on past the read: {other:?}"),
    }
    assert_eq!(port.0.load(Ordering::SeqCst), 1);
}

/// A power does not depend on how it is written: `x ^ e` gives what `x ^ a * x ^ b` gives
/// for `a + b = e`, at sizes far past any machine word, and each square of a power is below the
/// next.
#[test]
fn a_power_is_the_product_of_its_halves() {
    let pow = |x: &Term, e: i64| bin(Prim::Pow, x.clone(), lit(e));
    let big = pow(&lit(2), 1000);
    let cases = [
        (lit(2), 600_000),
        (lit(-2), 600_001),
        (lit(2), 1 << 20),
        (lit(2), 1 << 40),
        (lit(3), 661_578),
        (lit(-6), 1 << 33),
        (big.clone(), 1049),
        (big, 1 << 30),
    ];
    for (x, e) in cases {
        let whole = eval(&pow(&x, e)).unwrap();
        let halves = eval(&mul(pow(&x, e / 2), pow(&x, e - e / 2))).unwrap();
        assert_eq!(whole, halves, "{x:?}^{e} and its halves differ");
        let square = |e: i64| mul(pow(&x, e), pow(&x, e));
        let next = bin(Prim::Lt, square(e), square(e + 1));
        assert_eq!(eval(&next).unwrap(), Value::Bool(true), "{x:?}^{e}");
    }
}

/// An exponent past any machine word: `0`, `1` and `-1` stay small, and any other base gives
/// its power, kept as a power of primes, whose remainders are found without building it.
#[test]
fn a_power_by_a_huge_exponent() {
    let huge = bin(Prim::Pow, lit(2), lit(100));
    let to_huge = |x: i64| bin(Prim::Pow, lit(x), huge.clone());
    let odd = add(huge.clone(), lit(1));
    assert_eq!(eval(&to_huge(0)).unwrap(), Value::Int(0));
    assert_eq!(eval(&to_huge(1)).unwrap(), Value::Int(1));
    assert_eq!(eval(&to_huge(-1)).unwrap(), Value::Int(1));
    assert_eq!(eval(&bin(Prim::Pow, lit(-1), odd)).unwrap(), Value::Int(-1));
    // `2^100` is even, so the sign drops; `2^100 = 0 (mod 2)` and `= 1 (mod 3)`.
    let two = eval(&to_huge(2)).unwrap();
    assert_eq!(eval(&to_huge(-2)).unwrap(), two);
    let below = bin(Prim::Pow, lit(2), sub(huge.clone(), lit(1)));
    assert_eq!(
        eval(&bin(Prim::Lt, below.clone(), to_huge(2))).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(eval(&mul(below, lit(2))).unwrap(), two);
    // `2^(2^100) mod 7 = 2^(2^100 mod 3) mod 7 = 2`, and `3^(2^100) mod 4 = 1`.
    assert_eq!(
        eval(&bin(Prim::Mod, to_huge(2), lit(7))).unwrap(),
        Value::Int(2)
    );
    assert_eq!(
        eval(&bin(Prim::Mod, to_huge(3), lit(4))).unwrap(),
        Value::Int(1)
    );
}

/// `0`, `1` and `-1` raised to an exponent that is itself a power past any machine word,
/// `2 ^ 2 ^ 33`, read the exponent's parity from its kept form and build nothing.
#[test]
fn a_unit_to_a_kept_power_builds_no_exponent() {
    let exp = bin(Prim::Pow, lit(2), bin(Prim::Pow, lit(2), lit(33)));
    let pow = |x: i64, e: &Term| bin(Prim::Pow, lit(x), e.clone());
    assert_eq!(eval(&pow(1, &exp)).unwrap(), Value::Int(1));
    assert_eq!(eval(&pow(0, &exp)).unwrap(), Value::Int(0));
    assert_eq!(eval(&pow(-1, &exp)).unwrap(), Value::Int(1));
    // `3^(2^33)` is odd: its kept form has no power of 2 and an odd coefficient.
    let odd3 = bin(Prim::Pow, lit(3), bin(Prim::Pow, lit(2), lit(33)));
    assert_eq!(eval(&pow(-1, &odd3)).unwrap(), Value::Int(-1));
}

/// A sum whose operands share no powers builds them: `2^(2^100) + 1` needs `2^100` bits,
/// more than any machine's memory, and `2^(2^60) + 1` needs `2^57` bytes, more than any
/// address space. Each stops the run with an error naming the size, and the process goes on.
#[test]
fn a_sum_too_large_to_build_is_an_error_naming_its_size() {
    for (k, bytes) in [
        (100u32, "3.8 × 10^29 digits (1.6 × 10^29 bytes)"),
        (60, "3.5 × 10^17 digits (128 PiB)"),
    ] {
        let huge = bin(Prim::Pow, lit(2), bin(Prim::Pow, lit(2), lit(k as i64)));
        let err = eval(&add(huge.clone(), lit(1))).unwrap_err();
        assert!(
            matches!(&err, KernelError::NumberTooLarge { op: "+", .. }),
            "{err:?}"
        );
        assert_eq!(
            err.to_string(),
            format!(
                "Number too large for memory: `+` needs a number of about {bytes}{}",
                beyond_machine()
            )
        );
        // The same number is a value while it is kept: compared, multiplied, divided exactly.
        let half = bin(Prim::IntDiv, huge.clone(), lit(2));
        assert_eq!(
            eval(&bin(Prim::Lt, half.clone(), huge.clone())).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            eval(&bin(Prim::Mod, huge.clone(), lit(2))).unwrap(),
            Value::Int(0)
        );
        // A sum of two kept powers builds only what is above the powers they share: 1 + 2.
        let upper = bin(
            Prim::Pow,
            lit(2),
            add(bin(Prim::Pow, lit(2), lit(k as i64)), lit(1)),
        );
        assert_eq!(
            eval(&bin(
                Prim::Eq,
                add(huge.clone(), upper),
                bin(Prim::Mul, lit(3), huge.clone())
            ))
            .unwrap(),
            Value::Bool(true)
        );
    }
}

/// Printing a number builds its digits. `String(2 ^ 2 ^ 100)` would need `2^100` bits, so
/// it is an error naming that size, given before any digit is built; `2 ^ 2 ^ 16` prints
/// all of its 19729 digits, and `10 ^ 10 ^ 6` its million zeros.
#[test]
fn printing_a_number_too_large_to_build_is_an_error_naming_its_size() {
    let show = |t: Term| prim(Prim::Show, vec![t]);
    let pow = |a: Term, b: Term| bin(Prim::Pow, a, b);
    let huge = pow(lit(2), pow(lit(2), lit(100)));
    let err = eval(&show(huge.clone())).unwrap_err();
    assert!(
        matches!(&err, KernelError::NumberTooLarge { op: "String", .. }),
        "{err:?}"
    );
    assert_eq!(
        err.to_string(),
        format!(
            "Text too large for memory: `String` would write about 3.8 × 10^29 digits{}",
            beyond_machine()
        )
    );
    // A rational with a huge denominator is refused the same way.
    let rat = |t: Term| prim(Prim::CastRat, vec![t]);
    let tiny = bin(Prim::Div, rat(lit(3)), rat(huge));
    let err = eval(&show(tiny)).unwrap_err();
    assert!(
        matches!(&err, KernelError::NumberTooLarge { op: "String", .. }),
        "{err:?}"
    );
    let Value::Str(s) = eval(&show(pow(lit(2), pow(lit(2), lit(16))))).unwrap() else {
        panic!("a string")
    };
    assert_eq!(s.char_count(), 19729);
    assert!(s.flat().starts_with("2003529930406846464979"));
    let Value::Str(s) = eval(&show(pow(lit(10), pow(lit(10), lit(6))))).unwrap() else {
        panic!("a string")
    };
    assert_eq!(s.char_count(), 1_000_001);
    assert!(s.flat().starts_with("10") && s.flat()[1..].bytes().all(|b| b == b'0'));
}
