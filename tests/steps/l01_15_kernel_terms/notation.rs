//! One term per generator and per Tier 0 form, each written as sec:kernel writes it.

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Value, Witness};
use zed_tests::kernel::*;

#[test]
fn an_invoice_total_is_a_fold_over_a_family() {
    let line = |f: &str| get(var("line"), lit(f));
    let total = fold(
        fam(var("lines"), "line", mul(line("qty"), line("price"))),
        Term::PrimFn(Prim::Add),
        Some(lit(0)),
    );
    assert_eq!(
        total.to_string(),
        "fold(fam(lines, line -> (get(line, \"qty\") * get(line, \"price\"))), (+), \
         identity: 0, depth: 1, ev: {})"
    );
}

#[test]
fn grouping_orders_by_customer_is_a_reindex_with_its_witness() {
    let by_customer = Term::Reindex {
        family: rc(var("orders")),
        kf: rc(lam(
            &["k", "v"],
            path(vec![get(var("v"), lit("customer")), var("k")]),
        )),
        vf: rc(lam(&["k", "v"], var("v"))),
        witness: Witness::Residue,
    };
    assert_eq!(
        by_customer.to_string(),
        "reindex(orders, (k, v) -> path(get(v, \"customer\"), k), (k, v) -> v, witness: residue)"
    );
    let catalog = Term::Reindex {
        family: rc(var("orders")),
        kf: rc(var("swap")),
        vf: rc(var("id")),
        witness: Witness::Catalog("tuple.swap".into()),
    };
    assert!(
        catalog
            .to_string()
            .ends_with("witness: catalog(\"tuple.swap\"))")
    );
}

#[test]
fn a_filter_is_a_discard() {
    let open = discard(
        var("tickets"),
        lam(&["t"], eq(get(var("t"), lit("state")), atom("open"))),
    );
    assert_eq!(
        open.to_string(),
        "discard(tickets, t -> (get(t, \"state\") == #open))"
    );
}

#[test]
fn fibonacci_by_definedness_names_this_and_its_key() {
    let fib = Term::Fix {
        init: rc(var("upTo")),
        step: rc(if_(
            lt(var("n"), lit(2)),
            var("n"),
            add(
                app(var("fib"), vec![sub(var("n"), lit(1))]),
                app(var("fib"), vec![sub(var("n"), lit(2))]),
            ),
        )),
        this: "fib".into(),
        key: "n".into(),
        kind: FixKind::Definedness,
        ev: Evidence::new(),
    };
    assert_eq!(
        fib.to_string(),
        "fix(upTo, (fib, n) -> if (n < 2) { n } else { (fib((n - 1)) + fib((n - 2))) }, \
         definedness, ev: {})"
    );
}

#[test]
fn reachability_is_a_lattice_fix_with_its_join_and_evidence() {
    let ev: Evidence = [
        ("monotone".into(), Grade::Proved),
        ("ascendingChains".into(), Grade::Axiom),
    ]
    .into();
    let reach = Term::Fix {
        init: rc(var("start")),
        step: rc(var("next")),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: rc(Term::PrimFn(Prim::Union)),
        },
        ev,
    };
    // The record is written in property-name order, whatever order it was built in, and
    // in braces padded as a block's are.
    assert_eq!(
        reach.to_string(),
        "fix(start, next, join: union, ev: { ascendingChains: axiom, monotone: proved })"
    );
}

#[test]
fn a_countdown_is_a_gen_with_its_guard_position() {
    let countdown = Term::Gen {
        init: rc(lit(10)),
        step: rc(lam(&["n"], sub(var("n"), lit(1)))),
        guard: rc(lam(&["n"], prim(Prim::Gt, vec![var("n"), lit(0)]))),
        pos: GuardPos::Before,
    };
    assert_eq!(
        countdown.to_string(),
        "gen(10, n -> (n - 1), n -> (n > 0), guard: before)"
    );
}

#[test]
fn a_report_reads_stdin_and_pushes_to_stdout() {
    let echo = let_(
        "text",
        Term::Read("stdin".into()),
        Term::Push("stdout".into(), rc(var("text"))),
    );
    assert_eq!(
        echo.to_string(),
        "{ text = port.read(stdin); port.push(stdout, text) }"
    );
}

#[test]
fn a_shipping_rule_is_a_match_over_atoms() {
    let cost = Term::Match(
        rc(var("zone")),
        vec![
            (Pattern::Atom("local".into(), vec![]), lit(5)),
            (
                Pattern::Atom("abroad".into(), vec![Pattern::Bind("km".into())]),
                mul(var("km"), lit(2)),
            ),
            (Pattern::Lit(Value::Int(0)), lit(0)),
            (
                Pattern::Tuple(vec![Pattern::Wild, Pattern::Bind("x".into())]),
                var("x"),
            ),
            (Pattern::Tuple(vec![Pattern::Wild]), lit(1)),
        ],
    );
    assert_eq!(
        cost.to_string(),
        "match zone { #local -> 5, #abroad(km) -> (km * 2), 0 -> 0, (_, x) -> x, (_,) -> 1 }"
    );
}

#[test]
fn tuples_primitives_and_applied_lambdas_print_unambiguously() {
    let pair = prim(Prim::Tuple, vec![lit(1), lit("a")]);
    assert_eq!(pair.to_string(), "(1, \"a\")");
    assert_eq!(prim(Prim::Tuple, vec![lit(1)]).to_string(), "(1,)");
    assert_eq!(prim(Prim::Neg, vec![var("x")]).to_string(), "neg(x)");
    assert_eq!(count(var("orders")).to_string(), "count(orders)");
    assert_eq!(Term::PrimFn(Prim::Max).to_string(), "max");
    // A lambda applied in place is parenthesized, so its body does not swallow the call.
    let applied = app(lam(&["x"], add(var("x"), lit(1))), vec![lit(2)]);
    assert_eq!(applied.to_string(), "(x -> (x + 1))(2)");
    // Nested operators keep every parenthesis: no precedence is needed to read them.
    let nested = sub(var("a"), sub(var("b"), var("c")));
    assert_eq!(nested.to_string(), "(a - (b - c))");
}
