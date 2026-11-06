//! Item LOWER-legalize: one legalization pass on ZIR before planning. Each back end declares
//! the expansions it wants (`zed_native::EXPANSIONS`, `memory::EXPANSIONS`); a program that
//! uses each expanded operation gives the kernel's value on the counting machine and natively;
//! the Cranelift back end expands `>` and `>=` and the machine does not; a derived node's
//! certificate that holds a `>` is put in the node's place and its `>` expanded in turn; and a
//! back end handed an operation it declared expanded refuses it by name.

use std::sync::{Arc, Mutex};

use zed_kernel::term::Shared;
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim};
use zed_kernel::{Evaluator, Prim, Term, Value, World};
use zed_tests::scaling;
use zedc::zir::legalize::{Expansion, Expansions, legalize};
use zedc::zir::lower::{lower, raise};
use zedc::zir::memory::{self, plan};
use zedc::zir::{Edge, Node, Op, Region, RegionKind, Src, text};

use super::{float, kernel};

/// `g`'s value natively, on the counting machine, and by the kernel on the term the machine's
/// graph raises to; each back end gets `g` legalized by its own declaration.
fn every_back_end(g: &Region) -> [Result<Value, String>; 3] {
    let n = zed_native::legalize(g.clone());
    let native = zed_native::run(
        &n,
        &plan(n.graph(), true),
        &mut Evaluator::new(World::new()),
    );
    let m = legalize(g.clone(), memory::EXPANSIONS);
    let m = m.graph();
    let machine = memory::run(m, &plan(m, true), &mut Evaluator::new(World::new()));
    let kernel = raise(m).and_then(|t| super::kernel(&t));
    [native.map(|o| o.value), machine.map(|(v, _)| v), kernel]
}

/// Shipping rules that compare with `>` and `>=`: free shipping over 1,000 grams, a surcharge
/// at 20 kg or more, a float weight that is NaN or a negative zero, and names compared as text.
fn shipping_rules() -> Vec<Term> {
    let over = |w: Term, limit: Term| prim(Prim::Gt, vec![w, limit]);
    let at_least = |w: Term, limit: Term| prim(Prim::Ge, vec![w, limit]);
    vec![
        if_(over(lit(1200i64), lit(1000i64)), lit(0i64), lit(499i64)),
        if_(over(lit(1000i64), lit(1000i64)), lit(0i64), lit(499i64)),
        at_least(lit(20_000i64), lit(20_000i64)),
        at_least(lit(19_999i64), lit(20_000i64)),
        over(float(f64::NAN), float(0.0)),
        at_least(float(f64::NAN), float(f64::NAN)),
        at_least(float(-0.0), float(0.0)),
        over(float(2.5), float(-0.0)),
        over(lit("Oslo"), lit("Bergen")),
        at_least(lit("Bergen"), lit("Oslo")),
        over(lit(i64::MAX), lit(i64::MIN)),
    ]
}

#[test]
fn shipping_rules_compare_alike_on_every_back_end() {
    for t in shipping_rules() {
        let want = kernel(&t).unwrap();
        let g = lower(&t).unwrap();
        for got in every_back_end(&g) {
            assert_eq!(got.as_ref(), Ok(&want), "{t:?}");
        }
    }
}

#[test]
fn a_failure_compared_gives_the_same_failure_on_every_back_end() {
    // A missing weight is the atom `#none`; both sides missing merge their failures.
    let none = || Term::Lit(Value::atom("none"));
    let late = || Term::Lit(Value::atom("late"));
    for t in [
        prim(Prim::Gt, vec![none(), lit(1000i64)]),
        prim(Prim::Ge, vec![lit(1000i64), none()]),
        prim(Prim::Gt, vec![none(), late()]),
    ] {
        let want = kernel(&t).unwrap();
        for got in every_back_end(&lower(&t).unwrap()) {
            assert_eq!(got.as_ref(), Ok(&want), "{t:?}");
        }
    }
}

/// A parcel check as a derived node: its certificate, the node's definition, adds two parcel
/// weights and asks whether the sum is over a limit.
const PARCELS: &str = "\
zir 1
r region function ()
r.0 scan (1200, 450, 1500) -> (bool)
r.0/0 region function (int; int; int)
r.0/0.0 prim + (r.0/0^0, r.0/0^1) -> (int)
r.0/0.1 prim > (r.0/0.0^0, r.0/0^2) -> (bool)
r.0/0 results (r.0/0.1^0)
r results (r.0^0)
";

#[test]
fn a_refused_comparison_names_the_operator_and_operands_as_written() {
    // A weight compared with a city's name: the refusal shows `>` or `>=` on its operands in
    // the order the program wrote them, though the Cranelift back end computes `<` or `<=` on
    // them swapped.
    for (p, written) in [(Prim::Gt, "`>`"), (Prim::Ge, "`>=`")] {
        for weight_first in [true, false] {
            let types = if weight_first {
                "`int`, `String`"
            } else {
                "`String`, `int`"
            };
            let want = format!("type error: {written} applied to {types}");
            for t in refused_comparisons(p, weight_first) {
                assert_eq!(kernel(&t), Err(want.clone()), "{t:?}");
                for got in every_back_end(&lower(&t).unwrap()) {
                    assert_eq!(got, Err(want.clone()), "{t:?}");
                }
            }
        }
    }
}

/// The weight `1` compared by `p` with the city "Oslo", the weight first or second: alone; in
/// the body of a `fam`, which the kernel runs whole, the weight being its key; and in a
/// function the kernel is handed as a value and calls on the weight.
fn refused_comparisons(p: Prim, weight_first: bool) -> [Term; 3] {
    let compared = |w: Term| {
        let city = lit("Oslo");
        let args = if weight_first {
            vec![w, city]
        } else {
            vec![city, w]
        };
        prim(p, args)
    };
    let weights = || lit(Value::Family(zed_kernel::Family::of([(1i64, 0i64)])));
    let w = || Term::Var("w".into());
    let fam = |body: Term| Term::Fam {
        domain: Shared::new(weights()),
        var: "w".into(),
        body: Shared::new(body),
    };
    [
        compared(lit(1i64)),
        fam(compared(w())),
        let_(
            "check",
            lam(&["x"], compared(Term::Var("x".into()))),
            fam(app(Term::Var("check".into()), vec![w()])),
        ),
    ]
}

/// The bytes of the stack a native run maps (`zed_rt::Stack::new`): memory and swap together,
/// to a page or two.
fn native_stack() -> u64 {
    let info = std::fs::read_to_string("/proc/meminfo").expect("Linux has /proc");
    let kib = |key: &str| -> u64 {
        info.lines()
            .find_map(|l| l.strip_prefix(key))
            .and_then(|v| v.trim().strip_suffix("kB"))
            .and_then(|v| v.trim().parse().ok())
            .unwrap_or_else(|| panic!("/proc/meminfo has {key} in kB"))
    };
    (kib("MemTotal:") + kib("SwapTotal:") + 8) << 10
}

/// Two weights that agree in their first `2^30` bits, compared with `>` and `>=` when the
/// system has too little memory left to tell them apart: each back end refuses with the
/// operator the program wrote.
#[test]
fn an_order_refused_its_memory_names_the_operator_as_written() {
    use zed_tests::step_helpers::l01_17_value_representation::{
        MARGIN, WIDE, in_child_at, lower_limit, lower_limit_by,
    };
    if !in_child_at(
        module_path!(),
        "an_order_refused_its_memory_names_the_operator_as_written",
    ) {
        return;
    }
    let heavy = Value::integer(zed_kernel::Rat::int(
        (num_bigint::BigInt::from(1u32) << WIDE) + 1u32,
    ));
    let light = Value::integer(
        zed_kernel::Rat::int(num_bigint::BigInt::from(2))
            .pow(&num_bigint::BigUint::from(WIDE))
            .expect("a power of two is kept"),
    );
    // The graph is built here, not lowered: lowering gives each constant a content address
    // from its decimal digits, which for a number of 2^30 bits takes minutes.
    let cases = [(Prim::Gt, ">"), (Prim::Ge, ">=")].map(|(p, op)| {
        let g = Region {
            kind: RegionKind::Function,
            args: Vec::new(),
            nodes: vec![Node {
                op: Op::Prim(p),
                inputs: vec![Src::Const(heavy.clone()), Src::Const(light.clone())],
                outputs: vec![Edge::value(zed_kernel::types::Type::bool())],
                regions: Vec::new(),
            }],
            results: vec![Src::Out(0, 0)],
        };
        (
            op,
            zed_native::legalize(g.clone()),
            legalize(g, memory::EXPANSIONS),
        )
    });
    // A native run maps a stack as large as memory first, which leaves it the margin.
    lower_limit_by(native_stack() + MARGIN);
    let native: Vec<_> = cases
        .iter()
        .map(|(_, n, _)| {
            let p = plan(n.graph(), true);
            zed_native::run(n, &p, &mut Evaluator::new(World::new())).map(|o| o.value)
        })
        .collect();
    lower_limit();
    for ((op, _, m), native) in cases.iter().zip(native) {
        let m = m.graph();
        let machine = memory::run(m, &plan(m, true), &mut Evaluator::new(World::new()));
        let kernel = raise(m).and_then(|t| super::kernel(&t));
        let want = kernel.unwrap_err();
        assert!(
            want.starts_with(&format!("`{op}` must compare two numbers")),
            "{want}"
        );
        assert_eq!(machine.map(|(v, _)| v), Err(want.clone()), "{op}: machine");
        assert_eq!(native, Err(want.clone()), "{op}: native");
    }
}

#[test]
fn a_derived_node_runs_as_its_certificate_on_every_back_end() {
    let g = text::parse(PARCELS).unwrap();
    for got in every_back_end(&g) {
        assert_eq!(got, Ok(Value::Bool(true)));
    }
}

#[test]
fn an_expansion_that_yields_another_is_expanded_too() {
    // The certificate's `>` is in the root region once the `scan` is expanded, and the
    // Cranelift back end, which declares `>` expanded, gets it as `<` on swapped inputs.
    let g = text::parse(PARCELS).unwrap();
    let n = zed_native::legalize(g.clone());
    assert_eq!(
        text::print(n.graph()),
        "zir 1\n\
         r region function ()\n\
         r.0 prim + (1200, 450) -> (int)\n\
         r.1 prim < (1500, r.0^0) -> (bool)\n\
         r results (r.1^0)\n"
    );
    // Of the two nodes left, the `<` is the one swapped.
    assert!(!n.swapped().contains(0) && n.swapped().contains(1));
    // The machine expands the `scan` and keeps the `>`, which its kernel runs.
    assert_eq!(
        text::print(legalize(g, memory::EXPANSIONS).graph()),
        "zir 1\n\
         r region function ()\n\
         r.0 prim + (1200, 450) -> (int)\n\
         r.1 prim > (r.0^0, 1500) -> (bool)\n\
         r results (r.1^0)\n"
    );
}

#[test]
fn greater_than_as_a_function_value_is_not_rewritten() {
    // `>` with no inputs is the primitive itself, passed to a fold or a sort; only an applied
    // `>` has inputs to swap.
    let g = text::parse(
        "zir 1\n\
         r region function ()\n\
         r.0 prim > () -> ((-> (tuple int int) bool))\n\
         r results (r.0^0)\n",
    )
    .unwrap();
    let n = zed_native::legalize(g.clone());
    assert_eq!(**n.graph(), g);
    assert!(!n.swapped().contains(0));
}

#[test]
fn a_comparison_inside_a_lambda_and_a_branch_is_expanded() {
    let g = text::parse(
        "zir 1\n\
         r region function ()\n\
         r.0 lambda () -> ((-> int bool))\n\
         r.0/0 region function (int)\n\
         r.0/0.0 prim >= (r.0/0^0, 18) -> (bool)\n\
         r.0/0 results (r.0/0.0^0)\n\
         r.1 apply (r.0^0, 21) -> (bool)\n\
         r.2 if (r.1^0) -> (int)\n\
         r.2/0 region match ()\n\
         r.2/0.0 prim > (7, 3) -> (bool)\n\
         r.2/0 results (1)\n\
         r.2/1 region match ()\n\
         r.2/1 results (0)\n\
         r results (r.2^0)\n",
    )
    .unwrap();
    let n = text::print(zed_native::legalize(g.clone()).graph());
    assert!(n.contains("r.0/0.0 prim <= (18, r.0/0^0)"), "{n}");
    assert!(n.contains("r.2/0.0 prim < (3, 7)"), "{n}");
    for got in every_back_end(&g) {
        assert_eq!(got, Ok(Value::Int(1)));
    }
}

#[test]
fn each_back_end_refuses_what_it_declared_expanded_by_name() {
    // Cranelift handed a `>` that legalization did not expand, the graph legalized for the
    // machine, names it.
    let t = prim(Prim::Gt, vec![lit(2i64), lit(1i64)]);
    let g = legalize(lower(&t).unwrap(), memory::EXPANSIONS);
    let err = zed_native::run(
        &g,
        &plan(g.graph(), true),
        &mut Evaluator::new(World::new()),
    );
    let err = err.map(|o| o.value).unwrap_err();
    assert!(
        err.contains("`prim >` has no lowering here") && err.contains("(gt)"),
        "{err}"
    );
    // The machine handed a derived node it did not expand names it.
    let g = text::parse(PARCELS).unwrap();
    let err = memory::run(&g, &plan(&g, true), &mut Evaluator::new(World::new())).unwrap_err();
    assert!(err.contains("`scan` has no kernel term here"), "{err}");
}

#[test]
fn the_declarations_are_fixed_sets() {
    assert!(zed_native::EXPANSIONS.contains(Expansion::Gt));
    assert!(zed_native::EXPANSIONS.contains(Expansion::Ge));
    assert!(zed_native::EXPANSIONS.contains(Expansion::Derived));
    assert_eq!(
        memory::EXPANSIONS,
        Expansions::of(&[Expansion::Derived]),
        "the machine runs every primitive through its kernel"
    );
}

/// `n` parcel checks in a row, each a derived node whose certificate compares with `>` and
/// `>=`, and each reading the one before: legalization's work is linear in the graph.
fn parcel_checks(n: usize) -> Region {
    let int = || Edge::value(zed_kernel::types::Type::int());
    let certificate = Region {
        kind: RegionKind::Function,
        args: vec![int(), int()],
        nodes: vec![
            Node {
                op: Op::Prim(Prim::Gt),
                inputs: vec![Src::Arg(0), Src::Arg(1)],
                outputs: vec![int()],
                regions: Vec::new(),
            },
            Node {
                op: Op::Prim(Prim::Ge),
                inputs: vec![Src::Arg(1), Src::Arg(0)],
                outputs: vec![int()],
                regions: Vec::new(),
            },
        ],
        results: vec![Src::Out(1, 0)],
    };
    let nodes = (0..n)
        .map(|i| Node {
            op: Op::Derived(zedc::zir::Derived::Scan),
            inputs: vec![
                if i == 0 {
                    Src::Const(Value::Int(0))
                } else {
                    Src::Out(i - 1, 0)
                },
                Src::Const(Value::Int(i as i64)),
            ],
            outputs: vec![int()],
            regions: vec![Arc::new(certificate.clone())],
        })
        .collect();
    Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes,
        results: vec![Src::Out(n - 1, 0)],
    }
}

#[test]
fn legalization_is_linear_in_the_graph() {
    let n = 20_000;
    let (small_runs, large_runs) = scaling::Meter::new().runs();
    let pool = |k: usize, runs: usize| Mutex::new((0..runs).map(|_| parcel_checks(k)).collect());
    let (small, large): (Mutex<Vec<Region>>, Mutex<Vec<Region>>) =
        (pool(n, small_runs), pool(scaling::FACTOR * n, large_runs));
    let l = zed_native::legalize(parcel_checks(3));
    let g = l.graph();
    assert_eq!((g.nodes.len(), l.nodes()), (6, 6));
    assert!((0..6).all(|k| l.swapped().contains(k)));
    assert!(
        g.nodes
            .iter()
            .all(|n| matches!(n.op, Op::Prim(Prim::Lt | Prim::Le)))
    );
    scaling::check("legalizing parcel checks", n, |k| {
        let pool = if k == n { &small } else { &large };
        let g = pool.lock().expect("no run panicked").pop();
        drop(zed_native::legalize(g.expect("a graph built for each run")));
    });
}
