//! Each path of the hooks, reached by running a small program natively from the JIT, with
//! release fused and not, against the kernel's answer for the same program (DESIGN.md
//! sec:reduction: a native run gives the kernel's value or its error). A run that leaves a cell
//! live fails in `finish`, so every case also checks the counts. Paths that only a wrong plan
//! reaches are reached by changing the plan, as `l01_36_cranelift::checks` does.

use std::sync::Arc;

use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Lookup, Pattern, Prim, Shared, Term, Value, World};
use zedc::zir::legalize::Legalized;
use zedc::zir::lower::lower;
use zedc::zir::memory::{Mode, Plan, plan};

use super::*;
use crate::legal::legalize;

fn planned(t: &Term, fuse: bool) -> (Legalized, Plan) {
    let g = legalize(lower(t).unwrap());
    let p = plan(g.graph(), fuse);
    (g, p)
}

/// The native run of `t` in `w`: its value and kernel calls, or its error.
fn native(t: &Term, w: &World, fuse: bool) -> Result<(Value, u64), String> {
    let (g, p) = planned(t, fuse);
    crate::run(&g, &p, &mut Evaluator::new(w.clone())).map(|o| (o.value, o.kernel_calls))
}

/// The kernel's answer for `t` in `w`, which the native run gives with release fused and not;
/// with the kernel calls of the unfused run.
fn agreed(t: &Term, w: &World) -> Result<(Value, u64), String> {
    let want = Evaluator::new(w.clone()).run(t).map_err(|e| e.to_string());
    let mut calls = 0;
    for fuse in [true, false] {
        let got = native(t, w, fuse);
        assert_eq!(
            got.as_ref().map(|(v, _)| v),
            want.as_ref(),
            "{t}, fuse {fuse}"
        );
        calls = got.map_or(0, |(_, c)| c);
    }
    want.map(|v| (v, calls))
}

fn ok(t: &Term) -> (String, u64) {
    let (v, calls) = agreed(t, &World::new()).unwrap_or_else(|e| panic!("{t}: {e}"));
    (v.to_string(), calls)
}

fn refused(t: &Term) -> String {
    match agreed(t, &World::new()) {
        Ok((v, _)) => panic!("{t}: the kernel gives {v}"),
        Err(e) => e,
    }
}

/// `a ++ b`, a string the run makes in a cell.
fn cat(a: &str, b: &str) -> Term {
    prim(Prim::Concat, vec![lit(a), lit(b)])
}

/// `f(args…)` where `f` is the lambda `(params…) -> body`, so that the arguments reach the
/// body as words of the run rather than as constants of the graph.
fn called(params: &[&str], body: Term, args: Vec<Term>) -> Term {
    let_("f", lam(params, body), app(var("f"), args))
}

/// `#a(n0: a0, …)`; no names makes a tuple payload.
fn named(name: Term, names: &[&str], args: Vec<Term>) -> Term {
    let ns = Value::tuple(names.iter().map(|n| Value::str(n)).collect());
    let mut ins = vec![name, lit(ns)];
    ins.extend(args);
    prim(Prim::Atom, ins)
}

#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

fn with_source(name: &str, v: Value) -> World {
    let mut w = World::new();
    let p: Arc<dyn Lookup> = Arc::new(Same(v));
    w.sources.insert(name.into(), p);
    w
}

#[test]
fn a_tuple_of_data_is_made_natively_and_any_other_tuple_by_the_kernel() {
    let t = prim(Prim::Tuple, vec![cat("a", "b"), lit(1i64)]);
    assert_eq!(ok(&t), (r#"("ab", 1)"#.into(), 0));
    // The empty tuple and a tuple holding a function are the kernel's.
    assert_eq!(
        ok(&called(&["x"], prim(Prim::Tuple, vec![]), vec![lit(0i64)])).0,
        "()"
    );
    let holds = prim(Prim::Tuple, vec![lam(&["x"], var("x")), lit(1i64)]);
    let k = Evaluator::new(World::new()).run(&holds);
    assert_eq!(
        native(&holds, &World::new(), true).map(|(v, _)| v),
        k.map_err(|e| e.to_string())
    );
}

#[test]
fn atoms_by_name_by_position_and_empty_are_made_without_the_kernel() {
    let t = named(lit("a"), &["b", "a"], vec![cat("x", ""), lit(2i64)]);
    assert_eq!(ok(&t), (r#"#a(a: 2, b: "x")"#.into(), 0));
    let t = named(lit("a"), &[], vec![lit(2i64), cat("x", "")]);
    assert_eq!(ok(&t), (r#"#a(2, "x")"#.into(), 0));
    assert_eq!(ok(&named(lit("a"), &[], vec![])), ("#a()".into(), 0));
}

#[test]
fn an_atom_whose_name_is_made_by_the_run_is_not_kept_and_is_made_again() {
    // The name is a cell, so its shape is not kept: each call makes it again.
    let body = named(cat("n", "m"), &["v"], vec![var("y")]);
    let t = let_(
        "f",
        lam(&["y"], body),
        prim(
            Prim::Tuple,
            vec![
                app(var("f"), vec![lit(1i64)]),
                app(var("f"), vec![lit(2i64)]),
            ],
        ),
    );
    assert_eq!(ok(&t), ("(#nm(v: 1), #nm(v: 2))".into(), 0));
}

#[test]
fn an_atom_the_native_rules_refuse_is_the_kernels_refusal() {
    // A repeated field name, a name or a field name that is no string, unequal counts.
    refused(&named(lit("a"), &["a", "a"], vec![lit(1i64), lit(2i64)]));
    refused(&prim(
        Prim::Atom,
        vec![lit(1i64), lit(Value::tuple(vec![])), lit(2i64)],
    ));
    refused(&prim(
        Prim::Atom,
        vec![lit("a"), lit(Value::tuple(vec![Value::Int(1)])), lit(2i64)],
    ));
    refused(&named(lit("a"), &["a", "b"], vec![lit(1i64)]));
    // A payload holding a function is no data: the kernel decides.
    let t = named(lit("a"), &[], vec![lam(&["x"], var("x"))]);
    let k = Evaluator::new(World::new())
        .run(&t)
        .map_err(|e| e.to_string());
    assert_eq!(native(&t, &World::new(), false).map(|(v, _)| v), k);
}

#[test]
fn a_tuple_element_is_shared_and_any_other_read_is_the_kernels() {
    let pair = prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")]);
    let get = |i: i64| prim(Prim::TupleGet, vec![pair.clone(), lit(i)]);
    assert_eq!(ok(&get(1)), (r#""cd""#.into(), 0));
    // Past the end and below 0 are the failure `#outOfBounds`, which the kernel makes; a
    // value that is no tuple is refused.
    assert_eq!(ok(&get(2)), ("#outOfBounds".into(), 1));
    assert_eq!(ok(&get(-1)), ("#outOfBounds".into(), 1));
    refused(&prim(Prim::TupleGet, vec![cat("a", "b"), lit(0i64)]));
}

#[test]
fn strings_join_natively_and_any_other_concatenation_is_the_kernels() {
    assert_eq!(
        ok(&prim(Prim::Concat, vec![cat("a", "b"), lit("c")])),
        (r#""abc""#.into(), 0)
    );
    refused(&called(
        &["x"],
        prim(Prim::Concat, vec![var("x"), lit(1i64)]),
        vec![lit("a")],
    ));
}

#[test]
fn a_string_length_is_counted_natively_and_any_other_length_is_the_kernels() {
    assert_eq!(ok(&prim(Prim::Len, vec![cat("é", "ab")])), ("3".into(), 0));
    let t = called(&["x"], prim(Prim::Len, vec![var("x")]), vec![lit(5i64)]);
    let k = Evaluator::new(World::new())
        .run(&t)
        .map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &World::new()).map(|(v, _)| v), k);
}

#[test]
fn a_length_past_i64_max_is_the_kernels_big_integer() {
    // A string doubled 63 times holds 2^63 scalars, one past `i64::MAX`; joins share their
    // parts, so it is 63 small cells.
    let mut body = prim(Prim::Len, vec![var("s63")]);
    for i in (0..63).rev() {
        let s = format!("s{i}");
        body = let_(
            &format!("s{}", i + 1),
            prim(Prim::Concat, vec![var(&s), var(&s)]),
            body,
        );
    }
    let t = called(&["s0"], body, vec![lit("a")]);
    let (v, calls) = agreed(&t, &World::new()).unwrap();
    assert_eq!(v.to_string(), (1u128 << 63).to_string());
    assert_eq!(calls, 1, "the length alone is the kernel's");
}

#[test]
fn a_code_point_of_one_scalar_is_read_natively_and_any_other_is_the_kernels() {
    let cp = |x: Term| called(&["x"], prim(Prim::CodePoint, vec![var("x")]), vec![x]);
    assert_eq!(ok(&cp(cat("é", ""))), ("233".into(), 0));
    // Two scalars, none, and no string give the kernel's answer.
    for x in [cat("a", "b"), cat("", ""), lit(7i64)] {
        let t = cp(x);
        let k = Evaluator::new(World::new())
            .run(&t)
            .map_err(|e| e.to_string());
        assert_eq!(agreed(&t, &World::new()).map(|(v, _)| v), k, "{t}");
    }
}

#[test]
fn a_port_is_read_as_an_input_a_source_or_the_kernels_error() {
    let t = prim(Prim::Tuple, vec![Term::Read("x".into()), lit(1i64)]);
    let w = World::new().input("x", Value::str("in"));
    assert_eq!(agreed(&t, &w).unwrap().0.to_string(), r#"("in", 1)"#);
    // A lookup port is a word the kernel reads by a `let`, once however often it is used.
    let db = || Term::Read("db".into());
    let w = with_source("db", Value::Int(4));
    let t = prim(
        Prim::Tuple,
        vec![app(db(), vec![lit(0i64)]), app(db(), vec![lit(1i64)])],
    );
    assert_eq!(agreed(&t, &w).unwrap().0.to_string(), "(4, 4)");
    let t = prim(Prim::Eq, vec![db(), db()]);
    let k = Evaluator::new(w.clone()).run(&t).map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &w).map(|(v, _)| v), k);
    // A port the run was not given.
    let e = agreed(&Term::Read("y".into()), &World::new()).unwrap_err();
    assert!(e.contains('y'), "{e}");
}

#[test]
fn a_primitive_and_a_closure_given_to_the_kernel_are_its_function_terms() {
    // `g` is `+` as a value, and then a closure: an apply the runtime cannot resolve is the
    // kernel's, which gets the primitive and the closure's term.
    let apply = |g: Term| called(&["g"], app(var("g"), vec![lit(2i64), lit(3i64)]), vec![g]);
    assert_eq!(ok(&apply(Term::PrimFn(Prim::Add))).0, "5");
    let add = lam(&["a", "b"], prim(Prim::Mul, vec![var("a"), var("b")]));
    assert_eq!(ok(&apply(add)).0, "6");
    // A closure of the wrong number of parameters is the kernel's refusal.
    refused(&apply(lam(&["a"], var("a"))));
}

#[test]
fn a_function_value_called_twice_enters_its_code_by_its_registered_address() {
    let twice = lam(
        &["g", "x"],
        app(var("g"), vec![app(var("g"), vec![var("x")])]),
    );
    let inc = lam(&["y"], prim(Prim::Add, vec![var("y"), lit(1i64)]));
    let dbl = lam(&["y"], prim(Prim::Mul, vec![var("y"), lit(2i64)]));
    let t = let_(
        "twice",
        twice,
        prim(
            Prim::Tuple,
            vec![
                app(var("twice"), vec![inc, lit(1i64)]),
                app(var("twice"), vec![dbl, lit(3i64)]),
            ],
        ),
    );
    assert_eq!(ok(&t), ("(3, 12)".into(), 0));
}

#[test]
fn float_power_is_ieee_pow_with_the_canonical_nan() {
    let pow = |a: f64, b: f64| {
        called(
            &["a", "b"],
            prim(Prim::Pow, vec![var("a"), var("b")]),
            vec![lit(Value::float(a)), lit(Value::float(b))],
        )
    };
    assert_eq!(ok(&pow(2.0, 0.5)).0, ok(&lit(Value::float(2f64.sqrt()))).0);
    assert_eq!(ok(&pow(2.0, -1.0)).0, ok(&lit(Value::float(0.5))).0);
    // A finite base below -0.0 to a non-integer power is the NaN.
    let nan = ok(&pow(-8.0, 1.0 / 3.0)).0;
    assert_eq!(nan, Value::float(f64::NAN).to_string());
    // `rt_pow` itself gives the canonical NaN's bits.
    let bits = rt_pow((-8f64).to_bits() as i64, 0.5f64.to_bits() as i64);
    assert_eq!(bits as u64, zed_kernel::F64::new(f64::NAN).get().to_bits());
}

#[test]
fn a_condition_that_is_no_bool_is_the_kernels_decision() {
    // A failure atom as the condition is the result; any other value is refused.
    let c = |x: Term| called(&["c"], if_(var("c"), lit(1i64), lit(2i64)), vec![x]);
    let fail = named(lit("oops"), &[], vec![cat("a", "b")]);
    assert_eq!(ok(&c(fail)).0, r#"#oops("ab")"#);
    refused(&c(lit(3i64)));
    refused(&c(cat("a", "b")));
    // A lookup port as the condition is read by a `let`.
    let w = with_source("p", Value::Bool(true));
    let t = if_(Term::Read("p".into()), lit(1i64), lit(2i64));
    let k = Evaluator::new(w.clone()).run(&t).map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &w).map(|(v, _)| v), k);
}

#[test]
fn a_bool_given_to_the_branch_hook_picks_its_arm_without_the_kernel() {
    // Generated code tests a bool itself; the hook's own test is reached by a direct call.
    let t = called(&["c"], if_(var("c"), lit(1i64), lit(2i64)), vec![lit(true)]);
    let g = legalize(lower(&t).unwrap());
    let (t, _) = Tables::new(&g, &plan(g.graph(), false)).unwrap();
    let id = (0..t.nodes.len())
        .find(|&i| matches!(t.nodes[i].node().op, Op::If))
        .expect("an if");
    let mut s = State::new(Arc::new(t), Evaluator::new(World::new()));
    for (b, arm) in [(true, 0), (false, 1)] {
        let w = Word {
            tag: Word::BOOL,
            bits: i64::from(b),
        };
        assert_eq!(branch(&s.t, &mut s.run, id, &[w]), Ok(arm));
    }
    assert_eq!(s.run.kernel_calls, 0);
}

/// `match x { arms… }` with `x` given to a lambda, so it is a word of the run.
fn match_on(x: Term, arms: Vec<(Pattern, Term)>) -> Term {
    called(&["x"], Term::Match(Shared::new(var("x")), arms), vec![x])
}

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

#[test]
fn a_match_picks_the_first_arm_whose_pattern_the_data_matches() {
    let pair = prim(Prim::Tuple, vec![cat("a", "b"), lit(1i64)]);
    let arms = vec![
        (
            Pattern::Tuple(vec![Pattern::Wild, Pattern::Lit(Value::Int(2))]),
            lit(0i64),
        ),
        (
            Pattern::Tuple(vec![bind("s"), bind("n")]),
            prim(Prim::Tuple, vec![var("n"), var("s")]),
        ),
    ];
    assert_eq!(
        ok(&match_on(pair.clone(), arms)),
        (r#"(1, "ab")"#.into(), 0)
    );
    // An arm that reads one binder of an owned scrutinee: the other gets no copy.
    let arms = vec![(Pattern::Tuple(vec![bind("s"), bind("n")]), var("n"))];
    assert_eq!(ok(&match_on(pair.clone(), arms)).0, "1");
    // A scrutinee read again after the match is borrowed by it.
    let arms = vec![(
        Pattern::Tuple(vec![bind("s"), Pattern::Wild]),
        prim(Prim::Len, vec![var("s")]),
    )];
    let body = prim(
        Prim::Tuple,
        vec![Term::Match(Shared::new(var("x")), arms), var("x")],
    );
    assert_eq!(ok(&called(&["x"], body, vec![pair])).0, r#"(2, ("ab", 1))"#);
}

#[test]
fn data_no_arm_matches_is_the_kernels_failure() {
    let arms = vec![(Pattern::Lit(Value::Int(1)), lit(0i64))];
    let k = Evaluator::new(World::new())
        .run(&match_on(lit(2i64), arms.clone()))
        .map_err(|e| e.to_string());
    assert_eq!(
        agreed(&match_on(cat("a", ""), arms.clone()), &World::new()).is_err(),
        k.is_err()
    );
    assert_eq!(
        agreed(&match_on(lit(2i64), arms), &World::new()).map(|(v, _)| v),
        k
    );
}

#[test]
fn a_function_scrutinee_is_matched_by_the_kernel_and_bound_whole() {
    let f = lam(&["y"], prim(Prim::Add, vec![var("y"), lit(1i64)]));
    // A literal arm the function cannot match, then a binder that takes it whole.
    let arms = vec![
        (Pattern::Lit(Value::Int(0)), lit(0i64)),
        (bind("g"), app(var("g"), vec![lit(4i64)])),
    ];
    assert_eq!(ok(&match_on(f.clone(), arms)).0, "5");
    assert_eq!(
        ok(&match_on(f.clone(), vec![(Pattern::Wild, lit(9i64))])).0,
        "9"
    );
    // No arm: the kernel's failure or refusal.
    let arms = vec![(Pattern::Lit(Value::Int(0)), lit(0i64))];
    let t = match_on(f, arms);
    let k = Evaluator::new(World::new())
        .run(&t)
        .map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &World::new()).map(|(v, _)| v), k);
}

#[test]
fn a_function_result_is_refused_and_a_push_passes_the_ports_state() {
    let e = native(&lam(&["x"], var("x")), &World::new(), false).unwrap_err();
    assert_eq!(
        e,
        KernelError::Type("the program's result is a function".into()).to_string()
    );
    let w = World::new().output("o");
    let t = Term::Push("o".into(), Shared::new(cat("a", "b")));
    let k = Evaluator::new(w.clone()).run(&t).map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &w).map(|(v, _)| v), k);
}

#[test]
fn a_borrowed_argument_to_a_consuming_parameter_stops_at_the_call() {
    let t = let_(
        "f",
        lam(&["x"], prim(Prim::Concat, vec![var("x"), lit("!")])),
        let_(
            "s",
            cat("a", "b"),
            prim(
                Prim::Tuple,
                vec![
                    app(var("f"), vec![var("s")]),
                    prim(Prim::Len, vec![var("s")]),
                ],
            ),
        ),
    );
    let (g, mut p) = planned(&t, false);
    let (at, k) = (p.regions.iter().enumerate())
        .find_map(|(at, r)| {
            r.nodes
                .iter()
                .position(|n| n.callee.is_some())
                .map(|k| (at, k))
        })
        .expect("a resolved call");
    let n = &mut p.regions[at].nodes[k];
    n.modes[1] = Mode::Borrowed;
    let callee = n.callee.unwrap();
    p.regions[callee].args[0] = Mode::Owned;
    let e = crate::run(&g, &p, &mut Evaluator::new(World::new())).unwrap_err();
    assert!(
        e.contains("releases it, without a reference of its own"),
        "{e}"
    );
    assert!(e.contains("is passed borrowed to"), "{e}");
}

#[test]
fn a_borrowed_scrutinee_whose_arm_owns_a_binder_is_refused() {
    let arms = vec![(Pattern::Tuple(vec![bind("s"), Pattern::Wild]), var("s"))];
    let body = prim(
        Prim::Tuple,
        vec![Term::Match(Shared::new(var("x")), arms), var("x")],
    );
    let t = called(
        &["x"],
        body,
        vec![prim(Prim::Tuple, vec![cat("a", "b"), lit(1i64)])],
    );
    let (g, mut p) = planned(&t, false);
    let arm = (p.regions.iter())
        .find_map(|r| {
            (r.nodes.iter())
                .find(|n| n.regions.len() == 1 && n.modes.first() == Some(&Mode::Borrowed))
                .map(|n| n.regions[0])
        })
        .expect("a match with a borrowed scrutinee");
    p.regions[arm].args[0] = Mode::Owned;
    let e = crate::run(&g, &p, &mut Evaluator::new(World::new())).unwrap_err();
    assert!(
        e.contains("a part of a value that the `match` only borrows"),
        "{e}"
    );
}

#[test]
fn recorded_runs_list_the_cells_they_free() {
    crate::record_releases(true);
    let _ = crate::counted();
    let t = prim(Prim::Tuple, vec![cat("a", "b")]);
    assert_eq!(ok(&t).0, r#"("ab",)"#);
    let c = crate::counted();
    crate::record_releases(false);
    assert_eq!(c.runs, 2, "fused and not");
    assert_eq!(c.released.len(), 2);
    assert!(c.released.iter().all(|r| r.len() == 2), "{:?}", c.released);
    assert!(c.left.is_empty());
}

#[test]
fn an_atom_of_constant_names_keeps_its_shape_across_runs_of_its_node() {
    // The same atom node runs three times; its shape is found once and kept.
    let f = lam(&["y"], named(lit("a"), &["v"], vec![var("y")]));
    let calls = (1..=3)
        .map(|i| app(var("f"), vec![lit(i as i64)]))
        .collect();
    let t = let_("f", f, prim(Prim::Tuple, calls));
    assert_eq!(ok(&t), ("(#a(v: 1), #a(v: 2), #a(v: 3))".into(), 0));
}

#[test]
fn a_closure_reads_its_captured_values_from_its_cell() {
    let t = let_(
        "s",
        cat("a", "b"),
        let_(
            "g",
            lam(&["x"], prim(Prim::Concat, vec![var("x"), var("s")])),
            prim(
                Prim::Tuple,
                vec![app(var("g"), vec![lit("1")]), app(var("g"), vec![lit("2")])],
            ),
        ),
    );
    assert_eq!(ok(&t).0, r#"("1ab", "2ab")"#);
}

#[test]
fn a_string_joined_to_a_constant_or_a_cell_that_is_no_string_is_refused() {
    let tup = Value::tuple(vec![Value::Int(1)]);
    refused(&called(
        &["x"],
        prim(Prim::Concat, vec![var("x"), lit(tup)]),
        vec![lit("a")],
    ));
    let cell = prim(Prim::Tuple, vec![cat("b", "c")]);
    refused(&called(
        &["x"],
        prim(Prim::Concat, vec![var("x"), cell]),
        vec![lit("a")],
    ));
}

#[test]
fn a_failure_no_arm_names_is_refused_as_the_kernel_refuses_it() {
    let arms = vec![(Pattern::Lit(Value::Int(1)), lit(0i64))];
    let t = match_on(named(lit("oops"), &[], vec![cat("a", "b")]), arms);
    let k = Evaluator::new(World::new())
        .run(&t)
        .map_err(|e| e.to_string());
    assert_eq!(agreed(&t, &World::new()).map(|(v, _)| v), k);
}
