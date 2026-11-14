//! A wrong plan is caught natively as the machine catches it at the end of the run: a missed
//! drop leaves a cell live, a missing dup frees a cell still in use, and a borrowed argument
//! given to a parameter that consumes it is the machine's error, word for word; a plan with no
//! regions, or one that resolves a call to a region that is no lambda, is refused before any
//! code is made; and a borrowed scrutinee whose arm owns a binder is refused at the `match`.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, World};
use zedc::zir::memory::Mode;

use super::planned;

fn reads_twice() -> zed_kernel::Term {
    let_(
        "s",
        prim(Prim::Concat, vec![lit("ab"), lit("c")]),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    )
}

fn run(g: &zedc::zir::legalize::Legalized, p: &zedc::zir::memory::Plan) -> Result<String, String> {
    zed_native::run(g, p, &mut Evaluator::new(World::new())).map(|o| o.value.to_string())
}

#[test]
fn the_right_plan_runs() {
    let (g, p) = planned(&reads_twice());
    assert_eq!(run(&g, &p).unwrap(), "(3, \"ABC\")");
}

#[test]
fn a_missed_drop_leaves_a_cell_live() {
    let (g, mut p) = planned(&reads_twice());
    p["r"].nodes[2].drops.clear();
    assert_eq!(
        run(&g, &p).unwrap_err(),
        zed_rt::bug(
            "kept values in memory that nothing uses after the program's result was made",
            "1 cell live after the result is dropped: 1 String allocated by node r.0"
        )
    );
}

#[test]
fn a_missing_dup_frees_a_cell_still_in_use() {
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("ab"), lit("c")]),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let (g, mut p) = planned(&t);
    let r = &mut p["r"];
    let k = r
        .nodes
        .iter()
        .position(|n| !n.dups.is_empty())
        .expect("a dup");
    r.nodes[k].dups.clear();
    let e = run(&g, &p).unwrap_err();
    assert!(e.contains("freed"), "{e}");
}

#[test]
fn a_borrowed_argument_to_a_consuming_parameter_is_the_machines_error() {
    let t = let_(
        "f",
        lam(&["x"], prim(Prim::Concat, vec![var("x"), lit("!")])),
        let_(
            "s",
            prim(Prim::Concat, vec![lit("a"), lit("b")]),
            prim(
                Prim::Tuple,
                vec![
                    app(var("f"), vec![var("s")]),
                    prim(Prim::Len, vec![var("s")]),
                ],
            ),
        ),
    );
    let (g, mut p) = planned(&t);
    let (at, k) = p
        .regions
        .iter()
        .enumerate()
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
    let mut ev = Evaluator::new(World::new());
    let want = zedc::zir::memory::run(g.graph(), &p, &mut ev).unwrap_err();
    let got = run(&g, &p).unwrap_err();
    assert!(
        got.starts_with("the program stopped because of a bug in zedc")
            && got.ends_with(want.trim_start_matches("memory: ")),
        "{got}"
    );
    assert!(want.contains("is passed borrowed to"), "{want}");
}

#[test]
fn a_body_returning_its_capture_dups_it_and_without_the_dup_frees_it_early() {
    // The body borrows its capture `s` and returns it, so the result is a dup of it.
    let t = let_(
        "s",
        prim(Prim::Concat, vec![lit("ab"), lit("c")]),
        let_(
            "f",
            lam(&["x"], var("s")),
            prim(Prim::Tuple, vec![app(var("f"), vec![lit(1i64)])]),
        ),
    );
    let (g, mut p) = planned(&t);
    assert_eq!(run(&g, &p).unwrap(), "(\"abc\",)");
    let body = &mut p["r.1/0"];
    assert_eq!(body.result_dups, vec![0]);
    body.result_dups.clear();
    let e = run(&g, &p).unwrap_err();
    assert!(e.contains("freed"), "{e}");
}

/// The message of a failure of zedc's own making of machine code, with `detail` for zedc's
/// developers.
fn codegen_bug(detail: &str) -> String {
    format!(
        "zedc could not make machine code for the program because of a bug in zedc, not in the \
         program. Please report it to the Zed developers with the program's source and this \
         line: {detail}. Until it is fixed, `zedc run` runs the program without machine code"
    )
}

#[test]
fn a_plan_with_no_regions_or_a_call_to_no_lambda_is_refused_before_code_is_made() {
    // `g = x -> (x, 1); g("a" ++ "b")`, at the root and inside an `if` arm.
    let g = || lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1i64)]));
    let call = let_(
        "g",
        g(),
        app(var("g"), vec![prim(Prim::Concat, vec![lit("a"), lit("b")])]),
    );
    let nested = zed_kernel::term::build::if_(lit(true), call.clone(), lit(0i64));
    let (g1, mut p1) = planned(&call);
    assert_eq!(run(&g1, &p1).unwrap(), "(\"ab\", 1)");
    p1.regions.clear();
    assert_eq!(
        run(&g1, &p1).unwrap_err(),
        codegen_bug("region `r` has no plan; only the root, lambda bodies and arms do")
    );
    let (g1, mut p1) = planned(&call);
    p1["r"].nodes[2].callee = Some(0);
    assert_eq!(
        run(&g1, &p1).unwrap_err(),
        codegen_bug("r.2: the plan calls `r`, no lambda")
    );
    // Inside an arm the message names the call by its path through the `if`, node 0 of the
    // root (its condition is a constant), arm 0.
    let (g2, mut p2) = planned(&nested);
    assert_eq!(run(&g2, &p2).unwrap(), "(\"ab\", 1)");
    let (at, k) = p2
        .regions
        .iter()
        .enumerate()
        .find_map(|(at, r)| {
            r.nodes
                .iter()
                .position(|n| n.callee.is_some())
                .map(|k| (at, k))
        })
        .expect("a resolved call");
    p2.regions[at].nodes[k].callee = Some(0);
    assert_eq!(
        run(&g2, &p2).unwrap_err(),
        codegen_bug(&format!("r.0/0.{k}: the plan calls `r`, no lambda"))
    );
}

#[test]
fn an_argument_passed_owned_to_a_body_that_borrows_it_is_freed_after_the_call() {
    // `g = x -> len(x); g("a" ++ "b")`. The plan passes the string borrowed and drops it after
    // the call; a plan that passes it owned instead, with no drop, is as right: the caller
    // still holds it for the call and frees it when the body returns. The machine and native
    // code agree on both plans, and both free the string.
    let t = let_(
        "g",
        lam(&["x"], prim(Prim::Len, vec![var("x")])),
        app(var("g"), vec![prim(Prim::Concat, vec![lit("a"), lit("b")])]),
    );
    let (g, mut p) = planned(&t);
    let k = p["r"]
        .nodes
        .iter()
        .position(|n| n.callee.is_some())
        .expect("a resolved call");
    for owned in [false, true] {
        if owned {
            let n = &mut p["r"].nodes[k];
            assert_eq!(n.modes[1], Mode::Borrowed);
            n.modes[1] = Mode::Owned;
            let before = n.drops.len();
            n.drops.retain(|d| !matches!(d, zedc::zir::Src::Out(1, 0)));
            assert_eq!(
                n.drops.len() + 1,
                before,
                "the string is dropped after the call"
            );
        }
        let callee = p["r"].nodes[k].callee.unwrap();
        assert_eq!(p.regions[callee].args[0], Mode::Borrowed);
        let (v, s) = zedc::zir::memory::run(g.graph(), &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("owned {owned}: {e}"));
        let o = zed_native::run(&g, &p, &mut Evaluator::new(World::new()))
            .unwrap_or_else(|e| panic!("owned {owned}: {e}"));
        assert_eq!(
            (v.to_string(), o.value.to_string()),
            ("2".into(), "2".into())
        );
        assert_eq!(
            (o.stats.allocations, o.stats.frees),
            (s.allocations, s.frees),
            "owned {owned}"
        );
    }
}

#[test]
fn a_borrowed_scrutinee_whose_arm_owns_a_binder_is_refused_at_the_match() {
    // `match ("a" ++ "b", "c" ++ "d") { (x, _) -> x }`: the arm keeps `x` owned, so the plan
    // gives the `match` its scrutinee owned; a plan that borrows it cannot hand the part over.
    use zed_kernel::{Pattern, Shared, Term};
    let cat = |a: &str, b: &str| prim(Prim::Concat, vec![lit(a), lit(b)]);
    let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
    let t = Term::Match(
        Shared::new(prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")])),
        vec![(p, var("x"))],
    );
    let (g, mut p) = planned(&t);
    assert_eq!(run(&g, &p).unwrap(), "\"ab\"");
    p["r"].nodes[3].modes[0] = Mode::Borrowed;
    assert_eq!(
        run(&g, &p).unwrap_err(),
        zed_rt::bug(
            "took ownership of a part of a value that the `match` only borrows",
            "r.3: the scrutinee is borrowed, and arm 0 owns binder 0"
        )
    );
}
