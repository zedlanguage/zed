//! The machine's checks fail on a wrong plan: a missed drop, an extra dup, a missing dup, a
//! borrowed argument given to a parameter that consumes it, and each other check of the machine
//! (a region with no plan, a call to another region, an argument held other than it arrives, a
//! region that ends owning an edge, a read after a last use) is reported, with the node and the
//! edge.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zedc::zir::memory::Mode;

use super::{cat, planned, run};

fn reads_twice() -> zed_kernel::Term {
    let_(
        "s",
        cat("ab", "c"),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    )
}

#[test]
fn a_missed_drop_is_a_leak() {
    let (g, mut p) = planned(&reads_twice(), true);
    p["r"].nodes[2].drops.clear();
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.2: edge 0.0 is still owned after its last use, a leak"
    );
}

#[test]
fn an_extra_dup_is_a_count_above_its_references() {
    let (g, mut p) = planned(&reads_twice(), true);
    p["r"].nodes[1].dups.push(0);
    let e = run(&g, &p).unwrap_err();
    assert!(
        e.starts_with("memory: at node r.1, cell 0 has count 2 and 1 reference"),
        "{e}"
    );
}

#[test]
fn a_missing_dup_consumes_an_edge_twice() {
    let t = let_(
        "s",
        cat("ab", "c"),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let (g, mut p) = planned(&t, true);
    p["r"].nodes[1].dups.clear();
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.1: input 1, taken owned consumes edge 0.0, already consumed or past its \
         last use"
    );
}

#[test]
fn a_borrowed_argument_to_a_consuming_parameter_is_refused() {
    let g = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1)]));
    let t = let_("g", g, app(var("g"), vec![cat("a", "b")]));
    let (g, mut p) = planned(&t, true);
    p["r"].nodes[2].modes[1] = Mode::Borrowed;
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.2: argument 0 is passed borrowed to `r.0/0`, which consumes it"
    );
}

/// `(x -> (x, 1))("a" ++ "b")`: a lambda body that consumes its argument.
fn call() -> zed_kernel::Term {
    let g = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1)]));
    let_("g", g, app(var("g"), vec![cat("a", "b")]))
}

/// `s = "ab" ++ "c"; f = x -> s; f(0)`: a body that returns its capture.
fn capture() -> zed_kernel::Term {
    let f = lam(&["x"], var("s"));
    let_(
        "s",
        cat("ab", "c"),
        let_("f", f, app(var("f"), vec![lit(0)])),
    )
}

/// `match ("a" ++ "b", "c" ++ "d") { (x, _) -> x }`: an arm that keeps one part.
fn first() -> zed_kernel::Term {
    use zed_kernel::{Pattern, Shared, Term};
    let pair = prim(Prim::Tuple, vec![cat("a", "b"), cat("c", "d")]);
    let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
    Term::Match(Shared::new(pair), vec![(p, var("x"))])
}

/// `s = "ab" ++ "c"; if len(s) > 5 { (s, 1) } else { 0 }`: the `if` passes `s` owned, and
/// the arm that runs drops it on entry.
fn arm() -> zed_kernel::Term {
    let c = prim(Prim::Gt, vec![prim(Prim::Len, vec![var("s")]), lit(5)]);
    let t = zed_kernel::term::build::if_(c, prim(Prim::Tuple, vec![var("s"), lit(1)]), lit(0));
    let_("s", cat("ab", "c"), t)
}

/// A wrong plan: a program, the change that spoils its plan, and the machine's report.
type Wrong = (
    &'static str,
    fn() -> zed_kernel::Term,
    fn(&mut zedc::zir::memory::Plan),
    &'static str,
);

#[test]
fn each_check_of_the_machine_reports_its_wrong_plan() {
    let check = "(a count above its references is a missed drop, one below is an extra drop)";
    let cases: [Wrong; 16] = [
        (
            "a borrowed scrutinee whose arm owns a binder",
            first,
            |p| p["r"].nodes[3].modes[0] = Mode::Borrowed,
            "memory: r.3: the scrutinee is borrowed, and arm 0 owns binder 0",
        ),
        (
            "no plan at all",
            reads_twice,
            |p| p.regions.clear(),
            "memory: region `r` has no plan; only the root, lambda bodies and arms do",
        ),
        (
            "an arm with no plan",
            first,
            |p| p["r"].nodes[3].regions.clear(),
            "memory: region `r.3/0` has no plan; only the root, lambda bodies and arms do",
        ),
        (
            "a call the plan resolves to another region",
            call,
            |p| p["r"].nodes[2].callee = Some(0),
            "memory: r.2: the plan calls `r`, and the callee is `r.0/0`",
        ),
        (
            "a capture, passed borrowed, that the body's plan owns",
            capture,
            |p| p["r.1/0"].args[1] = Mode::Owned,
            "memory: argument 1 of `r.1/0` arrives borrowed, and the plan holds it owned",
        ),
        (
            "an arm argument, passed owned, that the arm's plan borrows",
            arm,
            |p| p["r.3/1"].args[0] = Mode::Borrowed,
            "memory: argument 0 of `r.3/1` arrives owned, and the plan holds it borrowed",
        ),
        (
            "the root's result dup'd, an edge left owned",
            reads_twice,
            |p| p["r"].result_dups.push(0),
            "memory: `r` ends still owning edge 3, a leak",
        ),
        (
            "a body's result dup'd, an edge left owned",
            call,
            |p| p["r.0/0"].result_dups.push(0),
            "memory: `r.0/0` ends still owning edge 1, a leak",
        ),
        (
            "an extra dup of the closure a call passes",
            call,
            |p| p["r"].nodes[2].dups.push(0),
            "memory: at the entry of `r.0/0`, cell 0 has count 2 and 1 reference",
        ),
        (
            "a closure taken owned by a call that borrows it, with its drop kept",
            call,
            |p| p["r"].nodes[2].modes[0] = Mode::Owned,
            "memory: at the entry of `r.0/0`, cell 0 has count 1 and 0 references",
        ),
        (
            "a dup at a last use",
            reads_twice,
            |p| p["r"].nodes[2].dups.push(0),
            "memory: at node r.2, cell 0 has count 1 and 0 references",
        ),
        (
            "a body that borrows the argument it owns, a leak",
            call,
            |p| p["r.0/0"].nodes[0].modes[0] = Mode::Borrowed,
            "memory: r.0/0.0: edge argument 0 is still owned after its last use, a leak",
        ),
        (
            "a body that consumes an argument its plan borrows",
            call,
            |p| p["r.0/0"].args[0] = Mode::Borrowed,
            "memory: r.0/0.0: input 0, taken owned consumes edge argument 0, which is borrowed \
             and has no dup",
        ),
        (
            "a borrowed capture returned with no dup",
            capture,
            |p| p["r.1/0"].result_dups.clear(),
            "memory: r.1/0: result 0 consumes edge argument 1, which is borrowed and has no dup",
        ),
        (
            "a drop of an edge a use consumed",
            reads_twice,
            |p| p["r"].nodes[2].modes[0] = Mode::Owned,
            "memory: r.2: a drop consumes edge 0.0, already consumed or past its last use",
        ),
        (
            "a read after an owned use consumed the edge",
            reads_twice,
            |p| p["r"].nodes[1].modes[0] = Mode::Owned,
            "memory: r.2: edge 0.0 is read after its last use",
        ),
    ];
    for (case, program, spoil, want) in cases {
        let (g, mut p) = planned(&program(), true);
        // The plan as made runs; only the change spoils it.
        if let Err(e) = run(&g, &p) {
            panic!("{case}: the plan as made: {e}");
        }
        spoil(&mut p);
        let Err(e) = run(&g, &p) else {
            panic!("{case}: the spoiled plan runs")
        };
        let want = if want.contains(" has count ") {
            format!("{want} {check}")
        } else {
            want.to_string()
        };
        assert_eq!(e, want, "{case}");
    }
}

#[test]
fn a_result_that_is_a_function_is_refused() {
    // A run gives data; a program whose result is a function is no program the checker
    // accepts, and the machine says so rather than count a closure out.
    let (g, p) = planned(&lam(&["x"], var("x")), true);
    let e = run(&g, &p).unwrap_err();
    assert!(e.contains("the program's result is a function"), "{e}");
}
