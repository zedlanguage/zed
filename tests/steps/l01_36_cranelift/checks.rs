//! A wrong plan is caught natively as the machine catches it at the end of the run: a missed
//! drop leaves a cell live, a missing dup frees a cell still in use, and a borrowed argument
//! given to a parameter that consumes it is the machine's error, word for word.

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

fn run(g: &zedc::zir::Region, p: &zedc::zir::memory::Plan) -> Result<String, String> {
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
    p.regions.get_mut("r").unwrap().nodes[2].drops.clear();
    assert_eq!(
        run(&g, &p).unwrap_err(),
        "memory: 1 cell live after the result is dropped"
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
    let r = p.regions.get_mut("r").unwrap();
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
    let (path, k) = p
        .regions
        .iter()
        .find_map(|(path, r)| {
            r.nodes
                .iter()
                .position(|n| n.callee.is_some())
                .map(|k| (path.clone(), k))
        })
        .expect("a resolved call");
    let n = &mut p.regions.get_mut(&path).unwrap().nodes[k];
    n.modes[1] = Mode::Borrowed;
    let callee = n.callee.clone().unwrap();
    p.regions.get_mut(&callee).unwrap().args[0] = Mode::Owned;
    let mut ev = Evaluator::new(World::new());
    let want = zedc::zir::memory::run(&g, &p, &mut ev).unwrap_err();
    assert_eq!(run(&g, &p).unwrap_err(), want);
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
    assert_eq!(run(&g, &p).unwrap(), "(\"abc\")");
    let body = p.regions.get_mut("r.1/0").unwrap();
    assert_eq!(body.result_dups, vec![0]);
    body.result_dups.clear();
    let e = run(&g, &p).unwrap_err();
    assert!(e.contains("freed"), "{e}");
}
