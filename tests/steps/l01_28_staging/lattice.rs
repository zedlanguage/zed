//! Row STAGE-subs-lattice-fix-names: a lattice `fix` binds no name. Its `this` and `key` name
//! the partial family of a definedness `fix` only (kernel `term::walk::kids`, the evaluator's
//! `attempt`); the init, step and join of a lattice `fix` are evaluated under the names around
//! it. So a step or join that reads `this` or `key` reads the binding outside, and staging must
//! count that read: else it takes the name as unread and drops the `let` that binds it.

use zed_kernel::term::build::{app, lam, let_, lit, var};
use zed_kernel::{Evidence, FixKind, Prim, Shared, Term, Value};
use zedc::stage::{self, free};

use super::cone::{def, unit};

/// A lattice `fix` from 0 whose step is `step` and whose join is `join`, with `this` and `key`
/// the names `this` and `k`.
fn lattice(step: Term, join: Term) -> Term {
    Term::Fix {
        init: Shared::new(lit(0i64)),
        step: Shared::new(step),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Lattice {
            join: Shared::new(join),
        },
        ev: Evidence::new(),
    }
}

/// `(a, b) -> max(a, b, name)`: a join that reads `name`.
fn join_reading(name: &str) -> Term {
    lam(
        &["a", "b"],
        Term::Prim(
            Prim::Max,
            vec![Term::Prim(Prim::Max, vec![var("a"), var("b")]), var(name)],
        ),
    )
}

#[test]
fn the_step_and_join_of_a_lattice_fix_read_the_names_this_and_key_outside_it() {
    let step = lam(&["x"], var("this"));
    let t = lattice(step.clone(), join_reading("k"));
    let names: Vec<String> = free(&t).iter().map(|x| x.to_string()).collect();
    assert_eq!(names, ["k", "this"], "free names of a lattice fix");
    // A definedness `fix` with the same names binds both over its step.
    let defined = Term::Fix {
        init: Shared::new(lit(0i64)),
        step: Shared::new(step),
        this: "this".into(),
        key: "k".into(),
        kind: FixKind::Definedness,
        ev: Evidence::new(),
    };
    assert!(free(&defined).is_empty(), "{:?}", free(&defined));
}

#[test]
fn staging_keeps_the_let_a_lattice_fix_reads_through_this_or_key() {
    // `main = (c) -> let this = 5; let k = 6; c + fix(0, x -> this, join reading k)`, run
    // stage since it reads its parameter. A `let` of a literal whose body does not read its
    // name is dropped, so the two `let`s stay only if the reads through the fix are counted.
    // Its value at 1 is 1 + max(0, 5, 6) = 7.
    let body = let_(
        "this",
        lit(5i64),
        let_(
            "k",
            lit(6i64),
            Term::Prim(
                Prim::Add,
                vec![
                    var("c"),
                    lattice(lam(&["x"], var("this")), join_reading("k")),
                ],
            ),
        ),
    );
    let u = unit(vec![def("main", lam(&["c"], body))]);
    let (mixed, _) = stage::mix(&u, &["main"]);
    let main = &mixed.defs.iter().find(|d| d.name == "main").unwrap().term;
    let got = zed_kernel::eval::eval(&app(Term::clone(main), vec![lit(1i64)]));
    assert_eq!(got, Ok(Value::Int(7)), "mixed main: {main:?}");
}
