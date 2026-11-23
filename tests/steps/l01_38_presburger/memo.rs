//! The memo of projections ([`ProjectionMemo`]): a question asked again while a memo is open,
//! or asked of a formula that differs from one asked before only in its names, is answered
//! from the memo, and with the answer the solver gives it.

use zedc::store::presburger::{
    Atom, Con, Formula, Lin, ProjectionMemo, ProjectionStore, Shared, project_each, systems_solved,
};

fn sym(n: &str) -> Lin {
    Lin::atom(Atom::Sym(n.into()))
}

fn ge(l: Lin, c: i64) -> Formula {
    Formula::Con(Con::ge(&l, &Lin::constant(c)))
}

/// `(x <= 0 || (x >= 10 && y == 5)) && 0 <= y - 3 z <= 30`, in the names `x`, `y`, `z`.
fn group(x: &str, y: &str, z: &str) -> Formula {
    let eq = Formula::Con(Con::eq(&sym(y), &Lin::constant(5)));
    let right = Formula::And(Shared::new(vec![ge(sym(x), 10), eq]));
    let left = ge(sym(x).times(-1), 0);
    let lin = sym(y).plus(&sym(z).times(-3));
    Formula::And(Shared::new(vec![
        Formula::Or(Shared::new(vec![left, right])),
        ge(lin.clone(), 0),
        ge(lin.times(-1), -30),
    ]))
}

fn sets(f: &Formula, syms: &[Atom]) -> String {
    format!("{:?}", project_each(f, syms).map(|e| e.0))
}

/// Red before the memo kept answers by the renamed question (b22-preimage9,
/// FAIL-points-asked-after-disjunction-timeout): the question in `u`, `v`, `w` asked the solver
/// again, since the memo kept answers only by the formula as written.
#[test]
fn a_question_under_other_names_is_answered_from_the_memo() {
    let at = |ns: [&str; 2]| ns.map(|n| Atom::Sym(n.into())).to_vec();
    let (first, second) = (group("x", "y", "z"), group("u", "v", "w"));
    // Each answer with no memo open.
    let alone = (
        sets(&first, &at(["x", "y"])),
        sets(&second, &at(["u", "v"])),
    );
    let store = ProjectionStore::default();
    let _memo = ProjectionMemo::open_in(&store);
    systems_solved();
    let got = sets(&first, &at(["x", "y"]));
    assert!(systems_solved() > 0, "the first question asks the solver");
    assert_eq!(got, alone.0);
    let got = sets(&second, &at(["u", "v"]));
    assert_eq!(
        systems_solved(),
        0,
        "the renamed question is answered from the memo"
    );
    assert_eq!(got, alone.1);
}
