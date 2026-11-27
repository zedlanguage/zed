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

/// Red before PROOF-memo-off-test-flags, for each control but the first two and the solver's:
/// with a memo open, a question asked again after a test control is set was answered from the
/// memo, so a test that compares the paths a control selects compared an answer with itself.
/// Each control here is set after the question was asked once, and the question asked again
/// must reach the solver, then be answered from the memo once the control is cleared.
#[test]
fn a_test_control_set_after_a_question_asks_it_again() {
    use zedc::store::presburger::exact::{
        CLASS_ROOM_OFF, DIRECT_OFF, EXACT_LIMIT_SET, EXACT_OFF, GUARDED_OFF, METHOD, Method,
        PART_CACHE_OFF, SHARED_OFF, SPARE_OFF, TWO_DISTRIBUTED_OFF, TWO_PIN_LINE_OFF,
    };
    use zedc::store::presburger::extend::counts::HOLE_ROUTE_OFF;
    use zedc::store::presburger::{JOIN_LIMIT_SET, ROW_SUMS_JOIN, ROW_SUMS_OFF};
    type Flag = std::thread::LocalKey<std::cell::Cell<bool>>;
    let flags: [(&str, &'static Flag); 11] = [
        ("EXACT_OFF", &EXACT_OFF),
        ("DIRECT_OFF", &DIRECT_OFF),
        ("GUARDED_OFF", &GUARDED_OFF),
        ("SHARED_OFF", &SHARED_OFF),
        ("PART_CACHE_OFF", &PART_CACHE_OFF),
        ("TWO_DISTRIBUTED_OFF", &TWO_DISTRIBUTED_OFF),
        ("TWO_PIN_LINE_OFF", &TWO_PIN_LINE_OFF),
        ("CLASS_ROOM_OFF", &CLASS_ROOM_OFF),
        ("SPARE_OFF", &SPARE_OFF),
        ("ROW_SUMS_OFF", &ROW_SUMS_OFF),
        ("ROW_SUMS_JOIN", &ROW_SUMS_JOIN),
    ];
    let set = |name: &str, on: bool| match name {
        "EXACT_LIMIT_SET" => EXACT_LIMIT_SET.set(on.then_some(u64::MAX)),
        "JOIN_LIMIT_SET" => JOIN_LIMIT_SET.set(on.then_some(u64::MAX)),
        "METHOD" => METHOD.set(on.then_some(Method::Pugh)),
        "HOLE_ROUTE_OFF" => HOLE_ROUTE_OFF.set(on),
        _ => flags.iter().find(|(n, _)| *n == name).unwrap().1.set(on),
    };
    let names = flags.iter().map(|(n, _)| *n).chain([
        "EXACT_LIMIT_SET",
        "JOIN_LIMIT_SET",
        "METHOD",
        "HOLE_ROUTE_OFF",
    ]);
    let syms = [Atom::Sym("x".into()), Atom::Sym("y".into())];
    let question = group("x", "y", "z");
    let alone = sets(&question, &syms);
    let store = ProjectionStore::default();
    let _memo = ProjectionMemo::open_in(&store);
    assert_eq!(sets(&question, &syms), alone);
    for name in names {
        set(name, true);
        systems_solved();
        let got = sets(&question, &syms);
        let solved = systems_solved();
        set(name, false);
        assert!(
            solved > 0,
            "with {name} set, the question is asked again, not answered from the memo"
        );
        assert_eq!(got, alone, "{name}");
        sets(&question, &syms);
        assert_eq!(
            systems_solved(),
            0,
            "{name} cleared: answered from the memo"
        );
    }
}
