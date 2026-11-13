//! The points and the witnesses: a difference at a point refutes at `int` and `rat`, the
//! witness of small integers found one binder at a time among `deg + 1` values.

use zed_kernel::poly::{Carrier, Verdict};

use super::law;

fn refuted(params: &str, lhs: &str, rhs: &str, carrier: Carrier) -> String {
    match law(params, lhs, rhs, carrier).verdict {
        Verdict::Refuted(p) => p.to_string(),
        v => panic!("{lhs} == {rhs}: {v:?}"),
    }
}

#[test]
fn small_values_first() {
    assert_eq!(refuted("x: int", "x + 1", "x", Carrier::Int), "x = 0");
    assert_eq!(refuted("x: int", "x * x", "x", Carrier::Int), "x = -1");
    // Zero at 0, 1, -1 and 2: the fifth value.
    assert_eq!(
        refuted(
            "x: int",
            "x * (x - 1) * (x + 1) * (x - 2)",
            "0",
            Carrier::Int
        ),
        "x = -2"
    );
    // The second binder is chosen with the first at its value.
    assert_eq!(
        refuted("x: int, y: int", "x * y", "0", Carrier::Int),
        "x = 1, y = 1"
    );
}

#[test]
fn at_rat() {
    assert_eq!(
        refuted("r: rat", "r / 2 + r / 3", "r", Carrier::Rat),
        "r = 1"
    );
    let d = law("r: rat", "r / 2 + r / 3", "r * 5r / 6r", Carrier::Rat);
    assert_eq!(d.verdict, Verdict::Proved);
}

#[test]
fn a_call_is_an_atom_and_never_refutes() {
    let d = law("x: int", "abs(x) * abs(x)", "abs(x) ^ 2", Carrier::Int);
    assert_eq!(d.verdict, Verdict::Proved);
    let d = law("x: int", "abs(x)", "x", Carrier::Int);
    assert_eq!(d.verdict, Verdict::Differs);
}

#[test]
fn a_let_is_shared() {
    // `s` is read once and used twice.
    let d = law(
        "x: int, y: int",
        "{ s = x + y; s * s }",
        "x * x + 2 * x * y + y * y",
        Carrier::Int,
    );
    assert_eq!(d.verdict, Verdict::Proved);
}
