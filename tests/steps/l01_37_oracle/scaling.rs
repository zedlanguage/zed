//! The oracle against the size of what it compares (the rule of low complexity, DESIGN.md
//! Part G): a unit of many bindings, a wave of many lines, and a report of many mismatches
//! each cost near linear in their number (`bench.rs`). The inputs and the checks of those
//! benchmarks, each run here at a small size.

use std::sync::Arc;

use zed_kernel::{Evaluator, Term, Value};
use zed_tests::oracle::{Engine, Report, bindings, counterexamples, native, program};
use zedc::elab::Unit;
use zedc::front::Front;
use zedc::query::Db;
use zedc::run;

/// `x0 = 0; x1 = 1; …`: `n` first-order bindings, elaborated.
pub(super) fn numbers(n: usize) -> Arc<Front> {
    let text: String = (0..n).map(|i| format!("x{i} = {i};\n")).collect();
    let front = Db::new().front(&text);
    assert!(front.is_ok(), "the unit of {n} bindings is accepted");
    front
}

/// The unit `front` holds.
pub(super) fn unit_of(front: &Front) -> &Unit {
    let Ok((_, u, _)) = front else {
        unreachable!("`numbers` and `chain` check that their unit is accepted")
    };
    u
}

pub(super) const ECHO: &str = "main(m: MainArgs) {\n  m.stdout <- m.stdin[0] else \"\";\n}\n";

/// `n` lines of input.
pub(super) fn lines(n: usize) -> Vec<u8> {
    (0..n)
        .flat_map(|i| format!("line {i}\n").into_bytes())
        .collect()
}

/// A report of `n` mismatches.
pub(super) fn mismatched(n: usize) -> Report {
    Report {
        compared: n,
        mismatches: (0..n).map(|i| format!("m{i}")).collect(),
        ..Report::default()
    }
}

/// The interpreter with every integer one more, in a tuple too, since the oracle runs a unit's
/// bindings as one tuple.
fn off_by_one(t: &Term, ev: &mut Evaluator) -> Result<Value, String> {
    fn bump(v: Value) -> Value {
        match v {
            Value::Int(i) => Value::Int(i + 1),
            Value::Tuple(items) => Value::tuple(items.iter().cloned().map(bump).collect()),
            v => v,
        }
    }
    run::direct(t, ev).map(bump)
}

pub(super) const OFF: &[Engine<'_>] = &[("off by one", &off_by_one)];

/// Compares the `n` bindings of `front` natively: each is compared under both engines, and
/// none differs.
pub(super) fn agree_natively(front: &Front, n: usize) {
    let (r, _) = native(|engines| bindings(unit_of(front), engines));
    assert_eq!((r.compared, r.mismatches.len()), (2 * n, 0));
}

/// Compares the `n` bindings of `front` with [`OFF`]: each differs.
pub(super) fn each_off_by_one(front: &Front, n: usize) {
    let r = bindings(unit_of(front), OFF);
    assert_eq!(r.mismatches.len(), n);
}

/// Runs [`ECHO`] on `input` natively: the engines agree, and it writes the first line.
pub(super) fn echoes_the_first_line(input: &[u8]) {
    let ((r, want), _) = native(|engines| program(ECHO, input, engines));
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(
        want.as_deref(),
        Some(r#"port `m.stdout` writes "line 0\n""#)
    );
}

/// Builds a report of `n` mismatches and adds it to another.
pub(super) fn adds_a_report(n: usize) {
    let mut r = Report::default();
    r.add("at", mismatched(n));
    assert_eq!(r.mismatches.len(), n);
}

#[test]
fn the_inputs_are_compared_as_they_should_be() {
    let three = numbers(3);
    // The three bindings run together, once under each engine.
    let (r, runs) = native(|engines| bindings(unit_of(&three), engines));
    assert_eq!((r.compared, runs), (6, 2));
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(
        bindings(unit_of(&three), OFF).mismatches,
        [
            "binding `x0`: the interpreter gives the value 0, and off by one gives the value 1",
            "binding `x1`: the interpreter gives the value 1, and off by one gives the value 2",
            "binding `x2`: the interpreter gives the value 2, and off by one gives the value 3",
        ]
    );
    echoes_the_first_line(&lines(2));
    let mut at = Report::default();
    at.add("at", mismatched(2));
    assert_eq!(
        (at.compared, at.mismatches),
        (2, vec!["at: m0".into(), "at: m1".into()])
    );
}

#[test]
fn a_unit_of_one_binding_or_none_is_compared() {
    // A binding reached by another gives what its run alone gives.
    let one = Db::new().front("x = 1;\ny = x + 1;\n");
    let Ok((_, u, _)) = &*one else {
        panic!("a unit of two bindings is accepted")
    };
    assert_eq!(
        bindings(u, OFF).mismatches,
        [
            "binding `x`: the interpreter gives the value 1, and off by one gives the value 2",
            "binding `y`: the interpreter gives the value 2, and off by one gives the value 3",
        ]
    );
    let r = bindings(unit_of(&numbers(1)), OFF);
    assert_eq!((r.compared, r.mismatches.len()), (1, 1));
    let r = bindings(unit_of(&numbers(0)), OFF);
    assert_eq!((r.compared, r.mismatches), (0, Vec::<String>::new()));
    // A unit of functions only has no binding to compare.
    let f = Db::new().front("f(positional x) = x + 1\ntest { 1 -> 2 }\n");
    let Ok((_, u, _)) = &*f else {
        panic!("a unit of one function is accepted")
    };
    assert_eq!(bindings(u, OFF).compared, 0);
}

/// `double(positional x) = x * 2` with a table of `n` rows, each wrong.
pub(super) fn wrong_rows(n: usize) -> String {
    let rows: Vec<String> = (0..n).map(|i| format!("{i} -> {}", 2 * i + 1)).collect();
    format!(
        "double(positional x) = x * 2\ntest {{ {} }}\n",
        rows.join(", ")
    )
}

/// Replays the `n` failing rows of `text`: each failure names its row's result, which the
/// interpreter gives again, so none differs.
pub(super) fn replays_each_row(text: &str, n: usize) {
    let (r, replayed) = counterexamples(text, &[]);
    assert_eq!((replayed, r.compared, r.mismatches.len()), (n, n, 0));
}

#[test]
fn wrong_rows_are_replayed() {
    let (r, replayed) = counterexamples(&wrong_rows(3), &[]);
    assert_eq!((replayed, r.compared), (3, 3));
    assert_eq!(r.mismatches, Vec::<String>::new());
    replays_each_row(&wrong_rows(3), 3);
}

/// `x0 = 0; x1 = x0 + 1; …`: `n` first-order bindings, each reading the one before,
/// elaborated.
pub(super) fn chain(n: usize) -> Arc<Front> {
    let text: String = (0..n)
        .map(|i| match i {
            0 => "x0 = 0;\n".to_string(),
            _ => format!("x{i} = x{} + 1;\n", i - 1),
        })
        .collect();
    let front = Db::new().front(&text);
    assert!(front.is_ok(), "the chain of {n} bindings is accepted");
    front
}

#[test]
fn a_chain_of_bindings_is_compared() {
    // Each binding of the chain reads the one before; each runs with the others.
    let three = chain(3);
    assert_eq!(
        bindings(unit_of(&three), OFF).mismatches,
        [
            "binding `x0`: the interpreter gives the value 0, and off by one gives the value 1",
            "binding `x1`: the interpreter gives the value 1, and off by one gives the value 2",
            "binding `x2`: the interpreter gives the value 2, and off by one gives the value 3",
        ]
    );
}
