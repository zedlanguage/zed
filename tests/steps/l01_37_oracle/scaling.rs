//! The oracle against the size of what it compares (the rule of low complexity, DESIGN.md
//! Part G): a unit of many bindings, a wave of many lines, and a report of many mismatches
//! each cost near linear in their number. Each input is built, and each unit elaborated,
//! before it is measured.

use std::collections::HashMap;
use std::sync::Arc;

use zed_kernel::{Evaluator, Term, Value};
use zed_tests::oracle::{Engine, Report, bindings, counterexamples, native, program};
use zed_tests::scaling::check;
use zedc::elab::Unit;
use zedc::front::Front;
use zedc::query::Db;
use zedc::run;

/// `x0 = 0; x1 = 1; …`: `n` first-order bindings, elaborated.
fn numbers(n: usize) -> Arc<Front> {
    let text: String = (0..n).map(|i| format!("x{i} = {i};\n")).collect();
    let front = Db::new().front(&text);
    assert!(front.is_ok(), "the unit of {n} bindings is accepted");
    front
}

/// The unit `front` holds.
fn unit_of(front: &Front) -> &Unit {
    let Ok((_, u, _)) = front else {
        unreachable!("`numbers` checks that its unit is accepted")
    };
    u
}

const ECHO: &str = "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- stdin[1] else \"\";\n}\n";

/// `n` lines of input.
fn lines(n: usize) -> Vec<u8> {
    (0..n)
        .flat_map(|i| format!("line {i}\n").into_bytes())
        .collect()
}

/// A report of `n` mismatches.
fn mismatched(n: usize) -> Report {
    Report {
        compared: n,
        mismatches: (0..n).map(|i| format!("m{i}")).collect(),
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

const OFF: &[Engine<'_>] = &[("off by one", &off_by_one)];

/// The inputs of `make` at `n` and `8n`, built before any is measured.
fn inputs<T>(n: usize, make: impl Fn(usize) -> T) -> HashMap<usize, T> {
    [n, 8 * n].into_iter().map(|k| (k, make(k))).collect()
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
    let ((r, want), _) = native(|engines| program(ECHO, &lines(2), engines));
    assert_eq!(r.mismatches, Vec::<String>::new());
    assert_eq!(want.as_deref(), Some(r#"port `stdout` writes "line 0\n""#));
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

#[test]
fn a_unit_of_many_bindings_scales() {
    let units = inputs(25, numbers);
    check("a unit of n bindings, run natively", 25, |k| {
        let (r, _) = native(|engines| bindings(unit_of(&units[&k]), engines));
        assert_eq!((r.compared, r.mismatches.len()), (2 * k, 0));
    });
}

#[test]
fn a_unit_of_many_bindings_scales_in_the_interpreter() {
    let units = inputs(500, numbers);
    check("a unit of n bindings, each mismatched", 500, |k| {
        let r = bindings(unit_of(&units[&k]), OFF);
        assert_eq!(r.mismatches.len(), k);
    });
}

#[test]
fn a_wave_of_many_lines_scales() {
    let input = inputs(2000, lines);
    check("a wave of n lines", 2000, |k| {
        let ((r, want), _) = native(|engines| program(ECHO, &input[&k], engines));
        assert_eq!(r.mismatches, Vec::<String>::new());
        assert_eq!(want.as_deref(), Some(r#"port `stdout` writes "line 0\n""#));
    });
}

#[test]
fn a_report_of_many_mismatches_scales() {
    // `Report::add` takes the report it adds, so each run builds its own, at linear cost.
    check("a report of n mismatches, built and added", 10000, |k| {
        let mut r = Report::default();
        r.add("at", mismatched(k));
        assert_eq!(r.mismatches.len(), k);
    });
}

/// `double(positional x) = x * 2` with a table of `n` rows, each wrong.
fn wrong_rows(n: usize) -> String {
    let rows: Vec<String> = (0..n).map(|i| format!("{i} -> {}", 2 * i + 1)).collect();
    format!(
        "double(positional x) = x * 2\ntest {{ {} }}\n",
        rows.join(", ")
    )
}

#[test]
fn many_wrong_rows_are_replayed() {
    // Each failure names its row's result, which the interpreter gives again; the replay of
    // each row finds its failure by a lookup, not a pass over the failures.
    let (r, replayed) = counterexamples(&wrong_rows(3), &[]);
    assert_eq!((replayed, r.compared), (3, 3));
    assert_eq!(r.mismatches, Vec::<String>::new());
    let texts = inputs(50, wrong_rows);
    check("a table of n wrong rows, each replayed", 50, |k| {
        let (r, replayed) = counterexamples(&texts[&k], &[]);
        assert_eq!((replayed, r.mismatches.len()), (k, 0));
    });
}

/// `x0 = 0; x1 = x0 + 1; …`: `n` first-order bindings, each reading the one before,
/// elaborated.
fn chain(n: usize) -> Arc<Front> {
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
fn a_chain_of_bindings_scales_in_the_interpreter() {
    let units = inputs(500, chain);
    check("a chain of n bindings, each mismatched", 500, |k| {
        let r = bindings(unit_of(&units[&k]), OFF);
        assert_eq!(r.mismatches.len(), k);
    });
}

#[test]
fn a_chain_of_bindings_scales_natively() {
    let units = inputs(25, chain);
    check("a chain of n bindings, run natively", 25, |k| {
        let (r, _) = native(|engines| bindings(unit_of(&units[&k]), engines));
        assert_eq!((r.compared, r.mismatches.len()), (2 * k, 0));
    });
}
