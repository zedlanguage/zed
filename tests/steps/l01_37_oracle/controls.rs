//! Negative controls: an engine that changes a value, drops a wave's writes or fails is
//! caught, and the mismatch names the binding or wave and both outcomes.

use zed_kernel::{Evaluator, Term, Value};
use zed_tests::oracle::{Engine, program, unit};

const LAMBDAS: &str =
    "inc = x -> x + 1;\ntwice(positional f) = x -> f(f(x));\nfive = twice(inc)(3);\n";

const GREETING: &str =
    "main(stdin: Lines) -> (stdout: Lines) {\n  stdout <- \"Hello, \" ++ stdin[1] ++ \"!\";\n}\n";

fn off_by_one(t: &Term, ev: &mut Evaluator) -> Result<Value, String> {
    match zed_native::through(true)(t, ev)? {
        Value::Int(n) => Ok(Value::Int(n + 1)),
        v => Ok(v),
    }
}

fn silent(_: &Term, _: &mut Evaluator) -> Result<Value, String> {
    Ok(Value::Tuple(Vec::new()))
}

fn failing(_: &Term, _: &mut Evaluator) -> Result<Value, String> {
    Err("out of memory".into())
}

#[test]
fn a_changed_integer_is_caught_with_both_values() {
    let engines: &[Engine<'_>] = &[("off by one", &off_by_one)];
    let r = unit(LAMBDAS, engines);
    assert_eq!(
        r.mismatches,
        ["binding `five`: the interpreter gives the value 5, and off by one gives the value 6"]
    );
    let same = zed_native::through(true);
    assert_eq!(unit(LAMBDAS, &[("native", &same)]).mismatches.len(), 0);
}

#[test]
fn dropped_writes_are_caught_in_the_wave() {
    let engines: &[Engine<'_>] = &[("silent", &silent)];
    let (r, want) = program(GREETING, b"Ada\n", engines);
    assert_eq!(
        want.as_deref(),
        Some("port `stdout` writes \"Hello, Ada!\\n\"")
    );
    assert_eq!(
        r.mismatches,
        [
            "the wave: the interpreter gives port `stdout` writes \"Hello, Ada!\\n\", and silent \
          gives no writes"
        ]
    );
}

#[test]
fn a_failing_engine_is_caught_everywhere() {
    let engines: &[Engine<'_>] = &[("failing", &failing)];
    let r = unit(LAMBDAS, engines);
    assert_eq!((r.compared, r.mismatches.len()), (2, 1));
    let (r, _) = program(GREETING, b"Ada\n", engines);
    assert_eq!(
        r.mismatches,
        [
            "the wave: the interpreter gives port `stdout` writes \"Hello, Ada!\\n\", and failing \
          gives the error `out of memory`"
        ]
    );
}
