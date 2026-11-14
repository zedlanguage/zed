//! The formatter over every case of the grammar's alternatives (`grammar_cases.rs` of step
//! L1.8): each case is placed where its rule fits in a unit, and each unit that builds formats
//! to text that builds to the same statements, keeps its comments and formats to itself.
//!
//! The formatter writes built statements, so a case of a form that this zedc refuses as not
//! compiled yet is counted and left out; once the form compiles, its case is checked here with
//! no change to this file.

use std::panic::{AssertUnwindSafe, catch_unwind};

use zed_tests::is_not_yet;

use super::grammar_cases::CASES;
use super::{build, fmt};

/// The places a case's text is tried in, in order; `@` stands for the text. A unit, an
/// expression and its tails, a type, a pattern, a generator, statements of a function body, a
/// call's arguments, a function's parameters, body and trailers, a struct's fields, an
/// interface's members, a reduction's levels.
const PLACES: &[&str] = &[
    "@",
    "x = @;",
    "x = y @;",
    "x = (@);",
    "x = f(@);",
    "x = y with { @ };",
    "type T = @;",
    "f(x: @) = x;",
    "x = match y { @ -> 0, };",
    "x = match y { @, };",
    "x = for @ { 0 };",
    "f() { @ }",
    "f() { @ 0 }",
    "f() { x = @; x }",
    "f(@) = 0;",
    "f(x) @",
    "f(x) = x @",
    "f[i in xs] = 0 @;",
    "struct S { @ }",
    "interface I { @ }",
    "@ f(x) = x;",
    "import a @;",
    "x = y into (@);",
    "x = y as (@).z;",
    "f(n) = loop t { @ x' = x + t; until x > n; };",
    "f(n, t) = loop { @ a', b' = (b, a + 1); until a > n; };",
    "f(n) = loop t { initial x = 0 @; x' = x + t; until x > n; };",
    "type T@ = A;",
    "f(x) = x test @ { 1 -> 1 }",
    "x = for x in xs@ { 0 };",
    "type T = int @;",
    "type T = @ -> int;",
    "type T = string @;",
    "type T = int[@];",
    "type T = string matching @;",
    "struct J grammar { @ }",
];

/// The rules whose every case is a piece that no place holds: a lone token that only a
/// lookahead reads; the policy word of a reduction, which the cases of `ReduceTail` place; and
/// the documentation notation of `notation.peg`, which is no unit.
const PIECES: &[&str] = &["AnnotEnd", "KeyOp", "ReducePolicy", "DocFence", "DocItem"];

/// What became of a case.
enum Outcome {
    /// It built as this unit.
    Built(String),
    /// A place parsed it and this zedc refused the form as not compiled yet.
    NotYet,
    /// No place built it.
    Unplaced,
}

/// The first place where `text` builds as a unit, else the first not-yet refusal.
fn place(text: &str) -> Outcome {
    let mut not_yet = false;
    for p in PLACES {
        let unit = p.replace('@', text);
        match build(&unit) {
            Ok(_) => return Outcome::Built(unit),
            Err(e) if is_not_yet(&e) => not_yet = true,
            Err(_) => {}
        }
    }
    if not_yet {
        Outcome::NotYet
    } else {
        Outcome::Unplaced
    }
}

#[test]
fn every_case_that_builds_formats_to_a_fixed_point() {
    let (mut unplaced, mut wrong, mut built, mut refused) = (Vec::new(), Vec::new(), 0, 0);
    for &(label, start, _, text, _) in CASES {
        let unit = match place(text) {
            Outcome::Built(unit) => unit,
            Outcome::NotYet => {
                refused += 1;
                continue;
            }
            Outcome::Unplaced => {
                if !PIECES.contains(&start) {
                    unplaced.push(format!("{label} | {start} | {text}"));
                }
                continue;
            }
        };
        built += 1;
        if let Err(e) = catch_unwind(AssertUnwindSafe(|| fmt(&unit))) {
            let why = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            wrong.push(format!("{label} | {unit}\n  {why}"));
        }
    }
    println!(
        "{} cases: {built} built and formatted, {refused} refused as not compiled yet",
        CASES.len()
    );
    assert!(built > 0, "no case builds, so this test checked nothing");
    assert!(
        wrong.is_empty(),
        "{} of {built} do not format to a fixed point:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
    assert!(
        unplaced.is_empty(),
        "{} cases build in no place and are not refused as not compiled yet:\n{}",
        unplaced.len(),
        unplaced.join("\n")
    );
}
