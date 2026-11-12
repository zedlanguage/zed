//! Step L6.1: the parser of the forms of layer L6: `loop` with primes, `with` boundaries,
//! `initial x = e with carryForward;`, the guards `while` and `until` and `break`; indexed
//! definitions, generation pushes `x' <- e`, expression statements `e;` and the call `*.`. Each
//! form builds and formats; name resolution refuses it, naming the step that compiles it.

mod carry_forward;
mod corners;
mod formatting;
mod forms;
mod initial;
mod later;
mod scaling;
mod test_case;

use zedc::ast::{Stmt, unit};
use zedc::format::format;
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};
use zedc::resolve::resolve;

/// The statements of the unit `text`, one s-expression per line, or its error: `error: …`
/// with each note `; note at byte …`, or `syntax` when it does not parse.
fn sx(text: &str) -> String {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(_) => "syntax".into(),
        Ok(tree) => match unit(text, &tokens, &tree) {
            Err(e) => {
                let mut out = format!("error: {e}");
                for n in &e.notes {
                    out += &format!("; {} at byte {}", n.text, n.span.start);
                }
                out
            }
            Ok(stmts) => stmts
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        },
    }
}

#[track_caller]
fn check(cases: &[(&str, &str)]) {
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|&(text, want)| {
            let got = sx(text);
            (got != want).then(|| format!("{text}\n  got  {got}\n  want {want}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The statements of the unit `text` and its tokens.
fn build(text: &str) -> (Vec<Token>, Vec<Stmt>) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    let stmts = unit(text, &tokens, &tree).unwrap_or_else(|e| panic!("{e} in\n{text}"));
    (tokens, stmts)
}

/// `text` formatted, after checking that the result builds to the same statements and formats
/// to itself.
#[track_caller]
fn fmt(text: &str) -> String {
    let (tokens, stmts) = build(text);
    let out = format(text, &tokens, &stmts);
    let (tokens2, stmts2) = build(&out);
    let show = |ss: &[Stmt]| ss.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    assert_eq!(
        show(&stmts),
        show(&stmts2),
        "the statements changed in\n{out}"
    );
    assert_eq!(format(&out, &tokens2, &stmts2), out, "not a fixed point");
    out
}

/// The errors name resolution gives the unit `text`, each as `message [text]`.
fn refused(text: &str) -> Vec<String> {
    let (_, stmts) = build(text);
    match resolve(&stmts) {
        Ok(_) => Vec::new(),
        Err(es) => es
            .iter()
            .map(|e| format!("{} [{}]", e.message, &text[e.span.start..e.span.end]))
            .collect(),
    }
}
