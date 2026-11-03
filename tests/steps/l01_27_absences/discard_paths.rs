//! `_` drops a loose failure only where an `else` on its own path names it (DESIGN.md
//! sec:tour_methods). Each branch of an `if`, each block's export and each argument is
//! checked on its own: a default in one branch names nothing in another, even when it writes
//! the same atom.

use zedc::lex::Span;
use zedc::rejection::Row;

use crate::l01_26_type_resolution::{info, type_errors};

/// A lookup that misses: a number, or the loose failure `#notFound`.
const LOOKUP: &str = "lookup(positional k: int) = if k > 0 { k } else { #notFound };\n";

/// `body` as the body of `f(positional c: int)`, after `lookup`.
fn in_f(body: &str) -> String {
    format!("{LOOKUP}f(positional c: int) = {{\n  {body}\n  0\n}};\n")
}

/// The text at `s` of `text`.
fn at(text: &str, s: Span) -> &str {
    &text[s.start..s.end]
}

/// The one error of `text`, a case of the row "Statement that writes nothing, or drops a
/// declared result": its message, its span's text, and each note as `text [span]`.
fn the_error(text: &str) -> (String, String, Vec<String>) {
    let (info, _) = info(text);
    assert_eq!(info.errors.len(), 1, "{text}: {:?}", info.errors);
    let e = &info.errors[0];
    assert_eq!(e.row, Some(Row::WritesNothing), "{text}: {e:?}");
    let notes = e
        .notes
        .iter()
        .map(|n| format!("{} [{}]", n.text, at(text, n.span)))
        .collect();
    (e.message.clone(), at(text, e.span).to_string(), notes)
}

fn accepted(text: &str) {
    assert!(
        type_errors(text).is_empty(),
        "{text}: {:?}",
        type_errors(text)
    );
}

#[test]
fn a_default_in_one_branch_names_nothing_in_the_other() {
    // The first branch names its own miss; the second branch's miss is the same atom, but
    // nothing on its path names it.
    let t = in_f("_ = if c > 0 { lookup(1) else #notFound } else { lookup(2) };");
    let (message, span, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound"
    );
    assert_eq!(
        span,
        "_ = if c > 0 { lookup(1) else #notFound } else { lookup(2) };"
    );
    // Where it enters: the second branch's call, and not the first branch's default.
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(2)]"
    );
    assert!(
        !notes
            .iter()
            .any(|n| n.starts_with("the loose failure") && n.ends_with("[#notFound]"))
    );
    // The derivation follows: the `if`, its branches, and the call's declaration.
    assert!(
        notes.contains(
            &"this `if` gives int | #notFound \
              [if c > 0 { lookup(1) else #notFound } else { lookup(2) }]"
                .to_string()
        ),
        "{notes:#?}"
    );
    assert!(
        notes.contains(&"this call of `lookup` gives int | #notFound [lookup(2)]".to_string()),
        "{notes:#?}"
    );
    assert!(
        notes
            .iter()
            .any(|n| n.starts_with("`lookup` is declared here")),
        "{notes:#?}"
    );
}

#[test]
fn a_default_in_each_branch_names_every_failure() {
    accepted(&in_f(
        "_ = if c > 0 { lookup(1) else #notFound } else { lookup(2) else #notFound };",
    ));
    // Each branch names its own atom.
    accepted(&in_f(
        "_ = if c > 0 { lookup(1) else #missing } else { lookup(2) else #absent };",
    ));
    // An `else if` chain, each arm defaulted.
    accepted(&in_f(
        "_ = if c > 1 { lookup(1) else #ok } else if c > 0 { lookup(2) else #ok } \
         else { lookup(3) else #ok };",
    ));
}

#[test]
fn a_default_on_an_inner_if_covers_both_its_branches() {
    // The default on the inner `if` is on the path of both inner branches.
    accepted(&in_f(
        "_ = if c > 0 { (if c > 1 { lookup(1) } else { lookup(2) }) else #notFound } else { 0 };",
    ));
    // It does not reach the outer `if`'s other branch.
    let t = in_f(
        "_ = if c > 0 { (if c > 1 { lookup(1) } else { lookup(2) }) else #notFound } \
         else { lookup(3) };",
    );
    let (_, _, notes) = the_error(&t);
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(3)]"
    );
    // A default on one inner branch covers that branch only.
    let t = in_f(
        "_ = if c > 0 { if c > 1 { lookup(1) else #notFound } else { lookup(2) } } else { 0 };",
    );
    let (message, _, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound"
    );
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(2)]"
    );
    // A default on the whole value covers everything under it.
    accepted(&in_f(
        "_ = (if c > 0 { if c > 1 { lookup(1) } else { lookup(2) } } else { lookup(3) }) \
         else #notFound;",
    ));
}

#[test]
fn a_block_export_and_a_name_keep_what_their_default_names() {
    // The block exports a value whose default names its miss.
    accepted(&format!(
        "{LOOKUP}_ = {{\n  y = lookup(1);\n  y else #notFound\n}};\n"
    ));
    // A name bound to a defaulted value carries the naming with it.
    accepted(&format!("{LOOKUP}y = lookup(1) else #notFound;\n_ = y;\n"));
    // A name bound to the bare call does not.
    let t = format!("{LOOKUP}y = lookup(1);\nz = y;\n_ = z;\n");
    let (_, span, notes) = the_error(&t);
    assert_eq!(span, "_ = z;");
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(1)]"
    );
    // A block whose export is a bare call drops its miss.
    let t = format!("{LOOKUP}_ = {{\n  y = lookup(1) else #notFound;\n  lookup(y)\n}};\n");
    let (_, _, notes) = the_error(&t);
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(y)]"
    );
}

#[test]
fn an_argument_with_a_default_carries_no_loose_failure_into_the_call() {
    // `id` passes its argument on and cannot fail itself.
    let id = "id(positional x) = x;\n";
    accepted(&format!("{LOOKUP}{id}_ = id(lookup(1) else #ok);\n"));
    // `positive` can fail itself: its own failure reaches `_` unnamed.
    let positive = "positive(positional x: int) = if x > 0 { x } else { #negative };\n";
    let t = format!("{LOOKUP}{positive}_ = positive(lookup(1) else 0);\n");
    let (message, _, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #negative"
    );
    assert_eq!(
        notes[0],
        "the loose failure #negative enters here [positive(lookup(1) else 0)]"
    );
    // The same when the argument's default writes the very atom the function fails with:
    // the default names the argument's failure, not the function's own.
    let check = "check(positional x: int) = if x > 0 { x } else { #notFound };\n";
    let t = format!("{LOOKUP}{check}_ = check(lookup(1) else #notFound);\n");
    let (message, _, notes) = the_error(&t);
    assert_eq!(
        message,
        "`_` drops a loose failure this value may be, #notFound"
    );
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [check(lookup(1) else #notFound)]"
    );
}

#[test]
#[ignore = "`match` arrives at step L2.4; until then resolve refuses it before the checker"]
fn a_match_arm_that_leaves_a_loose_failure_is_rejected() {
    // L2.4: each arm is checked on its own, as each branch of an `if` is.
    let t = in_f("_ = match lookup(c) { #notFound -> #ok, n -> lookup(n) };");
    let (_, _, notes) = the_error(&t);
    assert_eq!(
        notes[0],
        "the loose failure #notFound enters here [lookup(n)]"
    );
}
