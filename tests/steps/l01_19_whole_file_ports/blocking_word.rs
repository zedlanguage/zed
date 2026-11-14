//! There is no `@blocking` (DESIGN.md sec:ports, "A port operation can block unless it is
//! marked `@nonblocking`"; sec:diagnostics, "`@blocking` written"): an operation or function
//! with no mark can block, so the word would say nothing. Writing it is rejected at the word,
//! with the declaration's line rewritten without it as the repair; a function with no mark is
//! accepted, and blocks when its body reaches an operation that can.

use zed_tests::deep::statements;
use zedc::rejection::Row;
use zedc::resolve::{ANNOTATIONS, resolve_text};

use super::run;

/// The resolver's errors for `text`, which it refuses: each as its row, its place `line:col`,
/// its headline, and its notes, one per line.
fn refused(text: &str) -> Vec<(Option<Row>, String, String)> {
    let stmts = statements(text);
    let errs = resolve_text(&stmts, Some(text)).expect_err(text);
    (errs.into_iter())
        .map(|e| {
            let line = text[..e.span.start].matches('\n').count() + 1;
            let col = e.span.start - text[..e.span.start].rfind('\n').map_or(0, |i| i + 1) + 1;
            let mut s = e.message;
            for n in &e.notes {
                s.push_str(&format!("\n  {}", n.text));
            }
            (e.row, format!("{line}:{col}"), s)
        })
        .collect()
}

const WHY: &str = "a foreign function or port operation can block unless it is marked \
                   `@nonblocking`, and a function written in Zed blocks when its body reaches \
                   one, so nothing is written on one that can block";

/// The error the word gets at `at`, the declaration's line as written being `line` and its
/// repair `repaired`.
fn written(at: &str, line: &str, repaired: &str) -> (Option<Row>, String, String) {
    (
        Some(Row::BlockingWritten),
        at.into(),
        format!(
            "Zed has no `@blocking`: `{line}`. Write `{repaired}` instead.\n  {WHY}\n  \
             repair: `{repaired}`"
        ),
    )
}

const FEE: &str = "fee(positional base: int, rate: int) = base * rate;";
const MAIN: &str = "\nmain(m: MainArgs) -> int { 0 }\n";

/// The word on the line above the function, and on the function's own line: the repair is
/// the function's line without it.
#[test]
fn the_word_is_rejected_with_the_line_without_it() {
    assert_eq!(
        refused(&format!("@blocking\n{FEE}{MAIN}")),
        [written("1:1", &format!("@blocking {FEE}"), FEE)]
    );
    assert_eq!(
        refused(&format!("{MAIN}@blocking {FEE}\n")),
        [written("3:1", &format!("@blocking {FEE}"), FEE)]
    );
}

/// The word with arguments is deleted with them; another annotation of the declaration
/// stays, on the line the repair writes.
#[test]
fn the_repair_deletes_the_arguments_and_keeps_the_other_annotations() {
    assert_eq!(
        refused(&format!("@blocking(#io) {FEE}{MAIN}")),
        [written("1:1", &format!("@blocking(#io) {FEE}"), FEE)]
    );
    let scale = "scale(positional x: int) = x * 2;";
    assert_eq!(
        refused(&format!("@blocking\n@nonblocking\n{scale}{MAIN}")),
        [written(
            "1:1",
            &format!("@blocking @nonblocking {scale}"),
            &format!("@nonblocking {scale}")
        )]
    );
    assert_eq!(
        refused(&format!("@nonblocking @blocking {scale}{MAIN}")),
        [written(
            "1:14",
            &format!("@nonblocking @blocking {scale}"),
            &format!("@nonblocking {scale}")
        )]
    );
}

/// Before a declaration that is no function, and as a unit item, the word is rejected by the
/// same row: before a binding the repair is the binding; as a unit item, the line deleted.
#[test]
fn the_word_is_rejected_wherever_it_stands() {
    assert_eq!(
        refused("@blocking x = 3;\nmain(m: MainArgs) -> int { x }\n"),
        [written("1:1", "@blocking x = 3;", "x = 3;")]
    );
    assert_eq!(
        refused(&format!("@blocking;{MAIN}")),
        [(
            Some(Row::BlockingWritten),
            "1:1".into(),
            format!(
                "Zed has no `@blocking`: `@blocking;`. Delete the line.\n  {WHY}\n  repair: delete `@blocking;`"
            )
        )]
    );
}

/// The word is no annotation of any layer, so no listing of later words names it.
#[test]
fn the_word_is_no_annotation() {
    assert!(ANNOTATIONS.iter().all(|&(name, _)| name != "blocking"));
    assert!(ANNOTATIONS.contains(&("nonblocking", 2)));
}

/// A run of a file that writes the word prints the error at the word and runs nothing; the
/// same file without it runs.
#[test]
fn a_run_stops_at_the_word() {
    let main = "main(m: MainArgs) -> int {\n  if fee(2, rate: 3) == 6 { 5 } else { 0 }\n}\n";
    let out = run(
        "blocking_word",
        &format!("@blocking\n{FEE}\n{main}"),
        "",
        &[],
    );
    assert_eq!(out.status, 1);
    assert!(
        out.stderr
            .contains(&format!("1:1: Zed has no `@blocking`: `@blocking {FEE}`.")),
        "{}",
        out.stderr
    );
    assert_eq!(
        run("blocking_word_ok", &format!("{FEE}\n{main}"), "", &[]).status,
        5
    );
}
