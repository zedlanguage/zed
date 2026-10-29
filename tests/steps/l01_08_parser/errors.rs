//! A text that does not parse is reported at the furthest token any alternative reached, with
//! what the grammar expected there.

use zedc::lex::lex;
use zedc::parse::{TOP, parse};

fn report(text: &str) -> String {
    let tokens = lex(text).unwrap();
    let err = parse(text, &tokens, "Unit", TOP).unwrap_err();
    let line = text[..err.span.start].matches('\n').count() + 1;
    format!(
        "{text:?}\n  line {line}, at {:?}: {err}",
        &text[err.span.start..err.span.end]
    )
}

#[test]
fn golden_errors() {
    let out = [
        "total = price * ;",
        "discount = if member { 0.1 }; // `if` needs its `else`",
        "area(w, h) = w * h\nmain = area(2, 3);",
        "xs = [1, 2, 3;",
        "p = Point(x: 1 y: 2);",
        // `\` cannot follow a `|` union, so it is not expected here (`TypeUnion`)
        "type Bound = int | #unbounded\nlimit: Bound = 10;",
    ]
    .map(report)
    .join("\n");
    insta::assert_snapshot!(out);
}
