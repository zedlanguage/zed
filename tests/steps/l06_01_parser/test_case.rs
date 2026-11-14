//! A boundary clause in a test case (DESIGN.md sec:grammar, `TestCase = Expr12 '->' Expr12`;
//! sec:generations). Each side of a test case is an expression, and an expression takes `with`
//! only before a facet or an update of fields, so `1 with x = 0 -> 1` is refused at the `with`.
//! The item's value is read as a side of the case is, so it ends before the case's `->`, and the
//! menu offers the case with the clause deleted, and with it written as an update of fields when
//! that parses and the code before `with` is not a literal.

use zedc::ast::{Error, unit};
use zedc::lex::{Token, lex};
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

/// The error the unit `text` is refused with, from the parser or from building its statements.
fn refusal(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(e) => Error::of_parse(text, e),
        Ok(tree) => match unit(text, &tokens, &tree) {
            Err(e) => e,
            Ok(_) => panic!("accepted: {text}"),
        },
    }
}

/// The text of each note of `e`, with the text of `src` it points at.
fn notes(src: &str, e: &Error) -> Vec<String> {
    e.notes
        .iter()
        .map(|n| format!("{} [{}]", n.text, &src[n.span.start..n.span.end]))
        .collect()
}

/// Whether the unit `text` parses.
fn parses(text: &str) -> bool {
    let tokens = lex(text).unwrap();
    parse(text, &tokens, "Unit", TOP).is_ok()
}

/// The part of every message that names what `with` may be followed by and where a boundary
/// clause stands, for the code `before` and the first item `head` with name `name` and value
/// `value`.
fn middle(before: &str, head: &str, name: &str, value: &str) -> String {
    format!(
        "Each side of a test case is an expression, and in an expression `with` is followed only \
         by a facet, as `{before} with f(…)`, or by an update of fields, as `{before} with {{ \
         {name} = … }}`; here `with` is followed by `{head}`, which begins a boundary item. A \
         boundary clause follows only the value of an indexed definition, each item with its \
         key, as `{name}[i in 0..<n] = … with {name}[-1] = {value};`, and a variable a loop \
         updates takes its sentinel value, its value before step 0, from a statement of the \
         loop's body, `initial {name} = {value};`."
    )
}

/// The reported program: the item's value ends before the case's `->`, the clause is refused at
/// `with` with row BareBoundary, and the menu offers the case with the clause deleted.
#[test]
fn a_bare_item_on_the_left_side_is_refused_at_the_with() {
    let src = "double(positional x) = x * 2 test { 1 with x = 0 -> 1 }";
    let e = refusal(src);
    assert_eq!(
        e.message,
        format!(
            "The test case `1 with x = 0 -> 1` of `double` holds the boundary clause `with x = \
             0`, and a test case takes no boundary clause. It states that `double` applied to \
             `1` gives `1`. {} The item is read as `x = 0`: its value ends before `->`, the \
             arrow of the test case. Written with neither `initial` nor a key, `with x = 0` \
             would be refused on a statement of a loop too: it reads as though `x` took the \
             value `0` anew on every step.",
            middle("1", "x =", "x", "0")
        )
    );
    assert_eq!(&src[e.span.start..e.span.end], "with x = 0");
    assert_eq!(e.row, Some(Row::BareBoundary));
    assert_eq!(
        notes(src, &e),
        [
            "the test table that holds the case [test {]",
            "the test case, which takes no boundary clause [1 with x = 0 -> 1]",
            "repair: `1 -> 1`, the case with the `with` clause deleted [1 with x = 0 -> 1]",
        ]
    );
    assert!(parses("double(positional x) = x * 2 test { 1 -> 1 }"));
}

/// A value that is a name, or a parenthesized list of names, could begin a lambda
/// (`Lambda = (Name | '(' Params? ')') '->' …`); read as a side of the case is, an `Expr12`, it
/// ends before the case's `->`, so `y -> 2` is not taken as a lambda.
#[test]
fn a_value_that_could_begin_a_lambda_ends_before_the_arrow() {
    for (src, item, deleted) in [
        (
            "double(positional x) = x * 2 test { 1 with x = y -> 2 }",
            "x = y",
            "1 -> 2",
        ),
        (
            "double(positional x) = x * 2 test { 1 with initial x = (y) -> 2 }",
            "initial x = (y)",
            "1 -> 2",
        ),
    ] {
        let e = refusal(src);
        assert!(
            e.message.contains(&format!(
                "The item is read as `{item}`: its value ends before `->`, the arrow of the test \
                 case."
            )),
            "{src}: {}",
            e.message
        );
        assert!(
            e.message
                .contains("It states that `double` applied to `1` gives `2`."),
            "{src}: {}",
            e.message
        );
        assert_eq!(
            notes(src, &e)[2],
            format!(
                "repair: `{deleted}`, the case with the `with` clause deleted [{}]",
                &src[36..src.len() - 2]
            )
        );
    }
}

/// `with initial` in a test case: the same refusal, with row WithInitialItem, and a sentence
/// that the statement `initial x = 0;` gives the sentinel value.
#[test]
fn an_initial_item_in_a_test_case_is_refused() {
    let src = "double(positional x) = x * 2 test { 1 with initial x = 0 -> 1 }";
    let e = refusal(src);
    assert_eq!(
        e.message,
        format!(
            "The test case `1 with initial x = 0 -> 1` of `double` holds the boundary clause \
             `with initial x = 0`, and a test case takes no boundary clause. It states that \
             `double` applied to `1` gives `1`. {} The item is read as `initial x = 0`: its \
             value ends before `->`, the arrow of the test case. `with initial x = 0` would be \
             refused on a statement of a loop too: `with initial` is no longer how a sentinel \
             value is given, and the statement `initial x = 0;` gives it.",
            middle("1", "initial x =", "x", "0")
        )
    );
    assert_eq!(&src[e.span.start..e.span.end], "with initial x = 0");
    assert_eq!(e.row, Some(Row::WithInitialItem));
    assert_eq!(
        notes(src, &e)[2],
        "repair: `1 -> 1`, the case with the `with` clause deleted [1 with initial x = 0 -> 1]"
    );
}

/// An item with an index: refused the same way, with no row.
#[test]
fn an_indexed_item_in_a_test_case_is_refused() {
    let src = "double(positional x) = x * 2 test { 1 with x[0] = 0 -> 1 }";
    let e = refusal(src);
    assert!(e.message.starts_with(
        "The test case `1 with x[0] = 0 -> 1` of `double` holds the boundary clause `with x[0] \
         = 0`, and a test case takes no boundary clause."
    ));
    assert!(e.message.contains(&middle("1", "x[0] =", "x", "0")));
    assert!(e.message.ends_with(
        "The item is read as `x[0] = 0`: its value ends before `->`, the arrow of the test case."
    ));
    assert_eq!(e.row, None);
}

/// On the right side the clause ends the case; the message has no sentence about the arrow.
#[test]
fn a_clause_on_the_right_side_is_refused() {
    let src = "double(positional x) = x * 2 test { 1 -> 2 with x = 0 }";
    let e = refusal(src);
    assert_eq!(
        e.message,
        format!(
            "The test case `1 -> 2 with x = 0` of `double` holds the boundary clause `with x = \
             0`, and a test case takes no boundary clause. It states that `double` applied to \
             `1` gives `2`. {} Written with neither `initial` nor a key, `with x = 0` would be \
             refused on a statement of a loop too: it reads as though `x` took the value `0` \
             anew on every step.",
            middle("2", "x =", "x", "0")
        )
    );
    assert_eq!(
        notes(src, &e)[2],
        "repair: `1 -> 2`, the case with the `with` clause deleted [1 -> 2 with x = 0]"
    );
}

/// The case is the one between the commas of the table, not the cases before or after it.
#[test]
fn the_case_is_cut_from_its_table() {
    for (src, case) in [
        (
            "double(positional x) = x * 2 test { 1 with x = 0 -> 1, 2 -> 4 }",
            "1 with x = 0 -> 1",
        ),
        (
            "double(positional x) = x * 2 test { 2 -> 4, 1 with x = 0 -> 1 }",
            "1 with x = 0 -> 1",
        ),
        (
            "double(positional x) = x * 2 test { 2 -> 4, 1 with x = 0 -> 1, 3 -> 6, }",
            "1 with x = 0 -> 1",
        ),
    ] {
        let e = refusal(src);
        assert!(
            e.message
                .starts_with(&format!("The test case `{case}` of `double` holds")),
            "{src}: {}",
            e.message
        );
        assert_eq!(
            notes(src, &e)[1],
            format!("the test case, which takes no boundary clause [{case}]")
        );
    }
}

/// Several items: the clause is all of them, and the deletion takes them all.
#[test]
fn a_clause_of_several_items_is_deleted_whole() {
    let src = "double(positional x) = x * 2 test { 1 with x = 0, y = 1 -> 1 }";
    let e = refusal(src);
    assert_eq!(&src[e.span.start..e.span.end], "with x = 0, y = 1");
    assert!(
        e.message
            .contains("holds the boundary clause `with x = 0, y = 1`")
    );
    assert_eq!(
        notes(src, &e)[2],
        "repair: `1 -> 1`, the case with the `with` clause deleted [1 with x = 0, y = 1 -> 1]"
    );
}

/// For `main` a case states what a wave writes, as DESIGN.md's gloss of `TestCase` says.
#[test]
fn a_case_of_main_is_described_as_a_wave() {
    let src = "main(m: MainArgs) -> int { m.stdout <- \"a\"; 0 } test { \"\" with x = 0 -> \"a\" }";
    let e = refusal(src);
    assert!(e.message.contains(
        "It states that a wave of `main` reading the ports `\"\"` writes the bytes `\"a\"`."
    ));
}

/// A method is named with its type, and the update of fields is offered when the code before
/// `with` is not a literal and every item has neither `initial` nor an index.
#[test]
fn a_case_of_a_method_offers_an_update_of_fields() {
    let src = "struct P { a: int } P.twice() = self.a * 2 test { P(a: 1) with a = 2 -> 4 }";
    let e = refusal(src);
    assert!(e.message.starts_with(
        "The test case `P(a: 1) with a = 2 -> 4` of `P.twice` holds the boundary clause"
    ));
    assert!(
        e.message
            .contains("It states that `P.twice` applied to `P(a: 1)` gives `4`.")
    );
    assert_eq!(
        notes(src, &e)[2..],
        [
            "repair: `P(a: 1) -> 4`, the case with the `with` clause deleted [P(a: 1) with a = 2 \
             -> 4]",
            "repair: `P(a: 1) with { a = 2 } -> 4`, the case with `P(a: 1)` updated in its \
             fields [P(a: 1) with a = 2 -> 4]",
        ]
    );
    for fixed in [
        "struct P { a: int } P.twice() = self.a * 2 test { P(a: 1) -> 4 }",
        "struct P { a: int } P.twice() = self.a * 2 test { P(a: 1) with { a = 2 } -> 4 }",
    ] {
        assert!(parses(fixed), "{fixed}");
    }
}

/// An `else` arm after the value belongs to the value, as it would on a side of the case.
#[test]
fn an_else_arm_belongs_to_the_value() {
    let src = "half(positional x) = x div 2 test { half(2) with x = 0 else #e -> 0 -> 1 }";
    let e = refusal(src);
    assert!(
        e.message
            .contains("The item is read as `x = 0 else #e -> 0`")
    );
    assert_eq!(
        notes(src, &e)[2],
        "repair: `half(2) -> 1`, the case with the `with` clause deleted [half(2) with x = 0 \
         else #e -> 0 -> 1]"
    );
}

/// When the unit has a second error after the case, no function is named and no deletion is
/// claimed to repair the unit unless the parse gets past the case.
#[test]
fn a_later_error_leaves_the_function_unnamed() {
    let src = "double(positional x) = x * 2 test { 1 with x = 0 -> 1 } bad(";
    let e = refusal(src);
    assert!(e.message.starts_with(
        "The test case `1 with x = 0 -> 1` holds the boundary clause `with x = 0`, and a test \
         case takes no boundary clause. It states that the function the table follows, applied \
         to `1`, gives `1`."
    ));
    assert_eq!(
        notes(src, &e)[2],
        "repair: `1 -> 1`, the case with the `with` clause deleted [1 with x = 0 -> 1]"
    );
}

/// A `with` item outside a test table keeps the messages of its place: a parenthesized case side
/// is code that is neither an indexed definition nor a statement of a loop, and a statement of
/// a loop gets the bare-item message and repair.
#[test]
fn other_places_keep_their_messages() {
    let e = refusal("double(positional x) = x * 2 test { (1 with x = 0) -> 1 }");
    assert!(e.message.starts_with(
        "`with x = 0` stands on `1 with x = 0`, which is neither an indexed definition"
    ));
    assert_eq!(e.row, Some(Row::BareBoundary));
    let e = refusal("f(n) = loop t { while t < n; y' = y with y = 1; };");
    assert!(
        e.message
            .starts_with("`with y = 1` stands on `y' = y with y = 1;` in the body of a `loop`")
    );
    assert_eq!(e.row, Some(Row::BareBoundary));
}

/// A unit whose test table holds `n` cases and then a case with a clause, lexed.
pub(super) fn clause_after(n: usize) -> (String, Vec<Token>) {
    let cases: String = (0..n).map(|i| format!("{i} -> {}, ", 2 * i)).collect();
    let text = format!("double(positional x) = x * 2 test {{ {cases}1 with x = 0 -> 1 }}\n");
    let tokens = lex(&text).unwrap();
    (text, tokens)
}

/// Asserts the clause of the unit `u` found, with its message.
pub(super) fn clause_found(u: &(String, Vec<Token>)) {
    let (text, tokens) = u;
    let e = parse(text, tokens, "Unit", TOP).unwrap_err();
    let clause = e.clause.as_ref().unwrap();
    assert!(
        clause
            .message
            .starts_with("The test case `1 with x = 0 -> 1` of `double` holds"),
        "{}",
        clause.message
    );
}

/// A clause after a few cases is found; the time is held in `bench/test_case.rs`.
#[test]
fn finding_a_clause_after_a_few_test_cases() {
    for n in [0, 1, 2, 9] {
        clause_found(&clause_after(n));
    }
}

/// Code before `with` that is a literal, `true` or `false` among them, is never a struct, so the
/// menu offers only the case with the clause deleted; and when a later error stays after the
/// clause is deleted, the deletion is still offered, since it gets past the `with`.
#[test]
fn a_literal_before_with_gives_no_update_of_fields() {
    for lit in ["true", "false", "2", "-2", "\"s\"", "#a"] {
        let src = format!("f(positional x) = x test {{ {lit} with x = 0 -> 1 }}");
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::BareBoundary), "{src}: {e:?}");
        let repairs: Vec<String> = notes(&src, &e)
            .into_iter()
            .filter(|n| n.starts_with("repair: "))
            .collect();
        assert_eq!(
            repairs,
            [format!(
                "repair: `{lit} -> 1`, the case with the `with` clause deleted [{lit} with x = 0 -> 1]"
            )],
            "{src}"
        );
    }
    let src = "f(positional x) = x test { y with x = 0 -> 1, 2 3 }";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareBoundary), "{e:?}");
    assert!(
        notes(src, &e)
            .iter()
            .any(|n| n.starts_with("repair: `y -> 1`")),
        "{e:?}"
    );
}
