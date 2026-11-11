//! `with initial x = e` (DESIGN.md sec:generations; author decision, 2026-11-09): a boundary
//! item gives a sentinel value with `initial`, or an entry with an index. A bare `with x = e`
//! is refused (row "Boundary item with neither `initial` nor an index"), and so is a second
//! `with initial` for one variable in one body (row "Two `with initial` items for one
//! variable"), wherever the two items are written, since line order has no meaning.

use super::check;
use zed_tests::scaling;
use zedc::ast::{Error, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

/// The error the unit `text` is refused with, from the parser or from building its statements.
fn refusal(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(e) => Error::from(e),
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

#[test]
fn the_initial_form_builds_in_a_loop_and_outside_one() {
    check(&[
        (
            "f(n) = loop t { while t < n; x' = x + 1 with initial x = 0; };",
            "(def f (n) = (loop t (block (while (< t n)) (= (x') (+ x 1) (with (initial x 0))))))",
        ),
        (
            "d[i in 3..<n] = d[i - 1] + 1 with initial d = 0;",
            "(indexed d ((in i (..< 3 n))) (+ (index d (- i 1)) 1) (with (initial d 0)))",
        ),
        (
            "d[i in 3..<n] = d[i - 1] + 1 with d[2] = 0;",
            "(indexed d ((in i (..< 3 n))) (+ (index d (- i 1)) 1) (with (= d ((at 2)) 0)))",
        ),
        (
            "p' = p + q with initial p = 0, p[-2] = -1;",
            "(= (p') (+ p q) (with (initial p 0) (= p ((at (- 2))) (- 1))))",
        ),
    ]);
}

/// `initial` is reserved only by its position: before a name in a boundary item.
#[test]
fn initial_stays_a_name_elsewhere() {
    check(&[
        ("initial = 3;", "(= (initial) 3)"),
        (
            "f(initial) = initial + 1;",
            "(def f (initial) = (+ initial 1))",
        ),
        (
            "initial' = initial + 1 with initial initial = 0, initial[0] = 1;",
            "(= (initial') (+ initial 1) (with (initial initial 0) (= initial ((at 0)) 1)))",
        ),
        ("x' = x with initial;", "syntax"),
        ("x' = x with initial = 0;", "syntax"),
        ("x' = x with initial x;", "syntax"),
    ]);
}

/// The one `with initial` may stand on a statement that reads the variable rather than the
/// one that defines it: the statements run in the order their data dependencies fix.
#[test]
fn the_start_value_may_stand_on_a_reading_line() {
    check(&[(
        "f(n) = loop { s' = s + x with initial s = 0, initial x = 0; x' = x + 1; until x' == n; };",
        "(def f (n) = (loop (block (= (s') (+ s x) (with (initial s 0) (initial x 0))) (= (x') \
         (+ x 1)) (until (== x' n)))))",
    )]);
}

#[test]
fn a_bare_item_is_refused_with_a_menu() {
    let src = "f(n) = loop t { while t < n; x' = x + 1 with x = 0; };";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareBoundary), "{e:?}");
    assert_eq!(&src[e.span.start..e.span.end], "x = 0");
    assert!(
        e.message.starts_with(
            "`with x = 0` gives `x` no sentinel value: a boundary item is written `initial x = \
             0`, which gives the sentinel value, or with an index, as `x[k] = 0`."
        ),
        "{}",
        e.message
    );
    assert_eq!(
        notes(src, &e),
        [
            "the statement whose boundary clause holds the item [x' = x + 1 with x = 0;]",
            "repair: `with initial x = 0`, the sentinel value [x = 0]",
        ]
    );
}

/// For an indexed definition whose low edge is known, the menu also offers the entry one below
/// it.
#[test]
fn a_bare_item_on_an_indexed_definition_offers_the_entry_below() {
    let cases = [
        ("d[i in 0..<n] = d[i - 1] + 1 with d = 0;", "d[-1] = 0"),
        ("d[i in 3..<n] = d[i - 1] + 1 with d = 0;", "d[2] = 0"),
        ("d[i in lo..<n] = d[i - 1] + 1 with d = 0;", "d[lo - 1] = 0"),
        (
            "d[i in a + 1..<n] = d[i - 1] + 1 with d = f(1, 2);",
            "d[(a + 1) - 1] = f(1, 2)",
        ),
    ];
    for (src, entry) in cases {
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::BareBoundary), "{src}: {e:?}");
        let ns = notes(src, &e);
        assert_eq!(ns.len(), 3, "{src}: {ns:?}");
        assert!(
            ns[2].starts_with(&format!("repair: `with {entry}`, the entry one below")),
            "{src}: {ns:?}"
        );
    }
}

/// A bare item after an `initial` one, outside a loop, and in a `mutable` binding is refused
/// the same way.
#[test]
fn a_bare_item_is_refused_wherever_it_stands() {
    for (src, item) in [
        (
            "f(n) = loop { s' = s + x with initial s = 0, x = 0; x' = x + 1; };",
            "x = 0",
        ),
        ("x = 1 with x = 0;", "x = 0"),
        (
            "f(n) = loop { mutable c = g(c) with c = z; until c > n; };",
            "c = z",
        ),
        ("a', b' = (b, a + b) with a = 0, initial b = 1;", "a = 0"),
    ] {
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::BareBoundary), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], item, "{src}");
    }
}

#[test]
fn two_initial_items_for_one_variable_are_refused() {
    // Unequal values, on the defining line and on a reading line.
    let src = "f(n) = loop { s' = s + x with initial s = 0, initial x = 0; \
               x' = x + 1 with initial x = 1; until x' == n; };";
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::TwoInitials), "{e:?}");
    assert_eq!(&src[e.span.start..e.span.end], "initial x = 1");
    assert!(
        e.message.starts_with(
            "the sentinel value of `x`, its value below its first step or index, is given \
             twice in this body: by `with initial x = 1` here and by `with initial x = 0` \
             earlier."
        ),
        "{}",
        e.message
    );
    assert_eq!(
        notes(src, &e),
        [
            "the first `with initial x = 0` [initial x = 0]",
            "repair: keep the first and delete this one: `x' = x + 1;` [initial x = 1]",
            "repair: keep this one and delete the first: `s' = s + x with initial s = 0;` \
             [initial x = 0]",
        ]
    );
    // Equal values are refused too: a second writer of the same entry.
    for src in [
        "f(n) = loop { x' = x + 1 with initial x = 0; y' = x with initial x = 0; };",
        "x = 1 with initial x = 0;\ny = x with initial x = 0;",
        "f(n) = loop { x' = x + 1 with initial x = 0, initial x = 0; };",
    ] {
        let e = refusal(src);
        assert_eq!(e.row, Some(Row::TwoInitials), "{src}: {e:?}");
    }
}

/// Indexed entries for one variable on several statements are not `with initial` items and
/// stay accepted, beside one `with initial`.
#[test]
fn indexed_entries_on_several_lines_stay_accepted() {
    check(&[(
        "f(n) = loop { p' = p + q with initial p = 0, p[-2] = -1; q' = p with p[-3] = 5; };",
        "(def f (n) = (loop (block (= (p') (+ p q) (with (initial p 0) (= p ((at (- 2))) (- \
         1)))) (= (q') p (with (= p ((at (- 3))) 5))))))",
    )]);
}

/// `f(n) = loop t { x0' = x0 + t with initial x0 = 0; … }` with `n` distinct items and, if
/// `tail` is set, the statement `tail` last.
fn items(n: usize, tail: &str) -> String {
    let stmts: String = (0..n)
        .map(|i| format!("x{i}' = x{i} + t with initial x{i} = 0; "))
        .collect();
    format!("f(n) = loop t {{ {stmts}{tail} }};\n")
}

/// The check for a second `with initial` is one pass with a map from each name to its first
/// item, so finding the repeat after `n` distinct items is linear in `n`.
#[test]
fn finding_a_second_initial_scales() {
    let units = scaling::inputs(500, |n| {
        let text = items(n, "y' = x0 with initial x0 = 1;");
        let tokens = lex(&text).unwrap();
        let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
        (text, tokens, tree)
    });
    scaling::check("a second `with initial` after n items", 500, |n| {
        let (text, tokens, tree) = &units[&n];
        let e = unit(text, tokens, tree).unwrap_err();
        assert_eq!(e.row, Some(Row::TwoInitials));
    });
}

/// A bare item is found by parsing the unit once more with `initial` inserted, on the error
/// path only: linear in the unit's size.
#[test]
fn finding_a_bare_item_scales() {
    let units = scaling::inputs(500, |n| {
        let text = items(n, "y' = y with y = 1;");
        let tokens = lex(&text).unwrap();
        (text, tokens)
    });
    scaling::check("a bare item after n items", 500, |n| {
        let (text, tokens) = &units[&n];
        let e = parse(text, tokens, "Unit", TOP).unwrap_err();
        assert!(e.bare.is_some());
    });
}

/// The message for the bare item `name = value` written after `before`, which takes no boundary
/// clause: a push when `push` is set.
fn misplaced_message(name: &str, value: &str, before: &str, push: bool) -> String {
    let what = if push { "a push, which" } else { "code that" };
    format!(
        "`with {name} = {value}` gives `{name}` no sentinel value: a boundary item is written \
         `initial {name} = {value}`, which gives the sentinel value, or with an index, as \
         `{name}[k] = {value}`. Without `initial`, `with {name} = {value}` reads as though \
         `{name}` took the value `{value}` anew on every step, while a boundary item gives \
         `{name}` one value, below its first step or index, once. The item also follows \
         `{before}`, {what} takes no boundary clause: a boundary clause follows only the value \
         of a binding, as `{name}' = … with initial {name} = {value};`, or of an indexed \
         definition, as `{name}[i in 0..<n] = … with initial {name} = {value};`."
    )
}

/// Checks that `src`, which holds the bare item `name = value` after `before`, is refused with
/// row BareBoundary at the item, the whole message, and the notes `expected`; and that each
/// unit in `repaired`, the unit with one repair of the menu applied, parses and is not refused
/// for a boundary item when its statements are built (a keyed push is parsed but not yet built)
fn check_misplaced(
    src: &str,
    (name, value): (&str, &str),
    (before, push): (&str, bool),
    expected: &[&str],
    repaired: &[&str],
) {
    let e = refusal(src);
    assert_eq!(e.row, Some(Row::BareBoundary), "{src}: {e:?}");
    assert_eq!(
        &src[e.span.start..e.span.end],
        format!("{name} = {value}"),
        "{src}"
    );
    assert_eq!(
        e.message,
        misplaced_message(name, value, before, push),
        "{src}"
    );
    assert_eq!(notes(src, &e), expected, "{src}");
    assert_eq!(
        repaired.len() + 1,
        expected.len(),
        "{src}: one unit per repair"
    );
    for text in repaired {
        let tokens = lex(text).unwrap();
        let tree = parse(text, &tokens, "Unit", TOP).unwrap_or_else(|e| panic!("{text}: {e:?}"));
        if let Err(e) = unit(text, &tokens, &tree) {
            assert!(e.row.is_none(), "{text}: {e:?}");
        }
    }
}

/// The note on the code a bare item follows.
const FOLLOWS: &str = "the code the item follows, which takes no boundary clause";

/// The note on the repair that deletes the `with` clause, leaving `here`.
fn deleted(here: &str, name: &str, clause: &str) -> String {
    format!(
        "repair: `{here}`, the `with` clause deleted, where `{name}` takes its sentinel value \
         from another statement [{clause}]"
    )
}

/// A bare item after a generation push `x' <- e`: the menu offers the same next value written
/// as a binding, which takes the clause, and the clause deleted. Before this item the parser
/// reported only "expected '('" at the item.
#[test]
fn a_bare_item_after_a_generation_push_is_refused_with_a_menu() {
    check_misplaced(
        "f(n) = loop t { while t < n; x' <- x + 1 with x = 0; };",
        ("x", "0"),
        ("x' <- x + 1", true),
        &[
            &format!("{FOLLOWS} [x' <- x + 1 with x = 0;]"),
            "repair: `x' = x + 1 with initial x = 0;`, the same next value written as a binding, \
             which takes a boundary clause [x' <- x + 1 with x = 0;]",
            &deleted("x' <- x + 1;", "x", "with x = 0"),
        ],
        &[
            "f(n) = loop t { while t < n; x' = x + 1 with initial x = 0; };",
            "f(n) = loop t { while t < n; x' <- x + 1; };",
        ],
    );
}

/// A bare item after each other push form: whole, keyed, with an acknowledgment, and on a
/// field.
#[test]
fn a_bare_item_after_a_push_is_refused_with_a_menu() {
    let ok = "x' = x + 1 with initial x = 0;";
    check_misplaced(
        &format!("f(n) = loop t {{ while t < n; p <- t with x = 0; {ok} }};"),
        ("x", "0"),
        ("p <- t", true),
        &[
            &format!("{FOLLOWS} [p <- t with x = 0;]"),
            &deleted("p <- t;", "x", "with x = 0"),
        ],
        &[&format!("f(n) = loop t {{ while t < n; p <- t; {ok} }};")],
    );
    check_misplaced(
        &format!("f(n) = loop t {{ while t < n; p[t] <- t with x = 0; {ok} }};"),
        ("x", "0"),
        ("p[t] <- t", true),
        &[
            &format!("{FOLLOWS} [p[t] <- t with x = 0;]"),
            &deleted("p[t] <- t;", "x", "with x = 0"),
        ],
        &[&format!(
            "f(n) = loop t {{ while t < n; p[t] <- t; {ok} }};"
        )],
    );
    check_misplaced(
        &format!("f(n) = loop t {{ while t < n; a = p <- t with x = 0; {ok} }};"),
        ("x", "0"),
        ("a = p <- t", true),
        &[
            &format!("{FOLLOWS} [a = p <- t with x = 0;]"),
            &deleted("a = p <- t;", "x", "with x = 0"),
        ],
        &[&format!(
            "f(n) = loop t {{ while t < n; a = p <- t; {ok} }};"
        )],
    );
    check_misplaced(
        "main(m: MainArgs) -> int { m.stdout <- \"a\" with x = 0; 0 }",
        ("x", "0"),
        ("m.stdout <- \"a\"", true),
        &[
            &format!("{FOLLOWS} [m.stdout <- \"a\" with x = 0;]"),
            &deleted("m.stdout <- \"a\";", "x", "with x = 0"),
        ],
        &["main(m: MainArgs) -> int { m.stdout <- \"a\"; 0 }"],
    );
}

/// A bare item after a statement or expression that is not a binding: `return`, `while`,
/// `until`, an expression statement, a definition's body, and a string hole.
#[test]
fn a_bare_item_after_code_that_is_not_a_binding_is_refused_with_a_menu() {
    let ok = "x' = x + 1 with initial x = 0;";
    let cases = [
        (
            "f(n) = { return n with x = 0; };".to_string(),
            "return n",
            "return n with x = 0;",
            "return n;",
            "f(n) = { return n; };".to_string(),
        ),
        (
            format!("f(n) = loop t {{ while t < n with x = 0; {ok} }};"),
            "while t < n",
            "while t < n with x = 0;",
            "while t < n;",
            format!("f(n) = loop t {{ while t < n; {ok} }};"),
        ),
        (
            format!("f(n) = loop t {{ until t > n with x = 0; {ok} }};"),
            "until t > n",
            "until t > n with x = 0;",
            "until t > n;",
            format!("f(n) = loop t {{ until t > n; {ok} }};"),
        ),
        (
            format!("f(n) = loop t {{ while t < n; g(x) with x = 0; {ok} }};"),
            "g(x)",
            "g(x) with x = 0;",
            "g(x);",
            format!("f(n) = loop t {{ while t < n; g(x); {ok} }};"),
        ),
        (
            "f(n) = n with x = 0;".to_string(),
            "f(n) = n",
            "f(n) = n with x = 0;",
            "f(n) = n;",
            "f(n) = n;".to_string(),
        ),
        (
            "f(n) = \"${n with x = 0}\";".to_string(),
            "n",
            "n with x = 0",
            "n",
            "f(n) = \"${n}\";".to_string(),
        ),
    ];
    for (src, before, stmt, here, fixed) in cases {
        check_misplaced(
            &src,
            ("x", "0"),
            (before, false),
            &[
                &format!("{FOLLOWS} [{stmt}]"),
                &deleted(here, "x", "with x = 0"),
            ],
            &[&fixed],
        );
    }
}

/// When a binding in the same block defines the variable with no `with` clause, before or
/// after the item, the menu also offers to move the item there, as `with initial`.
#[test]
fn a_bare_item_may_move_to_the_binding_that_defines_the_variable() {
    check_misplaced(
        "f(n) = loop t { while t < n with x = 0; x' = x + 1; };",
        ("x", "0"),
        ("while t < n", false),
        &[
            &format!("{FOLLOWS} [while t < n with x = 0;]"),
            "repair: `x' = x + 1 with initial x = 0;`, the sentinel value given on the binding \
             that defines `x`, and the item deleted where it stood: `while t < n;` [x' = x + 1;]",
            &deleted("while t < n;", "x", "with x = 0"),
        ],
        &[
            "f(n) = loop t { while t < n; x' = x + 1 with initial x = 0; };",
            "f(n) = loop t { while t < n; x' = x + 1; };",
        ],
    );
    check_misplaced(
        "f(n) = loop t { x' = x + 1; p <- x with x = 0; until x > n; };",
        ("x", "0"),
        ("p <- x", true),
        &[
            &format!("{FOLLOWS} [p <- x with x = 0;]"),
            "repair: `x' = x + 1 with initial x = 0;`, the sentinel value given on the binding \
             that defines `x`, and the item deleted where it stood: `p <- x;` [x' = x + 1;]",
            &deleted("p <- x;", "x", "with x = 0"),
        ],
        &[
            "f(n) = loop t { x' = x + 1 with initial x = 0; p <- x; until x > n; };",
            "f(n) = loop t { x' = x + 1; p <- x; until x > n; };",
        ],
    );
    check_misplaced(
        "f(n) = loop { until c > n with c = z; local mutable c = g(c); };",
        ("c", "z"),
        ("until c > n", false),
        &[
            &format!("{FOLLOWS} [until c > n with c = z;]"),
            "repair: `local mutable c = g(c) with initial c = z;`, the sentinel value given on \
             the binding that defines `c`, and the item deleted where it stood: `until c > n;` \
             [local mutable c = g(c);]",
            &deleted("until c > n;", "c", "with c = z"),
        ],
        &[
            "f(n) = loop { until c > n; local mutable c = g(c) with initial c = z; };",
            "f(n) = loop { until c > n; local mutable c = g(c); };",
        ],
    );
    // A generation push and a later binding of the same variable: all three repairs.
    check_misplaced(
        "f(n) = loop t { while t < n; x' <- x + 1 with x = 0; x' = 2; };",
        ("x", "0"),
        ("x' <- x + 1", true),
        &[
            &format!("{FOLLOWS} [x' <- x + 1 with x = 0;]"),
            "repair: `x' = x + 1 with initial x = 0;`, the same next value written as a binding, \
             which takes a boundary clause [x' <- x + 1 with x = 0;]",
            "repair: `x' = 2 with initial x = 0;`, the sentinel value given on the binding that \
             defines `x`, and the item deleted where it stood: `x' <- x + 1;` [x' = 2;]",
            &deleted("x' <- x + 1;", "x", "with x = 0"),
        ],
        &[
            "f(n) = loop t { while t < n; x' = x + 1 with initial x = 0; x' = 2; };",
            "f(n) = loop t { while t < n; x' <- x + 1; x' = 2 with initial x = 0; };",
            "f(n) = loop t { while t < n; x' <- x + 1; x' = 2; };",
        ],
    );
}

/// With a second item after the bare one, the item is not moved, since the other item would be
/// lost; the deleting repair deletes the whole clause.
#[test]
fn a_bare_item_with_others_after_it_is_not_moved() {
    check_misplaced(
        "f(n) = loop t { while t < n; y' <- y + x with x = 0, y = 1; x' = x + 1; };",
        ("x", "0"),
        ("y' <- y + x", true),
        &[
            &format!("{FOLLOWS} [y' <- y + x with x = 0, y = 1;]"),
            &deleted("y' <- y + x;", "x", "with x = 0, y = 1"),
        ],
        &["f(n) = loop t { while t < n; y' <- y + x; x' = x + 1; };"],
    );
}

/// A bare item after a push is found by at most four parses of the unit, on the error path
/// only, and one scan of the enclosing block for a binding of the variable: linear in the
/// unit's size.
#[test]
fn finding_a_bare_item_after_a_push_scales() {
    let units = scaling::inputs(500, |n| {
        let text = items(n, "p <- t with y = 1; y' = y + 1;");
        let tokens = lex(&text).unwrap();
        (text, tokens)
    });
    scaling::check("a bare item after a push after n items", 500, |n| {
        let (text, tokens) = &units[&n];
        let e = parse(text, tokens, "Unit", TOP).unwrap_err();
        let bare = e.bare.as_ref().unwrap();
        assert_eq!(bare.misplaced.as_ref().unwrap().repairs.len(), 2);
    });
}

/// When another statement of the block already gives the variable its sentinel value, the menu
/// offers only to delete the item: writing the push as a binding with `with initial`, or moving
/// the item, would give a second sentinel value, which is refused.
#[test]
fn a_bare_item_is_only_deleted_when_the_sentinel_value_is_given_elsewhere() {
    check_misplaced(
        "f(n) = loop t { while t < n; x' <- x + 1 with x = 0; y' = x with initial x = 0; };",
        ("x", "0"),
        ("x' <- x + 1", true),
        &[
            &format!("{FOLLOWS} [x' <- x + 1 with x = 0;]"),
            &deleted("x' <- x + 1;", "x", "with x = 0"),
        ],
        &["f(n) = loop t { while t < n; x' <- x + 1; y' = x with initial x = 0; };"],
    );
    check_misplaced(
        "f(n) = loop t { while t < n with x = 0; x' = x + 1; y' = y + x with initial y = 0, \
         initial x = 0; };",
        ("x", "0"),
        ("while t < n", false),
        &[
            &format!("{FOLLOWS} [while t < n with x = 0;]"),
            &deleted("while t < n;", "x", "with x = 0"),
        ],
        &[
            "f(n) = loop t { while t < n; x' = x + 1; y' = y + x with initial y = 0, initial x = \
           0; };",
        ],
    );
}
