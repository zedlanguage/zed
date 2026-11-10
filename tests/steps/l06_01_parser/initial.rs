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
