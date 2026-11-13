//! The `initial` statement (DESIGN.md sec:generations; author decision, 2026-11-11):
//! `initial x = e;` gives `x` its sentinel value, its value before step 0 of the loop whose
//! body holds the statement, wherever among the body's statements it is written. Its forms are
//! `initial x = e;`, `initial x: T = e;`, `initial a, b = e;`, `initial x[k] = e;` and
//! `initial x[i in r] = e;`. `initial` is a reserved word, and the `with initial` item is gone:
//! a `with` clause stands only on an indexed definition. Each of the seven rows of
//! sec:diagnostics for the form is produced by one program here, with its message and its
//! notes in full, and each repair it offers, applied, is accepted.

use super::{build, fmt};
use zed_tests::scaling;
use zedc::ast::{Error, ExprKind, Stmt, StmtKind, unit};
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::query::Db;
use zedc::rejection::Row;

/// The error the unit `text` is refused with, from the parser or from building its statements.
pub(super) fn refusal(text: &str) -> Error {
    let tokens = lex(text).unwrap();
    match parse(text, &tokens, "Unit", TOP) {
        Err(e) => Error::of_parse(text, e),
        Ok(tree) => match unit(text, &tokens, &tree) {
            Err(e) => e,
            Ok(_) => panic!("accepted: {text}"),
        },
    }
}

/// The text of each note of `e`, with the text of `src` it points at: its first line, and `…`
/// for the rest when there is more.
pub(super) fn notes(src: &str, e: &Error) -> Vec<String> {
    e.notes
        .iter()
        .map(|n| {
            let at = &src[n.span.start..n.span.end];
            match at.split_once('\n') {
                Some((first, _)) => format!("{} [{first} …]", n.text),
                None => format!("{} [{at}]", n.text),
            }
        })
        .collect()
}

/// Checks that the unit `text` is accepted by the front end, as a user's program is read: or,
/// for a loop, which this zedc does not compile yet (step L6.2), refused only with the message
/// that says so.
#[track_caller]
pub(super) fn accepted(text: &str) {
    if let Err(ds) = &*Db::new().front(text) {
        assert!(
            ds.iter()
                .all(|d| d.message.ends_with(zed_tests::not_yet!(""))),
            "refused: {text}\n{ds:#?}"
        );
    }
}

/// Checks that `src` is refused in `row` at the text `at`, with the notes `expected` (and the
/// message `message`, when given), and that each unit of `repaired`, one for each repair the
/// notes offer, is accepted.
#[track_caller]
pub(super) fn refused(
    src: &str,
    row: Row,
    at: &str,
    message: Option<&str>,
    expected: &[&str],
    repaired: &[&str],
) {
    let e = refusal(src);
    assert_eq!(e.row, Some(row), "{src}: {e:?}");
    assert_eq!(&src[e.span.start..e.span.end], at, "{src}");
    if let Some(m) = message {
        assert_eq!(e.message, m, "{src}");
    }
    assert_eq!(notes(src, &e), expected, "{src}");
    let repairs = expected
        .iter()
        .filter(|n| n.starts_with("repair: "))
        .count();
    assert_eq!(repaired.len(), repairs, "{src}: one unit per repair");
    for text in repaired {
        accepted(text);
    }
}

/// The statements of the first loop of the unit `text`, each shown as an s-expression.
fn loop_body(text: &str) -> Vec<String> {
    let (_, stmts) = build(text);
    let StmtKind::Bind { value, .. } = &stmts[0].kind else {
        panic!("not a binding: {}", stmts[0]);
    };
    let ExprKind::Loop { body, .. } = &value.kind else {
        panic!("not a loop: {value:?}");
    };
    let ExprKind::Block(stmts) = &body.kind else {
        panic!("not a block: {body:?}");
    };
    stmts.iter().map(Stmt::to_string).collect()
}

#[test]
fn every_form_builds_and_formats_to_itself() {
    let forms = [
        "initial x = 0;",
        "initial x: int = 3;",
        "initial a, b = (1, 2);",
        "initial p[-2] = -1;",
        "initial q[i in -3..<0] = i;",
        "initial g[-1][j in 0..<2] = j;",
    ];
    let updates = "  x' = x + 1;\n  a' = b;\n  b' = a + b;\n  p' = p + 1;\n  q' = q + 1;\n  \
                   g' = g;\n";
    for form in forms {
        let text = format!("r = loop t {{\n  while t < 9;\n  {form}\n{updates}}};\n");
        assert_eq!(fmt(&text), text, "{form}");
        accepted(&text);
    }
    // Written on one line, each is laid out with the others.
    assert_eq!(
        fmt(
            "r=loop t{while t<9;initial x:int=3;initial a,b=(1,2);initial q[i in -3..<0]=i;\
             x'=x+1;a'=b;b'=a+b;q'=q+1;};"
        ),
        "r = loop t {\n  while t < 9;\n  initial x: int = 3;\n  initial a, b = (1, 2);\n  \
         initial q[i in -3..<0] = i;\n  x' = x + 1;\n  a' = b;\n  b' = a + b;\n  q' = q + 1;\n};\n"
    );
    assert_eq!(
        loop_body(
            "r = loop t { initial x: int = 3; initial a, b = (1, 2); initial p[-2] = -1; \
                   initial q[i in -3..<0] = i; x' = x + 1; a' = b; b' = a + b; p' = p + 1; \
                   q' = q + 1; until t > 9; };"
        )[..4],
        [
            "(initial (x: int) 3)",
            "(initial (a b) (tuple 1 2))",
            "(initial p ((at (- 2))) (- 1))",
            "(initial q ((in i (..< (- 3) 0))) i)",
        ]
    );
}

/// The author's example, with `initial` written first, between the guard and the push, after
/// the update, and last: one tree up to the order of the statements, and the formatter leaves
/// `initial` where it was written (the `while` guard alone is written first).
#[test]
fn initial_may_stand_anywhere_in_the_body() {
    let rest = ["while t < n;", "p <- x;", "x' = x + 1;"];
    let mut trees = Vec::new();
    for at in 0..=3 {
        let mut stmts: Vec<&str> = rest.to_vec();
        stmts.insert(at, "initial x = 0;");
        let text = format!(
            "f(n) = {{\n  r = loop t {{\n    {}\n  }};\n  0\n}};\n",
            stmts.join("\n    ")
        );
        let (_, unit) = build(&text);
        let StmtKind::Function(f) = &unit[0].kind else {
            panic!("not a function: {}", unit[0]);
        };
        let ExprKind::Block(body) = &f.body.kind else {
            panic!("not a block");
        };
        let StmtKind::Bind { value, .. } = &body[0].kind else {
            panic!("not a binding");
        };
        let ExprKind::Loop { body, .. } = &value.kind else {
            panic!("not a loop");
        };
        let ExprKind::Block(body) = &body.kind else {
            panic!("not a block");
        };
        let mut shown: Vec<String> = body.iter().map(Stmt::to_string).collect();
        shown.sort();
        trees.push(shown);
        // The guard moves before `initial` when `initial` is first; nothing else moves.
        let mut want = stmts.clone();
        if at == 0 {
            want.swap(0, 1);
        }
        let want = format!(
            "f(n) = {{\n  r = loop t {{\n    {}\n  }};\n  0\n}};\n",
            want.join("\n    ")
        );
        assert_eq!(fmt(&text), want, "at {at}");
        accepted(&text);
    }
    assert!(trees.iter().all(|t| *t == trees[0]), "{trees:#?}");
    assert_eq!(
        trees[0],
        [
            "(<- p x)",
            "(= (x') (+ x 1))",
            "(initial (x) 0)",
            "(while (< t n))"
        ]
    );
}

/// `initial` is a reserved word: as a name it is a parse error that says so, wherever it
/// stands (row "Reserved word written where a name stands"). `initial _ = 0;` begins the
/// statement as it should, and gets the parse's own message at `_`, which is no name.
#[test]
fn initial_is_a_reserved_word() {
    const WHAT: &str = "`initial` is reserved: it begins the statement `initial x = e;`, which \
                        gives `x` its value before step 0 of a loop that updates `x` [initial]";
    for (src, at, repair) in [
        ("initial = 0;", 0, "start = 0;"),
        ("initial[0] = 1;", 0, "start[0] = 1;"),
        ("f(initial) = initial + 1;", 2, "f(start) = start + 1;"),
    ] {
        let tokens = lex(src).unwrap();
        let e = parse(src, &tokens, "Unit", TOP).expect_err(src);
        let e = Error::of_parse(src, e);
        assert_eq!(e.row, Some(Row::ReservedWordAsName), "{src}");
        assert_eq!(
            e.message,
            format!("Reserved word used as a name: `{src}`. Try `{repair}` instead."),
            "{src}"
        );
        assert_eq!(e.span.start, at, "{src}");
        assert_eq!(
            notes(src, &e),
            [
                WHAT.to_string(),
                "rename the other uses of `initial` as a name too [initial]".to_string(),
                format!("repair: `{repair}` [initial]"),
            ],
            "{src}"
        );
    }
    let src = "initial _ = 0;";
    let tokens = lex(src).unwrap();
    let e = Error::of_parse(src, parse(src, &tokens, "Unit", TOP).expect_err(src));
    assert_eq!(
        (e.row, e.message.as_str(), e.span.start),
        (Some(Row::SyntaxError), "Syntax error at `_`.", 8)
    );
    assert_eq!(e.notes[0].text, "expected a name");
}

/// The forms `with initial` and a `with` clause on a statement of a loop are gone.
#[test]
fn a_with_clause_stands_only_on_an_indexed_definition() {
    accepted("d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;\n");
    for src in [
        "r = loop t { while t < 3; x' = x + 1 with initial x = 0; };",
        "r = loop t { while t < 3; x' = x + 1 with x[-2] = 0; };",
        "x = 1 with initial x = 0;",
    ] {
        let tokens = lex(src).unwrap();
        assert!(parse(src, &tokens, "Unit", TOP).is_err(), "{src}");
    }
}

const BARE_IN_LOOP: &str = "r = loop t {\n  while t < 3;\n  x' = x + 1 with x = 0;\n};\n";

/// Row "Boundary item with neither `initial` nor an index".
#[test]
fn a_bare_item_is_refused() {
    refused(
        BARE_IN_LOOP,
        Row::BareBoundary,
        "x = 0",
        Some(
            "`with x = 0` stands on `x' = x + 1 with x = 0;` in the body of a `loop`, and it \
             gives `x` no sentinel value: without `initial` or a key, it reads as though `x` took \
             the value `0` anew on every step. The sentinel value of `x`, its value before step \
             0, is given once, by a statement of its own, `initial x = 0;`, which may stand \
             anywhere among the statements of the loop's body.",
        ),
        &[
            "the statement the `with` clause stands on [x' = x + 1 with x = 0;]",
            "the loop whose body holds the statement [loop]",
            "repair: `initial x = 0; x' = x + 1;`, `initial x = 0;` written beside the statement, \
             the sentinel value given once, before step 0, and the `with` clause deleted [x = 0]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial x = 0; x' = x + 1;\n};\n"],
    );
    // On an indexed definition: the entry one below the low edge of the domain.
    refused(
        "d[i in 0..<5] = d[i - 1] + 1 with d = 0;\n",
        Row::BareBoundary,
        "d = 0",
        Some(
            "`with d = 0` stands on the definition of `d`, whose entries have keys, and it gives \
             no key: it reads as though `d` took the value `0` at every key. An entry of an \
             indexed definition below its domain is given in the definition's `with` clause \
             with its key, as `with d[-1] = 0`, the entry one below the low edge of the domain \
             of `d`.",
        ),
        &[
            "the statement the `with` clause stands on [d[i in 0..<5] = d[i - 1] + 1 with d = \
             0;]",
            "repair: `d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;`, the entry of `d` given with \
             its key [d = 0]",
        ],
        &["d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;\n"],
    );
    // When an `initial` statement already gives the sentinel value, the item is only deleted
    // (plan note MSG-bareboundary-delete-note).
    refused(
        "r = loop t {\n  while t < 3;\n  initial x = 0;\n  p <- t with x = 0;\n  x' = x + 1;\n};\n",
        Row::BareBoundary,
        "x = 0",
        None,
        &[
            "the statement the `with` clause stands on [p <- t with x = 0;]",
            "the loop whose body holds the statement [loop]",
            "`initial x = 0;` already gives `x` its sentinel value, so the item is deleted, not \
             written as a statement [initial x = 0;]",
            "repair: `p <- t;`, the `with` clause deleted [x = 0]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial x = 0;\n  p <- t;\n  x' = x + 1;\n};\n"],
    );
    // Outside a loop and an indexed definition, the clause is deleted.
    refused(
        "f(n) = n with x = 0;\n",
        Row::BareBoundary,
        "x = 0",
        None,
        &[
            "the statement the `with` clause stands on [f(n) = n with x = 0;]",
            "repair: `f(n) = n;`, the `with` clause deleted [x = 0]",
        ],
        &["f(n) = n;\n"],
    );
}

/// Row "A `with initial` item".
#[test]
fn a_with_initial_item_is_refused() {
    refused(
        "r = loop t {\n  while t < 3;\n  x' = x + 1 with initial x = 0;\n};\n",
        Row::WithInitialItem,
        "initial x = 0",
        Some(
            "`with initial x = 0` stands on `x' = x + 1 with initial x = 0;` in the body of a \
             `loop`, and `with initial` is no longer how a sentinel value is given. The sentinel \
             value of `x`, its value before step 0, is given once, by a statement of its own, \
             `initial x = 0;`, which may stand anywhere among the statements of the loop's body.",
        ),
        &[
            "the statement the `with` clause stands on [x' = x + 1 with initial x = 0;]",
            "the loop whose body holds the statement [loop]",
            "repair: `initial x = 0; x' = x + 1;`, `initial x = 0;` written beside the statement, \
             the sentinel value given once, before step 0, and the `with` clause deleted \
             [initial x = 0]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial x = 0; x' = x + 1;\n};\n"],
    );
    refused(
        "d[i in 0..<5] = d[i - 1] + 1 with initial d = 0;\n",
        Row::WithInitialItem,
        "initial d = 0",
        None,
        &[
            "the statement the `with` clause stands on [d[i in 0..<5] = d[i - 1] + 1 with \
             initial d = 0;]",
            "repair: `d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;`, the entry of `d` given with \
             its key [initial d = 0]",
        ],
        &["d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;\n"],
    );
}

/// Row "A boundary entry of a loop written without `initial`".
#[test]
fn a_bare_loop_entry_is_refused() {
    refused(
        "r = loop t {\n  while t < 3;\n  p' = p + 1;\n  p[-2] = -1;\n};\n",
        Row::BareLoopEntry,
        "p[-2] = -1;",
        Some(
            "`p[-2] = -1;` defines an entry of `p` below generation 0 in the body of a loop that \
             updates `p`. An entry below generation 0 is a sentinel value, given once, before \
             the first step, while a statement of the body without `initial` reads as a \
             definition made on every step. Write it as an `initial` statement.",
        ),
        &[
            "the loop, which updates `p` [loop t { …]",
            "repair: `initial p[-2] = -1;`, the entry given once, before the first step [p[-2] = \
             -1;]",
        ],
        &["r = loop t {\n  while t < 3;\n  p' = p + 1;\n  initial p[-2] = -1;\n};\n"],
    );
    refused(
        "r = loop t {\n  while t < 3;\n  p[i in -3..<0] = i;\n  p' = p + 1;\n};\n",
        Row::BareLoopEntry,
        "p[i in -3..<0] = i;",
        None,
        &[
            "the loop, which updates `p` [loop t { …]",
            "repair: `initial p[i in -3..<0] = i;`, the entry given once, before the first step \
             [p[i in -3..<0] = i;]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial p[i in -3..<0] = i;\n  p' = p + 1;\n};\n"],
    );
    // As a `with` item in a loop, found by the parser.
    refused(
        "r = loop t {\n  while t < 3;\n  x' = x + 1 with x[-2] = 0;\n};\n",
        Row::BareLoopEntry,
        "x[-2] = 0",
        Some(
            "`with x[-2] = 0` stands on `x' = x + 1 with x[-2] = 0;` in the body of a `loop`, \
             and a `with` clause stands only on an indexed definition. An entry of `x` below \
             generation 0 is a sentinel value, given once, before the first step, by an \
             `initial` statement among the statements of the loop's body, `initial x[-2] = 0;`; \
             a `with` item in a loop has no statement it belongs to more than any other.",
        ),
        &[
            "the statement the `with` clause stands on [x' = x + 1 with x[-2] = 0;]",
            "the loop whose body holds the statement [loop]",
            "repair: `initial x[-2] = 0; x' = x + 1;`, `initial x[-2] = 0;` written beside the \
             statement, the sentinel value given once, before step 0, and the `with` clause \
             deleted [x[-2] = 0]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial x[-2] = 0; x' = x + 1;\n};\n"],
    );
}

/// Row "An `initial` statement outside a loop, or under `local`".
#[test]
fn an_initial_statement_outside_a_loop_is_refused() {
    refused(
        "initial x = 0;\n",
        Row::InitialOutsideLoop,
        "initial x = 0;",
        Some(
            "`initial x = 0;` stands at the top level of the unit. An `initial` statement gives \
             the value of `x` before step 0 of a loop that updates `x`, so it is written among \
             the statements of that loop's body, and it has no meaning where no loop updates \
             `x`.",
        ),
        &["repair: `x = 0;`, a plain binding [initial x = 0;]"],
        &["x = 0;\n"],
    );
    refused(
        "f(n) {\n  initial x = 0;\n  return x;\n}\n",
        Row::InitialOutsideLoop,
        "initial x = 0;",
        None,
        &[
            "the block it stands in, which is not the body of a `loop` [{ …]",
            "repair: `x = 0;`, a plain binding [initial x = 0;]",
        ],
        &["f(n) {\n  x = 0;\n  return x;\n}\n"],
    );
    refused(
        "d[i in 0..<5] = d[i - 1] + 1;\ninitial d[-1] = 0;\n",
        Row::InitialOutsideLoop,
        "initial d[-1] = 0;",
        None,
        &[
            "repair: `d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;`, the entry given with its key \
           in the `with` clause of the definition of `d`, and `initial d[-1] = 0;` deleted \
           [initial d[-1] = 0;]",
        ],
        &["d[i in 0..<5] = d[i - 1] + 1 with d[-1] = 0;\n"],
    );
    refused(
        "r = loop t {\n  while t < 3;\n  local initial x = 0;\n  x' = x + 1;\n};\n",
        Row::InitialOutsideLoop,
        "local initial x = 0;",
        Some(
            "`local initial x = 0;` writes `local` on an `initial` statement. `local` is written \
             on the update of `x`, `local x' = …;`, which is what keeps `x` out of the loop's \
             result; an `initial` statement only gives `x` its value before step 0, and puts \
             nothing in the result.",
        ),
        &[
            "repair: `initial x = 0;` and `local x' = x + 1;`, `local` moved to the update \
           [local initial x = 0;]",
        ],
        &["r = loop t {\n  while t < 3;\n  initial x = 0;\n  local x' = x + 1;\n};\n"],
    );
}

/// Row "An `initial` statement for a name the loop does not update".
#[test]
fn an_initial_statement_for_a_name_not_updated_is_refused() {
    refused(
        "r = loop t {\n  while t < 3;\n  initial y = 0;\n  x' = t;\n};\n",
        Row::InitialNotUpdated,
        "initial y = 0;",
        Some(
            "`initial y = 0;` gives `y` a value before step 0, and no statement of this loop \
             updates `y`: none writes `y' = …`, `y' <- e` or `y*.m(…)`. An `initial` statement \
             gives a value before the first step only, so `y` would have no value at any later \
             step.",
        ),
        &[
            "the loop, none of whose statements updates `y` [loop t { …]",
            "repair: add the update the loop is meant to make, `y' = …;`, to its body [initial y \
             = 0;]",
            "repair: `y = 0;` written before the loop, and `initial y = 0;` deleted, for a value \
             that does not change [loop t { …]",
        ],
        &[
            "r = loop t {\n  while t < 3;\n  initial y = 0;\n  y' = y + 1;\n  x' = t;\n};\n",
            "y = 0;\nr = loop t {\n  while t < 3;\n  x' = t;\n};\n",
        ],
    );
}

/// Each form that updates a variable lets an `initial` statement name it: a primed definition,
/// a keyed primed definition, a generation push and a `*.` call (EXAMPLES section 15.4 writes
/// the keyed one).
#[test]
fn every_form_of_update_lets_an_initial_statement_name_its_variable() {
    for body in [
        "y' = y + 1;",
        "y'[v in 0..<4] = y[v] + 1;",
        "y' <- t;",
        "y*.push(t);",
    ] {
        accepted(&format!(
            "r = loop t {{\n  while t < 3;\n  initial y = 0;\n  {body}\n}};\n"
        ));
    }
}

/// Row "An `initial` value that reads a name of its own loop": a generation variable, the step
/// index, and a step-local.
#[test]
fn an_initial_value_that_reads_the_loop_is_refused() {
    refused(
        "r = loop t {\n  while t < 3;\n  initial x = 0;\n  initial y = x;\n  x' = x + 1;\n  \
         y' = y + x;\n};\n",
        Row::InitialReadsLoop,
        "x",
        Some(
            "the value of `initial y = x;` reads `x`, a variable the loop updates. The value of \
             an `initial` statement is computed once, before the first step, when no name of the \
             loop has a value yet, so it reads only names given a value before the loop.",
        ),
        &[
            "the read of `x`, a variable the loop updates [x]",
            "the loop [loop t { …]",
            "repair: compute the start value before the loop, `y0 = …;` above it, and write \
             `initial y = y0;` [initial y = x;]",
            "repair: `initial y = 0;`, the start value of `x` written in place of `x` [initial y \
             = x;]",
        ],
        &[
            "y0 = 0;\nr = loop t {\n  while t < 3;\n  initial x = 0;\n  initial y = y0;\n  \
             x' = x + 1;\n  y' = y + x;\n};\n",
            "r = loop t {\n  while t < 3;\n  initial x = 0;\n  initial y = 0;\n  x' = x + 1;\n  \
             y' = y + x;\n};\n",
        ],
    );
    refused(
        "r = loop t {\n  while t < 3;\n  initial x = t;\n  x' = x + 1;\n};\n",
        Row::InitialReadsLoop,
        "t",
        Some(
            "the value of `initial x = t;` reads `t`, the step index of the loop. The value of \
             an `initial` statement is computed once, before the first step, when no name of the \
             loop has a value yet, so it reads only names given a value before the loop.",
        ),
        &[
            "the read of `t`, the step index of the loop [t]",
            "the loop [loop t { …]",
            "repair: compute the start value before the loop, `x0 = …;` above it, and write \
             `initial x = x0;` [initial x = t;]",
        ],
        &["x0 = 0;\nr = loop t {\n  while t < 3;\n  initial x = x0;\n  x' = x + 1;\n};\n"],
    );
    refused(
        "r = loop t {\n  while t < 3;\n  s = t * 2;\n  initial x = s;\n  x' = x + s;\n};\n",
        Row::InitialReadsLoop,
        "s",
        None,
        &[
            "the read of `s`, a value the loop's body defines on each step [s]",
            "the loop [loop t { …]",
            "repair: compute the start value before the loop, `x0 = …;` above it, and write \
             `initial x = x0;` [initial x = s;]",
        ],
        &[
            "x0 = 0;\nr = loop t {\n  while t < 3;\n  s = t * 2;\n  initial x = x0;\n  \
           x' = x + s;\n};\n",
        ],
    );
}

/// Row "Two sentinel values for one variable", wherever the two sites stand and even where the
/// values agree.
#[test]
fn two_sentinel_values_for_one_variable_are_refused() {
    refused(
        "r = loop t {\n  while t < 3;\n  initial x = 0;\n  x' = x + 1;\n  initial x = 1;\n};\n",
        Row::TwoSentinels,
        "initial x = 1;",
        Some(
            "`x` is given its sentinel value, its value before step 0, twice in this loop: first \
             by `initial x = 0;`, then by `initial x = 1;`. The statements of a loop's body run \
             in the order their data dependencies fix, not the order they are written, so one \
             statement gives the sentinel value wherever it stands, and a second one is a second \
             writer of the same entry, even where the two values agree. Keep one of the two.",
        ),
        &[
            "the first site, which gives `x` the value `0` [initial x = 0;]",
            "the second site, which gives `x` the value `1` [initial x = 1;]",
            "repair: keep the first, `initial x = 0;`, and delete this one, `initial x = 1;` \
             [initial x = 1;]",
            "repair: keep the second, `initial x = 1;`, and delete this one, `initial x = 0;` \
             [initial x = 0;]",
        ],
        &[
            "r = loop t {\n  while t < 3;\n  initial x = 0;\n  x' = x + 1;\n};\n",
            "r = loop t {\n  while t < 3;\n  x' = x + 1;\n  initial x = 1;\n};\n",
        ],
    );
    // Equal values, an unkeyed name beside `[-1]`, and the two in either order.
    for src in [
        "r = loop { initial x = 0; x' = x + 1; initial x = 0; until x > 3; };",
        "r = loop { initial x[-1] = 0; x' = x + 1; initial x = 0; until x > 3; };",
        "r = loop { initial x[-2] = 0; x' = x + 1; initial x[- 2] = 5; until x > 3; };",
    ] {
        assert_eq!(refusal(src).row, Some(Row::TwoSentinels), "{src}");
    }
    // Distinct entries of one variable are two sites of two entries, and accepted.
    accepted("r = loop { initial x = 0; initial x[-2] = 5; x' = x + 1; until x > 3; };");
    // A site of several names keeps the others when the repair takes one name out of it.
    refused(
        "r = loop {\n  initial a, b = (0, 1);\n  a', b' = (b, a + b);\n  until a > 9;\n  \
         initial b = 2;\n};\n",
        Row::TwoSentinels,
        "initial b = 2;",
        None,
        &[
            "the first site, which gives `b` the value `1` [initial a, b = (0, 1);]",
            "the second site, which gives `b` the value `2` [initial b = 2;]",
            "repair: keep the first, `initial a, b = (0, 1);`, and delete this one, `initial b = \
             2;` [initial b = 2;]",
            "repair: keep the second, `initial b = 2;`, and write this one without `b`: `initial \
             a = 0;` [initial a, b = (0, 1);]",
        ],
        &[
            "r = loop {\n  initial a, b = (0, 1);\n  a', b' = (b, a + b);\n  until a > 9;\n};\n",
            "r = loop {\n  initial a = 0;\n  a', b' = (b, a + b);\n  until a > 9;\n  \
             initial b = 2;\n};\n",
        ],
    );
    refused(
        "r = loop {\n  initial a, b = f(0);\n  a', b' = (b, a + b);\n  until a > 9;\n  \
         initial b = 2;\n};\n",
        Row::TwoSentinels,
        "initial b = 2;",
        None,
        &[
            "the first site, which gives `a, b` the value `f(0)` [initial a, b = f(0);]",
            "the second site, which gives `b` the value `2` [initial b = 2;]",
            "repair: keep the first, `initial a, b = f(0);`, and delete this one, `initial b = \
             2;` [initial b = 2;]",
            "repair: keep the second, `initial b = 2;`, and write this one without `b`: `initial \
             a = …;`, with the value of `a` alone in place of `…` [initial a, b = f(0);]",
        ],
        &[
            "r = loop {\n  initial a, b = f(0);\n  a', b' = (b, a + b);\n  until a > 9;\n};\n",
            "r = loop {\n  initial a = 0;\n  a', b' = (b, a + b);\n  until a > 9;\n  \
             initial b = 2;\n};\n",
        ],
    );
}

/// `r = loop t { while t < 3; x' = x + 1; … };` with the statements `sites` in its body.
fn x_loop(sites: &str) -> String {
    format!("r = loop t {{ while t < 3; x' = x + 1; {sites} }};")
}

/// Two sites give one entry when their keys meet by value, not by text: a key inside a range,
/// two ranges that share a key, and one key written in two ways. Ranges that only touch, keys
/// apart, and a range that holds no key give no entry twice.
#[test]
fn entries_given_twice_are_found_by_the_values_of_their_keys() {
    refused(
        "r = loop t {\n  while t < 3;\n  initial x[i in -3..<0] = 0;\n  x' = x + 1;\n  \
         initial x[-2] = 1;\n};\n",
        Row::TwoSentinels,
        "initial x[-2] = 1;",
        Some(
            "`x` is given the entry `x[-2]` twice in this loop: first by `initial x[i in \
             -3..<0] = 0;`, then by `initial x[-2] = 1;`. The statements of a loop's body run in \
             the order their data dependencies fix, not the order they are written, so one \
             statement gives a sentinel value wherever it stands, and a second one is a second \
             writer of the same entry, even where the two values agree. Give each entry once.",
        ),
        &[
            "the first site, which gives `x[i in -3..<0]` the value `0` [initial x[i in -3..<0] \
             = 0;]",
            "the second site, which gives `x[-2]` the value `1` [initial x[-2] = 1;]",
            "repair: keep the first, `initial x[i in -3..<0] = 0;`, and delete this one, \
             `initial x[-2] = 1;` [initial x[-2] = 1;]",
            "repair: keep the second, `initial x[-2] = 1;`, and delete this one, `initial x[i in \
             -3..<0] = 0;` [initial x[i in -3..<0] = 0;]",
            "repair: split this one into two, around the keys the other gives: `initial x[i in \
             -3..<-2] = 0;` and `initial x[i in -1..<0] = 0;` [initial x[i in -3..<0] = 0;]",
        ],
        &[
            "r = loop t {\n  while t < 3;\n  initial x[i in -3..<0] = 0;\n  x' = x + 1;\n};\n",
            "r = loop t {\n  while t < 3;\n  x' = x + 1;\n  initial x[-2] = 1;\n};\n",
            "r = loop t {\n  while t < 3;\n  initial x[i in -3..<-2] = 0;\n  initial x[i in \
             -1..<0] = 0;\n  x' = x + 1;\n  initial x[-2] = 1;\n};\n",
        ],
    );
    // How each pair names the entries it gives twice.
    for (sites, entries) in [
        // A key in a range, either one first, and `initial x = e;` inside a range.
        (
            "initial x[-2] = 1; initial x[i in -3..<0] = 0;",
            "the entry `x[-2]`",
        ),
        (
            "initial x[i in -3..<0] = 0; initial x = 1;",
            "the entry `x[-1]`",
        ),
        (
            "initial x = 1; initial x[i in -3..<0] = 0;",
            "the entry `x[-1]`",
        ),
        // Ranges that share keys: one key, where `..=` holds the key `..<` would not, and more.
        (
            "initial x[i in -3..=-1] = 0; initial x[i in -1..<0] = 1;",
            "the entry `x[-1]`",
        ),
        (
            "initial x[i in -5..<-1] = 0; initial x[i in -3..<0] = 1;",
            "the entries `x[-3]` to `x[-2]`",
        ),
        (
            "initial x[i in -2..<0] = 0; initial x[i in -5..<-1] = 1;",
            "the entry `x[-2]`",
        ),
        // A range inside another, and a range with no last key.
        (
            "initial x[i in -9..<0] = 0; initial x[i in -4..<-2] = 1;",
            "the entries `x[-4]` to `x[-3]`",
        ),
        (
            "initial x[i in -3..] = 0; initial x[i in -6..<-1] = 1;",
            "the entries `x[-3]` to `x[-2]`",
        ),
        (
            "initial x[i in -6..] = 0; initial x[i in -3..] = 1;",
            "the entries from `x[-3]` up",
        ),
        // One key written in two ways: spaces, another base, a range of one key, a range
        // written with each end.
        (
            "initial x[-2] = 0; initial x[- 2] = 1;",
            "the entry `x[-2]`",
        ),
        (
            "initial x[-2] = 0; initial x[-0x2] = 1;",
            "the entry `x[-2]`",
        ),
        (
            "initial x[-2] = 0; initial x[i in -2..=-2] = 1;",
            "the entry `x[-2]`",
        ),
        (
            "initial x[i in -3..<-1] = 0; initial x[j in -3..=-2] = 1;",
            "the entries `x[-3]` to `x[-2]`",
        ),
        // A key the text does not fix as an integer, written the same way twice.
        (
            "initial x[-t0] = 0; initial x[-t0] = 1;",
            "the entry `x[-t0]`",
        ),
    ] {
        let src = format!("t0 = 2; {}", x_loop(sites));
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::TwoSentinels), "{src}: {e:?}");
        assert!(
            e.message
                .starts_with(&format!("`x` is given {entries} twice")),
            "{src}: {}",
            e.message
        );
    }
    // Entries apart: ranges that touch but share no key, keys apart, a range that holds no
    // key, and keys around a range.
    for sites in [
        "initial x[i in -3..<-1] = 0; initial x[i in -1..<0] = 1;",
        "initial x[i in -3..=-2] = 0; initial x = 1;",
        "initial x[i in -9..<-5] = 0; initial x[i in -3..<0] = 1;",
        "initial x[-3] = 0; initial x[-2] = 1; initial x = 2;",
        "initial x[i in -1..<-1] = 0; initial x = 1;",
        "initial x[-4] = 0; initial x[i in -3..<-1] = 1; initial x[-1] = 2;",
    ] {
        accepted(&x_loop(sites));
    }
}

/// A later bracket gives entries inside a frame: a site that gives the whole frame gives those
/// too, and two sites with the same later brackets meet by their first keys; sites whose later
/// brackets have other values are apart.
#[test]
fn entries_inside_a_frame_are_found_against_the_whole_frame() {
    let g_loop = |sites: &str| format!("r = loop t {{ while t < 3; g' = g; {sites} }};");
    for (sites, entries) in [
        (
            "initial g[-1][j in 0..<2] = j; initial g = 0;",
            "the entries `g[-1][j in 0..<2]`",
        ),
        (
            "initial g = 0; initial g[-1][j in 0..<2] = j;",
            "the entries `g[-1][j in 0..<2]`",
        ),
        (
            "initial g[i in -3..<0] = 0; initial g[-2][0] = 1;",
            "the entry `g[-2][0]`",
        ),
        (
            "initial g[-2][0] = 1; initial g[i in -3..<0] = 0;",
            "the entry `g[-2][0]`",
        ),
        (
            "initial g[i in -3..<0][1] = 0; initial g[-1][1] = 1;",
            "the entry `g[-1][1]`",
        ),
    ] {
        let src = g_loop(sites);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::TwoSentinels), "{src}: {e:?}");
        assert!(
            e.message
                .starts_with(&format!("`g` is given {entries} twice")),
            "{src}: {}",
            e.message
        );
    }
    // The range of a whole-frame site is narrowed around the frame the other gives in full,
    // and not around one entry inside a frame.
    let e = refusal(&g_loop("initial g[i in -3..<0][0] = 0; initial g[-2] = 1;"));
    assert!(
        e.notes
            .iter()
            .any(|n| n.text.contains("split this one into two")),
        "{e:?}"
    );
    let e = refusal(&g_loop("initial g[i in -3..<0] = 0; initial g[-2][0] = 1;"));
    assert!(
        !e.notes.iter().any(|n| n.text.contains("this one into two")),
        "{e:?}"
    );
    for sites in [
        "initial g[-1][0] = 0; initial g[-1][1] = 1;",
        "initial g[-2][0] = 0; initial g[-1][0] = 1; initial g[-3] = 2;",
    ] {
        accepted(&g_loop(sites));
    }
}

/// `f(n) = loop t { while t < n; x' = x + t; … }` with `3n` keys of `x` given by `2n` sites
/// apart, `initial x[i in -3k-3..=-3k-2] = 0;` and `initial x[-3k-1] = 0;` for each `k`
/// below `n`, written from the farthest key in, and `tail` last.
fn many_entries(n: usize, tail: &str) -> String {
    let sites: String = (0..n)
        .rev()
        .map(|k| {
            format!(
                "initial x[i in -{}..=-{}] = 0; initial x[-{}] = 0; ",
                3 * k + 3,
                3 * k + 2,
                3 * k + 1
            )
        })
        .collect();
    format!("f(n) = loop t {{ while t < n; x' = x + t; {sites}{tail} }};\n")
}

/// Each site is one query and one insertion into a Fenwick tree over the first keys of its
/// class (`crate::ast::sentinel` in zedc-syntax), so `2n` sites of one variable whose entries
/// are apart are checked in time of order `n log n`, and a site after them that meets one is
/// found in the same time.
#[test]
fn overlapping_entries_scale() {
    for (what, tail, ok) in [
        ("2n sites of one variable, apart", "", true),
        (
            "a site after 2n that meets one",
            "initial x[i in -2..<0] = 1;",
            false,
        ),
    ] {
        let units = scaling::inputs(500, |n| {
            let text = many_entries(n, tail);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
            (text, tokens, tree)
        });
        scaling::check(what, 500, |n| {
            let (text, tokens, tree) = &units[&n];
            match unit(text, tokens, tree) {
                Ok(_) => assert!(ok, "{what}: accepted"),
                Err(e) => assert_eq!((ok, e.row), (false, Some(Row::TwoSentinels)), "{e:?}"),
            }
        });
    }
}

/// `f(n) = loop t { while t < n; initial x0 = 0; x0' = x0 + t; … }` with `n` variables, and
/// `tail` last.
fn one_body(n: usize, tail: &str) -> String {
    let stmts: String = (0..n)
        .map(|i| format!("initial x{i} = 0; x{i}' = x{i} + t; "))
        .collect();
    format!("f(n) = loop t {{ while t < n; {stmts}{tail} }};\n")
}

/// `n` loops, each with one `initial` statement.
fn many_loops(n: usize) -> String {
    (0..n)
        .map(|i| format!("r{i} = loop t {{ while t < 9; initial x = {i}; x' = x + t; }};\n"))
        .collect()
}

/// The checks of a loop body are one pass over its statements, with a Fenwick tree over the
/// first keys of the sites of each variable, so `n` `initial` statements in one body, and `n`
/// loops with one each, are built in time of order `n log n`; and a second site after `n` is
/// found in the same time.
#[test]
fn initial_statements_scale() {
    for (what, make) in [
        (
            "n initial statements in one loop body",
            one_body as fn(usize, &str) -> String,
        ),
        ("n loops with one initial statement each", |n, _| {
            many_loops(n)
        }),
    ] {
        let units = scaling::inputs(500, |n| {
            let text = make(n, "");
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
            (text, tokens, tree)
        });
        scaling::check(what, 500, |n| {
            let (text, tokens, tree) = &units[&n];
            assert!(unit(text, tokens, tree).is_ok());
        });
    }
    let units = scaling::inputs(500, |n| {
        let text = one_body(n, "initial x0 = 1;");
        let tokens = lex(&text).unwrap();
        let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
        (text, tokens, tree)
    });
    scaling::check("a second initial statement after n", 500, |n| {
        let (text, tokens, tree) = &units[&n];
        let e = unit(text, tokens, tree).unwrap_err();
        assert_eq!(e.row, Some(Row::TwoSentinels));
    });
}

/// A bare `with` item is found by the parser on the error path, which parses the unit again
/// with each repair written in, a fixed number of times: linear in the unit's size.
#[test]
fn finding_a_bare_item_scales() {
    let units = scaling::inputs(500, |n| {
        let text = one_body(n, "y' = y + 1 with y = 0;");
        let tokens = lex(&text).unwrap();
        (text, tokens)
    });
    scaling::check("a bare item after n statements", 500, |n| {
        let (text, tokens) = &units[&n];
        let e = Error::of_parse(text, parse(text, tokens, "Unit", TOP).unwrap_err());
        assert_eq!(e.row, Some(Row::BareBoundary));
    });
}
