//! Recurrences and `with carryForward` (DESIGN.md sec:generations; author decision,
//! 2026-11-12): a variable a loop updates is a recurrence, defined on every frame, so each step
//! updates it on every path; `initial x = e with carryForward;` instead keeps its value on a step
//! that does not update it. `mutable` is gone and is an ordinary name; the old declaration
//! `mutable x = e;` is refused with the repair `initial x = e with carryForward;`, and so is any
//! other word after `with` there, as `initial x = e with carry;`. Each row the
//! form adds to sec:diagnostics is produced here with its message and notes in full, and each
//! repair it offers, applied, is accepted.

use super::initial::{accepted, notes, refusal, refused};
use super::{check, fmt};
use zed_tests::scaling;
use zedc::ast::unit;
use zedc::lex::lex;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;

#[test]
fn with_carry_forward_builds_and_formats() {
    check(&[
        (
            "r = loop t { while t < 3; initial c = 0 with carryForward; c' = c + 1; };",
            "(= (r) (loop t (block (while (< t 3)) (initial (c) 0 carryForward) (= (c') (+ c \
             1)))))",
        ),
        (
            "r = loop { initial a, b = (0, 1) with carryForward; a', b' = (b, a + b); until a > \
             9; };",
            "(= (r) (loop (block (initial (a b) (tuple 0 1) carryForward) (= (a' b') (tuple b (+ \
             a b))) (until (> a 9)))))",
        ),
        // The word is read as the facet only after `with` at the end of an `initial`
        // statement: elsewhere it is a name, and so is the carried variable here.
        ("carryForward = 3;", "(= (carryForward) 3)"),
        (
            "r = loop { initial carryForward = 0 with carryForward; carryForward' = \
             carryForward + 1; until carryForward > 9; };",
            "(= (r) (loop (block (initial (carryForward) 0 carryForward) (= (carryForward') (+ \
             carryForward 1)) (until (> carryForward 9)))))",
        ),
        // The word is `carryForward`, written once.
        (
            "r = loop { initial c = 0 with carry; c' = c + 1; until c > 9; };",
            "syntax",
        ),
        (
            "r = loop { initial c = 0 with carryForward with carryForward; c' = c + 1; until c \
             > 9; };",
            "syntax",
        ),
        // `mutable` is an ordinary name.
        ("mutable = 3;", "(= (mutable) 3)"),
        (
            "f(mutable) = mutable + 1;",
            "(def f (mutable) = (+ mutable 1))",
        ),
        ("mutable x;", "syntax"),
    ]);
    for (text, want) in [
        (
            "r=loop{initial a,b=(0,1)with   carryForward;a',b'=(b,a+b);until a>9;};",
            "r = loop {\n  initial a, b = (0, 1) with carryForward;\n  a', b' = (b, a + b);\n  \
             until a > 9;\n};\n",
        ),
        (
            "r=loop t{while t<3;initial c:int=0 with carryForward;c'=c+1;};",
            "r = loop t {\n  while t < 3;\n  initial c: int = 0 with carryForward;\n  c' = c + \
             1;\n};\n",
        ),
    ] {
        assert_eq!(fmt(text), want, "{text}");
        accepted(want);
    }
}

/// A loop `r = loop t { while t < 3; … }` with the statements `body` in it, one per line.
fn t_loop(body: &[&str]) -> String {
    let lines: String = body.iter().map(|s| format!("  {s}\n")).collect();
    format!("r = loop t {{\n  while t < 3;\n{lines}}};\n")
}

/// The note of row "A loop variable not updated on every path of a step" at the loop, for `c`.
const LOOP_NOTE: &str = "the loop, which updates `c`: a variable a loop updates is a \
                         recurrence, defined on every frame, so each step updates it on every \
                         path; `with carryForward` on its `initial` statement keeps its value on \
                         a step that does not update it [loop t { …]";

/// Row "A loop variable not updated on every path of a step".
#[test]
fn a_recurrence_updated_on_some_paths_only_is_refused() {
    refused(
        &t_loop(&["initial c = 0;", "if t > 1 { c*.bump(1) } else { 0 };"]),
        Row::NotEveryPath,
        "c*.bump",
        Some(
            "Not updated on every path of a step: `c*.bump` updates `c` only in a branch of the \
             `if`. Try `initial c = 0 with carryForward;` instead.",
        ),
        &[
            LOOP_NOTE,
            "`c*.bump` updates `c` only on the paths through a branch of the `if` [c*.bump]",
            "the `if` that `c*.bump` stands in [if t > 1 { c*.bump(1) } else { 0 }]",
            "repair: `initial c = 0 with carryForward;` in place of `initial c = 0;`, so a step \
             that does not update `c` keeps its value [initial c = 0;]",
            "repair: update `c` on every path, with the update written where the branch is \
             chosen and `c` itself on the paths that leave it as it is: `c' = if … { … } else { \
             c };` [c*.bump]",
        ],
        &[
            &t_loop(&[
                "initial c = 0 with carryForward;",
                "if t > 1 { c*.bump(1) } else { 0 };",
            ]),
            &t_loop(&["initial c = 0;", "c' = if t > 1 { c + 1 } else { c };"]),
        ],
    );
    // Two updates, each on some paths, and no `initial` statement for the variable.
    refused(
        &t_loop(&[
            "x' = if t > 1 { c*.bump(1) } else { 0 };",
            "y' = t > 2 && c*.ok();",
        ]),
        Row::NotEveryPath,
        "c*.bump",
        Some(
            "Not updated on every path of a step: `c*.bump` and `c*.ok` update `c` only on some \
             paths. Try `initial c = … with carryForward;` instead.",
        ),
        &[
            LOOP_NOTE,
            "`c*.bump` updates `c` only on the paths through a branch of the `if` [c*.bump]",
            "the `if` that `c*.bump` stands in [if t > 1 { c*.bump(1) } else { 0 }]",
            "`c*.ok` updates `c` only on the paths through the right side of the `&&` [c*.ok]",
            "the `&&` that `c*.ok` stands in [t > 2 && c*.ok()]",
            "repair: `initial c = … with carryForward;` among the statements of the loop's \
             body, with the value of `c` before step 0 in place of `…`, so a step that does not \
             update `c` keeps its value [loop t { …]",
            "repair: update `c` on every path, with the update written where the branch is \
             chosen and `c` itself on the paths that leave it as it is: `c' = if … { … } else { \
             c };` [c*.bump]",
        ],
        &[
            &t_loop(&[
                "initial c = 0 with carryForward;",
                "x' = if t > 1 { c*.bump(1) } else { 0 };",
                "y' = t > 2 && c*.ok();",
            ]),
            &t_loop(&["x' = t;", "c' = if t > 1 { c + 1 } else { c };"]),
        ],
    );
}

/// Each construct whose parts run on some paths only: an update in such a part alone is refused
/// for a recurrence, named by the part, and accepted for a carried variable.
#[test]
fn every_construct_with_paths_is_checked() {
    for (update, part) in [
        (
            "x' = if t > 1 { c*.a() } else { 0 };",
            "a branch of the `if`",
        ),
        (
            "x' = if t > 1 { 0 } else { c*.a() };",
            "a branch of the `if`",
        ),
        (
            "x' = match t { 0 -> c*.a(), _ -> 1 };",
            "an arm of the `match`",
        ),
        (
            "x' = match t { n where c*.a() > n -> 0, _ -> 1 };",
            "an arm of the `match`",
        ),
        ("x' = f(t) else c*.a();", "the default of the `else`"),
        ("x' = t > 1 && c*.a();", "the right side of the `&&`"),
        ("x' = t > 1 || c*.a();", "the right side of the `||`"),
        ("x' = for i in 0..<t { c*.a() };", "the body of the `for`"),
        ("x' = (i -> c*.a());", "the body of the lambda"),
        // A nested block in a branch is still in the branch.
        (
            "x' = if t > 1 { y = c*.a(); y } else { 0 };",
            "a branch of the `if`",
        ),
        // The value of an indexed definition is computed once for each key.
        (
            "d[i in 0..<2] = c*.a();",
            "the value of the indexed definition",
        ),
    ] {
        let src = t_loop(&["initial c = 0;", update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], "c*.a", "{src}");
        assert!(
            e.notes
                .iter()
                .any(|n| n.text == format!("`c*.a` updates `c` only on the paths through {part}")),
            "{src}: {e:?}"
        );
        accepted(&t_loop(&["initial c = 0 with carryForward;", update]));
    }
}

/// A recurrence is accepted when every path of a step updates it or ends in `break`; parts that
/// run on every path, such as the condition of an `if`, update it on every path.
#[test]
fn every_path_that_updates_or_breaks_is_accepted() {
    for update in [
        "c*.a();",
        "x' = if c*.a() > 1 { 0 } else { 1 };",
        "x' = if t > 1 { c*.a() } else { c*.b() };",
        "x' = if t > 1 { c*.a() } else { break 0 };",
        "x' = if t > 1 { break 0 } else { if t > 2 { c*.a() } else { c*.b() } };",
        "x' = match t { 0 -> c*.a(), 1 -> break 1, _ -> c*.b() };",
        "x' = c*.a() && t > 1;",
        "x' = (c*.a() else 0) + 1;",
        "x' = { y = c*.a(); y };",
        // An update on some paths beside one on every path.
        "x' = c*.a() + (if t > 1 { c*.b() } else { 0 });",
    ] {
        accepted(&t_loop(&["initial c = 0;", update]));
    }
    // A primed definition or a push updates on every path, beside a `*.` call on some.
    accepted(&t_loop(&[
        "initial c = 0;",
        "c' = c + 1;",
        "x' = if t > 1 { c*.a() } else { 0 };",
    ]));
    // A nested loop's variables are its own: its updates do not count for the outer loop.
    let src = t_loop(&[
        "initial c = 0;",
        "x' = if t > 1 { c*.a() } else { 0 };",
        "y' = loop u { while u < t; initial d = 0; d' = d + 1; };",
    ]);
    assert_eq!(refusal(&src).row, Some(Row::NotEveryPath), "{src}");
}

/// An update written in a nested block counts on the paths through that block: a primed
/// definition, a push, a primed indexed definition and a `*.` call alike (sec:generations).
#[test]
fn an_update_in_a_nested_block_counts() {
    for body in [
        &["initial c = 0;", "x' = { c' = c + 1; 0 };"][..],
        &["initial c = 0;", "{ c' = c + 1; 0 };"],
        &["initial c = 0;", "x' = { y = { c' = c + 1; 0 }; y };"],
        &[
            "initial c = 0;",
            "x' = if t > 1 { c' = c + 1; 0 } else { c' = c; 1 };",
        ],
        &[
            "initial c = 0;",
            "x' = if t > 1 { c*.a() } else { c' = c + 1; 1 };",
        ],
        &[
            "initial c = 0;",
            "x' = if t > 1 { c' <- 1; 0 } else { c' <- 2; 1 };",
        ],
        &["initial c = 0;", "x' = { c'[v in 0..<2] = v; 0 };"],
        &[
            "initial c = 0;",
            "x' = match t { 0 -> { c' = 1; 0 }, _ -> { c' = 2; 1 } };",
        ],
        &[
            "initial c = 0;",
            "x' = if t > 1 { c' = 1; 0 } else { break 0 };",
        ],
        // A domain of an indexed definition is computed once on a step.
        &["initial c = 0;", "d[i in 0..<c*.a()] = i;"],
    ] {
        accepted(&t_loop(body));
    }
    // An update in one branch only: the update is named by its statement.
    refused(
        &t_loop(&[
            "initial c = 0;",
            "x' = if t > 1 { c' = c + 1; 0 } else { 1 };",
        ]),
        Row::NotEveryPath,
        "c' = c + 1;",
        Some(
            "Not updated on every path of a step: `c' = c + 1;` updates `c` only in a branch of \
             the `if`. Try `initial c = 0 with carryForward;` instead.",
        ),
        &[
            LOOP_NOTE,
            "`c' = c + 1;` updates `c` only on the paths through a branch of the `if` [c' = c + \
             1;]",
            "the `if` that `c' = c + 1;` stands in [if t > 1 { c' = c + 1; 0 } else { 1 }]",
            "repair: `initial c = 0 with carryForward;` in place of `initial c = 0;`, so a step \
             that does not update `c` keeps its value [initial c = 0;]",
            "repair: update `c` on every path, with the update written where the branch is \
             chosen and `c` itself on the paths that leave it as it is: `c' = if … { … } else { \
             c };` [c' = c + 1;]",
        ],
        &[
            &t_loop(&[
                "initial c = 0 with carryForward;",
                "x' = if t > 1 { c' = c + 1; 0 } else { 1 };",
            ]),
            &t_loop(&[
                "initial c = 0;",
                "c' = if t > 1 { c + 1 } else { c };",
                "x' = if t > 1 { 0 } else { 1 };",
            ]),
        ],
    );
    // Each form, in one branch, with no `initial` statement for the variable.
    for update in [
        "x' = if t > 1 { c' = 1; 0 } else { 1 };",
        "x' = if t > 1 { c' <- 1; 0 } else { 1 };",
        "x' = if t > 1 { c'[v in 0..<2] = v; 0 } else { 1 };",
        "x' = t > 1 && { c' = 1; true };",
        "x' = for i in 0..<t { c' = i; i };",
    ] {
        let src = t_loop(&[update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert!(
            src[e.span.start..e.span.end].starts_with("c'"),
            "{src}: {e:?}"
        );
        accepted(&t_loop(&["initial c = 0 with carryForward;", update]));
    }
}

/// `return` exports a block's value and ends no path: the other statements of its block run on
/// the same path, and a `return` in a branch updates nothing on the other branch
/// (sec:values_morphisms, "Blocks bind; `return` exports").
#[test]
fn return_ends_no_path() {
    for body in [
        &["initial c = 0;", "c' = c + 1;", "return 0;"][..],
        &["initial c = 0;", "return c*.a();"],
        &["initial c = 0;", "x' = { return c*.a(); };"],
        &[
            "initial c = 0;",
            "x' = if t > 1 { return 0; c' = c + 1; } else { c' = c; 1 };",
        ],
        &[
            "initial c = 0;",
            "x' = if t > 1 { return break 0; } else { c*.a() };",
        ],
    ] {
        accepted(&t_loop(body));
    }
    for (update, at) in [
        ("x' = if t > 1 { return 0; } else { c' = c; 1 };", "c' = c;"),
        ("x' = if t > 1 { return c*.a(); } else { 1 };", "c*.a"),
    ] {
        let src = t_loop(&["initial c = 0;", update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], at, "{src}");
    }
}

/// The value of an `initial` statement and the bodies of the functions and methods the body
/// declares are not part of a step: a `*.` call there updates no variable of the loop.
#[test]
fn updates_outside_the_step_do_not_count() {
    for (body, site) in [
        (
            &["initial c = 0;", "f() = c*.a();", "x' = t;"][..],
            "initial c = 0;",
        ),
        (
            &["initial c = 0;", "Counter.f = c*.a();", "x' = t;"],
            "initial c = 0;",
        ),
        (
            &["initial c = 0;", "initial y = c*.a();", "y' = y + 1;"],
            "initial c = 0;",
        ),
        (
            &[
                "initial c = 0 with carryForward;",
                "f() = c*.a();",
                "x' = t;",
            ],
            "initial c = 0 with carryForward;",
        ),
    ] {
        let src = t_loop(body);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::InitialNotUpdated), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], site, "{src}");
    }
    // A `*.` call in a function body beside one on some paths of the step: only the step's
    // counts, so the variable is updated on some paths only.
    let src = t_loop(&[
        "initial c = 0;",
        "f() = c*.a();",
        "x' = if t > 1 { c*.b() } else { 0 };",
    ]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
    assert_eq!(&src[e.span.start..e.span.end], "c*.b", "{src}");
    // A `*.` call in an `initial` value on a name defined before the loop does not make that
    // name a variable of the loop, so the value reads no name of the loop here.
    accepted(&format!(
        "c = 0;\n{}",
        t_loop(&["initial y = c*.a();", "y' = y + 1;"])
    ));
}

/// A `*.` call on an entry, `grid[i]*.relax()`, writes `grid'[i]` and so updates `grid`
/// (sec:generations, "the receiver … may be any keypath the one-writer rule accepts, entries
/// included"). As the whole value of an indexed definition it writes `grid'[i]` for each key, as
/// the indexed definition `grid'[i in cells] = relax(grid[i])` does, so it updates `grid` on
/// every path through the statement.
#[test]
fn an_update_of_an_entry_counts() {
    for body in [
        &["initial grid = 0;", "old[i in 0..<4] = grid[i]*.relax();"][..],
        &["initial grid = 0;", "grid[0]*.relax();"],
        &["initial grid = 0;", "x' = grid[0][1]*.relax();"],
        &["initial grid = 0;", "grid'[i in 0..<4] = grid[i] + 1;"],
        &[
            "initial grid = 0;",
            "x' = if t > 1 { grid[0]*.relax() } else { grid[1]*.relax() };",
        ],
    ] {
        accepted(&t_loop(body));
    }
    for (update, at, part) in [
        (
            "x' = if t > 1 { grid[0]*.relax() } else { 0 };",
            "grid[0]*.relax",
            "a branch of the `if`",
        ),
        // In a part of the value, the call runs on some keys' paths only.
        (
            "old[i in 0..<4] = if i > 1 { grid[i]*.relax() } else { 0 };",
            "grid[i]*.relax",
            "a branch of the `if`",
        ),
    ] {
        let src = t_loop(&["initial grid = 0;", update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], at, "{src}");
        assert!(
            e.notes.iter().any(
                |n| n.text == format!("`{at}` updates `grid` only on the paths through {part}")
            ),
            "{src}: {e:?}"
        );
        accepted(&t_loop(&["initial grid = 0 with carryForward;", update]));
    }
}

/// A `*.` call on a field path, `p.pos*.m()`, or on a path of fields and entries,
/// `p.items[i]*.m()` or `grid[i].pos*.m()`, updates the variable the path starts at
/// (sec:generations). As the whole value of an indexed definition, a path with an entry on it
/// updates its variable key by key, on every path through the statement; a path of fields only
/// writes the same place once for each key, and counts on some paths only.
#[test]
fn an_update_of_a_field_counts() {
    for body in [
        &["initial p = 0;", "p.pos*.m();"][..],
        &["initial p = 0;", "x' = p?.pos*.m();"],
        &["initial p = 0;", "x' = p.items[0]*.m();"],
        &["initial p = 0;", "x' = p.a.b[0].c[1]*.m();"],
        &["initial grid = 0;", "grid[0].pos*.m();"],
        &[
            "initial grid = 0;",
            "old[i in 0..<4] = grid[i].pos*.relax();",
        ],
        &["initial p = 0;", "old[i in 0..<4] = p.items[i]*.relax();"],
        &[
            "initial p = 0;",
            "x' = if t > 1 { p.pos*.m() } else { p.items[1]*.m() };",
        ],
    ] {
        accepted(&t_loop(body));
    }
    for (update, at, part) in [
        (
            "x' = if t > 1 { p.pos*.m() } else { 0 };",
            "p.pos*.m",
            "a branch of the `if`",
        ),
        (
            "x' = if t > 1 { p.items[0]*.m() } else { 0 };",
            "p.items[0]*.m",
            "a branch of the `if`",
        ),
        (
            "x' = if t > 1 { p[0].pos*.m() } else { 0 };",
            "p[0].pos*.m",
            "a branch of the `if`",
        ),
        (
            "old[i in 0..<4] = p.pos*.relax();",
            "p.pos*.relax",
            "the value of the indexed definition",
        ),
    ] {
        let src = t_loop(&["initial p = 0;", update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], at, "{src}");
        assert!(
            e.notes
                .iter()
                .any(|n| n.text == format!("`{at}` updates `p` only on the paths through {part}")),
            "{src}: {e:?}"
        );
        accepted(&t_loop(&["initial p = 0 with carryForward;", update]));
    }
}

/// The name of an imported unit, `shapes` after `import geometry.shapes;` or `g` after `import
/// geometry.shapes as g;`, is no variable: a `*.` call on a path it starts, `shapes.origin*.m()`,
/// updates no variable of the loop. A name the text binds otherwise is a variable, even when an
/// import also spells it, and so is a name an `import a.{x}` binds.
#[test]
fn a_qualified_name_is_no_receiver() {
    let branch = "x' = if t > 1 { shapes.origin*.m() } else { 0 };";
    for src in [
        format!("import geometry.shapes;\n{}", t_loop(&[branch])),
        format!(
            "import geometry.shapes as g;\n{}",
            t_loop(&["x' = if t > 1 { g.origin*.m() } else { 0 };"])
        ),
        format!(
            "import geometry.shapes;\n{}",
            t_loop(&["x' = if t > 1 { shapes.origin.corner*.m() } else { 0 };"])
        ),
    ] {
        // The unit is built and checked; `accepted` would also load the imported unit, which
        // these tests do not have.
        let tokens = lex(&src).unwrap();
        let tree = parse(&src, &tokens, "Unit", TOP).unwrap();
        if let Err(e) = unit(&src, &tokens, &tree) {
            panic!("refused: {src}\n{e:?}");
        }
    }
    for src in [
        format!(
            "import geometry.shapes;\n{}",
            t_loop(&["initial shapes = 0;", branch])
        ),
        format!("import geometry.{{shapes}};\n{}", t_loop(&[branch])),
        format!(
            "import geometry.shapes;\nf(shapes) = 0;\n{}",
            t_loop(&[branch])
        ),
        format!("import geometry.shapes as g;\n{}", t_loop(&[branch])),
        t_loop(&[branch]),
    ] {
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}: {e:?}");
        assert_eq!(&src[e.span.start..e.span.end], "shapes.origin*.m", "{src}");
    }
}

/// The rule notes of row "A `mutable` declaration", in a loop and outside one.
const IN_LOOP: &str = "the loop whose body holds the declaration: a variable a loop updates is a \
                       recurrence, defined on every frame, so each step updates it on every \
                       path; one that keeps its value on a step that does not update it is given \
                       its value before step 0 by an `initial` statement with `with \
                       carryForward` [loop]";
const OUTSIDE: &str = "outside the body of a loop a name is bound once, with no `mutable`; in a \
                       loop, a variable that keeps its value on a step that does not update it \
                       is given its value before step 0 by an `initial` statement with `with \
                       carryForward`";

/// Row "A `mutable` declaration": in a loop the repair carries the value forward; outside one it
/// is a plain binding.
#[test]
fn a_mutable_declaration_is_refused() {
    refused(
        &t_loop(&["mutable c = 0;", "c' = c + 1;"]),
        Row::MutableDeclaration,
        "mutable c = 0;",
        Some(
            "Zed has no `mutable`: `mutable c = 0;`. Try `initial c = 0 with carryForward;` instead.",
        ),
        &[
            IN_LOOP,
            "repair: `initial c = 0 with carryForward;`, its value before step 0, carried \
             forward on a step that does not update `c` [mutable c = 0;]",
        ],
        &[&t_loop(&[
            "initial c = 0 with carryForward;",
            "c' = c + 1;",
        ])],
    );
    refused(
        &t_loop(&["local mutable c: int = 0;", "c' = c + 1;"]),
        Row::MutableDeclaration,
        "local mutable c: int = 0;",
        None,
        &[
            IN_LOOP,
            "repair: `initial c: int = 0 with carryForward;`, its value before step 0, carried \
             forward on a step that does not update `c`, with `local` moved to the update of \
             `c`, `local c' = …;` [local mutable c: int = 0;]",
        ],
        &[&t_loop(&[
            "initial c: int = 0 with carryForward;",
            "local c' = c + 1;",
        ])],
    );
    refused(
        "mutable c = 0;\n",
        Row::MutableDeclaration,
        "mutable c = 0;",
        Some("Zed has no `mutable`: `mutable c = 0;`. Try `c = 0;` instead."),
        &[
            &format!("{OUTSIDE} [mutable c = 0;]"),
            "repair: `c = 0;`, a plain binding [mutable c = 0;]",
        ],
        &["c = 0;\n"],
    );
    refused(
        "f(x) = {\n  mutable a, b = (x, 1);\n  a + b\n};\n",
        Row::MutableDeclaration,
        "mutable a, b = (x, 1);",
        None,
        &[
            &format!("{OUTSIDE} [mutable a, b = (x, 1);]"),
            "repair: `a, b = (x, 1);`, a plain binding [mutable a, b = (x, 1);]",
        ],
        &["f(x) = {\n  a, b = (x, 1);\n  a + b\n};\n"],
    );
}

/// The note of row "A word other than `carryForward` after `with` at the end of an `initial`
/// statement": it keeps `named`, `them` being the pronoun for them, shows the facet form `with
/// word(…)`, and points at the text `at`.
fn carry_note(named: &str, them: &str, word: &str, at: &str) -> String {
    format!(
        "`carryForward` is the one word that stands alone after `with` at the end of an \
         `initial` statement, and keeps {named} on a step that does not update {them}; a facet \
         after `with` takes its arguments in parentheses, as `with {word}(…)` [{at}]"
    )
}

/// Row "A word other than `carryForward` after `with` at the end of an `initial` statement":
/// any word there, close to `carryForward` in spelling or not, and several words, are refused
/// with the statement rewritten with `carryForward` as the repair; the word there is read as a
/// facet missing its parentheses, so the plain parser message was "expected '('".
#[test]
fn a_word_other_than_carry_forward_is_refused() {
    let carried = t_loop(&["initial c = 0 with carryForward;", "c' = c + 1;"]);
    for word in ["carry", "carryforward", "carry_forward", "keep", "mutable"] {
        let stmt = format!("initial c = 0 with {word};");
        refused(
            &t_loop(&[&stmt, "c' = c + 1;"]),
            Row::CarryWord,
            &stmt,
            Some(&format!(
                "Expected `carryForward` after `with`: `{stmt}`. Try `initial c = 0 with \
                 carryForward;` instead."
            )),
            &[
                &carry_note("the value of `c`", "it", word, word),
                &format!(
                    "repair: `initial c = 0 with carryForward;`, `carryForward` in place of \
                     `{word}` [{stmt}]"
                ),
            ],
            &[&carried],
        );
    }
    // Several words, and several names.
    refused(
        &t_loop(&[
            "initial a, b = (0, 1) with carry forward;",
            "a', b' = (b, a + b);",
        ]),
        Row::CarryWord,
        "initial a, b = (0, 1) with carry forward;",
        Some(
            "Expected `carryForward` after `with`: `initial a, b = (0, 1) with carry \
             forward;`. Try `initial a, b = (0, 1) with carryForward;` instead.",
        ),
        &[
            &carry_note(
                "the values of `a` and `b`",
                "them",
                "carry",
                "carry forward",
            ),
            "repair: `initial a, b = (0, 1) with carryForward;`, `carryForward` in \
             place of `carry forward` [initial a, b = (0, 1) with carry forward;]",
        ],
        &[&t_loop(&[
            "initial a, b = (0, 1) with carryForward;",
            "a', b' = (b, a + b);",
        ])],
    );
    // A declared type is kept in the repair, and the note names the one variable.
    let src = t_loop(&["initial c: int = 0 with carry;", "c' = c + 1;"]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::CarryWord), "{e:?}");
    assert_eq!(
        e.message,
        "Expected `carryForward` after `with`: `initial c: int = 0 with carry;`. Try `initial c: \
         int = 0 with carryForward;` instead."
    );
    assert_eq!(
        notes(&src, &e)[0],
        carry_note("the value of `c`", "it", "carry", "carry")
    );
    // The name of a facet, written without its arguments, gets the same message: the note
    // shows the facet's form with them.
    let e = refusal(&t_loop(&["initial c = 0 with units;", "c' = c + 1;"]));
    assert_eq!(e.row, Some(Row::CarryWord), "{e:?}");
    assert_eq!(
        e.message,
        "Expected `carryForward` after `with`: `initial c = 0 with units;`. Try `initial c = 0 \
         with carryForward;` instead."
    );
}

/// The contrast cases of row "A word other than `carryForward` after `with` at the end of an
/// `initial` statement": `carryForward` itself is accepted, and a word after `with` that is not
/// at the end of an `initial` statement keeps the parser's own message.
#[test]
fn a_word_after_with_elsewhere_keeps_the_parser_message() {
    accepted(&t_loop(&[
        "initial c = 0 with carryForward;",
        "c' = c + 1;",
    ]));
    for text in [
        // On a binding, not an `initial` statement.
        "c = 0 with carry;\n",
        &t_loop(&["c' = c + 1 with carry;"]),
        // Inside the value, not at the end of the statement.
        &t_loop(&["initial c = f(0 with carry);", "c' = c + 1;"]),
        // `carryForward` written twice: the second `with` is no word.
        &t_loop(&[
            "initial c = 0 with carryForward with carryForward;",
            "c' = c + 1;",
        ]),
    ] {
        let e = refusal(text);
        assert_eq!(e.row, None, "{text}: {e:?}");
        assert!(e.message.starts_with("expected "), "{text}: {e:?}");
    }
}

/// The message for a word after `with` scans the statement and parses the repair once, so a
/// loop of `n` statements whose `initial` value has `n` terms is refused in time of order `n`.
#[test]
fn the_carry_word_message_scales() {
    let units = scaling::inputs(500, |n| {
        let terms: String = (0..n).map(|i| format!(" + {i}")).collect();
        let stmts: String = (0..n).map(|i| format!("x{i}' = {i}; ")).collect();
        format!(
            "r = loop t {{ while t < 9; {stmts}initial c = 0{terms} with carry; c' = c + 1; }};\n"
        )
    });
    scaling::check("a word after `with`", 500, |n| {
        let e = refusal(&units[&n]);
        assert_eq!(e.row, Some(Row::CarryWord), "{e:?}");
    });
}

/// Row "`with carryForward` on a keyed boundary entry", with each repair it offers. Decision:
/// the facet keeps the value of the step before, `x[t-1]`, which at step 0 is the entry `x[-1]`,
/// so it stands on the statement without keys that gives that entry; on a keyed entry it would
/// say nothing that statement does not, or carry from an entry no step reads that way.
#[test]
fn with_carry_forward_on_a_keyed_entry_is_refused() {
    let why = |s: &str| {
        format!(
            "`with carryForward` makes a step that does not update `c` keep `c[t-1]`, which at \
             step 0 is the entry `c[-1]`; the `initial` statement without keys gives that entry, \
             so `with carryForward` stands on it [{s}]"
        )
    };
    // The entry `c[-1]` alone: the statement without keys says the same.
    let at = "initial c[-1] = 0 with carryForward;";
    refused(
        &t_loop(&[at, "c' = c + 1;"]),
        Row::CarryOnKeyedEntry,
        at,
        Some(
            "`with carryForward` on an `initial` statement with keys: `initial c[-1] = 0 with \
             carryForward;`. Try `initial c = 0 with carryForward;` instead.",
        ),
        &[
            &why(at),
            "repair: `initial c = 0 with carryForward;`, the statement without keys, which \
             gives the entry `c[-1]` [initial c[-1] = 0 with carryForward;]",
        ],
        &[&t_loop(&[
            "initial c = 0 with carryForward;",
            "c' = c + 1;",
        ])],
    );
    // An entry below `c[-1]`, with no statement without keys.
    let at = "initial c[-2] = 0 with carryForward;";
    refused(
        &t_loop(&[at, "c' = c + 1;"]),
        Row::CarryOnKeyedEntry,
        at,
        Some(
            "`with carryForward` on an `initial` statement with keys: `initial c[-2] = 0 with \
             carryForward;`. Try `initial c = … with carryForward; initial c[-2] = 0;` instead.",
        ),
        &[
            &why(at),
            "repair: `initial c = … with carryForward; initial c[-2] = 0;`, with the value of \
             `c[-1]` in place of `…` [initial c[-2] = 0 with carryForward;]",
        ],
        &[&t_loop(&[
            "initial c = 1 with carryForward;",
            "initial c[-2] = 0;",
            "c' = c + 1;",
        ])],
    );
    // A statement without keys that does not carry: the facet moves to it.
    let at = "initial c[i in -3..<-1] = 0 with carryForward;";
    refused(
        &t_loop(&["initial c = 1;", at, "c' = c + 1;"]),
        Row::CarryOnKeyedEntry,
        at,
        None,
        &[
            &why(at),
            "repair: `initial c = 1 with carryForward; initial c[i in -3..<-1] = 0;`, `with \
             carryForward` moved to the statement without keys [initial c[i in -3..<-1] = 0 \
             with carryForward;]",
        ],
        &[&t_loop(&[
            "initial c = 1 with carryForward;",
            "initial c[i in -3..<-1] = 0;",
            "c' = c + 1;",
        ])],
    );
    // A statement without keys that carries already: the facet here is deleted.
    let at = "initial c[-2] = 0 with carryForward;";
    refused(
        &t_loop(&["initial c = 1 with carryForward;", at, "c' = c + 1;"]),
        Row::CarryOnKeyedEntry,
        at,
        None,
        &[
            &why(at),
            "repair: `initial c[-2] = 0;`, since `initial c = 1 with carryForward;` already \
             carries `c` forward [initial c[-2] = 0 with carryForward;]",
        ],
        &[&t_loop(&[
            "initial c = 1 with carryForward;",
            "initial c[-2] = 0;",
            "c' = c + 1;",
        ])],
    );
}

/// `with carryForward` on a variable every path updates is accepted: it changes nothing. On a
/// variable no statement updates, it is refused, since a value no step changes is a constant.
#[test]
fn with_carry_forward_needs_an_update() {
    accepted(&t_loop(&[
        "initial c = 0 with carryForward;",
        "c' = c + 1;",
    ]));
    accepted(&t_loop(&["initial c = 0 with carryForward;", "c*.a();"]));
    accepted(&t_loop(&["initial c = 0 with carryForward;", "c' <- t;"]));
    refused(
        &t_loop(&["initial y = 0 with carryForward;", "x' = t;"]),
        Row::InitialNotUpdated,
        "initial y = 0 with carryForward;",
        Some(
            "`initial y = 0 with carryForward;` gives `y` a value before step 0, and no \
             statement of this loop updates `y`: none writes `y' = …`, `y' <- e` or `y*.m(…)`. \
             `with carryForward` keeps the value of a variable the loop updates on a step that \
             does not update it, and does not make `y` a variable of the loop: a value no step \
             changes is a constant, written as a binding before the loop.",
        ),
        &[
            "the loop, none of whose statements updates `y` [loop t { …]",
            "repair: add the update the loop is meant to make, `y' = …;`, to its body [initial y \
             = 0 with carryForward;]",
            "repair: `y = 0;` written before the loop, and `initial y = 0 with carryForward;` \
             deleted, for a value that does not change [loop t { …]",
        ],
        &[
            &t_loop(&["initial y = 0 with carryForward;", "y' = y + 1;", "x' = t;"]),
            &format!("y = 0;\n{}", t_loop(&["x' = t;"])),
        ],
    );
}

/// Row "Two sentinel values for one variable" when one of the two carries: the repair that keeps
/// the other moves `with carryForward` to it, so either repair keeps the carry.
#[test]
fn two_sentinels_keep_the_carry_in_each_repair() {
    let src = t_loop(&[
        "initial x = 1 with carryForward;",
        "x*.a();",
        "initial x = 0;",
    ]);
    refused(
        &src,
        Row::TwoSentinels,
        "initial x = 0;",
        None,
        &[
            "the first site, which gives `x` the value `1` [initial x = 1 with carryForward;]",
            "the second site, which gives `x` the value `0` [initial x = 0;]",
            "repair: keep the first, `initial x = 1 with carryForward;`, and delete this one, \
             `initial x = 0;` [initial x = 0;]",
            "repair: keep the second, `initial x = 0 with carryForward;`, which now carries `x` \
             forward, and delete this one, `initial x = 1 with carryForward;` [initial x = 1 \
             with carryForward;]",
        ],
        &[
            &t_loop(&["initial x = 1 with carryForward;", "x*.a();"]),
            &t_loop(&["x*.a();", "initial x = 0 with carryForward;"]),
        ],
    );
    refused(
        &t_loop(&[
            "initial x = 1;",
            "x' = x + 1;",
            "initial x = 0 with carryForward;",
        ]),
        Row::TwoSentinels,
        "initial x = 0 with carryForward;",
        None,
        &[
            "the first site, which gives `x` the value `1` [initial x = 1;]",
            "the second site, which gives `x` the value `0` [initial x = 0 with carryForward;]",
            "repair: keep the first, `initial x = 1 with carryForward;`, which now carries `x` \
             forward, and delete this one, `initial x = 0 with carryForward;` [initial x = 0 \
             with carryForward;]",
            "repair: keep the second, `initial x = 0 with carryForward;`, and delete this one, \
             `initial x = 1;` [initial x = 1;]",
        ],
        &[
            &t_loop(&["initial x = 1 with carryForward;", "x' = x + 1;"]),
            &t_loop(&["x' = x + 1;", "initial x = 0 with carryForward;"]),
        ],
    );
    // Both carry: each repair keeps one as it is.
    let e = refusal(&t_loop(&[
        "initial x = 1 with carryForward;",
        "x' = x + 1;",
        "initial x = 0 with carryForward;",
    ]));
    assert_eq!(e.row, Some(Row::TwoSentinels));
    assert!(
        e.notes.iter().all(|n| !n.text.contains("now carries")),
        "{e:?}"
    );
}

/// `n` statements `x' = if t > i { ci*.a() } else { break 0 };`, each with its own variable
/// updated on one path and the other ending in `break`, then `tail`.
fn wide(n: usize, tail: &str) -> String {
    let stmts: String = (0..n)
        .map(|i| format!("x{i}' = if t > {i} {{ c{i}*.a() }} else {{ break 0 }}; "))
        .collect();
    format!("r = loop t {{ while t < 9; {stmts}{tail} }};\n")
}

/// [`wide`] with each call on a path of a field and an entry, `c{i}.pos[{i}]*.a()`.
fn fields(n: usize, tail: &str) -> String {
    let stmts: String = (0..n)
        .map(|i| format!("x{i}' = if t > {i} {{ c{i}.pos[{i}]*.a() }} else {{ break 0 }}; "))
        .collect();
    format!("r = loop t {{ while t < 9; {stmts}{tail} }};\n")
}

/// `n` imported units `u{i}` and `n` calls `u{i}.x*.a()`, each in one branch of its own `if`:
/// no call updates a variable of the loop, so the loop is accepted.
fn qualified(n: usize) -> String {
    let imports: String = (0..n).map(|i| format!("import m.u{i};\n")).collect();
    let stmts: String = (0..n)
        .map(|i| format!("x{i}' = if t > {i} {{ u{i}.x*.a() }} else {{ 0 }}; "))
        .collect();
    format!("{imports}r = loop t {{ while t < 9; {stmts} }};\n")
}

/// One `if` whose two branches each update the same `n` variables, then `tail`.
fn branches(n: usize, tail: &str) -> String {
    let calls: String = (0..n).map(|i| format!("c{i}*.a(); ")).collect();
    format!(
        "r = loop t {{ while t < 9; x' = if t > 1 {{ {calls}0 }} else {{ {calls}1 }}; {tail} }};\n"
    )
}

/// `n` nested `if`s, the innermost updating `c` in one branch and every other branch ending in
/// `break`; with `carried`, `c` carries.
fn deep(n: usize, carried: bool) -> String {
    let open = "if t > 1 { ".repeat(n);
    let close = " } else { break 0 }".repeat(n);
    let facet = if carried { " with carryForward" } else { "" };
    format!(
        "r = loop t {{ while t < 9; initial c = 0{facet}; x' = {open}if t > 2 {{ c*.a() }} else \
         {{ 0 }}{close}; }};\n"
    )
}

/// One `if` whose two branches each update the same `n` variables by primed definitions in
/// nested blocks, then `tail`.
fn nested_branches(n: usize, tail: &str) -> String {
    let defs: String = (0..n).map(|i| format!("c{i}' = {i}; ")).collect();
    format!(
        "r = loop t {{ while t < 9; x' = if t > 1 {{ {{ {defs}0 }} }} else {{ {{ {defs}1 }} \
         }}; {tail} }};\n"
    )
}

/// An update of `c` in the innermost of `n` nested blocks, each bound to a name; with
/// `branch`, the innermost update stands in one branch of an `if`.
fn nested_blocks(n: usize, branch: bool) -> String {
    let open: String = (0..n).map(|i| format!("{{ y{i} = ")).collect();
    let close: String = (0..n).rev().map(|i| format!("; y{i} }}")).collect();
    let inner = if branch {
        "if t > 2 { c' = c + 1; 0 } else { 0 }"
    } else {
        "{ c' = c + 1; 0 }"
    };
    format!("r = loop t {{ while t < 9; initial c = 0; x' = {open}{inner}{close}; }};\n")
}

/// The must-assign check is one walk of the body with sets merged smaller into larger, so `n`
/// variables updated each on its own paths, `n` variables updated on both branches of one `if`,
/// directly or in nested blocks, and an update `n` constructs or blocks deep are each checked in
/// time of order `n log n`, accepted or refused. `n` calls on paths of fields and entries, and
/// `n` calls on the names of `n` imported units, which one pass over the tokens lists, are too.
#[test]
fn the_must_assign_check_scales() {
    type Make = fn(usize) -> String;
    let cases: [(&str, Make, Option<Row>); 12] = [
        ("fields, accepted", |n| fields(n, ""), None),
        (
            "fields, refused at the end",
            |n| fields(n, "y' = t > 1 && d.e[0]*.a();"),
            Some(Row::NotEveryPath),
        ),
        ("qualified names, accepted", qualified, None),
        ("wide, accepted", |n| wide(n, ""), None),
        (
            "wide, refused at the end",
            |n| wide(n, "y' = t > 1 && d*.a();"),
            Some(Row::NotEveryPath),
        ),
        ("branches, accepted", |n| branches(n, ""), None),
        ("deep, refused", |n| deep(n, false), Some(Row::NotEveryPath)),
        ("deep, carried", |n| deep(n, true), None),
        (
            "nested branches, accepted",
            |n| nested_branches(n, ""),
            None,
        ),
        (
            "nested branches, refused at the end",
            |n| nested_branches(n, "y' = t > 1 && { d' = 1; true };"),
            Some(Row::NotEveryPath),
        ),
        ("nested blocks, accepted", |n| nested_blocks(n, false), None),
        (
            "nested blocks, refused",
            |n| nested_blocks(n, true),
            Some(Row::NotEveryPath),
        ),
    ];
    for (what, make, row) in cases {
        let units = scaling::inputs(500, |n| {
            let text = make(n);
            let tokens = lex(&text).unwrap();
            let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
            (text, tokens, tree)
        });
        scaling::check(what, 500, |n| {
            let (text, tokens, tree) = &units[&n];
            match (unit(text, tokens, tree), row) {
                (Ok(_), None) => {}
                (Err(e), Some(r)) => assert_eq!(e.row, Some(r), "{what}: {e:?}"),
                (got, _) => panic!("{what}: {:?}", got.err()),
            }
        });
    }
}

/// A struct with methods that update their receiver (`tick`, `add`) and one that reads it
/// (`peek`), for the loops below.
const COUNTER: &str = "struct Counter { n: int }\nCounter.tick() { n' = n + 1; }\nCounter.add(positional by) { n' = n + by; }\nCounter.peek() = n;\n";

/// A unit with [`COUNTER`] and a loop with `initial c = Counter(n: 0);` and the statements
/// `body`.
fn c_loop(body: &[&str]) -> String {
    let mut stmts = vec!["initial c = Counter(n: 0);"];
    stmts.extend(body);
    format!("{COUNTER}{}", t_loop(&stmts))
}

/// Checks that the statements of the unit `text` build. Methods are not compiled by this zedc
/// yet, so a unit with them is checked by building its statements, which is where these rows
/// are produced.
#[track_caller]
fn builds(text: &str) {
    let tokens = lex(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    if let Err(e) = unit(text, &tokens, &tree) {
        panic!("refused: {text}\n{e:?}");
    }
}

/// The note at the loop of row "An `initial` statement in a loop that never updates its
/// variable", for `c`.
const NONE_NOTE: &str = "the loop, none of whose statements updates `c` [loop t { …]";
/// The note at the `initial` statement of `c` when that row stands at a `.` call.
const INITIAL_NOTE: &str = "the `initial` statement of `c`, which gives it a value before step 0 \
                            only [initial c = Counter(n: 0);]";
/// The two repairs that row offers for `c` when no repair with `*.` applies.
const NONE_REPAIRS: [&str; 2] = [
    "repair: add the update the loop is meant to make, `c' = …;`, to its body [initial c = \
     Counter(n: 0);]",
    "repair: `c = Counter(n: 0);` written before the loop, and `initial c = Counter(n: 0);` \
     deleted, for a value that does not change [loop t { …]",
];

/// A `.` call never updates its receiver (DESIGN.md sec:generations, "`.` never mutates"): a
/// loop variable whose only calls are `.` calls of methods that write primes is not updated,
/// and the message, at the first call, names each call and writes the repair with `*.`, the
/// update call, with no repair that would drop the calls.
#[test]
fn a_dot_call_does_not_update_its_receiver() {
    let notes = vec![
        NONE_NOTE,
        INITIAL_NOTE,
        "`c.add(3)` does not update `c`: a `.` call never updates its receiver, and `c*.add(3)` \
         does [c.add(3)]",
        "repair: `c*.add(3);` in place of `c.add(3);` [c.add(3)]",
    ];
    let src = c_loop(&["c.add(3);"]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(&src[e.span.start..e.span.end], "c.add(3)");
    assert_eq!(
        e.message,
        "No statement of this loop updates `c`: `c.add(3)` does not update `c`. Try \
         `c*.add(3);` instead."
    );
    assert_eq!(super::initial::notes(&src, &e), notes);
    builds(&c_loop(&["c*.add(3);"]));
    builds(&c_loop(&["c' = c;", "c.add(3);"]));
    builds(&format!(
        "{COUNTER}c = Counter(n: 0);\n{}",
        t_loop(&["c.add(3);"])
    ));

    // Two calls: both are named, in the order they are written, and one repair rewrites both.
    let src = c_loop(&["c.tick();", "c.add(2);"]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(
        e.message,
        "No statement of this loop updates `c`: `c.tick()` and `c.add(2)` do not update `c`. \
         Try `c*.tick();` and `c*.add(2);` instead."
    );
    assert_eq!(&src[e.span.start..e.span.end], "c.tick()");
    let want = vec![
        NONE_NOTE,
        INITIAL_NOTE,
        "`c.tick()` does not update `c`: a `.` call never updates its receiver, and \
         `c*.tick()` does [c.tick()]",
        "`c.add(2)` does not update `c`: a `.` call never updates its receiver, and \
         `c*.add(2)` does [c.add(2)]",
        "repair: `c*.tick();` in place of `c.tick();` and `c*.add(2);` in place of `c.add(2);` \
         [c.tick()]",
    ];
    assert_eq!(super::initial::notes(&src, &e), want);
    builds(&c_loop(&["c*.tick();", "c*.add(2);"]));

    // A `.` call on a field of the variable: `*.` on the path updates the variable the path
    // starts at, and the method is the one of the field's type, not of the variable's.
    let pos = "struct Pos { x: int }\nPos.shift() { x' = x + 1; }\nstruct P { pos: Pos }\n";
    let src = format!(
        "{pos}{}",
        t_loop(&["initial p = P(pos: Pos(x: 0));", "p.pos.shift();"])
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(
        e.message,
        "No statement of this loop updates `p`: `p.pos.shift()` does not update `p`. Try \
         `p.pos*.shift();` instead."
    );
    builds(&format!(
        "{pos}{}",
        t_loop(&["initial p = P(pos: Pos(x: 0));", "p.pos*.shift();"])
    ));
}

/// A `.` call on some paths only: its note names the part of the step it runs in. When the
/// other paths update the variable, the row is "not updated on every path" and the `*.` repair
/// completes it, the only repair offered; when no other path does, `*.` alone leaves the other
/// paths, so the repair also carries the variable forward.
#[test]
fn a_dot_call_on_some_paths_is_named_with_its_part() {
    let src = c_loop(&["if t > 1 { c*.tick() } else { c.add(2) };"]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::NotEveryPath), "{e:?}");
    assert_eq!(&src[e.span.start..e.span.end], "c*.tick");
    assert_eq!(
        e.message,
        "Not updated on every path of a step: `c*.tick` updates `c` only in a branch of the \
         `if`, and `c.add(2)` does not update `c`. Try `c*.add(2)` instead."
    );
    assert_eq!(
        super::initial::notes(&src, &e),
        [
            LOOP_NOTE,
            "`c*.tick` updates `c` only on the paths through a branch of the `if` [c*.tick]",
            "the `if` that `c*.tick` stands in [if t > 1 { c*.tick() } else { c.add(2) }]",
            "`c.add(2)` does not update `c`: a `.` call never updates its receiver, and \
             `c*.add(2)` does; it runs only on the paths through a branch of the `if` \
             [c.add(2)]",
            "repair: `c*.add(2)` in place of `c.add(2)` [c.add(2)]",
        ]
    );
    builds(&c_loop(&["if t > 1 { c*.tick() } else { c*.add(2) };"]));

    let src = c_loop(&["if t > 1 { c.tick() } else { 0 };"]);
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(
        e.message,
        "No statement of this loop updates `c`: `c.tick()` does not update `c`. Try \
         `c*.tick()` and `initial c = Counter(n: 0) with carryForward;` instead."
    );
    assert_eq!(&src[e.span.start..e.span.end], "c.tick()");
    let want = vec![
        NONE_NOTE,
        INITIAL_NOTE,
        "`c.tick()` does not update `c`: a `.` call never updates its receiver, and \
         `c*.tick()` does; it runs only on the paths through a branch of the `if` [c.tick()]",
        "repair: `c*.tick()` in place of `c.tick()` and `initial c = Counter(n: 0) with \
         carryForward;` in place of `initial c = Counter(n: 0);` [c.tick()]",
    ];
    assert_eq!(super::initial::notes(&src, &e), want);
    let mut carried = c_loop(&["if t > 1 { c*.tick() } else { 0 };"]);
    carried = carried.replace(
        "Counter(n: 0);\n  if",
        "Counter(n: 0) with carryForward;\n  if",
    );
    builds(&carried);
}

/// No `*.` repair where `*.` is not the fix: a `*.` call already written, a method that writes
/// no primes and so has no `*.` form, a method the unit does not declare, and a call whose
/// value is used, where `*.` would change the value.
#[test]
fn a_dot_call_gets_the_update_repair_only_where_it_applies() {
    builds(&c_loop(&["c*.add(3);"]));
    builds(&c_loop(&["c*.tick();", "x' = c.peek();"]));
    let old = "`initial c = Counter(n: 0);` gives `c` a value before step 0, and no statement \
               of this loop updates `c`: none writes `c' = …`, `c' <- e` or `c*.m(…)`. An \
               `initial` statement gives a value before the first step only, so `c` would have \
               no value at any later step.";
    for body in [
        "c.peek();",
        "c.zap();",
        "x' = if t > 1 { c.tick() } else { c };",
        "x' = c.add(1).n;",
    ] {
        let src = c_loop(&[body]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::InitialNotUpdated), "{body}: {e:?}");
        assert_eq!(e.message, old, "{body}");
        let mut want = vec![NONE_NOTE];
        want.extend(NONE_REPAIRS);
        assert_eq!(super::initial::notes(&src, &e), want, "{body}");
    }
}

/// The method a `.` call names is looked up among the methods the unit declares. Of two
/// methods of one name on different types, the one of the variable's type is taken when its
/// `initial` statement shows the type; otherwise they must agree. A method the unit does not
/// declare, as one of an imported unit or the prelude, gives no `*.` repair: the rows are
/// produced when the unit is built, before its imports are read; a method the unit declares is
/// taken even when the unit imports another.
#[test]
fn a_dot_call_finds_its_method_in_the_unit() {
    let other = "struct Other { n: int }\nOther.tick() = n;\n";
    // `Counter.tick` writes a prime and `Other.tick` does not: the variable's type decides.
    let src = format!(
        "{COUNTER}{other}{}",
        t_loop(&["initial c = Counter(n: 0);", "c.tick();"])
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(
        e.message,
        "No statement of this loop updates `c`: `c.tick()` does not update `c`. Try \
         `c*.tick();` instead."
    );
    let old = "`initial c = make();` gives `c` a value before step 0, and no statement of this \
               loop updates `c`: none writes `c' = …`, `c' <- e` or `c*.m(…)`. An `initial` \
               statement gives a value before the first step only, so `c` would have no value \
               at any later step.";
    // The type is not shown, and the two methods disagree: no `*.` repair, and the older two.
    let src = format!(
        "{COUNTER}{other}make() = Counter(n: 0);\n{}",
        t_loop(&["initial c = make();", "c.tick();"])
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(e.message, old);
    assert_eq!(&src[e.span.start..e.span.end], "initial c = make();");
    assert_eq!(e.notes.len(), 3, "{e:?}");

    // A method of an imported unit is not known when the unit is built.
    let src = format!(
        "import geometry.counters;\n{}",
        t_loop(&["initial c = make();", "c.bump(1);"])
    );
    let e = refusal(&src);
    assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
    assert_eq!(e.message, old);
    // The unit's own `Counter.tick` is taken beside an import.
    let src = format!(
        "import geometry.counters;\n{COUNTER}{}",
        t_loop(&["initial c = Counter(n: 0);", "c.tick();"])
    );
    let e = refusal(&src);
    assert_eq!(&src[e.span.start..e.span.end], "c.tick()");
    assert_eq!(
        e.message,
        "No statement of this loop updates `c`: `c.tick()` does not update `c`. Try \
         `c*.tick();` instead."
    );
}

/// `n` methods that each write a prime and `n` statements, each a `.` call of one of them.
fn dot_calls(n: usize) -> String {
    let methods: String = (0..n)
        .map(|i| format!("Counter.m{i}() {{ n' = n + {i}; }}\n"))
        .collect();
    let calls: String = (0..n).map(|i| format!("c.m{i}(); ")).collect();
    format!(
        "struct Counter {{ n: int }}\n{methods}r = loop t {{ while t < 9; initial c = Counter(n: \
         0); {calls}}};\n"
    )
}

/// The `.` call notes cost one walk of the method declarations, one lookup per call and one
/// more walk of the step for the repair: `n` methods and `n` calls of them are refused in time
/// of order `n log n`.
#[test]
fn the_dot_call_notes_scale() {
    let units = scaling::inputs(500, |n| {
        let text = dot_calls(n);
        let tokens = lex(&text).unwrap();
        let tree = parse(&text, &tokens, "Unit", TOP).unwrap();
        (text, tokens, tree)
    });
    scaling::check("dot calls, refused", 500, |n| {
        let (text, tokens, tree) = &units[&n];
        let e = unit(text, tokens, tree).unwrap_err();
        assert_eq!(e.row, Some(Row::InitialNotUpdated), "{e:?}");
        // The loop, the `initial` statement, one note per call and the one repair.
        assert_eq!(e.notes.len(), n + 3, "{e:?}");
    });
}
