//! Output ports passed to functions (DESIGN.md L1.19): "a function other than `main` takes a
//! port as an argument", `say(positional s, out: Lines) { out <- s; }` called as
//! `say("hi", out: m.stdout)`, "and the port's direction is the field's". Passing an output
//! port whole to a parameter the function pushes to is no read of the port; every other use of
//! an output port reads it and is rejected.

use zed_tests::deep::resolved;
use zed_tests::oracle;
use zedc::check::ports::ports;
use zedc::check::walk::check_text;
use zedc::resolve::tables::Tables;

use super::run;

/// The helper of the L1.19 example and a `main` that gives it `call`.
fn with_say(call: &str) -> String {
    format!("say(positional s, out: Lines) {{ out <- s; }}\n\nmain(m: MainArgs) {{\n  {call}\n}}\n")
}

/// The first line `zedc run` writes to standard error for `src`, which it rejects.
fn rejected(name: &str, src: &str) -> String {
    let out = run(name, src, "", &[]);
    assert_eq!((out.status, out.stdout.as_str()), (1, ""), "{}", out.stderr);
    let first = out.stderr.lines().next().unwrap_or_default();
    // Each message starts with the path of the program and the place.
    first
        .split_once(".zed:")
        .map_or(first, |(_, m)| m)
        .to_string()
}

/// Red before green: zedc rejected the example's call as a read of `m.stdout`, "`m.stdout` is
/// read here, and `m.stdout` is an output of the program".
#[test]
fn the_example_of_l1_19_writes_through_the_port_it_is_given() {
    let out = run("say", &with_say("_ = say(\"hi\", out: m.stdout);"), "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hi\n", "")
    );
    let out = run(
        "say_err",
        &with_say("_ = say(\"oops\", out: m.stderr);"),
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "", "oops\n")
    );
}

/// Red before green: zedc refused every expression statement as a form of layer L6, so the
/// example of L1.19 had to be written `_ = say("hi", out: m.stdout);`. A call in statement
/// position that pushes to a port is a statement (DESIGN.md sec:tour_methods, "a call in
/// statement position is legal when it writes a generation (`c*.tick()`) or a port").
#[test]
fn a_call_that_pushes_to_a_port_is_a_statement() {
    let out = run(
        "say_stmt",
        &with_say("say(\"hi\", out: m.stdout);"),
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hi\n", "")
    );
    // Beside a push of `main` to the other output, in a helper's block body, and on each
    // branch of an `if`.
    let src = "say(positional s, out: Lines) { out <- s; }\n\
               shout(positional s, out: Lines) { say(s ++ \"!\", out: out); }\n\
               main(m: MainArgs) {\n  shout(\"hi\", out: m.stdout);\n  m.stderr <- \"e\";\n}\n";
    let out = run("stmt_block_body", src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "hi!\n", "e\n")
    );
    let branches = "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  \
                    if k > 1 { say(\"many\", out: m.stdout); } else { say(\"one\", out: m.stdout); };";
    let out = run("stmt_branches", &with_say(branches), "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "one\n"),
        "{}",
        out.stderr
    );
    let out = run("stmt_branches_args", &with_say(branches), "", &["--", "5"]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "many\n"),
        "{}",
        out.stderr
    );
}

/// The contrast: a call in statement position that writes to no port is refused, on any path,
/// and so is one that drops the result of a function that pushes (DESIGN.md sec:diagnostics,
/// "Statement that writes nothing, or drops a declared result").
#[test]
fn a_statement_that_writes_nothing_or_drops_a_result_is_refused() {
    let src =
        "f(positional x: int) = x + 1;\n\nmain(m: MainArgs) {\n  f(1);\n  m.stdout <- \"x\";\n}\n";
    assert_eq!(
        rejected("stmt_pure", src),
        "4:3: Statement has no effect: `f(1)` writes to no port, and its value is dropped."
    );
    // An arm of an `if` statement ends with a statement, so a value there is refused by the
    // parser, named (author, P348).
    let branch = "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  \
                  if k > 1 { say(\"many\", out: m.stdout); } else { 0 };";
    assert_eq!(
        rejected("stmt_one_branch", &with_say(branch)),
        "5:51: Value at the end of an arm of an `if` statement: `0`."
    );
    let src = "bump(positional s, out: Lines) { out <- s; 3 }\n\n\
               main(m: MainArgs) {\n  bump(\"hi\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("stmt_result", src),
        "4:3: Result of `bump` is unused: `bump(\"hi\", out: m.stdout) : 3`. Try \
         `_ = bump(\"hi\", out: m.stdout);` instead."
    );
    // The repair the headline offers runs.
    let src = src.replace("  bump(", "  _ = bump(");
    let out = run("stmt_result_dropped", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "hi\n"),
        "{}",
        out.stderr
    );
    // A loose failure is dropped only where the text names it: `e else #a -> d;` drops only
    // `d`, so it stands when every other member of `e` is a loose failure (DESIGN.md
    // sec:tour_methods).
    let full = "full(positional s, out: Lines) { out <- s; #full }\n\n\
                main(m: MainArgs) {\n  full(\"hi\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("stmt_loose", full),
        "4:3: Result of `full` is unused: `full(\"hi\", out: m.stdout) : #full`. Try \
         `_ = full(\"hi\", out: m.stdout) else #full -> #ok;` instead."
    );
    for (name, repaired) in [
        (
            "stmt_loose_else",
            "  full(\"hi\", out: m.stdout) else #full -> #ok;",
        ),
        (
            "stmt_loose_dropped",
            "  _ = full(\"hi\", out: m.stdout) else #full -> #ok;",
        ),
    ] {
        let src = full.replace("  full(\"hi\", out: m.stdout);", repaired);
        let out = run(name, &src, "", &[]);
        assert_eq!(
            (out.status, out.stdout.as_str()),
            (0, "hi\n"),
            "{src}\n{}",
            out.stderr
        );
    }
}

/// The notes of a statement that writes nothing: why, at the call, and the repairs.
#[test]
fn a_statement_that_writes_nothing_names_the_call_and_the_repairs() {
    let text =
        "f(positional x: int) = x + 1;\nmain(m: MainArgs) {\n  f(1);\n  m.stdout <- \"x\";\n}\n";
    let (stmts, res) = resolved(text);
    let info = check_text(&stmts, &res, Some(text));
    assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    let e = &info.errors[0];
    assert_eq!(e.row, Some(zedc::rejection::Row::WritesNothing));
    assert_eq!(&text[e.span.start..e.span.end], "f(1);");
    let notes: Vec<(&str, &str)> = (e.notes.iter())
        .map(|n| (&*n.text, &text[n.span.start..n.span.end]))
        .collect();
    assert_eq!(
        notes,
        [
            (
                "`f` has no output port parameter, so `f(1)` writes to no port",
                "f(1)"
            ),
            (
                "repair: delete the statement, which changes nothing the program gives",
                "f(1)"
            ),
            (
                "repair: bind the value to a name, and use the name, as `… = f(1);`",
                "f(1)"
            ),
        ]
    );
}

/// Row FAIL-push-twice-old-benches: a checker given no source text (as the benchmarks' helpers
/// call it) cannot quote the two pushes, so the headline says "twice in one run" and leaves
/// the pushes to the note at the first one and to the error's own place. Before, the sentence
/// kept its words for the quotes, "twice in one run: by and then by".
#[test]
fn two_pushes_checked_without_the_source_text_are_named_by_their_places() {
    let text = "main(m: MainArgs) {\n  m.stdout <- \"a\";\n  m.stdout <- \"b\";\n}\n";
    let (stmts, res) = resolved(text);
    let info = check_text(&stmts, &res, None);
    assert_eq!(info.errors.len(), 1, "{:?}", info.errors);
    let e = &info.errors[0];
    assert_eq!(
        e.message,
        "`m.stdout` may be pushed to twice in one run, and a port takes one push per run, \
         which holds everything it writes."
    );
    assert_eq!(&text[e.span.start..e.span.end], "m.stdout <- \"b\";");
    let first = &e.notes[0];
    assert_eq!(&*first.text, "the first push to `m.stdout`");
    assert_eq!(
        &text[first.span.start..first.span.end],
        "m.stdout <- \"a\";"
    );
}

/// The errors the checker gives `main`'s body `body`, after the helper `say` of L1.19 and a
/// `k` read from the arguments: each its message, the statement it is reported at, and the
/// text each note is placed at.
fn statement_errors(body: &str) -> Vec<(String, String, Vec<String>)> {
    let text = format!(
        "say(positional s, out: Lines) {{ out <- s; }}\n\nmain(m: MainArgs) {{\n  \
         k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  {body}\n}}\n"
    );
    let (stmts, res) = resolved(&text);
    let info = check_text(&stmts, &res, Some(&text));
    let at = |s: zedc::lex::Span| text[s.start..s.end].to_string();
    (info.errors.iter())
        .map(|e| {
            assert_eq!(e.row, Some(zedc::rejection::Row::WritesNothing), "{e:?}");
            let notes = e.notes.iter().map(|n| at(n.span)).collect();
            (e.message.clone(), at(e.span), notes)
        })
        .collect()
}

/// Red before green: the parser refused every block here that exports nothing, "this block
/// exports nothing, and a block gives a value, so it must export one", and an `if` with no
/// `else`. A block in statement position may export nothing, and writes when one of its
/// statements writes; an `if` statement may leave out its `else`, and its arms end with a
/// statement (author, P348; DESIGN.md sec:tour_methods, "Statement position must write
/// something, and drop nothing"; row FAIL-exprstmt-empty-paths). Each statement here writes
/// when its condition holds and nothing otherwise, run with no argument (`k` is 0) and with 5.
#[test]
fn a_block_with_a_write_on_one_branch_and_no_export_is_a_statement() {
    // A brace in statement position is a block when a statement follows it (sec:grammar,
    // `!HEAD &('{' Item) ~Block`), here `j = k;`.
    for (name, body, none, five) in [
        // The write in the `then` arm only, by a push and by a call.
        (
            "stmt_block_then_push",
            "{ j = k; if j > 1 { m.stdout <- \"x\"; }; };",
            "",
            "x\n",
        ),
        (
            "stmt_then_call",
            "if k > 1 { say(\"x\", out: m.stdout); };",
            "",
            "x\n",
        ),
        // A binding before the statement that ends the arm.
        (
            "stmt_then_binding",
            "if k > 1 { y = \"x\"; m.stdout <- y; };",
            "",
            "x\n",
        ),
        // The write when the condition is false, by the negated condition.
        (
            "stmt_block_else_call",
            "{ j = k; if !(j > 1) { say(\"x\", out: m.stdout); }; };",
            "x\n",
            "",
        ),
        // Nested twice, the `if` with no `else` two blocks down.
        (
            "stmt_block_nested",
            "{ j = k; if j > 1 { if j > 2 { say(\"x\", out: m.stdout); }; } \
             else { say(\"y\", out: m.stdout); }; };",
            "y\n",
            "x\n",
        ),
    ] {
        assert_eq!(statement_errors(body), [], "{body}");
        let src = with_say(&format!(
            "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  {body}"
        ));
        for (args, want) in [(&[][..], none), (&["--", "5"][..], five)] {
            let out = run(name, &src, "", args);
            assert_eq!(
                (out.status, out.stdout.as_str(), out.stderr.as_str()),
                (0, want, ""),
                "{src} {args:?}"
            );
        }
        // The interpreter and the native code (step L1.37) write the same bytes, with `k`
        // read from the first line of standard input.
        let src = with_say(&format!(
            "k = int(m.stdin[0] else #ioError -> \"\" else #outOfBounds -> \"\") else #invalid -> 0;\n  {body}"
        ));
        for input in ["", "5\n"] {
            let ((report, want), _) =
                oracle::native(|engines| oracle::program(&src, input.as_bytes(), engines));
            assert_eq!(report.mismatches, Vec::<String>::new(), "{src} {input:?}");
            assert!(report.compared > 0 && want.is_some(), "{src} {input:?}");
        }
    }
}

/// The contrasts: a statement that writes on no path, an `if` whose arm only binds or a block
/// of bindings, is refused at the statement; an empty `else { }`, an empty `if` and a value at
/// the end of an arm of an `if` statement are refused by the parser (author, P348); and a block
/// in the place of a value still exports one (step L1.11), so `x = if c { } else { 1 };` is
/// refused by the parser, and so is `x = if c { 1 };` (DESIGN.md sec:tour_methods).
#[test]
fn a_statement_whose_paths_write_nothing_or_drop_a_value_is_refused() {
    let none = |stmt: &str| {
        let shown = stmt.strip_suffix(';').unwrap();
        vec![(
            format!("Statement has no effect: `{shown}` writes to no port on any path."),
            stmt.to_string(),
            vec![shown.to_string()],
        )]
    };
    for body in ["if k > 1 { j = k; };", "{ j = k; };"] {
        assert_eq!(statement_errors(body), none(body), "{body}");
    }
    // The `if` is a statement of the block: it is refused itself, and the block counts it as a
    // statement and is not refused again.
    assert_eq!(
        statement_errors("{ j = k; if j > 1 { i = j; }; };"),
        none("if j > 1 { i = j; };")
    );
    let src = with_say(
        "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  if k > 1 { j = k; };",
    );
    assert_eq!(
        rejected("stmt_empty_paths", &src),
        "5:3: Statement has no effect: `if k > 1 { j = k; }` writes to no port on any path."
    );
    for (name, stmt, want) in [
        (
            "stmt_empty_else",
            "if k > 1 { say(\"x\", out: m.stdout); } else { };",
            "5:41: Empty `else { }` in an `if` statement. Leave out the `else`: \
             `if k > 1 { say(\"x\", out: m.stdout); };`.",
        ),
        (
            "stmt_empty_if",
            "if k > 1 { };",
            "5:12: Empty `if` statement: `if k > 1 { };` does nothing. Delete it.",
        ),
        (
            "stmt_arm_call",
            "if k > 1 { say(\"x\", out: m.stdout) };",
            "5:14: Value at the end of an arm of an `if` statement: `say(\"x\", out: m.stdout)`. \
             End the arm with a statement, `say(\"x\", out: m.stdout);`.",
        ),
        (
            "stmt_arm_value",
            "if k > 1 { 1 };",
            "5:14: Value at the end of an arm of an `if` statement: `1`.",
        ),
        (
            "stmt_value_no_else",
            "x = if k > 1 { 1 };\n  m.stdout <- \"a\";",
            "5:21: Missing `else` in an `if` that gives a value: `if k > 1 { 1 }`. An `if` that \
             gives a value has both arms.",
        ),
    ] {
        let src = with_say(&format!(
            "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  {stmt}"
        ));
        assert_eq!(rejected(name, &src), want, "{stmt}");
    }
    let src = with_say(
        "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  x = if k > 1 { } else { 1 };\n  \
         m.stdout <- \"a\";",
    );
    assert_eq!(
        rejected("stmt_value_block_empty", &src),
        "5:16: this `{}` is an empty block, and a block gives a value, so it must export one: a \
         brace after `->`, `else`, or the head of an `if` or a `for` is a block. To write the \
         empty family there, write `{ {} }`, or `({})` after `->` or a fallback's `else`."
    );
}

/// The forms of a write on one branch that a program can write: each branch ends in an export,
/// and the silent one exports a value that writes nothing. The statement is refused at that
/// export, named in the headline and at each note, whichever branch writes, however deep the
/// `if` stands, and whatever the block holds before its export (DESIGN.md sec:tour_methods,
/// "the check is per flow path: each branch of an `if` or `match` and each block's export is
/// checked on its own"; `check::ports::silent_tail`). Each `if` here is the export of a block,
/// so it gives a value and has one expression in each arm; an `if` that is a statement of a
/// block ends each arm with a statement, so a value there is refused by the parser (author,
/// P348; `a_statement_whose_paths_write_nothing_or_drop_a_value_is_refused`).
#[test]
fn a_block_that_writes_on_one_branch_only_is_refused_at_the_silent_branch() {
    let silent = |stmt: &str, branch: &str| {
        let message = format!(
            "Statement has no effect: `{branch}` writes to no port, and its value is dropped."
        );
        vec![(message, stmt.to_string(), vec![branch.to_string(); 3])]
    };
    // The write in the `then` branch only, and in the `else` branch only, of an `if` that a
    // block exports.
    let body = "{ j = k; if j > 1 { say(\"x\", out: m.stdout) } else { 0 } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    let body = "{ j = k; if j > 1 { 0 } else { say(\"x\", out: m.stdout) } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    // A write in a statement of the silent branch's block does not make its export write.
    let body = "{ j = k; if j > 1 { say(\"x\", out: m.stdout) } else { m.stdout <- \"y\"; 0 } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    // Nested twice: the silent branch is the inner `if`'s, two blocks down; the outer `if`
    // writes on its other branch.
    let body = "{ j = k; if j > 1 { if j > 2 { say(\"x\", out: m.stdout) } else { 0 } } \
                else { say(\"y\", out: m.stdout) } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    let body = "{ j = k; if j > 1 { say(\"y\", out: m.stdout) } \
                else { if j > 2 { 0 } else { say(\"x\", out: m.stdout) } } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    // A write before the `if` does not make its silent branch write.
    let body = "{ say(\"a\", out: m.stderr); if k > 1 { say(\"x\", out: m.stdout) } else { 0 } };";
    assert_eq!(statement_errors(body), silent(body, "0"));
    // The same through `zedc run`: refused, placed at the statement.
    let src = with_say(
        "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  \
         { j = k; if j > 1 { if j > 2 { say(\"x\", out: m.stdout) } else { 0 } } \
         else { say(\"y\", out: m.stdout) } };",
    );
    assert_eq!(
        rejected("stmt_block_nested_value", &src),
        "5:3: Statement has no effect: `0` writes to no port, and its value is dropped."
    );
}

/// The contrast: a block whose `if` writes on both branches, at any depth, writes on every
/// path, and stands as a statement.
#[test]
fn a_block_that_writes_on_both_branches_is_a_statement() {
    for body in [
        "{ j = k; if j > 1 { say(\"many\", out: m.stdout) } else { say(\"one\", out: m.stdout) } };",
        "{ j = k; if j > 1 { m.stdout <- \"many\"; say(\"\", out: m.stderr) } \
         else { say(\"one\", out: m.stdout) } };",
        "{ j = k; if j > 1 { if j > 2 { say(\"many\", out: m.stdout) } else \
         { say(\"many\", out: m.stdout) } } else { say(\"one\", out: m.stdout) } };",
    ] {
        assert_eq!(statement_errors(body), [], "{body}");
        let src = with_say(&format!(
            "k = int(m.args[0] else #outOfBounds -> \"\") else #invalid -> 0;\n  {body}"
        ));
        for (args, want) in [(&[][..], "one\n"), (&["--", "5"][..], "many\n")] {
            let out = run("stmt_block_both", &src, "", args);
            assert_eq!(
                (out.status, out.stdout.as_str()),
                (0, want),
                "{src}\n{}",
                out.stderr
            );
        }
    }
}

/// The port reaches the push whatever the path: through a chain of helpers, by position, in
/// parentheses, from a lambda in the helper, beside a push of `main` to the other output.
#[test]
fn a_port_reaches_the_push_by_any_path() {
    let src = "say(positional s, out: Lines) { out <- s; }\n\
               shout(positional s, out: Lines) = say(s ++ \"!\", out: out);\n\
               main(m: MainArgs) {\n  _ = shout(\"hi\", out: m.stdout);\n}\n";
    assert_eq!(run("chain", src, "", &[]).stdout, "hi!\n");
    let src = "say(positional out: Lines, positional s) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(m.stdout, \"pos\");\n}\n";
    assert_eq!(run("positional", src, "", &[]).stdout, "pos\n");
    let out = run(
        "group",
        &with_say("_ = say(\"g\", out: ((m.stdout)));"),
        "",
        &[],
    );
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "g\n"),
        "{}",
        out.stderr
    );
    let src = "say(positional s, out: Lines) {\n  g = x -> { out <- x; 0 };\n  g(s)\n}\n\
               main(m: MainArgs) {\n  _ = say(\"lam\", out: m.stdout);\n}\n";
    assert_eq!(run("lambda", src, "", &[]).stdout, "lam\n");
    let src = with_say("_ = say(\"a\", out: m.stderr);\n  m.stdout <- \"b\";");
    let out = run("both", &src, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "b\n", "a\n")
    );
    // A helper that is never called is checked and costs nothing.
    let src = with_say("m.stdout <- \"b\";");
    assert_eq!(run("uncalled", &src, "", &[]).stdout, "b\n");
}

/// The contrast: a use of an output port other than as a whole argument of a parameter that
/// is pushed to reads the port, and is rejected as before.
#[test]
fn a_read_of_an_output_port_is_still_rejected() {
    let read = "`m.stdout` is read here, and `m.stdout` is an output of the program";
    for (name, call) in [
        (
            "index",
            "x = m.stdout[0] else #ioError -> \"\" else #outOfBounds -> \"\";\n  m.stderr <- x;",
        ),
        ("bind", "x = m.stdout;\n  m.stderr <- \"z\";"),
        (
            "inside",
            "_ = say(m.stdout[0] else #ioError -> \"\" else #outOfBounds -> \"\", out: m.stderr);",
        ),
    ] {
        let got = rejected(name, &with_say(call));
        assert!(got.contains(read), "{name}: {got}");
    }
    // Passed whole, but to a function that reads it, or to no declared function.
    let src = "count(positional s, out: Lines) = out[0] else #ioError -> \"\" else #outOfBounds -> \"\";\n\
               main(m: MainArgs) {\n  _ = count(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("reads", src),
        "3:23: `m.stdout` is an output port, pushed to and never read, and `count` reads `out`: \
         `count(\"x\", out: m.stdout)`."
    );
    let src = "main(m: MainArgs) {\n  n = len(m.stdout);\n  m.stderr <- \"x\";\n}\n";
    assert_eq!(
        rejected("prelude", src),
        "2:11: `m.stdout` is an output port, pushed to and never read, and it is read here: \
         `m.stdout`."
    );
    let src = "main(m: MainArgs) {\n  f = o -> 0;\n  n = f(m.stdout);\n  m.stderr <- \"x\";\n}\n";
    assert!(rejected("value", src).starts_with("3:9: `m.stdout` is an output port"));
    // A helper that pushes to its parameter and reads it.
    let src = "say(positional s, out: Lines) { out <- s; return out[0] else #ioError -> \"\" else #outOfBounds -> \"\"; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("push_read", src),
        "1:50: `out` is an output port, pushed to and never read, and it is read here: `out`."
    );
}

/// What a parameter that is pushed to requires: an output port at every call, the declared
/// type `Lines`, no default, `[]` in a test key, and calls by name only.
#[test]
fn a_parameter_pushed_to_takes_an_output_port_at_each_call() {
    assert_eq!(
        rejected("stdin", &with_say("_ = say(\"x\", out: m.stdin);")),
        "4:21: `say` pushes to `out`, so `out` takes an output port: `say(\"x\", out: m.stdin)`. \
         Try `say(\"x\", out: m.stdout)` instead."
    );
    let src = "say(positional s, out) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    let out = run("untyped_out_parameter", src, "", &[]);
    assert!(
        out.stderr.contains(
            "1:26: Invalid push to `out`, a parameter of `say` not declared `Lines`. Try `out: \
             Lines` instead."
        ),
        "{}",
        out.stderr
    );
    // The one error: the call is checked as a call of a function that pushes to `out`.
    assert_eq!(out.stderr.matches(".zed:").count(), 1, "{}", out.stderr);
    let src = "say(positional s, out: Lines = 1) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", out: m.stdout);\n}\n";
    assert_eq!(
        rejected("default_out_parameter", src),
        "1:32: An output port has no default: `out` of `say`, which it pushes to."
    );
    let src = "say(positional s, positional out: Lines) { out <- s; 0 } test { (\"a\", 1) -> 0 }\n\
               main(m: MainArgs) {\n  _ = say(\"x\", m.stdout);\n}\n";
    // A test table gives the port as `[]` (DESIGN.md sec:ports, "A test table gives a port its
    // values"); the rows that do are in `a_test_table_gives_a_port_its_values`.
    assert_eq!(
        rejected("table", src),
        "1:71: A test key gives the output port `out` of `say` as `[]`, the port before the row \
         pushes to it."
    );
    let src = with_say("g = say;\n  m.stdout <- \"b\";");
    assert_eq!(
        rejected("function_value", &src),
        "4:7: `say` pushes to its parameter `out`, so it is called by name with the port it \
         writes to, and not used as a value: `say`."
    );
    // A value of the wrong type pushed through the parameter is rejected where it is pushed.
    let src = "say(positional s: int, out: Lines) { out <- s; }\n\
               main(m: MainArgs) {\n  _ = say(3, out: m.stdout);\n}\n";
    assert!(
        rejected("int", src).starts_with("1:45: A `Lines` port takes a `String`"),
        "{src}"
    );
}

/// The failures of the rows of `src`, one per row, `None` for a row that passes.
fn row_failures(src: &str) -> Vec<Option<String>> {
    let outcomes = zedc::testing::test(src);
    assert!(outcomes.iter().all(|o| o.not_run.is_none()), "{outcomes:?}");
    outcomes.into_iter().map(|o| o.failure).collect()
}

/// A row of a function with an output port parameter gives the port as `[]` in its key and
/// expects the record `{ result:, <port>: [lines] }` (DESIGN.md sec:ports, "A test table gives
/// a port its values", whose example is the first row). Red before green: each table was
/// refused, "a test table gives a function values, never a port"
/// (PORT-table-param).
#[test]
fn a_test_table_gives_a_port_its_values() {
    let main = "main(m: MainArgs) {\n  _ = greet(\"x\", out: m.stdout);\n}\n";
    let src = format!(
        "greet(positional name: String, out: Lines) {{ out <- \"hi ${{name}}\"; }}\n\
         test {{\n  (\"a\", []) -> {{ result: (), out: [\"hi a\"] }},\n  \
         (\"b\", []) -> {{ out: [\"hi b\"], result: () }},\n}}\n{main}"
    );
    assert_eq!(row_failures(&src), [None, None], "{src}");
    // The lines are compared: a wrong line, a missing one, or a port left out of the record
    // (expected to be pushed nothing) fails the row.
    for want in [r#"["hi b"]"#, r#"["hi a", "hi a"]"#, "[]"] {
        let src = format!(
            "greet(positional name: String, out: Lines) {{ out <- \"hi ${{name}}\"; }}\n\
             test {{\n  (\"a\", []) -> {{ result: (), out: {want} }},\n}}\n{main}"
        );
        let failures = row_failures(&src);
        assert!(
            failures.len() == 1 && failures[0].as_ref().is_some_and(|f| f.contains("hi a")),
            "{want}: {failures:?}"
        );
    }
    let src = format!(
        "greet(positional name: String, out: Lines) {{ out <- \"hi ${{name}}\"; }}\n\
         test {{\n  (\"a\", []) -> {{ result: () }},\n}}\n{main}"
    );
    assert!(row_failures(&src)[0].is_some(), "{src}");
    // A result beside the push, and a family pushed: one line per entry, as `main` writes it.
    let src = format!(
        "greet(positional name: String, out: Lines) {{\n  out <- [\"hi\", name, name];\n  \
         return 7;\n}}\n\
         test {{\n  (\"a\", []) -> {{ result: 7, out: [\"hi\", \"a\", \"a\"] }},\n}}\n{main}"
    );
    assert_eq!(row_failures(&src), [None], "{src}");
    // Two port parameters where `main` writes one output: each port parameter of a row has a
    // port of its own (`row.out1` past `main`'s).
    let src = "two(positional s: String, a: Lines, b: Lines) { a <- s; b <- [\"b\", s]; }\n\
               test {\n  (\"x\", [], []) -> { result: (), a: [\"x\"], b: [\"b\", \"x\"] },\n  \
               (\"y\", [], []) -> { result: (), b: [\"b\", \"y\"], a: [\"y\"] },\n}\n\
               main(m: MainArgs) {\n  m.stdout <- \"z\";\n}\n";
    let failures = row_failures(src);
    assert_eq!(failures, [None, None], "{src}");
    // The native back end runs the rows alike, its pushes landing in the row's world.
    let native = zed_native::through(zedc::build::Mode::Debug, true);
    let outcomes = zedc::testing::test_through(src, &native);
    let failures: Vec<_> = outcomes.into_iter().map(|o| o.failure).collect();
    assert_eq!(failures, [None, None], "{src}");
}

/// What a row of a function with an output port parameter must be: `[]` for the port in its
/// key, and a record of `result` and the ports, each once.
#[test]
fn a_test_row_of_a_port_function_is_checked_for_its_shape() {
    let src = |row: &str| {
        format!(
            "greet(positional name: String, out: Lines) {{ out <- \"hi ${{name}}\"; }}\n\
             test {{\n  {row},\n}}\n\
             main(m: MainArgs) {{\n  _ = greet(\"x\", out: m.stdout);\n}}\n"
        )
    };
    let cases = [
        (
            "key",
            r#"("a", ["hi"]) -> { result: (), out: ["hi a"] }"#,
            "3:9: A test key gives the output port `out` of `greet` as `[]`, the port before \
             the row pushes to it.",
        ),
        (
            "not_record",
            r#"("a", []) -> ()"#,
            "3:16: A row of `greet`, which pushes to its parameter `out`, expects a record: \
             `{ result: …, out: […] }`.",
        ),
        (
            "unknown",
            r#"("a", []) -> { result: (), out: ["hi a"], err: [] }"#,
            "3:50: `err` is not an output port of `greet`: the record of a row of it has the \
             fields `result` and `out`.",
        ),
        (
            "twice",
            r#"("a", []) -> { result: (), out: ["hi a"], out: [] }"#,
            "3:45: the field `out` is given twice, and each field is given once. Remove one of \
             the two.",
        ),
        (
            "no_result",
            r#"("a", []) -> { out: ["hi a"] }"#,
            "3:16: A row of `greet` gives its result as the field `result`: \
             `{ result: …, out: […] }`.",
        ),
    ];
    for (name, row, want) in cases {
        assert_eq!(rejected(name, &src(row)), want, "{row}");
    }
}

/// A push to a name that is no output port is rejected when the program is checked; before,
/// `x <- "a";` with `x` a binding was accepted and failed when run, the run having no port `x`.
#[test]
fn a_push_to_a_name_that_is_no_port_is_rejected() {
    let src = "main(m: MainArgs) {\n  x = 1;\n  x <- \"a\";\n}\n";
    assert_eq!(
        rejected("binding", src),
        "3:3: Invalid push to `x`, a binding: a push goes to a port or a declared accumulator."
    );
}

/// The port is still pushed once per run: a helper's push and `main`'s to one port are two,
/// rejected at the second when the program is checked (DESIGN.md step L1.19, "a call of a
/// function with an output port parameter counts the pushes the function's body makes to that
/// parameter"; plan row PORT-push-twice-static). Before, the run stopped, "`m.stdout` was
/// pushed to 2 times in this run". A helper that pushes in each branch of an `if`, called once,
/// pushes once; called twice, twice; and a helper that pushes twice is rejected in its body.
#[test]
fn a_port_given_to_a_helper_is_still_pushed_once() {
    let after = ", and a port takes one push per run, which holds everything it writes.";
    assert_eq!(
        rejected(
            "twice_through_a_helper",
            &with_say("_ = say(\"a\", out: m.stdout);\n  m.stdout <- \"b\";"),
        ),
        format!(
            "5:3: `m.stdout` may be pushed to twice in one run: by `say(\"a\", out: m.stdout)` \
             and then by `m.stdout <- \"b\";`{after}"
        )
    );
    let either = "pick(positional c: bool, out: Lines) {\n  if c { out <- \"y\"; } else { out <- \
                  \"n\"; };\n}\n\nmain(m: MainArgs) {\n  ";
    let once = format!("{either}_ = pick(true, out: m.stdout);\n}}\n");
    let out = run("helper_branches_once", &once, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "y\n"),
        "{}",
        out.stderr
    );
    let twice =
        format!("{either}_ = pick(true, out: m.stdout);\n  _ = pick(false, out: m.stdout);\n}}\n");
    assert!(
        rejected("helper_branches_twice", &twice).starts_with(
            "7:7: `m.stdout` may be pushed to twice in one run: by `pick(true, out: m.stdout)` \
             and then by `pick(false, out: m.stdout)`"
        ),
        "{twice}"
    );
    let inside = "both(out: Lines) {\n  out <- \"a\";\n  out <- \"b\";\n}\n\nmain(m: MainArgs) \
                  {\n  _ = both(out: m.stdout);\n}\n";
    assert_eq!(
        rejected("helper_pushes_twice", inside),
        format!(
            "3:3: `out` may be pushed to twice in one run: by `out <- \"a\";` and then by `out \
             <- \"b\";`{after}"
        )
    );
}

/// A chain of `n` helpers, each passing its port to the next, the last pushing, and a `main`
/// that gives the last its `m.stdout`.
pub(super) fn helper_chain(n: usize) -> String {
    let mut text = String::from("h0(positional s, out: Lines) { out <- s; }\n");
    for i in 1..n {
        text.push_str(&format!(
            "h{i}(positional s, out: Lines) = h{}(s, out: out);\n",
            i - 1
        ));
    }
    text.push_str(&format!(
        "main(m: MainArgs) {{\n  _ = h{}(\"x\", out: m.stdout);\n}}\n",
        n - 1
    ));
    text
}

/// A chain of `n` helpers as [`helper_chain`] builds it, but each body above the first, and
/// `main`, an expression statement that calls the one below: `h1(…) { h0(s, out: out); }`.
pub(super) fn statement_chain(n: usize) -> String {
    let mut text = String::from("h0(positional s, out: Lines) { out <- s; }\n");
    for i in 1..n {
        text.push_str(&format!(
            "h{i}(positional s, out: Lines) {{ h{}(s, out: out); }}\n",
            i - 1
        ));
    }
    text.push_str(&format!(
        "main(m: MainArgs) {{\n  h{}(\"x\", out: m.stdout);\n}}\n",
        n - 1
    ));
    text
}

/// A function of `n` output port parameters, each pushed in an `if` of its own, and with
/// `twice`, the last pushed again after them; `main` calls nothing.
pub(super) fn wide_ports(n: usize, twice: bool) -> String {
    let params: Vec<String> = (0..n).map(|i| format!("o{i}: Lines")).collect();
    let mut text = format!("w(positional c: bool, {}) {{\n", params.join(", "));
    for i in 0..n {
        text.push_str(&format!("  if c {{ o{i} <- \"a\"; }};\n"));
    }
    if twice {
        text.push_str(&format!("  o{} <- \"b\";\n", n - 1));
    }
    text.push_str("}\n\nmain(m: MainArgs) {\n  m.stdout <- \"x\";\n}\n");
    text
}

/// Checks a [`wide_ports`] of `n`: accepted, or with `twice` one error, at the last push.
pub(super) fn counts_the_wide_ports(
    text: &str,
    stmts: &[zedc::ast::Stmt],
    res: &zedc::resolve::Resolution,
    n: usize,
    twice: bool,
) {
    let info = check_text(stmts, res, Some(text));
    let errors: Vec<&str> = (info.errors.iter())
        .map(|e| e.message.as_str())
        .filter(|m| m.contains("may be pushed"))
        .collect();
    let want = if twice {
        vec![format!("`o{}` may be pushed to twice in one run", n - 1)]
    } else {
        Vec::new()
    };
    assert_eq!(errors.len(), want.len(), "{:?}", info.errors);
    for (e, w) in errors.iter().zip(&want) {
        assert!(e.starts_with(w.as_str()), "{e}");
    }
    if !twice {
        assert!(info.errors.is_empty(), "{:?}", info.errors);
    }
}

/// Many ports each pushed in an `if` are counted once each, and a push again after them is
/// found (`bench::many_ports_each_pushed_in_an_if_are_counted_in_n_log_n_time` at a small
/// size).
#[test]
fn many_ports_each_pushed_in_an_if_are_counted() {
    for twice in [false, true] {
        let text = wide_ports(4, twice);
        let (stmts, res) = resolved(&text);
        counts_the_wide_ports(&text, &stmts, &res, 4, twice);
    }
}

/// Checks a [`statement_chain`] of `n`: each of its `n` expression statements writes, so it is
/// accepted.
pub(super) fn accepts_the_statements(
    text: &str,
    stmts: &[zedc::ast::Stmt],
    res: &zedc::resolve::Resolution,
) {
    let info = check_text(stmts, res, Some(text));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
}

#[test]
fn a_chain_of_expression_statements_passing_a_port_writes_once() {
    let text = statement_chain(3);
    let (stmts, res) = resolved(&text);
    accepts_the_statements(&text, &stmts, &res);
    let out = run("stmt_chain", &text, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str(), out.stderr.as_str()),
        (0, "x\n", "")
    );
}

/// The output ports of a [`helper_chain`] of `n`: each parameter is an output port, decided
/// once, and none is an error.
pub(super) fn finds_the_ports(
    text: &str,
    stmts: &[zedc::ast::Stmt],
    res: &zedc::resolve::Resolution,
    n: usize,
) {
    let t = Tables::with_text(stmts, res, Some(text));
    let found = ports(&t);
    assert_eq!((found.params.len(), found.errors.len()), (n, 0));
}

/// A chain of helpers passing a port is accepted, each parameter is found an output port, and
/// the run writes once through the chain
/// (`bench::a_chain_of_helpers_passing_a_port_scales` at a small size).
#[test]
fn a_chain_of_helpers_passing_a_port_writes_once() {
    let text = helper_chain(3);
    let (stmts, res) = resolved(&text);
    let info = check_text(&stmts, &res, Some(&text));
    assert!(info.errors.is_empty(), "{:?}", info.errors);
    finds_the_ports(&text, &stmts, &res, 3);
    let out = run("helper_chain", &text, "", &[]);
    assert_eq!(
        (out.status, out.stdout.as_str()),
        (0, "x\n"),
        "{}",
        out.stderr
    );
}
