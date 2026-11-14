//! Row "A loop variable not updated on every path of a step" (DESIGN.md sec:generations) over
//! the parts of an expression the other tests leave out: each entry of a map display, each field
//! of a record display, each value of a `with` update, a string hole and the operand of `is` run
//! on every path, so a `*.` update in one counts; the default of an `else` with an atom pattern,
//! with or without a payload it binds, runs on some paths only. Row "`initial` outside a loop"
//! for an `initial` statement in a block nested in the loop's body.

use super::initial::{accepted, notes, refusal};
use zedc::rejection::Row;

/// A loop over `t` whose body is `body`, one statement to a line.
fn t_loop(body: &[&str]) -> String {
    let lines: String = body.iter().map(|s| format!("  {s}\n")).collect();
    format!("r = loop t {{\n  while t < 3;\n{lines}}};\n")
}

#[test]
fn an_update_in_a_part_run_on_every_path_counts() {
    for update in [
        "x' = { c*.a() -> 1 };",
        "x' = { 1 -> c*.a() };",
        "x' = { k: c*.a() };",
        "x' = q with { k = c*.a() };",
        "x' = \"${c*.a()}\";",
        "x' = c*.a() is int;",
    ] {
        accepted(&t_loop(&["initial c = 0;", update]));
    }
}

#[test]
fn an_update_in_the_default_of_an_else_with_an_atom_pattern_is_on_some_paths() {
    for update in [
        "x' = f(t) else #e -> c*.a();",
        "x' = f(t) else #e(v) -> c*.a() + v;",
        "x' = f(t) else #e(k: v) -> c*.a() + v;",
    ] {
        let src = t_loop(&["initial c = 0;", update]);
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::NotEveryPath), "{src}");
        assert_eq!(
            e.message,
            "Not updated on every path of a step: `c*.a` updates `c` only in the default of the \
             `else`. Try `initial c = 0 with carryForward;` instead.",
            "{src}"
        );
        assert!(
            notes(&src, &e).contains(
                &"`c*.a` updates `c` only on the paths through the default of the `else` [c*.a]"
                    .to_string()
            ),
            "{src}"
        );
    }
}

#[test]
fn an_initial_statement_in_a_block_inside_the_loop_body_is_refused() {
    for src in [
        t_loop(&[
            "x' = if t > 1 { initial c = 0; 1 } else { 2 };",
            "c' = c + 1;",
        ]),
        t_loop(&["x' = { initial c = 0; 1 };", "c' = c + 1;"]),
    ] {
        let e = refusal(&src);
        assert_eq!(e.row, Some(Row::InitialOutsideLoop), "{src}");
        assert_eq!(
            e.message,
            "`initial c = 0;` stands in a block inside the body of a `loop`, not among the \
             statements of the loop's body itself. An `initial` statement gives the value of `c` \
             before step 0 of a loop that updates `c`, so it is written among the statements of \
             that loop's body, and it has no meaning where no loop updates `c`.",
            "{src}"
        );
        assert_eq!(
            notes(&src, &e),
            [
                "the block it stands in, inside the body of the loop [{ initial c = 0; 1 }]",
                "the loop, whose body's own statements may include it [loop t { …]",
                "repair: `c = 0;`, a plain binding [initial c = 0;]",
            ],
            "{src}"
        );
    }
}
