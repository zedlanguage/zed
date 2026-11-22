//! A statement at a unit's top level (plan row TOP-statements-reject; DESIGN.md sec:units, "A
//! unit's top level holds declarations only", and sec:diagnostics, row "Statement at a unit's
//! top level"): each of the eight kinds the grammar's `Decl` takes is rejected with the row,
//! the statement quoted, why the top level holds declarations, and the statement moved into
//! `main` as code; a push also names its port, and an expression statement offers to keep its
//! value or delete it.

use zedc::rejection::Row;

/// The program: `item` at the top level, then `main`.
fn unit(item: &str) -> String {
    format!("{item}\nmain(m: MainArgs) {{\n    m.stdout <- \"hi\";\n}}\n")
}

/// The errors of building `src`'s syntax tree: each one's row, headline and notes.
fn errors(src: &str) -> Vec<(Option<Row>, String, Vec<String>)> {
    let tokens = zedc::lex::lex_fence(src).expect("the text lexes");
    let tree = zedc::parse::parse(src, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
    let errs = zedc::ast::unit_all_errors(src, &tokens, &tree).expect_err(src);
    errs.into_iter()
        .map(|e| {
            (
                e.row,
                e.message,
                e.notes.into_iter().map(|n| n.text).collect(),
            )
        })
        .collect()
}

const WHY: &str = "a unit's top level holds declarations, which take any order and run in no \
                   frame; a statement has an order and runs in a frame, so it stands in a body";

/// The one error of `item` at the top level, which is `stmt`: the row, the headline and the
/// notes, the first two of which are why and `extra`, and the last the repair moving it.
fn rejected_with(item: &str, stmt: &str, extra: &[String]) {
    let src = unit(item);
    let moved = format!("main(m: MainArgs) {{ {stmt} }}");
    let mut notes = vec![WHY.to_string()];
    notes.extend(
        extra
            .iter()
            .take_while(|n| !n.starts_with("repair"))
            .cloned(),
    );
    notes.push(format!("repair: `{moved}`"));
    notes.extend(
        extra
            .iter()
            .skip_while(|n| !n.starts_with("repair"))
            .cloned(),
    );
    assert_eq!(
        errors(&src),
        [(
            Some(Row::TopLevelStatement),
            format!(
                "Statement at the top level of the unit: `{stmt}`. Move it into the body of \
                 `main`, as in `{moved}`."
            ),
            notes
        )],
        "{src}"
    );
}

#[test]
fn a_push_to_a_name_that_is_no_port_at_the_top_level_is_rejected() {
    rejected_with(
        "log <- \"loaded\";",
        "log <- \"loaded\";",
        &[
            "`log` is no port here: a program's ports are the fields of `m`, the parameter of \
           `main`, as `m.stdout`"
                .into(),
        ],
    );
}

#[test]
fn a_push_to_a_port_of_main_at_the_top_level_is_rejected() {
    rejected_with(
        "m.stdout <- \"x\";",
        "m.stdout <- \"x\";",
        &[
            "`m.stdout` is a field of `m`, the parameter of `main`, and is a port only in \
           `main`'s body"
                .into(),
        ],
    );
}

#[test]
fn emit_at_the_top_level_is_rejected() {
    rejected_with("emit 1;", "emit 1;", &[]);
}

/// The one error of the loop statement `stmt`, of keyword `kw`, at the top level: it stands
/// only in a `loop` or `for` body (DESIGN.md, the generation forms), so the repair is a move
/// into such a loop in `main`, in words, or deleting it, never `main(m) { stmt }`, which is
/// rejected again.
fn loop_statement_rejected(stmt: &str, kw: &str) {
    let src = unit(stmt);
    assert_eq!(
        errors(&src),
        [(
            Some(Row::TopLevelStatement),
            format!(
                "Statement at the top level of the unit: `{stmt}`. A `{kw}` statement stands \
                 in the body of a `loop` or `for`, and none is around it here. Move it into a \
                 `loop` or `for` in the body of `main`, or delete it."
            ),
            vec![
                WHY.to_string(),
                "repair: delete the statement; no loop is around it".to_string()
            ]
        )],
        "{src}"
    );
}

#[test]
fn while_at_the_top_level_is_rejected() {
    loop_statement_rejected("while true;", "while");
}

#[test]
fn until_at_the_top_level_is_rejected() {
    loop_statement_rejected("until true;", "until");
}

#[test]
fn break_at_the_top_level_is_rejected() {
    loop_statement_rejected("break;", "break");
}

/// The move into `main` that a loop statement's repair describes is legal: inside a `loop`
/// in `main`'s body each of the three is accepted, where `main(m) { break; }` is not.
#[test]
fn a_loop_statement_moved_into_a_loop_in_main_is_accepted() {
    for stmt in ["while true;", "until true;", "break;"] {
        let src = format!(
            "main(m: MainArgs) {{\n    sim = loop {{\n        {stmt}\n    }};\n    \
             m.stdout <- \"hi\";\n}}\n"
        );
        let tokens = zedc::lex::lex_fence(&src).expect("the text lexes");
        let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
        assert!(
            zedc::ast::unit_all_errors(&src, &tokens, &tree).is_ok(),
            "{src}"
        );
    }
}

#[test]
fn return_at_the_top_level_is_rejected() {
    rejected_with("return 1;", "return 1;", &[]);
}

#[test]
fn an_if_statement_at_the_top_level_is_rejected() {
    let stmt = "if true { m.stdout <- \"a\"; };";
    rejected_with(stmt, stmt, &[]);
}

#[test]
fn an_expression_statement_at_the_top_level_is_rejected() {
    let src = unit("total = 3;\ntotal * 10;");
    let errs = errors(&src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    let moved = "main(m: MainArgs) { total * 10; }";
    assert_eq!(
        errs[0],
        (
            Some(Row::TopLevelStatement),
            format!(
                "Statement at the top level of the unit: `total * 10;`. Move it into the body \
                 of `main`, as in `{moved}`."
            ),
            vec![
                WHY.to_string(),
                format!("repair: `{moved}`"),
                "repair: `value = total * 10;`, to keep the value".into(),
                "repair: delete the statement; nothing reads its value".into(),
            ]
        )
    );
}

/// `x with f(…);` at the top level attaches a facet to a collection, which is declaration
/// metadata (DESIGN.md, "Stored collections": "attached with `with`"), so it is not a
/// statement: its one error is the facet's later layer, as for EXAMPLES.md's
/// `orders with store(…);`. A struct update `p with { … };` is still a statement.
#[test]
fn a_facet_attached_at_the_top_level_is_a_declaration_and_a_struct_update_is_not() {
    let src = unit("orders with store(kv(\"localhost\"));");
    let errs = errors(&src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_ne!(errs[0].0, Some(Row::TopLevelStatement), "{errs:?}");
    assert!(zed_tests::is_not_yet(&errs[0].1), "{errs:?}");
    let errs = errors(&unit("p = 1;\np with { x = 1 };"));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(errs[0].0, Some(Row::TopLevelStatement), "{errs:?}");
}

#[test]
fn local_and_annotations_do_not_hide_a_statement_and_declarations_stay() {
    // A statement behind `local` is still one.
    let errs = errors(&unit("local return 1;"));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(errs[0].0, Some(Row::TopLevelStatement));
    // Declarations at the top level are accepted.
    let src = unit("x = 1;\nf(a: int) = a + x;\ntype T = int;");
    let tokens = zedc::lex::lex_fence(&src).expect("the text lexes");
    let tree = zedc::parse::parse(&src, &tokens, "Unit", zedc::parse::TOP).expect("it parses");
    assert!(zedc::ast::unit_all_errors(&src, &tokens, &tree).is_ok());
}

#[test]
fn a_statement_on_two_lines_is_not_quoted() {
    let errs = errors(&unit("if true {\n    m.stdout <- \"a\";\n};"));
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert_eq!(
        errs[0].1,
        "Statement at the top level of the unit. Move it into the body of `main`."
    );
    assert_eq!(errs[0].2, [WHY]);
}

#[test]
fn the_repair_names_mains_own_header() {
    let src = "x <- 1;\nmain(args: MainArgs) {\n    args.stdout <- \"hi\";\n}\n";
    let errs = errors(src);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(
        errs[0]
            .1
            .ends_with("as in `main(args: MainArgs) { x <- 1; }`."),
        "{errs:?}"
    );
    assert!(errs[0].2[1].contains("the fields of `args`"), "{errs:?}");
}
