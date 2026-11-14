//! A name is defined above every use (DESIGN.md sec:lexical): in a block, a parameter list
//! or a field list, a use above its definition is rejected in the row "Name used above its
//! definition"; a unit's top level declares in any order.

use zedc::ast::unit;
use zedc::lex::lex_fence;
use zedc::parse::{TOP, parse};
use zedc::rejection::Row;
use zedc::resolve::resolve_text;

use super::{at, run};

/// The errors of the unit `text`, resolved with its text so the messages give line numbers,
/// each as `message [text]` with its notes after it as `; note [text]`. Errors in other rows
/// are left out: a struct declaration is a later form at L1, and its fields resolve all the
/// same.
fn above(text: &str) -> Vec<String> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    let stmts = unit(text, &tokens, &tree).unwrap();
    let errors = resolve_text(&stmts, Some(text)).err().unwrap_or_default();
    errors
        .iter()
        .filter(|e| e.row == Some(Row::NameAboveDefinition))
        .map(|e| {
            let mut out = format!("{} [{}]", e.message, &text[e.span.start..e.span.end]);
            for n in &e.notes {
                out += &format!("; {} [{}]", n.text, &text[n.span.start..n.span.end]);
            }
            out
        })
        .collect()
}

const BLOCK: &str = "`b` is used on line 2, above its definition on line 3 [b]; in a block a name is \
                     used only below its definition, so that the text reads from the top; the \
                     order of the lines changes no result, since evaluation follows the \
                     dependencies, so moving the definition above its first use changes nothing \
                     else";

#[test]
fn a_block_binding_used_above_its_definition_is_rejected() {
    let text = "f(n) {\n  a = b + 1;\n  b = n * 2;\n  a\n}\n";
    assert_eq!(
        above(text),
        [format!(
            "{BLOCK} [b]; `b` is used here, above its definition [b]; \
             the definition of `b`, below its first use [b = n * 2;]; \
             repair: move `b = n * 2;` above line 2, where `b` is first used [b = n * 2;]"
        )]
    );
    // The same block in the order the repair gives resolves.
    let fixed = "f(n) {\n  b = n * 2;\n  a = b + 1;\n  a\n}\n";
    assert_eq!(at(fixed, "b", 1), ["binding b = n * 2;"]);
}

#[test]
fn each_binding_is_reported_once_at_its_first_use() {
    let text = "f(n) {\n  a = b + b;\n  c = b;\n  b = n;\n  a + c\n}\n";
    let errors = above(text);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].starts_with("`b` is used on line 2, above its definition on line 4 ["));
    // The move puts `b` above line 2, so both uses are below it.
    assert!(
        errors[0].contains("repair: move `b = n;` above line 2"),
        "{errors:?}"
    );
}

#[test]
fn a_use_inside_a_nested_block_or_lambda_is_checked_against_the_outer_binding() {
    for text in [
        "f(n) {\n  a = { c = b; c + 1 };\n  b = n;\n  a\n}\n",
        "f(n) {\n  g = x -> x + b;\n  b = n;\n  g(1)\n}\n",
    ] {
        let errors = above(text);
        assert_eq!(errors.len(), 1, "{text}");
        assert!(errors[0].starts_with("`b` is used on line 2, above its definition on line 3 ["));
    }
}

#[test]
fn a_statement_over_several_lines_is_moved_above_its_first_line() {
    let text = "f(n) {\n  a = 1 +\n    t;\n  t = n;\n  a\n}\n";
    let errors = above(text);
    assert!(
        errors[0].contains(
            "repair: move `t = n;` above line 2, where the statement that first uses `t` begins"
        ),
        "{errors:?}"
    );
}

#[test]
fn a_definition_over_several_lines_is_named_by_its_lines() {
    let text = "f(n) {\n  a = t;\n  t = n +\n    1;\n  a\n}\n";
    let errors = above(text);
    assert!(
        errors[0].contains("repair: move lines 3 to 4, the definition of `t`, above line 2"),
        "{errors:?}"
    );
}

#[test]
fn a_move_that_would_put_a_definition_above_what_it_reads_is_not_offered() {
    // `b` reads `c`, which `a` defines after reading `b`: no order of the lines works.
    let text = "f(n) {\n  a = b;\n  c = a;\n  b = c;\n  n\n}\n";
    let errors = above(text);
    assert!(!errors[0].contains("repair:"), "{errors:?}");
}

#[test]
fn a_parameter_default_naming_a_later_parameter_is_rejected() {
    let text = "total(n, k = m, m = 2) = n + k + m;\n";
    assert_eq!(
        above(text),
        [
            "`m` is used on line 1, before its definition later on that line [m]; in a parameter \
          list a name is used only below its definition, so that the text reads from the \
          top; the order of the parameters changes no result, since evaluation follows the \
          dependencies, so moving the parameter above its first use changes nothing else [m]; \
          `m` is used here, above its definition [m]; the parameter `m`, below its first use \
          [m = 2]; repair: move `m = 2` in front of `k = m` [m = 2]"
        ]
    );
    let fixed = "total(n, m = 2, k = m) = n + k + m;\n";
    assert_eq!(at(fixed, "m", 1), ["param m = 2"]);
}

#[test]
fn a_field_default_naming_a_later_field_is_rejected() {
    // A field refinement naming a later field is the same check; refinements are built from
    // L10.4b on (`int[lo..]` and `where` are later forms here), and its test covers them.
    let errors = above("struct Box { h: f64 = w, w: f64 }\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("in a field list a name is used only below its definition"));
    assert!(
        errors[0].ends_with("repair: move `w: f64` in front of `h: f64 = w` [w: f64]"),
        "{errors:?}"
    );
    assert_eq!(
        above("struct Box { w: f64, h: f64 = w }\n"),
        Vec::<String>::new()
    );
}

#[test]
fn the_top_level_declares_in_any_order() {
    assert!(run("a = b + 1;\nb = 2;\n").is_ok());
}

#[test]
fn a_name_bound_again_in_an_inner_block_is_its_own_binding() {
    // The inner `b` is used below the inner definition; the outer `b` is above both.
    let text = "f(n) {\n  b = n;\n  a = { b = 2; b + 1 };\n  a + b\n}\n";
    assert_eq!(at(text, "b", 2), ["binding b = 2;"]);
    assert_eq!(at(text, "b", 3), ["binding b = n;"]);
}

#[test]
fn a_binding_that_names_itself_is_not_this_row() {
    let errors = run("f(n) {\n  a = a + 1;\n  a\n}\n")
        .err()
        .unwrap_or_default();
    assert!(
        !errors.iter().any(|e| e.contains("above its definition")),
        "{errors:?}"
    );
}

/// The statements of the unit `text`.
fn parsed(text: &str) -> Vec<zedc::ast::Stmt> {
    let tokens = lex_fence(text).unwrap();
    let tree = parse(text, &tokens, "Unit", TOP).unwrap();
    unit(text, &tokens, &tree).unwrap()
}

/// A block of `n` bindings, each reading the one before it, in order or with each line using
/// the next, which is below it; and a parameter list of `n` defaults, each naming the next.
pub(super) fn chains(n: usize) -> [(String, Vec<zedc::ast::Stmt>); 3] {
    let ordered = (1..n)
        .map(|i| format!("  b{i} = b{} + 1;\n", i - 1))
        .collect::<String>();
    let reversed = (0..n - 1)
        .map(|i| format!("  b{i} = b{} + 1;\n", i + 1))
        .collect::<String>();
    let params = (0..n - 1)
        .map(|i| format!("p{i} = p{}, ", i + 1))
        .collect::<String>();
    [
        format!("f(x) {{\n  b0 = x;\n{ordered}  b{}\n}}\n", n - 1),
        format!("f(x) {{\n{reversed}  b{} = x;\n  b0\n}}\n", n - 1),
        format!("f({params}p{} = 1) = p0;\n", n - 1),
    ]
    .map(|text| {
        let stmts = parsed(&text);
        (text, stmts)
    })
}

/// What each of the [`chains`] of `n` is, and how many errors its resolution reports: none in
/// order, and one for each use above its definition.
pub(super) fn chain_errors(n: usize) -> [(&'static str, usize); 3] {
    [
        ("a block of n bindings in order", 0),
        ("a block of n bindings each used above it", n - 1),
        (
            "a parameter list of n defaults each naming a later one",
            n - 1,
        ),
    ]
}

/// Resolves `stmts` of `text`, the chain `what`, and checks that it reports `errors` errors.
pub(super) fn reports(text: &str, stmts: &[zedc::ast::Stmt], what: &str, errors: usize) {
    let got = resolve_text(stmts, Some(text)).err().unwrap_or_default();
    assert_eq!(got.len(), errors, "{what}");
}

/// Short chains in order resolve, and in reverse order report each use above its definition;
/// `bench/above.rs` holds the timing.
#[test]
fn short_chains_in_and_out_of_order_report_each_use_above_its_definition() {
    for n in [1, 2, 9] {
        for ((text, stmts), (what, errors)) in chains(n).iter().zip(chain_errors(n)) {
            reports(text, stmts, what, errors);
        }
    }
}
